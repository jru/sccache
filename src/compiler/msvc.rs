// Copyright 2016 Mozilla Foundation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use ::compiler::{
    Cacheable,
    Compiler,
    CompilerArguments,
    ParsedArguments,
    run_input_output,
};
use local_encoding::{Encoding, Encoder};
use log::LogLevel::Trace;
use mock_command::{
    CommandCreatorSync,
    RunCommand,
};
use std::collections::{HashMap,HashSet};
use std::ffi::OsStr;
use std::fs::File;
use std::io::{
    self,
    Error,
    ErrorKind,
    Write,
};
use std::path::{Path, PathBuf};
use std::process::{self,Stdio};
use tempdir::TempDir;

fn from_local_codepage(bytes: &Vec<u8>) -> io::Result<String> {
    Encoding::OEM.to_string(bytes)
}

/// Detect the prefix included in the output of MSVC's -showIncludes output.
pub fn detect_showincludes_prefix<T : CommandCreatorSync, U: AsRef<OsStr>>(mut creator: &mut T, exe: U) -> io::Result<String> {
    let tempdir = try!(TempDir::new("sccache"));
    let input = tempdir.path().join("test.c");
    {
        try!(File::create(&input)
             .and_then(|mut f| f.write_all(b"#include <stdio.h>\n")))
    }

    let mut cmd = creator.new_command_sync(&exe);
    cmd.args(&["-nologo", "-showIncludes", "-c", "-Fonul"])
        .arg(&input)
        // The MSDN docs say the -showIncludes output goes to stderr,
        // but that's not true unless running with -E.
        .stdout(Stdio::piped())
        .stderr(Stdio::null());

    if log_enabled!(Trace) {
        trace!("detect_showincludes_prefix: {:?}", cmd);
    }

    let output = try!(run_input_output(cmd, None));
    if output.status.success() {
        let process::Output { stdout: stdout_bytes, .. } = output;
        let stdout = try!(from_local_codepage(&stdout_bytes));
        for line in stdout.lines() {
            if line.ends_with("stdio.h") {
                for (i, c) in line.char_indices().rev() {
                    if c == ' ' {
                        // See if the rest of this line is a full pathname.
                        if Path::new(&line[i+1..]).exists() {
                            // Everything from the beginning of the line
                            // to this index is the prefix.
                            return Ok(line[..i+1].to_owned());
                        }
                    }
                }
            }
        }
    }
    Err(Error::new(ErrorKind::Other, "Failed to detect showIncludes prefix"))
}

pub fn parse_arguments(arguments: &[String]) -> CompilerArguments {
    let mut output_arg = None;
    let mut input_arg = None;
    let mut compiler_args = vec!();
    let mut preproc_args = vec!();
    let mut compilation = false;
    let mut debug_info = false;
    let mut pdb = None;
    let mut depfile = None;

    let mut it = arguments.iter();
    loop {
        match it.next() {
            Some(arg) => {
                match arg {
                    v if v.starts_with("/") | v.starts_with("-") => match &v[1..] {
                        "c" => compilation = true,
                        v if v.starts_with("Fo") => {
                            output_arg = Some(String::from(&v[2..]));
                        },
                        v if v.starts_with("deps") => {
                            depfile = Some(v[4..].to_owned());
                        }
                        // Arguments we can't handle
                        // TODO: support more multi-file outputs.
                        "showIncludes" | "FA" | "Fa" | "Fe" | "Fm" | "Fp" | "FR" | "Fx" => {
                            info!("Cannot cache: Argument {:?} is unsupported", arg);
                            return CompilerArguments::CannotCache;
                        },
                        "Zi" | "ZI" => {
                            debug_info = true;
                            compiler_args.push(arg.clone());
                        }
                        v if v.starts_with("Fd") => {
                            let index_start = if v.len() > 2 && v.as_bytes()[2] == ':' as u8 {3} else {2};
                            pdb = Some(String::from(&v[index_start..]));
                            compiler_args.push(arg.clone());
                        }
                        // Other options.
                        v => {

                            // Special bucket for preprocesor arguments (all take a value)
                            let preproc_switches = ["FI", "I", "D", "U"];
                            let found = preproc_switches.iter().find(|&&a| v.starts_with(a));
                            if let Some(switch) = found {
                                preproc_args.push(arg.clone());

                                //Check if the value is passed as a separate argument
                                if v.len() == switch.len() {
                                    if let Some(value) = it.next() {
                                        preproc_args.push(value.clone());
                                    }
                                }
                            }
                            else {
                                //Any other unrecognized switch goes to the compiler bucket
                                compiler_args.push(arg.clone());
                            }
                        }
                    },
                    response_file if response_file.starts_with('@') => {
                        info!("Cannot cache: Found response file {:?}", response_file);
                        return CompilerArguments::CannotCache;
                    },
                    // Anything else is an input file.
                    _ => {
                        if let Some(first) = input_arg {
                            info!("Cannot cache: More than one input provided. First {:?} and second {:?}", first, arg);
                            // Can't cache compilations with multiple inputs.
                            return CompilerArguments::CannotCache;
                        }
                        input_arg = Some(arg);
                    }
                }
            }
            None => break,
        }
    }
    // We only support compilation.
    if !compilation {
        info!("Cannot cache: Not a compilation command");
        return CompilerArguments::NotCompilation;
    }
    let (input, filestem, extension) = match input_arg {
        Some(i) => {
            let input_path = Path::new(i);
            match input_path.extension().and_then(|e| e.to_str()) {
                Some(e) => (i.to_owned(), input_path.file_stem().unwrap(), e.to_owned()),
                _ => {
                    info!("Cannot cache: Bad or missing source extension for {:?}", i);
                    return CompilerArguments::CannotCache;
                }
            }
        }
        // We can't cache compilation without an input.
        None => {
            info!("Cannot cache: No inputs provided");
            return CompilerArguments::CannotCache;
        },
    };
    let mut outputs = HashMap::new();
    match output_arg {
        // We can't cache compilation that doesn't go to a file
        None => {
            info!("Cannot cache: Compilation output does not go to a file");
            return CompilerArguments::CannotCache;
        },
        Some(o) => {

            //If the path given for the output is a directory, CL will
            //assign it the name of the input but ending with .obj
            let output_path = Path::new(&o);
            if output_path.is_dir() {
                let mut buf = PathBuf::new();
                buf.push(output_path);
                buf.push(filestem);
                buf.set_extension("obj");
                outputs.insert("obj", buf.to_string_lossy().into_owned());
            }
            else {
                outputs.insert("obj", o.to_owned());
            }
            // -Fd is not taken into account unless -Zi is given
            if debug_info {
                match pdb {
                    Some(p) => outputs.insert("pdb", p.to_owned()),
                    None => {
                        info!("Cannot cache: Debug info is enabled but no PDB file is specified");
                        // -Zi without -Fd defaults to vcxxx.pdb (where xxx depends on the
                        // MSVC version), and that's used for all compilations with the same
                        // working directory. We can't cache such a pdb.
                        return CompilerArguments::CannotCache;
                    }
                };
            }
        }
    }
    CompilerArguments::Ok(ParsedArguments {
        input: input,
        extension: extension,
        depfile: depfile,
        outputs: outputs,
        preprocessor_args: preproc_args,
        compiler_args: compiler_args,
    })
}

#[cfg(windows)]
fn normpath(path: &str) -> String {
    use kernel32;
    use std::ffi::OsString;
    use std::os::windows::ffi::OsStringExt;
    use std::ptr;
    use std::os::windows::io::AsRawHandle;
    File::open(path)
        .and_then(|f| {
            let handle = f.as_raw_handle();
            let size = unsafe { kernel32::GetFinalPathNameByHandleW(handle,
                                                         ptr::null_mut(),
                                                         0,
                                                         0)
            };
            if size == 0 {
                return Err(Error::last_os_error());
            }
            let mut wchars = Vec::with_capacity(size as usize);
            wchars.resize(size as usize, 0);
            if unsafe { kernel32::GetFinalPathNameByHandleW(handle,
                                                            wchars.as_mut_ptr(),
                                                            wchars.len() as u32,
                                                            0) } == 0 {
                return Err(Error::last_os_error());
            }
            // The return value of GetFinalPathNameByHandleW uses the
            // '\\?\' prefix.
            let o = OsString::from_wide(&wchars[4..wchars.len() - 1]);
            o.into_string()
                .map(|s| s.replace('\\', "/"))
                .or(Err(Error::new(ErrorKind::Other, "Error converting string")))
        })
        .unwrap_or(path.replace('\\', "/"))
}

#[cfg(not(windows))]
fn normpath(path: &str) -> String {
    path.to_owned()
}

pub fn preprocess<T : CommandCreatorSync>(mut creator: T, compiler: &Compiler, parsed_args: &ParsedArguments, cwd: &str, includes_prefix: &str) -> io::Result<process::Output> {
    let mut cmd = creator.new_command_sync(&compiler.executable);
    cmd.arg("-E")
        .arg(&parsed_args.input)
        .arg("-nologo")
        .args(&parsed_args.preprocessor_args)
        .args(&parsed_args.compiler_args)
        .current_dir(cwd);
    if parsed_args.depfile.is_some() {
        cmd.arg("-showIncludes");
    }

    if log_enabled!(Trace) {
        debug!("preprocess: {:?}", cmd);
    }

    let output = try!(run_input_output(cmd, None));
    if let (Some(ref objfile), &Some(ref depfile)) = (parsed_args.outputs.get("obj"), &parsed_args.depfile) {
        File::create(Path::new(cwd).join(depfile))
            .and_then(move |mut f| {
                try!(write!(f, "{}: {} ", objfile, parsed_args.input));
                let process::Output { status, stdout, stderr: stderr_bytes } = output;
                let stderr = try!(from_local_codepage(&stderr_bytes));
                let mut deps = HashSet::new();
                let mut stderr_bytes = vec!();
                for line in stderr.lines() {
                    if line.starts_with(includes_prefix) {
                        let dep = normpath(line[includes_prefix.len()..].trim());
                        trace!("included: {}", dep);
                        if deps.insert(dep.clone()) && !dep.contains(' ') {
                            try!(write!(f, "{} ", dep));
                        }
                    } else {
                        stderr_bytes.extend_from_slice(line.as_bytes());
                        stderr_bytes.push(b'\n');
                    }
                }
                try!(writeln!(f, ""));
                // Write extra rules for each dependency to handle
                // removed files.
                try!(writeln!(f, "{}:", parsed_args.input));
                let mut sorted = deps.into_iter().collect::<Vec<_>>();
                sorted.sort();
                for dep in sorted {
                    if !dep.contains(' ') {
                        try!(writeln!(f, "{}:", dep));
                    }
                }
                Ok(process::Output { status: status, stdout: stdout, stderr: stderr_bytes })
            })
    } else {
        Ok(output)
    }
}

pub fn compile<T : CommandCreatorSync>(mut creator: T, compiler: &Compiler, preprocessor_output: Vec<u8>, parsed_args: &ParsedArguments, cwd: &str) -> io::Result<(Cacheable, process::Output)> {
    trace!("compile");
    let out_file = try!(parsed_args.outputs.get("obj").ok_or(Error::new(ErrorKind::Other, "Missing object file output")));
    // MSVC doesn't read anything from stdin, so it needs a temporary file
    // as input.
    let tempdir = try!(TempDir::new("sccache"));
    let filename = try!(Path::new(&parsed_args.input).file_name().ok_or(Error::new(ErrorKind::Other, "Missing input filename")));
    let input = tempdir.path().join(filename);
    {
        try!(File::create(&input)
             .and_then(|mut f| f.write_all(&preprocessor_output)))
    }

    let mut cmd = creator.new_command_sync(&compiler.executable);
    cmd.arg("-c")
        .arg(&input)
        .arg(&format!("-Fo{}", out_file))
        .args(&parsed_args.compiler_args)
        .current_dir(cwd);

    if log_enabled!(Trace) {
        trace!("first try to compile, from preprocessed source: {:?}", cmd);
    }

    let output = try!(run_input_output(cmd, None));
    if output.status.success() {
        Ok((Cacheable::Yes, output))
    } else {
        // Sometimes MSVC can't handle compiling from the preprocessed source,
        // so just compile from the original input file.
        let mut cmd = creator.new_command_sync(&compiler.executable);
        cmd.arg("-c")
            .arg(&parsed_args.input)
            .arg(&format!("-Fo{}", out_file))
            .args(&parsed_args.preprocessor_args)
            .args(&parsed_args.compiler_args)
            .current_dir(cwd);

        if log_enabled!(Trace) {
            trace!("second try to compile, from input: {:?}", cmd);
        }

        let output = try!(run_input_output(cmd, None));
        Ok((Cacheable::Yes, output))
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use env_logger;
    use std::collections::HashMap;
    use mock_command::*;
    use ::compiler::*;
    use test::utils::*;

    #[test]
    fn test_detect_showincludes_prefix() {
        match env_logger::init() {
            Ok(_) => {},
            Err(_) => {},
        }
        let mut creator = new_creator();
        let f = TestFixture::new();
        let srcfile = f.touch("stdio.h").unwrap();
        let mut s = srcfile.to_str().unwrap();
        if s.starts_with("\\\\?\\") {
            s = &s[4..];
        }
        let stdout = format!("blah: {}\r\n", s);
        let stderr = String::from("some\r\nstderr\r\n");
        next_command(&creator, Ok(MockChild::new(exit_status(0), &stdout, &stderr)));
        assert_eq!("blah: ", detect_showincludes_prefix(&mut creator, "cl.exe").unwrap());
    }

    fn test_parse_arguments_good_compile(arguments: &[String])
    {
        match parse_arguments(&arguments) {
            CompilerArguments::Ok(ParsedArguments { input, extension, depfile: _depfile, outputs, preprocessor_args, compiler_args }) => {
                assert!(true, "Parsed ok");
                assert_eq!("foo.c", input);
                assert_eq!("c", extension);
                assert_map_contains!(outputs, ("obj", "foo.obj"));
                //TODO: fix assert_map_contains to assert no extra keys!
                assert_eq!(1, outputs.len());
                assert!(preprocessor_args.is_empty());
                assert!(compiler_args.is_empty());
            }
            o @ _ => assert!(false, format!("Got unexpected parse result: {:?}", o)),
        }
    }

    #[test]
    fn test_parse_arguments_simple() {
        test_parse_arguments_good_compile(&stringvec!["-c", "foo.c", "-Fofoo.obj"]);
    }

    #[test]
    fn test_parse_arguments_slash() {
        test_parse_arguments_good_compile(&stringvec!["/c", "foo.c", "/Fofoo.obj"]);
    }

    #[test]
    fn test_parse_arguments_extra() {
        match parse_arguments(&stringvec!["-c", "foo.c", "-foo", "-Fofoo.obj", "-bar"]) {
            CompilerArguments::Ok(ParsedArguments { input, extension, depfile: _depfile, outputs, preprocessor_args, compiler_args }) => {
                assert!(true, "Parsed ok");
                assert_eq!("foo.c", input);
                assert_eq!("c", extension);
                assert_map_contains!(outputs, ("obj", "foo.obj"));
                //TODO: fix assert_map_contains to assert no extra keys!
                assert_eq!(1, outputs.len());
                assert!(preprocessor_args.is_empty());
                assert_eq!(compiler_args, &["-foo", "-bar"]);
            }
            o @ _ => assert!(false, format!("Got unexpected parse result: {:?}", o)),
        }
    }

    #[test]
    fn test_parse_arguments_values() {
        match parse_arguments(&stringvec!["-c", "foo.c", "-FI", "file", "-Fofoo.obj"]) {
            CompilerArguments::Ok(ParsedArguments { input, extension, depfile: _depfile, outputs, preprocessor_args, compiler_args }) => {
                assert!(true, "Parsed ok");
                assert_eq!("foo.c", input);
                assert_eq!("c", extension);
                assert_map_contains!(outputs, ("obj", "foo.obj"));
                //TODO: fix assert_map_contains to assert no extra keys!
                assert_eq!(1, outputs.len());
                assert_eq!(preprocessor_args, &["-FI", "file"]);
                assert!(compiler_args.is_empty());
            }
            o @ _ => assert!(false, format!("Got unexpected parse result: {:?}", o)),
        }
    }

    #[test]
    fn test_parse_arguments_pdb() {
        match parse_arguments(&stringvec!["-c", "foo.c", "-Zi", "-Fdfoo.pdb", "-Fofoo.obj"]) {
            CompilerArguments::Ok(ParsedArguments { input, extension, depfile: _depfile, outputs, preprocessor_args, compiler_args }) => {
                assert!(true, "Parsed ok");
                assert_eq!("foo.c", input);
                assert_eq!("c", extension);
                assert_map_contains!(outputs, ("obj", "foo.obj"), ("pdb", "foo.pdb"));
                //TODO: fix assert_map_contains to assert no extra keys!
                assert_eq!(2, outputs.len());
                assert!(preprocessor_args.is_empty());
                assert_eq!(compiler_args, &["-Zi", "-Fdfoo.pdb"]);
            }
            o @ _ => assert!(false, format!("Got unexpected parse result: {:?}", o)),
        }
    }

    #[test]
    fn test_parse_arguments_empty_args() {
        assert_eq!(CompilerArguments::NotCompilation,
                   parse_arguments(&vec!()));
    }

    #[test]
    fn test_parse_arguments_not_compile() {
        assert_eq!(CompilerArguments::NotCompilation,
                   parse_arguments(&stringvec!["-Fofoo", "foo.c"]));
    }

    #[test]
    fn test_parse_arguments_too_many_inputs() {
        assert_eq!(CompilerArguments::CannotCache,
                   parse_arguments(&stringvec!["-c", "foo.c", "-Fofoo.obj", "bar.c"]));
    }

    #[test]
    fn test_parse_arguments_unsupported() {
        assert_eq!(CompilerArguments::CannotCache,
                   parse_arguments(&stringvec!["-c", "foo.c", "-Fofoo.obj", "-FA"]));

        assert_eq!(CompilerArguments::CannotCache,
                   parse_arguments(&stringvec!["-Fa", "-c", "foo.c", "-Fofoo.obj"]));

        assert_eq!(CompilerArguments::CannotCache,
                   parse_arguments(&stringvec!["-c", "foo.c", "-FR", "-Fofoo.obj"]));
    }

    #[test]
    fn test_parse_arguments_response_file() {
        assert_eq!(CompilerArguments::CannotCache,
                   parse_arguments(&stringvec!["-c", "foo.c", "@foo", "-Fofoo.obj"]));
    }

    #[test]
    fn test_parse_arguments_missing_pdb() {
        assert_eq!(CompilerArguments::CannotCache,
                   parse_arguments(&stringvec!["-c", "foo.c", "-Zi", "-Fofoo.obj"]));
    }

    #[test]
    fn test_compile_simple() {
        let creator = new_creator();
        let f = TestFixture::new();
        let parsed_args = ParsedArguments {
            input: "foo.c".to_owned(),
            extension: "c".to_owned(),
            depfile: None,
            outputs: vec![("obj", "foo.obj".to_owned())].into_iter().collect::<HashMap<&'static str, String>>(),
            preprocessor_args: vec!(),
            compiler_args: vec!(),
        };
        let compiler = Compiler::new(f.bins[0].to_str().unwrap(),
                                     CompilerKind::Msvc { includes_prefix: String::new() }).unwrap();
        // Compiler invocation.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "", "")));
        let (cacheable, _) = compile(creator.clone(), &compiler, vec!(), &parsed_args, f.tempdir.path().to_str().unwrap()).unwrap();
        assert_eq!(Cacheable::Yes, cacheable);
        // Ensure that we ran all processes.
        assert_eq!(0, creator.lock().unwrap().children.len());
    }

    #[test]
    fn test_compile_not_cacheable_pdb() {
        let creator = new_creator();
        let f = TestFixture::new();
        let pdb = f.touch("foo.pdb").unwrap();
        let parsed_args = ParsedArguments {
            input: "foo.c".to_owned(),
            extension: "c".to_owned(),
            depfile: None,
            outputs: vec![("obj", "foo.obj".to_owned()),
                          ("pdb", pdb.to_str().unwrap().to_owned())].into_iter().collect::<HashMap<&'static str, String>>(),
            preprocessor_args: vec!(),
            compiler_args: vec!(),
        };
        let compiler = Compiler::new(f.bins[0].to_str().unwrap(),
                                     CompilerKind::Msvc { includes_prefix: String::new() }).unwrap();
        // Compiler invocation.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "", "")));
        let (cacheable, _) = compile(creator.clone(), &compiler, vec!(), &parsed_args, f.tempdir.path().to_str().unwrap()).unwrap();
        assert_eq!(Cacheable::No, cacheable);
        // Ensure that we ran all processes.
        assert_eq!(0, creator.lock().unwrap().children.len());
    }

    #[test]
    fn test_compile_preprocessed_fails() {
        let creator = new_creator();
        let f = TestFixture::new();
        let parsed_args = ParsedArguments {
            input: "foo.c".to_owned(),
            extension: "c".to_owned(),
            depfile: None,
            outputs: vec![("obj", "foo.obj".to_owned())].into_iter().collect::<HashMap<&'static str, String>>(),
            preprocessor_args: vec!(),
            compiler_args: vec!(),
        };
        let compiler = Compiler::new(f.bins[0].to_str().unwrap(),
                                     CompilerKind::Msvc { includes_prefix: String::new() }).unwrap();
        // First compiler invocation fails.
        next_command(&creator, Ok(MockChild::new(exit_status(1), "", "")));
        // Second compiler invocation succeeds.
        next_command(&creator, Ok(MockChild::new(exit_status(0), "", "")));
        let (cacheable, _) = compile(creator.clone(), &compiler, vec!(), &parsed_args, f.tempdir.path().to_str().unwrap()).unwrap();
        assert_eq!(Cacheable::Yes, cacheable);
        // Ensure that we ran all processes.
        assert_eq!(0, creator.lock().unwrap().children.len());
    }
}
