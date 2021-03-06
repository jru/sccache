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

use cache::{
    Cache,
    CacheRead,
    CacheWrite,
    CacheWriteFuture,
    Storage,
};
use futures::{self,Future};
use std::ffi::OsStr;
use std::fs::{self,File};
use std::io;
use std::path::{Path,PathBuf};
use std::time::Instant;

/// A cache that stores entries at local disk paths.
#[derive(Clone)]
pub struct DiskCache {
    /// The root directory of the cache.
    root: PathBuf,
}

impl DiskCache {
    /// Create a new `DiskCache` rooted at `root`.
    pub fn new<T: AsRef<OsStr>>(root: &T) -> DiskCache {
        DiskCache {
            root: PathBuf::from(root),
        }
    }
}

/// Make a path to the cache entry with key `key`.
fn make_key_path(root: &Path, key: &str) -> PathBuf {
    root.join(&key[0..1]).join(&key[1..2]).join(key)
}

impl Storage for DiskCache {
    fn get(&self, key: &str) -> Cache {
        trace!("DiskCache::get({})", key);
        match File::open(make_key_path(&self.root, key))
            .and_then(CacheRead::from) {
                Err(e) => match e.kind() {
                    // If the file doesn't exist it's just a cache miss.
                    io::ErrorKind::NotFound => Cache::Miss,
                    // Otherwise propogate the error upward.
                    _ => Cache::Error(e),
                },
                Ok(cache_read) => Cache::Hit(cache_read),
            }
    }

    fn start_put(&self, key: &str) -> io::Result<CacheWrite> {
        trace!("DiskCache::start_put({})", key);
        let path = make_key_path(&self.root, key);
        try!(path.parent().ok_or(io::Error::new(io::ErrorKind::Other, "No parent directory?")).and_then(fs::create_dir_all));
        File::create(&path)
            .or_else(|e| {
                error!("Failed to create cache entry `{:?}`: {:?}", path, e);
                Err(e)
            })
            .map(CacheWrite::new)
    }

    fn finish_put(&self, key: &str, entry: CacheWrite) -> CacheWriteFuture {
        // There's not much point in trying to do this on a background
        // thread, since most of the disk I/O should be done already.
        trace!("DiskCache::finish_put({})", key);
        let start = Instant::now();
        // Dropping the ZipWriter is enough to finish it.
        drop(entry);
        futures::finished(Ok(start.elapsed())).boxed()
    }

    fn get_location(&self) -> String {
        format!("Local disk: {:?}", self.root)
    }
}
