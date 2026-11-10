// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Thin `#[inline(never)]` wrappers exposing `hashbrown::HashMap<u64, u64, FxBuildHasher>`
//! with a deterministic `FxHasher64` (`BuildHasher`) for AArch64 machine-code verification.
//!
//! No `RandomState` or `getrandom` is used (`default-features = false` on `hashbrown` v0.17.1).

#![no_std]

use core::hash::{BuildHasher, Hasher};
use hashbrown::HashMap;

/// Deterministic 64-bit FxHasher (`rustc_hash::FxHasher` polynomial multiplier).
///
/// Mixes input words by rotating left 5 bits, XORing, and multiplying by the odd 64-bit
/// constant `0x517cc1b727220a95`, followed by a 32-bit xor-shift finalizer in `finish` so
/// low bits of a single `u64` key also affect both `h1` (low bits, bucket index) and `h2`
/// (top 7 bits, SwissTable control tag).
#[derive(Clone, Copy, Default)]
pub struct FxHasher64 {
    state: u64,
}

const FX_SEED: u64 = 0x517cc1b727220a95;

impl FxHasher64 {
    #[inline]
    fn add_to_hash(&mut self, word: u64) {
        self.state = (self.state.rotate_left(5) ^ word).wrapping_mul(FX_SEED);
    }
}

impl Hasher for FxHasher64 {
    #[inline]
    fn write(&mut self, mut bytes: &[u8]) {
        while bytes.len() >= 8 {
            let (chunk, rest) = bytes.split_at(8);
            self.add_to_hash(u64::from_le_bytes([
                chunk[0], chunk[1], chunk[2], chunk[3], chunk[4], chunk[5], chunk[6], chunk[7],
            ]));
            bytes = rest;
        }
        if !bytes.is_empty() {
            let mut buf = [0u8; 8];
            let mut i = 0;
            while i < bytes.len() {
                buf[i] = bytes[i];
                i += 1;
            }
            self.add_to_hash(u64::from_le_bytes(buf));
        }
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add_to_hash(i);
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.state ^ (self.state >> 32)
    }
}

/// Zero-sized deterministic `BuildHasher` producing a fresh [`FxHasher64`] initialized to `0`.
#[derive(Clone, Copy, Default)]
pub struct FxBuildHasher;

impl BuildHasher for FxBuildHasher {
    type Hasher = FxHasher64;

    #[inline]
    fn build_hasher(&self) -> Self::Hasher {
        FxHasher64 { state: 0 }
    }
}

/// Concrete `HashMap<u64, u64, FxBuildHasher>` instantiation.
pub type U64Map = HashMap<u64, u64, FxBuildHasher>;

/// Create an empty `U64Map` without allocating (`HashMap::with_hasher(FxBuildHasher)`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_new() -> U64Map {
    HashMap::with_hasher(FxBuildHasher)
}

/// Create an empty `U64Map` with space for at least `capacity` elements
/// (`HashMap::with_capacity_and_hasher(capacity, FxBuildHasher)`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_with_capacity(capacity: usize) -> U64Map {
    HashMap::with_capacity_and_hasher(capacity, FxBuildHasher)
}

/// Insert `(k, v)` into `map`, returning the previous value associated with `k` if present.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_insert(map: &mut U64Map, k: u64, v: u64) -> Option<u64> {
    map.insert(k, v)
}

/// Look up key `k` in `map`, returning a copy of its value if present (`map.get(&k).copied()`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_get(map: &U64Map, k: u64) -> Option<u64> {
    map.get(&k).copied()
}

/// Return `true` iff `map` contains a mapping for key `k` (`map.contains_key(&k)`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_contains_key(map: &U64Map, k: u64) -> bool {
    map.contains_key(&k)
}

/// Remove key `k` from `map`, returning the previous value if `k` was present (`map.remove(&k)`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_remove(map: &mut U64Map, k: u64) -> Option<u64> {
    map.remove(&k)
}

/// Return the number of key-value pairs currently in `map` (`map.len()`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_len(map: &U64Map) -> usize {
    map.len()
}

/// Return `true` iff `map` contains no elements (`map.is_empty()`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_is_empty(map: &U64Map) -> bool {
    map.is_empty()
}

/// Clear all elements from `map`, keeping the allocated memory for reuse (`map.clear()`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_clear(map: &mut U64Map) {
    map.clear()
}

/// Drop `map` and deallocate its backing table if allocated (`drop(map)`).
#[unsafe(no_mangle)]
#[inline(never)]
pub fn hashbrown_drop(map: U64Map) {
    drop(map)
}
