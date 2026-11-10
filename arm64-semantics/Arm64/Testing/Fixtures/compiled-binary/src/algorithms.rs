// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Rust implementations of classic algorithms compiled to AArch64
//! (`cargo build --release --target aarch64-unknown-linux-gnu`)
//! and exported to `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! for differential and regression testing in `Arm64/Testing/`
//! (exercised concretely by `Arm64/Testing/Regression/UnitTests.lean`).

use alloc::vec::Vec;

/// 1. Binary search (`lower_bound`) over a sorted `Vec<u64>`.
/// Returns the first index `i` in `0..=v.len()` such that `v[i] >= target`
/// (or `v.len()` if all elements are `< target`).
#[inline(never)]
pub unsafe fn vec_binary_search(v: &Vec<u64>, target: u64) -> usize {
    let ptr = v.as_ptr();
    let mut lo: usize = 0;
    let mut hi: usize = v.len();
    while lo < hi {
        let mid = lo + ((hi - lo) >> 1);
        let val = unsafe { *ptr.add(mid) };
        if val < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

/// 2a. Disjoint-Set Union-Find: `uf_find` climbs parent pointers `parent[x]` until reaching
/// a canonical root `r` where `parent[r] == r`.
#[inline(never)]
pub unsafe fn uf_find(parent: *const usize, mut x: usize) -> usize {
    loop {
        let p = unsafe { *parent.add(x) };
        if p == x {
            return x;
        }
        x = p;
    }
}

/// 2b. Disjoint-Set Union-Find: `uf_union` finds the roots of `x` and `y` and links
/// `parent[root_x] = root_y` if they are in different sets, returning the merged root `root_y`.
#[inline(never)]
pub unsafe fn uf_union(parent: *mut usize, mut x: usize, mut y: usize) -> usize {
    loop {
        let px = unsafe { *parent.add(x) };
        if px == x {
            break;
        }
        x = px;
    }
    loop {
        let py = unsafe { *parent.add(y) };
        if py == y {
            break;
        }
        y = py;
    }
    if x != y {
        unsafe {
            *parent.add(x) = y;
        }
    }
    y
}

/// 3. Euclidean Greatest Common Divisor (`gcd_u64`).
#[inline(never)]
pub fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/// 4. Binary Exponentiation (`pow_u64`) via the branchless square-and-multiply algorithm.
#[inline(never)]
pub fn pow_u64(mut base: u64, mut exp: u64) -> u64 {
    let mut acc: u64 = 1;
    while exp != 0 {
        if (exp & 1) != 0 {
            acc = acc.wrapping_mul(base);
        }
        base = base.wrapping_mul(base);
        exp >>= 1;
    }
    acc
}

/// 5. 64-bit FNV-1a hash (`fnv1a_u64`) over a contiguous slice of `u64` words in memory.
#[inline(never)]
pub unsafe fn fnv1a_u64(ptr: *const u64, len: usize) -> u64 {
    let mut hash: u64 = 0xcbf29ce484222325;
    let mut i: usize = 0;
    while i < len {
        let word = unsafe { *ptr.add(i) };
        hash ^= word;
        hash = hash.wrapping_mul(0x100000001b3);
        i += 1;
    }
    hash
}
