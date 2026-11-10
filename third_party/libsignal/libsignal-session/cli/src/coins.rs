// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// This file is ORIGINAL code written for this repository; it copies no upstream source. See
// `third_party/libsignal/README.md`.

//! The call's coins: the bytes of the party's `coins` file, which libsignal draws as its
//! randomness, in order, and then zeros.
//!
//! libsignal draws them through the `Coins` CSPRNGs of the ratchet and handshake crates
//! (`ratchet/`, `handshake/`). Those are zero-sized and call [`signal_session_coins_fill`], which
//! is here, so the coins are this module's state: [`install`] sets them once, before the call.

use std::ptr;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering::Relaxed};

/// The coins not drawn yet: `LEFT` bytes from `NEXT`. Empty until `install`, so a draw then gives
/// zeros. (Atomics only so that the statics are safe to share; the process is single-threaded.)
static NEXT: AtomicPtr<u8> = AtomicPtr::new(ptr::dangling_mut());
static LEFT: AtomicUsize = AtomicUsize::new(0);

/// Makes `coins` the call's coins. They must outlive every draw, hence `'static` (`main` leaks the
/// file's bytes, which the process holds until it exits anyway).
pub fn install(coins: &'static [u8]) {
    NEXT.store(coins.as_ptr().cast_mut(), Relaxed);
    LEFT.store(coins.len(), Relaxed);
}

/// Fills `dst[0..len]` with the next `len` coins: the coins not drawn yet, then zeros.
///
/// # Safety
/// `dst` must be valid for writes of `len` bytes, and must not overlap the coins.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn signal_session_coins_fill(dst: *mut u8, len: usize) {
    // SAFETY: `dst` is the caller's (above). `NEXT`/`LEFT` are a suffix of the `'static` slice that
    // `install` stored (or empty), only read here, as `install` stores them before any draw.
    let (dst, coins) = unsafe {
        (
            std::slice::from_raw_parts_mut(dst, len),
            std::slice::from_raw_parts(NEXT.load(Relaxed), LEFT.load(Relaxed)),
        )
    };
    let (now, later) = coins.split_at(len.min(coins.len()));
    dst[..now.len()].copy_from_slice(now);
    dst[now.len()..].fill(0);
    NEXT.store(later.as_ptr().cast_mut(), Relaxed);
    LEFT.store(later.len(), Relaxed);
}
