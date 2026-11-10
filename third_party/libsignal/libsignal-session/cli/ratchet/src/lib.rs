// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// This file is ORIGINAL code written for this repository; it copies no upstream source. The
// machine code produced by compiling it together with libsignal is a derived work of libsignal
// (`Copyright 2020-2026 Signal Messenger, LLC.`, `SPDX-License-Identifier: AGPL-3.0-only`); see
// `third_party/libsignal/README.md`.

//! The ratchet calls of the `libsignal-cli` CLI: libsignal's `message_encrypt` (`send`) and
//! `message_decrypt_signal` (`recv` of a signal message), each driven to completion by one poll,
//! with the CLI's coins as the CSPRNG.
//!
//! Why a crate of its own: so that the compiled code of these two calls, and of the libsignal
//! code monomorphized into them, is the code that the image's wrapper crate
//! (`libsignal-session`, `../../src/lib.rs`) already compiles for its `session_message_encrypt`
//! and `session_message_decrypt_signal`, up to relocations, so that the proofs about that code
//! carry over. rustc's inlining decisions depend on everything in a codegen unit, and a release
//! build does not share generic instances between crates, so that code comes out the same only
//! if the crate holds the same functions as the image's: these two calls, their RNG, and nothing
//! else. Hence also the RNG's bodies (as the image's `HookRng`) and `poll_once` below, which the
//! handshake crate (`../handshake`) has too.

use std::future::Future;
use std::pin::pin;
use std::task::{Context, Poll, Waker};
use std::time::SystemTime;

use libsignal_protocol::{
    CiphertextMessage, IdentityKeyStore, ProtocolAddress, SessionStore, SignalMessage,
    SignalProtocolError, message_decrypt_signal, message_encrypt,
};

unsafe extern "C" {
    /// Fills `dst[0..len]` with the next coins (defined by the CLI: `../src/coins.rs`).
    fn signal_session_coins_fill(dst: *mut u8, len: usize);
}

/// The CLI's coins as libsignal's CSPRNG: every byte comes from `signal_session_coins_fill`.
pub struct Coins;

impl rand_core::RngCore for Coins {
    fn next_u32(&mut self) -> u32 {
        let mut b = [0u8; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }
    fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }
    fn fill_bytes(&mut self, dst: &mut [u8]) {
        // SAFETY: `dst` is `dst.len()` writable bytes.
        unsafe { signal_session_coins_fill(dst.as_mut_ptr(), dst.len()) }
    }
}

impl rand_core::CryptoRng for Coins {}

/// Polls `fut` once with a no-op waker; `None` means it is pending, which the CLI's stores
/// never are (they answer at once).
#[inline(always)]
fn poll_once<F: Future>(fut: F) -> Option<F::Output> {
    let mut fut = pin!(fut);
    let mut cx = Context::from_waker(Waker::noop());
    match fut.as_mut().poll(&mut cx) {
        Poll::Ready(v) => Some(v),
        Poll::Pending => None,
    }
}

/// `send`: libsignal's `message_encrypt`, which encrypts `ptext` to `remote_address` in the
/// session that `session_store` holds for it.
#[inline(never)]
pub fn encrypt(
    ptext: &[u8],
    remote_address: &ProtocolAddress,
    local_address: &ProtocolAddress,
    session_store: &mut dyn SessionStore,
    identity_store: &mut dyn IdentityKeyStore,
    now: SystemTime,
) -> Option<Result<CiphertextMessage, SignalProtocolError>> {
    poll_once(message_encrypt(
        ptext,
        remote_address,
        local_address,
        session_store,
        identity_store,
        now,
        &mut Coins,
    ))
}

/// `recv` of a signal message: libsignal's `message_decrypt_signal`, which decrypts `ciphertext`
/// from `remote_address` in an existing session.
#[inline(never)]
pub fn decrypt_signal(
    ciphertext: &SignalMessage,
    remote_address: &ProtocolAddress,
    local_address: &ProtocolAddress,
    session_store: &mut dyn SessionStore,
    identity_store: &mut dyn IdentityKeyStore,
) -> Option<Result<Vec<u8>, SignalProtocolError>> {
    poll_once(message_decrypt_signal(
        ciphertext,
        remote_address,
        local_address,
        session_store,
        identity_store,
        &mut Coins,
    ))
}
