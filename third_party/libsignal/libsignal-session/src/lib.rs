// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// Rung 7b image (`docs/LIBSIGNAL_SESSION_7B.md`): entry points into libsignal v0.105.4's REAL 1:1
// session code, compiled for aarch64 with `rust-obj2lean`'s flags and extracted to Lean.
//
// This file is ORIGINAL code written for this repository; it copies no upstream source. The
// machine code produced by compiling it together with libsignal is a derived work of libsignal
// (`Copyright 2020-2026 Signal Messenger, LLC.`, `SPDX-License-Identifier: AGPL-3.0-only`); see
// `third_party/libsignal/README.md`.
//
// What gets verified where:
//
// * Stage 1 (Double Ratchet core) verifies NON-GENERIC upstream methods, which rustc emits into the
//   `libsignal-protocol` object whatever this crate does: `RatchetState::consume_message_key`,
//   `find_receiver_chain_index`, `find_receiver_chain_key`, `ChainKey::{next_chain_key,
//   message_keys}`, `MessageKeyGenerator::generate_keys`, `RootKey::create_chain`,
//   `crypto::hmac_sha256`, ... (`translation.toml` extracts that whole object).
// * Stages 2-3 verify GENERIC upstream code (`try_decrypt_with_state::<HookRng>` with the inlined
//   `dh_ratchet_step`, `OutgoingTripleRatchet::encrypt::<HookRng>`, the async session API), which
//   is monomorphized into THIS crate's object by the wrappers below. They are here from the start
//   so that the image does not change between stages.
//
// Entry points (all `#[inline(never)] #[unsafe(no_mangle)]`, Rust ABI):
//   `session_message_encrypt`        = `libsignal_protocol::message_encrypt::<HookRng>`
//   `session_message_decrypt_signal` = `libsignal_protocol::message_decrypt_signal::<HookRng>`
//   `session_signal_message_parse`   = `<SignalMessage as TryFrom<&[u8]>>::try_from`
// The async fns are driven by one `poll` with `Waker::noop()` (libsignal's in-memory stores never
// return `Pending`); the stores are `&mut dyn` trait objects exactly as upstream takes them, so
// every store call stays an indirect call through a caller-supplied vtable.
//
// The RNG is the extern `libsignal_session_rng_fill(dst, len)` (a hook), wrapped as a
// `rand_core` 0.9 `RngCore + CryptoRng`; every `csprng` in the session code is monomorphized at
// `HookRng`.

#![allow(clippy::missing_safety_doc)]

use std::future::Future;
use std::pin::pin;
use std::task::{Context, Poll, Waker};
use std::time::SystemTime;

use libsignal_protocol::{
    CiphertextMessage, IdentityKeyStore, ProtocolAddress, SessionStore, SignalMessage,
    SignalProtocolError, message_decrypt_signal, message_encrypt,
};

// ---------------------------------------------------------------------------
// RNG hook
// ---------------------------------------------------------------------------

unsafe extern "C" {
    /// Fill `dst[0..len]` with random bytes (the RNG hook).
    pub fn libsignal_session_rng_fill(dst: *mut u8, len: usize);
}

/// The CSPRNG passed to libsignal: every byte comes from the `libsignal_session_rng_fill` hook.
pub struct HookRng;

impl rand_core::RngCore for HookRng {
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
        unsafe { libsignal_session_rng_fill(dst.as_mut_ptr(), dst.len()) }
    }
}

impl rand_core::CryptoRng for HookRng {}

// ---------------------------------------------------------------------------
// Synchronous driver
// ---------------------------------------------------------------------------

/// Poll `fut` once with a no-op waker; `None` = the future was pending (not reachable with stores
/// whose futures are always ready).
#[inline(always)]
fn poll_once<F: Future>(fut: F) -> Option<F::Output> {
    let mut fut = pin!(fut);
    let mut cx = Context::from_waker(Waker::noop());
    match fut.as_mut().poll(&mut cx) {
        Poll::Ready(v) => Some(v),
        Poll::Pending => None,
    }
}

// ---------------------------------------------------------------------------
// The real public API (stages 2-3)
// ---------------------------------------------------------------------------

/// `libsignal_protocol::message_encrypt::<HookRng>` (`session_management.rs:43`), driven
/// synchronously.
#[inline(never)]
#[unsafe(no_mangle)]
pub fn session_message_encrypt(
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
        &mut HookRng,
    ))
}

/// `libsignal_protocol::message_decrypt_signal::<HookRng>` (`session_management.rs:297`),
/// driven synchronously.
#[inline(never)]
#[unsafe(no_mangle)]
pub fn session_message_decrypt_signal(
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
        &mut HookRng,
    ))
}

/// `<SignalMessage as TryFrom<&[u8]>>::try_from` (`protocol.rs:261`): the wire parse that
/// precedes `message_decrypt_signal`.
#[inline(never)]
#[unsafe(no_mangle)]
pub fn session_signal_message_parse(bytes: &[u8]) -> Result<SignalMessage, SignalProtocolError> {
    SignalMessage::try_from(bytes)
}
