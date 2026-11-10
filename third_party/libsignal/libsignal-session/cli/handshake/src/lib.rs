// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// This file is ORIGINAL code written for this repository; it copies no upstream source. The
// machine code produced by compiling it together with libsignal is a derived work of libsignal
// (`Copyright 2020-2026 Signal Messenger, LLC.`, `SPDX-License-Identifier: AGPL-3.0-only`); see
// `third_party/libsignal/README.md`.

//! The handshake calls of the `libsignal-cli` CLI: libsignal's `process_prekey_bundle` (`init`)
//! and `message_decrypt_prekey` (`recv` of a pre-key message), each driven to completion by one
//! poll, with the CLI's coins as the CSPRNG.
//!
//! Why a crate of its own: so that the libsignal code monomorphized into these two calls is the
//! code that the image's handshake crate (`libsignal-pqxdh-e2e`, `../../pqxdh/src/lib.rs`)
//! already compiles at its `PqxdhRng`, up to relocations, so that the proofs about that code
//! carry over. As for the ratchet crate (`../ratchet/src/lib.rs`, which says why), that needs a
//! crate holding only these calls and their RNG, so the RNG and `poll_once` are repeated here.

use std::future::Future;
use std::pin::pin;
use std::task::{Context, Poll, Waker};
use std::time::SystemTime;

use libsignal_protocol::{
    IdentityKeyStore, KyberPreKeyStore, PreKeyBundle, PreKeySignalMessage, PreKeyStore,
    ProtocolAddress, SessionStore, SignalProtocolError, SignedPreKeyStore, message_decrypt_prekey,
    process_prekey_bundle,
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

/// `init`: libsignal's `process_prekey_bundle`, which checks `bundle`'s signatures, trusts the
/// identity key of `remote_address` and stores a new session with it.
#[inline(never)]
pub fn initiate(
    remote_address: &ProtocolAddress,
    local_address: &ProtocolAddress,
    session_store: &mut dyn SessionStore,
    identity_store: &mut dyn IdentityKeyStore,
    bundle: &PreKeyBundle,
    now: SystemTime,
) -> Option<Result<(), SignalProtocolError>> {
    poll_once(process_prekey_bundle(
        remote_address,
        local_address,
        session_store,
        identity_store,
        bundle,
        now,
        &mut Coins,
    ))
}

/// `recv` of a pre-key message: libsignal's `message_decrypt_prekey`, which decrypts
/// `ciphertext` from `remote_address`, in a new session made from the pre-keys it names (or in
/// the session it already made).
#[allow(clippy::too_many_arguments)] // libsignal's own parameters
#[inline(never)]
pub fn decrypt_prekey(
    ciphertext: &PreKeySignalMessage,
    remote_address: &ProtocolAddress,
    local_address: &ProtocolAddress,
    session_store: &mut dyn SessionStore,
    identity_store: &mut dyn IdentityKeyStore,
    pre_key_store: &mut dyn PreKeyStore,
    signed_pre_key_store: &dyn SignedPreKeyStore,
    kyber_pre_key_store: &mut dyn KyberPreKeyStore,
) -> Option<Result<Vec<u8>, SignalProtocolError>> {
    poll_once(message_decrypt_prekey(
        ciphertext,
        remote_address,
        local_address,
        session_store,
        identity_store,
        pre_key_store,
        signed_pre_key_store,
        kyber_pre_key_store,
        &mut Coins,
    ))
}
