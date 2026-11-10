// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// This file is ORIGINAL code written for this repository; it copies no upstream source. See
// `third_party/libsignal/README.md`.

//! What a party publishes, and the bundles made from it. `keygen` writes the public halves of the
//! party's keys under `public/`, as a client uploads them to Signal's server. The caller plays that
//! server: to let a party start a session, it gives it a bundle, a directory of copies of some of
//! the peer's public files.
//!
//! ```text
//! public/identity-key                     IdentityKey
//! public/registration-id                  u32 (little-endian)
//! public/signed-pre-keys/<id>             id:u32 ‖ public key ‖ signature[64]
//! public/one-time-pre-keys/<id>           id:u32 ‖ public key
//! public/one-time-kyber-pre-keys/<id>     id:u32 ‖ Kyber public key ‖ signature[64]
//! public/last-resort-kyber-pre-keys/<id>  id:u32 ‖ Kyber public key ‖ signature[64]
//!
//! <bundle>/identity-key                   a copy of public/identity-key
//!          registration-id                a copy of public/registration-id
//!          signed-pre-key                 a copy of a public/signed-pre-keys/<id>
//!          kyber-pre-key                  a copy of a public/*-kyber-pre-keys/<id>
//!          one-time-pre-key               a copy of a public/one-time-pre-keys/<id>; none if absent
//! ```
//!
//! - Keys are in libsignal's own serializations; each signature is the identity key's, over the
//!   serialized public key.
//! - The id comes first in a key's file, so a bundle needs only fixed file names: the ARM64 process
//!   model cannot list a directory.
//! - `public/` and its four subdirectories must exist: the process model has no `mkdir`.

use libsignal_protocol::{
    DeviceId, GenericSignedPreKey, IdentityKey, KyberPreKeyId, KyberPreKeyRecord, PreKeyBundle,
    PreKeyId, PreKeyRecord, PublicKey, SignalProtocolError, SignedPreKeyId, SignedPreKeyRecord,
    kem,
};

use crate::io;
use crate::stores::{Dir, malformed, name, path, unreadable};

type Result<T> = std::result::Result<T, SignalProtocolError>;

/// What the party uploads to Signal's server (`public/`), written by `keygen`.
pub struct PublicFiles(pub(crate) Dir);

impl PublicFiles {
    /// Publishes the party's identity key and registration id.
    pub fn identity(&mut self, key: &IdentityKey, registration_id: u32) {
        self.0.put("identity-key", key.serialize().into_vec());
        self.0
            .put("registration-id", registration_id.to_le_bytes().to_vec());
    }

    /// Publishes a signed pre-key.
    pub fn signed_pre_key(&mut self, key: &SignedPreKeyRecord) -> Result<()> {
        let id = u32::from(key.id()?);
        let file = signed(id, &key.public_key()?.serialize(), &key.signature()?);
        self.0.put(path("signed-pre-keys", &name(id)), file);
        Ok(())
    }

    /// Publishes a one-time pre-key.
    pub fn one_time_pre_key(&mut self, key: &PreKeyRecord) -> Result<()> {
        let id = u32::from(key.id()?);
        let file = [&id.to_le_bytes()[..], &key.public_key()?.serialize()].concat();
        self.0.put(path("one-time-pre-keys", &name(id)), file);
        Ok(())
    }

    /// Publishes a one-time Kyber pre-key.
    pub fn one_time_kyber_pre_key(&mut self, key: &KyberPreKeyRecord) -> Result<()> {
        self.kyber_pre_key("one-time-kyber-pre-keys", key)
    }

    /// Publishes a last-resort Kyber pre-key.
    pub fn last_resort_kyber_pre_key(&mut self, key: &KyberPreKeyRecord) -> Result<()> {
        self.kyber_pre_key("last-resort-kyber-pre-keys", key)
    }

    fn kyber_pre_key(&mut self, dir: &str, key: &KyberPreKeyRecord) -> Result<()> {
        let id = u32::from(key.id()?);
        let file = signed(id, &key.public_key()?.serialize(), &key.signature()?);
        self.0.put(path(dir, &name(id)), file);
        Ok(())
    }
}

/// The file of a signed key: `id:u32 ‖ public key ‖ signature`.
fn signed(id: u32, public_key: &[u8], signature: &[u8]) -> Vec<u8> {
    [&id.to_le_bytes()[..], public_key, signature].concat()
}

/// The bundle in directory `dir`, for the peer's device `device`.
pub fn read_bundle(dir: &str, device: DeviceId) -> Result<PreKeyBundle> {
    let read = |name: &str| io::read_file(&path(dir, name)).map_err(unreadable);
    let identity = IdentityKey::decode(&read("identity-key")?)?;
    let registration_id = read("registration-id")?;
    let registration_id = registration_id[..]
        .try_into()
        .map_err(|_| malformed("registration-id"))?;
    let spk_file = read("signed-pre-key")?;
    let (spk_id, spk, spk_signature) = split_signed(&spk_file)?;
    let kyber_file = read("kyber-pre-key")?;
    let (kyber_id, kyber, kyber_signature) = split_signed(&kyber_file)?;
    let one_time = match &read("one-time-pre-key")?[..] {
        [] => None,
        file => {
            let (id, key) = split_id(file)?;
            Some((PreKeyId::from(id), PublicKey::deserialize(key)?))
        }
    };
    PreKeyBundle::new(
        u32::from_le_bytes(registration_id),
        device,
        one_time,
        SignedPreKeyId::from(spk_id),
        PublicKey::deserialize(spk)?,
        spk_signature.to_vec(),
        KyberPreKeyId::from(kyber_id),
        kem::PublicKey::deserialize(kyber)?,
        kyber_signature.to_vec(),
        identity,
    )
}

/// A signed key's file, as `(id, public key, signature)`.
fn split_signed(file: &[u8]) -> Result<(u32, &[u8], &[u8])> {
    let (id, rest) = split_id(file)?;
    let at = rest.len().checked_sub(64).ok_or(malformed("bundle"))?;
    let (key, signature) = rest.split_at(at);
    Ok((id, key, signature))
}

/// A key's file, as `(id, rest)`.
fn split_id(file: &[u8]) -> Result<(u32, &[u8])> {
    let (id, rest) = file.split_first_chunk().ok_or(malformed("bundle"))?;
    Ok((u32::from_le_bytes(*id), rest))
}
