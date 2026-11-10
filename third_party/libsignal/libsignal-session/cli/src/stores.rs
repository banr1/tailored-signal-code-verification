// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// This file is ORIGINAL code written for this repository; it copies no upstream source. See
// `third_party/libsignal/README.md`.

//! A party's libsignal stores, kept in the files of its directory (the current directory): one
//! file per record, as a real client keeps them in its database. libsignal's five store traits are
//! implemented over those files. (What the party publishes, under `public/`, is in `public.rs`.)
//!
//! ```text
//! address                                    the party's address: service id . device id (text)
//! identity-key-pair                          IdentityKeyPair      ┐
//! registration-id                            u32 (little-endian)  │ IdentityFiles
//! identities/<service id>                    IdentityKey          ┘
//! sessions/<service id>.<device id>          SessionRecord          SessionFiles
//! signed-pre-keys/<id>                       SignedPreKeyRecord     SignedPreKeyFiles
//! one-time-pre-keys/<id>                     PreKeyRecord           OneTimePreKeyFiles
//! one-time-kyber-pre-keys/<id>               KyberPreKeyRecord    ┐
//! last-resort-kyber-pre-keys/<id>            KyberPreKeyRecord    │ KyberPreKeyFiles
//! last-resort-kyber-pre-keys/<id>.base-keys  (signed id:u32 ‖ base key[33])*  ┘
//! ```
//!
//! - Records are in libsignal's own serializations. An empty or missing file holds no record, and
//!   a used one-time key is emptied: the ARM64 process model has no `unlink`.
//! - A store opens a file only when libsignal asks for its record, by the name libsignal gives (an
//!   address or a key id), and never lists a directory: the process model cannot.
//! - The stores keep what they change in memory, and [`Stores::commit`] writes it, so a call that
//!   fails half-way writes nothing, as in Signal's own apps (see [`Stores::commit`]).
//! - The directory and its six subdirectories must exist (and `public/`, see `public.rs`): the
//!   process model has no `mkdir`.

use async_trait::async_trait;
use libsignal_protocol::{
    CiphertextMessageType, Direction, GenericSignedPreKey, IdentityChange, IdentityKey,
    IdentityKeyPair, IdentityKeyStore, KyberPreKeyId, KyberPreKeyRecord, KyberPreKeyStore,
    PreKeyId, PreKeyRecord, PreKeyStore, ProtocolAddress, PublicKey, SessionRecord, SessionStore,
    SignalProtocolError, SignedPreKeyId, SignedPreKeyRecord, SignedPreKeyStore,
};

use crate::io::{self, IoError};
use crate::public::PublicFiles;

type Result<T> = std::result::Result<T, SignalProtocolError>;

/// A party's stores, one for each of libsignal's store traits, and what it publishes.
pub struct Stores {
    pub identity: IdentityFiles,
    pub signed: SignedPreKeyFiles,
    pub kyber: KyberPreKeyFiles,
    pub one_time: OneTimePreKeyFiles,
    pub sessions: SessionFiles,
    pub public: PublicFiles,
}

impl Stores {
    /// The stores of the party whose directory is the current directory.
    pub fn open() -> Stores {
        Stores {
            identity: IdentityFiles {
                own: Dir::new(""),
                peers: Dir::new("identities"),
            },
            signed: SignedPreKeyFiles(Dir::new("signed-pre-keys")),
            kyber: KyberPreKeyFiles {
                one_time: Dir::new("one-time-kyber-pre-keys"),
                last_resort: Dir::new("last-resort-kyber-pre-keys"),
            },
            one_time: OneTimePreKeyFiles(Dir::new("one-time-pre-keys")),
            sessions: SessionFiles(Dir::new("sessions")),
            public: PublicFiles(Dir::new("public")),
        }
    }

    /// Writes every file the stores changed. Until then the stores change only memory, so a call
    /// that libsignal rejects writes nothing.
    ///
    /// This is needed because libsignal calls the stores one at a time and can still fail after
    /// some of them: on a pre-key message it saves the peer's identity key, and only then may the
    /// Kyber pre-key store refuse a reused base key. libsignal leaves atomicity to the app, and
    /// Signal's own apps hold back their store writes the same way:
    /// - Signal-Desktop keeps a decryption's sessions, used pre-keys and Kyber base keys pending in
    ///   a "zone", then writes them in one database transaction, or drops them if the decryption
    ///   fails (`withZone` and `commitDecryptResult` in `ts/SignalProtocolStore.preload.ts`). It
    ///   writes identity keys at once; these stores hold them back too.
    /// - Signal-Android buffers them in a `BufferedProtocolStore` ("read from disk, but never
    ///   write") and calls its `flushToDisk()` inside `SignalDatabase.runInTransaction`
    ///   (`IncomingMessageObserver.kt`).
    pub fn commit(self) -> std::result::Result<(), IoError> {
        let Stores {
            identity,
            signed,
            kyber,
            one_time,
            sessions,
            public,
        } = self;
        for dir in [
            identity.own,
            identity.peers,
            signed.0,
            kyber.one_time,
            kyber.last_resort,
            one_time.0,
            sessions.0,
            public.0,
        ] {
            dir.commit()?;
        }
        Ok(())
    }
}

/// One directory of the party's files ("" is the party's directory itself): files are read when
/// asked for, and changed in memory until `commit`, in the order they were first changed.
pub(crate) struct Dir {
    path: &'static str,
    changed: Vec<(String, Vec<u8>)>,
}

impl Dir {
    fn new(path: &'static str) -> Dir {
        Dir {
            path,
            changed: Vec::new(),
        }
    }

    fn path_of(&self, name: &str) -> String {
        match self.path {
            "" => name.to_owned(),
            dir => path(dir, name),
        }
    }

    /// The bytes of file `name`: as changed, or else as on disk.
    fn get(&self, name: &str) -> Result<Vec<u8>> {
        match self.changed.iter().find(|(changed, _)| changed == name) {
            Some((_, bytes)) => Ok(bytes.clone()),
            None => io::read_file(&self.path_of(name)).map_err(unreadable),
        }
    }

    pub(crate) fn put(&mut self, name: impl Into<String>, bytes: Vec<u8>) {
        let name = name.into();
        match self
            .changed
            .iter_mut()
            .find(|(changed, _)| *changed == name)
        {
            Some((_, old)) => *old = bytes,
            None => self.changed.push((name, bytes)),
        }
    }

    fn commit(self) -> std::result::Result<(), IoError> {
        for (name, bytes) in &self.changed {
            io::write_file(&self.path_of(name), bytes)?;
        }
        Ok(())
    }
}

/// The record in a file's `bytes`: none if they are empty.
fn record<T>(bytes: &[u8], decode: impl FnOnce(&[u8]) -> Result<T>) -> Result<Option<T>> {
    match bytes {
        [] => Ok(None),
        bytes => decode(bytes).map(Some),
    }
}

/// `SignedPreKeyRecord::deserialize`, as its own function of the compiled code: libsignal's generic
/// `GenericSignedPreKey::deserialize` is instantiated in this crate, and its proof is the record
/// codec's.
#[inline(never)]
fn decode_signed_pre_key(bytes: &[u8]) -> Result<SignedPreKeyRecord> {
    SignedPreKeyRecord::deserialize(bytes)
}

/// `KyberPreKeyRecord::deserialize`, as its own function of the compiled code (as
/// [`decode_signed_pre_key`]).
///
/// Both records are a `SignedPreKeyRecordStructure`, so the two functions compile to the same
/// code, and LLVM keeps one of them (with rustc 1.98.1: this one) for both calls.
#[inline(never)]
fn decode_kyber_pre_key(bytes: &[u8]) -> Result<KyberPreKeyRecord> {
    KyberPreKeyRecord::deserialize(bytes)
}

/// The path of file `name` in directory `dir`.
pub(crate) fn path(dir: &str, name: &str) -> String {
    dir.to_owned() + "/" + name
}

/// The file name of a key id: the id in decimal.
pub(crate) fn name(id: impl Into<u32>) -> String {
    decimal(id.into())
}

/// `n` in decimal, as `n.to_string()` but without `core::fmt`.
fn decimal(n: u32) -> String {
    let mut text = if n < 10 {
        String::new()
    } else {
        decimal(n / 10)
    };
    text.push(char::from(b'0' + (n % 10) as u8));
    text
}

/// An address as text, `<service id>.<device id>`, as `address.to_string()` but without
/// `core::fmt`.
fn address_text(address: &ProtocolAddress) -> String {
    address.name().to_owned() + "." + &name(address.device_id())
}

/// `file` does not have its layout.
pub(crate) fn malformed(file: &'static str) -> SignalProtocolError {
    SignalProtocolError::InvalidState(file, "malformed file".to_owned())
}

/// A file could not be read.
pub(crate) fn unreadable(_: IoError) -> SignalProtocolError {
    SignalProtocolError::InvalidState("read", "file could not be read".to_owned())
}

/// The party's own identity (`address`, `identity-key-pair`, `registration-id`), and the identity
/// keys of the accounts it talks to (`identities/<service id>`): trusted on first use, then pinned.
/// One key per account, not per device: an account's devices share its identity key.
pub struct IdentityFiles {
    own: Dir,
    peers: Dir,
}

impl IdentityFiles {
    /// Makes the party the one with this address, identity key pair and registration id.
    pub fn create(&mut self, address: &ProtocolAddress, key_pair: &IdentityKeyPair, id: u32) {
        self.own.put("address", address_text(address).into_bytes());
        self.own
            .put("identity-key-pair", key_pair.serialize().into_vec());
        self.own.put("registration-id", id.to_le_bytes().to_vec());
    }

    /// The party's own address, as text.
    pub fn address(&self) -> Result<String> {
        String::from_utf8(self.own.get("address")?).map_err(|_| malformed("address"))
    }

    fn peer(&self, address: &ProtocolAddress) -> Result<Option<IdentityKey>> {
        record(&self.peers.get(address.name())?, IdentityKey::decode)
    }
}

#[async_trait(?Send)]
impl IdentityKeyStore for IdentityFiles {
    async fn get_identity_key_pair(&self) -> Result<IdentityKeyPair> {
        IdentityKeyPair::try_from(&self.own.get("identity-key-pair")?[..])
    }

    async fn get_local_registration_id(&self) -> Result<u32> {
        let bytes = self.own.get("registration-id")?;
        let bytes = bytes[..]
            .try_into()
            .map_err(|_| malformed("registration-id"))?;
        Ok(u32::from_le_bytes(bytes))
    }

    async fn save_identity(
        &mut self,
        address: &ProtocolAddress,
        key: &IdentityKey,
    ) -> Result<IdentityChange> {
        let replaced = self.peer(address)?.is_some_and(|known| known != *key);
        self.peers.put(address.name(), key.serialize().into_vec());
        Ok(IdentityChange::from_changed(replaced))
    }

    async fn is_trusted_identity(
        &self,
        address: &ProtocolAddress,
        key: &IdentityKey,
        _: Direction,
    ) -> Result<bool> {
        Ok(self.peer(address)?.is_none_or(|known| known == *key))
    }

    async fn get_identity(&self, address: &ProtocolAddress) -> Result<Option<IdentityKey>> {
        self.peer(address)
    }
}

/// The sessions, one for each device the party talks to (`sessions/<service id>.<device id>`).
pub struct SessionFiles(Dir);

#[async_trait(?Send)]
impl SessionStore for SessionFiles {
    async fn load_session(&self, address: &ProtocolAddress) -> Result<Option<SessionRecord>> {
        record(
            &self.0.get(&address_text(address))?,
            SessionRecord::deserialize,
        )
    }

    async fn store_session(
        &mut self,
        address: &ProtocolAddress,
        session: &SessionRecord,
    ) -> Result<()> {
        self.0.put(address_text(address), session.serialize()?);
        Ok(())
    }
}

/// The signed pre-keys (`signed-pre-keys/<id>`).
pub struct SignedPreKeyFiles(Dir);

impl SignedPreKeyFiles {
    /// Adds a signed pre-key.
    pub fn save(&mut self, id: SignedPreKeyId, key: &SignedPreKeyRecord) -> Result<()> {
        self.0.put(name(id), key.serialize()?);
        Ok(())
    }
}

#[async_trait(?Send)]
impl SignedPreKeyStore for SignedPreKeyFiles {
    async fn get_signed_pre_key(&self, id: SignedPreKeyId) -> Result<SignedPreKeyRecord> {
        let key = record(&self.0.get(&name(id))?, decode_signed_pre_key)?;
        key.ok_or(SignalProtocolError::InvalidSignedPreKeyId)
    }

    async fn save_signed_pre_key(
        &mut self,
        id: SignedPreKeyId,
        key: &SignedPreKeyRecord,
    ) -> Result<()> {
        self.save(id, key)
    }
}

/// The one-time pre-keys (`one-time-pre-keys/<id>`), each emptied by the session that uses it.
pub struct OneTimePreKeyFiles(Dir);

impl OneTimePreKeyFiles {
    /// Adds a one-time pre-key.
    pub fn save(&mut self, id: PreKeyId, key: &PreKeyRecord) -> Result<()> {
        self.0.put(name(id), key.serialize()?);
        Ok(())
    }
}

#[async_trait(?Send)]
impl PreKeyStore for OneTimePreKeyFiles {
    async fn get_pre_key(&self, id: PreKeyId) -> Result<PreKeyRecord> {
        let key = record(&self.0.get(&name(id))?, PreKeyRecord::deserialize)?;
        key.ok_or(SignalProtocolError::InvalidPreKeyId)
    }

    async fn save_pre_key(&mut self, id: PreKeyId, key: &PreKeyRecord) -> Result<()> {
        self.save(id, key)
    }

    async fn remove_pre_key(&mut self, id: PreKeyId) -> Result<()> {
        if !self.0.get(&name(id))?.is_empty() {
            self.0.put(name(id), Vec::new());
        }
        Ok(())
    }
}

/// The Kyber pre-keys. libsignal does not tell one-time keys from last-resort ones (its trait doc
/// says so), so the directory a key is in does:
/// - a one-time key (`one-time-kyber-pre-keys/<id>`) is emptied by the session that uses it;
/// - a last-resort key (`last-resort-kyber-pre-keys/<id>`) is kept, but refuses a base key it was
///   already used with, with the same signed pre-key (`<id>.base-keys`: `signed id:u32 ‖ base
///   key[33]` each).
///
/// Their ids are one space: libsignal names a Kyber pre-key by id alone.
pub struct KyberPreKeyFiles {
    one_time: Dir,
    last_resort: Dir,
}

impl KyberPreKeyFiles {
    /// Adds a one-time Kyber pre-key.
    pub fn save_one_time(&mut self, id: KyberPreKeyId, key: &KyberPreKeyRecord) -> Result<()> {
        self.one_time.put(name(id), key.serialize()?);
        Ok(())
    }

    /// Adds a last-resort Kyber pre-key.
    pub fn save_last_resort(&mut self, id: KyberPreKeyId, key: &KyberPreKeyRecord) -> Result<()> {
        self.last_resort.put(name(id), key.serialize()?);
        Ok(())
    }
}

#[async_trait(?Send)]
impl KyberPreKeyStore for KyberPreKeyFiles {
    async fn get_kyber_pre_key(&self, id: KyberPreKeyId) -> Result<KyberPreKeyRecord> {
        for dir in [&self.one_time, &self.last_resort] {
            if let Some(key) = record(&dir.get(&name(id))?, decode_kyber_pre_key)? {
                return Ok(key);
            }
        }
        Err(SignalProtocolError::InvalidKyberPreKeyId)
    }

    /// Saves a one-time key; [`KyberPreKeyFiles::save_last_resort`] saves a last-resort one.
    async fn save_kyber_pre_key(
        &mut self,
        id: KyberPreKeyId,
        key: &KyberPreKeyRecord,
    ) -> Result<()> {
        self.save_one_time(id, key)
    }

    async fn mark_kyber_pre_key_used(
        &mut self,
        id: KyberPreKeyId,
        signed_id: SignedPreKeyId,
        base_key: &PublicKey,
    ) -> Result<()> {
        if !self.one_time.get(&name(id))?.is_empty() {
            self.one_time.put(name(id), Vec::new());
            return Ok(());
        }
        let file = name(id) + ".base-keys";
        let mut seen = self.last_resort.get(&file)?;
        let used = [
            &u32::from(signed_id).to_le_bytes()[..],
            &base_key.serialize(),
        ]
        .concat();
        if !seen.len().is_multiple_of(used.len()) {
            return Err(malformed("base-keys"));
        }
        if seen.chunks(used.len()).any(|entry| entry == used) {
            let reused = "reused base key".to_owned();
            return Err(SignalProtocolError::InvalidMessage(
                CiphertextMessageType::PreKey,
                reused,
            ));
        }
        seen.extend(used);
        self.last_resort.put(file, seen);
        Ok(())
    }
}
