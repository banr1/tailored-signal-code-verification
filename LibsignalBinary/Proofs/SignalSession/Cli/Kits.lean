/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
public import LibsignalBinary.Specifications.RecordCodecs
public import LibsignalBinary.Specifications.LibsignalPublicApiRepr

/-!
# Pure File-Store Model for the `signal-session` CLI

Pure specification of `cli/src/stores.rs`: models buffered file directories (`DirGhost`)
parameterized by a `ReadRule` and initial file table `F0`, together with the callback answers
and `Stores::commit` write lists for `IdentityFiles` (`IdGhost`), `SessionFiles`,
`OneTimePreKeyFiles`, `SignedPreKeyFiles`, and `KyberPreKeyFiles` (`KyberGhost`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RecordCodecs CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- UTF-8 bytes of a `String`. -/
def utf8 (s : String) : List (BitVec 8) := s.toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- `decimal(n)`: `n` in decimal ASCII, no leading zeros (`stores.rs` `decimal`). -/
def decimalText (n : Nat) : List (BitVec 8) := utf8 (toString n)

/-- `path(dir, name) = dir + "/" + name`; `Dir::path_of` uses `name` itself in the party's
directory (`dir = ""`). -/
def pathOf (dir name : List (BitVec 8)) : List (BitVec 8) :=
  if dir = [] then name else dir ++ utf8 "/" ++ name

/-- `address_text(a) = name + "." + decimal(device)`. -/
def addressText (a : AddrVal) : List (BitVec 8) :=
  a.name ++ utf8 "." ++ decimalText a.device.toNat

/-- Abstract `io::read_file` contract mapping `(files, path)` to file bytes or `()`. -/
abbrev ReadRule : Type := FsFiles → List (BitVec 8) → Except Unit (List (BitVec 8))

/-- One `Dir`: its path and its in-memory changes, in first-change order. -/
structure DirGhost where
  path : List (BitVec 8)
  changed : List (List (BitVec 8) × List (BitVec 8))

namespace DirGhost

def new (path : List (BitVec 8)) : DirGhost := ⟨path, []⟩

/-- `Dir::get(name)`: the changed bytes, else `read_file(path_of(name))` (any error →
`InvalidState("read", …)`, here `()`). -/
def get (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (name : List (BitVec 8)) :
    Except Unit (List (BitVec 8)) :=
  match d.changed.find? (fun e => e.1 == name) with
  | some e => .ok e.2
  | none => rd F0 (pathOf d.path name)

/-- Replace the first entry named `name`, or push `(name, bs)`. -/
def setOrPush (name bs : List (BitVec 8)) :
    List (List (BitVec 8) × List (BitVec 8)) → List (List (BitVec 8) × List (BitVec 8))
  | [] => [(name, bs)]
  | e :: es => if e.1 = name then (name, bs) :: es else e :: setOrPush name bs es

def put (d : DirGhost) (name bs : List (BitVec 8)) : DirGhost :=
  { d with changed := setOrPush name bs d.changed }

/-- What `Dir::commit` writes, in order: `(path_of(name), bytes)` for every changed entry. -/
def writes (d : DirGhost) : List (List (BitVec 8) × List (BitVec 8)) :=
  d.changed.map fun e => (pathOf d.path e.1, e.2)

theorem find_setOrPush_self (n bs : List (BitVec 8)) :
    ∀ l, (setOrPush n bs l).find? (fun e => e.1 == n) = some (n, bs) := by
  intro l
  induction l with
  | nil => simp [setOrPush]
  | cons e es ih =>
    by_cases h : e.1 = n
    · simp [setOrPush, h]
    · simp [setOrPush, h, ih]

theorem find_setOrPush_ne {n n' : List (BitVec 8)} (hne : n' ≠ n) (bs : List (BitVec 8)) :
    ∀ l, (setOrPush n bs l).find? (fun e => e.1 == n') = l.find? (fun e => e.1 == n') := by
  intro l
  have hne' : n ≠ n' := Ne.symm hne
  induction l with
  | nil => simp [setOrPush, hne']
  | cons e es ih =>
    by_cases h : e.1 = n
    · simp [setOrPush, h, hne']
    · simp only [setOrPush, h, ↓reduceIte, List.find?_cons]
      cases e.1 == n'
      · exact ih
      · rfl

@[simp] theorem get_put_self (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (n bs : List (BitVec 8)) :
    (d.put n bs).get rd F0 n = .ok bs := by
  simp [get, put, find_setOrPush_self]

theorem get_put_ne (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) {n n' : List (BitVec 8)}
    (hne : n' ≠ n) (bs : List (BitVec 8)) : (d.put n bs).get rd F0 n' = d.get rd F0 n' := by
  simp [get, put, find_setOrPush_ne hne]

end DirGhost

/-- `record(bytes, decode)`: no record in an empty file; else the decoder (errors → `()`). -/
def record {α ε : Type} (dec : List (BitVec 8) → Except ε α) :
    List (BitVec 8) → Except Unit (Option α)
  | [] => .ok none
  | bs => match dec bs with
    | .ok a => .ok (some a)
    | .error _ => .error ()

/-! ## `IdentityFiles` (own `""`, peers `"identities"`) -/

/-- The identity store's state: `own` (the party's directory) and `peers` (`identities/`). -/
structure IdGhost where
  own : DirGhost
  peers : DirGhost

/-- `peer(address)`: the pinned identity key of `address.name()`, if any. -/
def IdGhost.peer (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal) :
    Except Unit (Option IdentityKey) :=
  (g.peers.get rd F0 a.name).bind (record decodeIdentityKey)

/-- `is_trusted_identity`: trusted on first use, then pinned. -/
def IdGhost.trusted (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal) (k : IdentityKey) :
    Except Unit Bool :=
  (g.peer rd F0 a).map fun o => match o with
    | none => true
    | some known => decide (known = k)

/-- `save_identity`'s answer: `ReplacedExisting` iff a different key was pinned. -/
def IdGhost.saveAns (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal) (k : IdentityKey) :
    Except Unit IdentityChange :=
  (g.peer rd F0 a).map fun o => match o with
    | some known => if known = k then .newOrUnchanged else .replacedExisting
    | none => .newOrUnchanged

/-- `save_identity`'s update: `put(name, key.serialize())` after `peer` succeeded; unchanged if
`peer` failed (the `?` returns first). -/
def IdGhost.saveUpd (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) (a : AddrVal) (k : IdentityKey) :
    IdGhost :=
  match g.peer rd F0 a with
  | .ok _ => { g with peers := g.peers.put a.name k.serialize }
  | .error _ => g

/-- `get_identity_key_pair`: `IdentityKeyPair::try_from` on `identity-key-pair` (no `record`: an
empty file is a decode error). -/
def IdGhost.keyPair (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) :
    Except Unit RecordCodecs.IdentityKeyPair :=
  (g.own.get rd F0 (utf8 "identity-key-pair")).bind fun bs =>
    match RecordCodecs.IdentityKeyPair.tryFrom bs with
    | .ok kp => .ok kp
    | .error _ => .error ()

/-- `get_local_registration_id`: exactly 4 bytes, little-endian. -/
def IdGhost.regId (rd : ReadRule) (F0 : FsFiles) (g : IdGhost) : Except Unit (BitVec 32) :=
  (g.own.get rd F0 (utf8 "registration-id")).bind fun bs =>
    match bs with
    | [b0, b1, b2, b3] => .ok (b3 ++ b2 ++ b1 ++ b0)
    | _ => .error ()

/-! ## `SessionFiles` (`"sessions"`) -/

/-- `load_session`: `record(get(address_text), SessionRecord::deserialize)`. -/
def loadSession {R ε : Type} (dec : List (BitVec 8) → Except ε R) (rd : ReadRule) (F0 : FsFiles)
    (d : DirGhost) (a : AddrVal) : Except Unit (Option R) :=
  (d.get rd F0 (addressText a)).bind (record dec)

/-- `store_session`: `put(address_text, session.serialize()?)`; the answer is `Ok` iff `serialize`
succeeds, and only then is the store changed. -/
def storeSession {R ε : Type} (enc : R → Except ε (List (BitVec 8))) (d : DirGhost) (a : AddrVal)
    (r : R) : Except Unit Unit × DirGhost :=
  match enc r with
  | .ok bs => (.ok (), d.put (addressText a) bs)
  | .error _ => (.error (), d)

/-! ## Pre-key stores -/

def keyName (id : BitVec 32) : List (BitVec 8) := decimalText id.toNat

/-- `get_pre_key` (`one-time-pre-keys`): the record, `InvalidPreKeyId` if the file is empty. -/
def getPreKey (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (id : BitVec 32) :
    Except Unit PreKeyRecord :=
  (d.get rd F0 (keyName id)).bind (record PreKeyRecord.deserialize) |>.bind fun
    | some r => .ok r
    | none => .error ()

/-- `remove_pre_key`: empty a nonempty file; a read error is returned before any change. -/
def removePreKey (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (id : BitVec 32) :
    Except Unit Unit × DirGhost :=
  match d.get rd F0 (keyName id) with
  | .error _ => (.error (), d)
  | .ok [] => (.ok (), d)
  | .ok _ => (.ok (), d.put (keyName id) [])

/-- `get_signed_pre_key` (`signed-pre-keys`), through `decode_kyber_pre_key`'s code (LLVM keeps
one function for both decoders). -/
def getSignedPreKey (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (id : BitVec 32) :
    Except Unit SignedPreKeyRecord :=
  (d.get rd F0 (keyName id)).bind (record SignedPreKeyRecord.deserialize) |>.bind fun
    | some r => .ok r
    | none => .error ()

/-- The Kyber store's state: one-time and last-resort directories. -/
structure KyberGhost where
  oneTime : DirGhost
  lastResort : DirGhost

/-- `get_kyber_pre_key`: the one-time directory, then the last-resort one; an error in the first
returns at once; empty in both → `InvalidKyberPreKeyId`. -/
def KyberGhost.get (rd : ReadRule) (F0 : FsFiles) (g : KyberGhost) (id : BitVec 32) :
    Except Unit KyberPreKeyRecord := do
  match ← (g.oneTime.get rd F0 (keyName id)).bind (record KyberPreKeyRecord.deserialize) with
  | some r => pure r
  | none =>
    match ← (g.lastResort.get rd F0 (keyName id)).bind (record KyberPreKeyRecord.deserialize) with
    | some r => pure r
    | none => .error ()

def le32 (v : BitVec 32) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8]

def baseKeysName (id : BitVec 32) : List (BitVec 8) := keyName id ++ utf8 ".base-keys"

/-- The 37-byte entry `signed id ‖ base key` of a last-resort use. -/
def baseKeyEntry (signedId : BitVec 32) (baseKey : PublicKey) : List (BitVec 8) :=
  le32 signedId ++ baseKey.serialize

/-- `seen` holds `used` as one of its `used.length`-byte chunks. -/
def hasChunk (seen used : List (BitVec 8)) : Bool :=
  (List.range (seen.length / used.length)).any fun i =>
    (seen.drop (i * used.length)).take used.length == used

/-- `mark_kyber_pre_key_used`: empty a nonempty one-time key; else append the entry to the
last-resort key's `<id>.base-keys`, refusing a malformed file (length not a multiple of 37) and a
reused `(signed id, base key)` pair. Every error returns before any change. -/
def KyberGhost.mark (rd : ReadRule) (F0 : FsFiles) (g : KyberGhost) (id signedId : BitVec 32)
    (baseKey : PublicKey) : Except Unit Unit × KyberGhost :=
  match g.oneTime.get rd F0 (keyName id) with
  | .error _ => (.error (), g)
  | .ok (_ :: _) => (.ok (), { g with oneTime := g.oneTime.put (keyName id) [] })
  | .ok [] =>
    match g.lastResort.get rd F0 (baseKeysName id) with
    | .error _ => (.error (), g)
    | .ok seen =>
      let used := baseKeyEntry signedId baseKey
      if seen.length % used.length ≠ 0 then (.error (), g)
      else if hasChunk seen used then (.error (), g)
      else (.ok (), { g with lastResort := g.lastResort.put (baseKeysName id) (seen ++ used) })

/-! ## All stores, and what `Stores::commit` writes -/

/-- The stores of `Stores::open()`, with their changes. -/
structure StoresGhost where
  identity : IdGhost
  signed : DirGhost
  kyber : KyberGhost
  oneTime : DirGhost
  sessions : DirGhost
  pub : DirGhost

/-- `Stores::open()`: the eight directories, nothing changed. -/
def StoresGhost.opened : StoresGhost where
  identity := ⟨.new [], .new (utf8 "identities")⟩
  signed := .new (utf8 "signed-pre-keys")
  kyber := ⟨.new (utf8 "one-time-kyber-pre-keys"), .new (utf8 "last-resort-kyber-pre-keys")⟩
  oneTime := .new (utf8 "one-time-pre-keys")
  sessions := .new (utf8 "sessions")
  pub := .new (utf8 "public")

/-- `Stores::commit`'s writes, in order: own, peers, signed, Kyber one-time, Kyber last-resort,
one-time, sessions, public; each `Dir` in first-change order. -/
def StoresGhost.writes (g : StoresGhost) : List (List (BitVec 8) × List (BitVec 8)) :=
  g.identity.own.writes ++ g.identity.peers.writes ++ g.signed.writes ++
    g.kyber.oneTime.writes ++ g.kyber.lastResort.writes ++ g.oneTime.writes ++
    g.sessions.writes ++ g.pub.writes

end CryptoVerification.SignalSession.Cli
