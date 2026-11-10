/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
import all Init.Data.Range.Basic

/-!
# SPQR V1: symmetric key chain (`Chain`, `src/chain.rs` and `src/lib.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use only part of this file (see
`Computational/docs/TRUSTED_BASE.md`): the rest (the private self-test drivers `run*`, `sendMany`,
`recvAndCheckAll`, `testHkdf` and `testShaCompress`, and the `isPanic` helpers of `ChainError`
and `ChainResult`) is checked by Lean.

Panic-explicit specification of SPQR's symmetric per-epoch, per-direction hash chain (`src/chain.rs`
and `src/lib.rs`): `HkdfFn`, `spqrHkdfWith`, `ChainPanic`, `ChainError`, `ChainResult`, bounded
skipped-key store `KeyHistory` (`get`, `add`, `gc`), directional chain state `ChainEpochDirection`
(`nextKey`, `key`), and multi-epoch `ChainEpoch` / `Chain` (`new`, `addEpoch`, `sendKey`, `recvKey`,
`intoPb`, `fromPb`, `chainFromVersionNegotiation`, `chainFrom`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.HKDF (hkdfExpand)

/-! ## Helper functions and HKDF parameter signature -/

/-- Signature of `kdf::hkdf_to_vec` / `kdf::hkdf_to_slice`: `salt → ikm → info → okm_len → Bytes`. -/
abbrev HkdfFn := Bytes → Bytes → Bytes → Nat → Bytes

/-- HKDF-SHA256 instantiation of `HkdfFn` over compression function `F` (`src/kdf.rs:14–18`). -/
def spqrHkdfWith (F : ShaState → Bytes → ShaState) : HkdfFn :=
  fun salt ikm info okmLen => hkdfExpand F (hmacWith F salt ikm) info okmLen

def asciiBytes (s : String) : Bytes :=
  s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- Lexicographical `<` on byte slices. -/
def bytesLt : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else bytesLt xs ys

/-- Rust panic sites in `src/chain.rs`. -/
inductive ChainPanic where
  /-- `src/chain.rs:149`: `current_key < params.max_ooo_keys_or_default()` in `KeyHistory::gc`. -/
  | gcKeyUnderflow
  /-- `src/chain.rs:157`: `&self.data[i..i + 4]` out of bounds in `KeyHistory::gc`. -/
  | gcSliceBounds
  /-- `src/chain.rs:191`: `self.data.len() % KEY_SIZE != 0` in `KeyHistory::get`. -/
  | keyHistoryUnaligned
  /-- `src/chain.rs:192`: `at + max_ooo_keys_or_default()` `u32` overflow in `KeyHistory::get`. -/
  | keyHistoryAddOverflow
  /-- `src/chain.rs:230`: `next.len() != 32` in `ChainEpochDirection::next_key_internal`. -/
  | nextKeyBadLen
  /-- `src/chain.rs:231, 266, 271, 280`: `u32` addition overflow on `ctr`. -/
  | ctrOverflow
  /-- `src/chain.rs:361`: `self.current_epoch + 1` `u64` overflow in `Chain::add_epoch`. -/
  | addEpochOverflow
  /-- `src/chain.rs:361`: `epoch_secret.epoch != self.current_epoch + 1` in `Chain::add_epoch`. -/
  | addEpochMismatch
  /-- `src/chain.rs:405, 413, 421`: `self.links[epoch_index]` out of bounds. -/
  | linksOutOfBounds
  deriving DecidableEq, Repr, Inhabited

/-- Error or panic outcome of a fallible chain operation. -/
inductive ChainError where
  | err (e : Error)
  | panic (p : ChainPanic)
  deriving DecidableEq, Repr, Inhabited

namespace ChainError

def isPanic : ChainError → Bool
  | .panic _ => true
  | .err _ => false

end ChainError

abbrev ChainResult (α : Type) := Except ChainError α

namespace ChainResult

def ofPanic (r : Except ChainPanic α) : ChainResult α :=
  match r with
  | .ok v => .ok v
  | .error p => .error (.panic p)

def ofError (r : Except Error α) : ChainResult α :=
  match r with
  | .ok v => .ok v
  | .error e => .error (.err e)

def isPanic (r : ChainResult α) : Bool :=
  match r with
  | .ok _ => false
  | .error e => e.isPanic

end ChainResult

/-! ## `KeyHistory` (`src/chain.rs:91–208`) -/

/-- Skipped-key table storing 36-byte entries `[u8; 4][u8; 32]` (4-byte BE index + 32-byte key). -/
structure KeyHistory where
  data : Bytes := []
  deriving DecidableEq, Repr, Inhabited

namespace KeyHistory

def KEY_SIZE : Nat := 4 + 32

def new : KeyHistory :=
  { data := [] }

def add (self : KeyHistory) (k : BitVec 32 × Bytes) (_params : ChainParamsPB) : KeyHistory :=
  { data := self.data ++ toBEBytes 4 k.1 ++ k.2 }

def clear (_self : KeyHistory) : KeyHistory :=
  { data := [] }

/-- Swap-remove the 36-byte entry at byte offset `myArrayIndex` (`src/chain.rs:175–182`). -/
def remove (self : KeyHistory) (myArrayIndex : Nat) (_params : ChainParamsPB) : KeyHistory :=
  { data :=
      if myArrayIndex + KEY_SIZE < self.data.length then
        let newEnd := self.data.length - KEY_SIZE
        let moved := self.data.drop newEnd
        let prefixBytes := self.data.take myArrayIndex
        let restBytes := (self.data.take newEnd).drop (myArrayIndex + KEY_SIZE)
        (prefixBytes ++ moved ++ restBytes).take newEnd
      else
        self.data.take myArrayIndex }

theorem remove_length_lt (self : KeyHistory) (i : Nat) (params : ChainParamsPB)
    (hi : i < self.data.length) :
    (self.remove i params).data.length < self.data.length := by
  simp only [remove, KEY_SIZE]
  by_cases h : i + (4 + 32) < self.data.length <;> simp [h] <;> omega

/-- Inner `while i < self.data.len()` loop of `KeyHistory::gc` (`src/chain.rs:155–166`). -/
def gcLoop (self : KeyHistory) (trimHorizon : Bytes) (params : ChainParamsPB) (i : Nat) :
    Except ChainPanic KeyHistory :=
  if h : i < self.data.length then
    if self.data.length < i + 4 then
      .error .gcSliceBounds
    else
      let entryKey := (self.data.drop i).take 4
      if bytesLt entryKey trimHorizon then
        have _hlt : (self.remove i params).data.length < self.data.length :=
          remove_length_lt self i params h
        gcLoop (self.remove i params) trimHorizon params i
      else
        gcLoop self trimHorizon params (i + KEY_SIZE)
  else
    .ok self
termination_by self.data.length - i
decreasing_by
  · omega
  · simp only [KEY_SIZE]; omega

/-- `KeyHistory::gc(&mut self, current_key: u32, params: &pqrpb::ChainParams)`
(`src/chain.rs:145–168`).
Panics with `.gcKeyUnderflow` at `src/chain.rs:149` if `self.data.len() >= trim_size * 36` and
`current_key < max_ooo_keys_or_default()`. -/
def gc (self : KeyHistory) (currentKey : BitVec 32) (params : ChainParamsPB) :
    Except ChainPanic KeyHistory :=
  if self.data.length ≥ params.trimSize * KEY_SIZE then
    let maxOoo := params.maxOooKeysOrDefault
    if currentKey < maxOoo then
      .error .gcKeyUnderflow
    else
      let trimHorizon := toBEBytes 4 (currentKey - maxOoo)
      gcLoop self trimHorizon params 0
  else
    .ok self

/-- Inner `for i in (0..self.data.len()).step_by(Self::KEY_SIZE)` loop of `KeyHistory::get`
(`src/chain.rs:197–203`). -/
def getLoop (self : KeyHistory) (atIdx : BitVec 32) (want : Bytes) (params : ChainParamsPB)
    (i : Nat) : ChainResult (KeyHistory × Bytes) :=
  if _h : i < self.data.length then
    if (self.data.drop i).take 4 == want then
      let out := (self.data.drop (i + 4)).take 32
      let self' := self.remove i params
      .ok (self', out)
    else
      getLoop self atIdx want params (i + KEY_SIZE)
  else
    .error (.err (.keyAlreadyRequested atIdx))
termination_by self.data.length - i
decreasing_by
  simp only [KEY_SIZE]; omega

/-- `KeyHistory::get` (`src/chain.rs:185–207`): retrieves and swap-removes the key for `atIdx`,
checking 36-byte alignment, `u32` overflow on `atIdx + maxOoo`, and the trim horizon `currentCtr`. -/
def get (self : KeyHistory) (atIdx currentCtr : BitVec 32) (params : ChainParamsPB) :
    ChainResult (KeyHistory × Bytes) :=
  if self.data.length % KEY_SIZE != 0 then
    .error (.panic .keyHistoryUnaligned)
  else
    let maxOoo := params.maxOooKeysOrDefault
    if atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32 then
      .error (.panic .keyHistoryAddOverflow)
    else if atIdx + maxOoo < currentCtr then
      .error (.err (.keyTrimmed atIdx))
    else
      let want := toBEBytes 4 atIdx
      getLoop self atIdx want params 0

end KeyHistory

/-! ## `ChainEpochDirection` (`src/chain.rs:99–104, 210–321`) -/

/-- Directional chain state within one epoch (`src/chain.rs:99–104`). -/
structure ChainEpochDirection where
  ctr : BitVec 32
  next : Bytes
  prev : KeyHistory
  deriving DecidableEq, Repr, Inhabited

def chainNextInfo : Bytes :=
  asciiBytes "Signal PQ Ratchet V1 Chain Next"

namespace ChainEpochDirection

def new (k : Bytes) : ChainEpochDirection :=
  { ctr := 0#32
    prev := KeyHistory.new
    next := k }

/-- `ChainEpochDirection::next_key_internal` (`src/chain.rs:229–246`): advances `(next, ctr)` via
64-byte HKDF (`next' = out[..32]`, `key = out[32..64]`), panicking if `next.length != 32` or
`ctr == u32::MAX`. -/
def nextKeyInternal (hkdf : HkdfFn) (next : Bytes) (ctr : BitVec 32) :
    Except ChainPanic (Bytes × BitVec 32 × (BitVec 32 × Bytes)) :=
  if next.length != 32 then
    .error .nextKeyBadLen
  else if ctr == 0xffffffff#32 then
    .error .ctrOverflow
  else
    let ctr' := ctr + 1#32
    let salt := List.replicate 32 0#8
    let info := toBEBytes 4 ctr' ++ chainNextInfo
    let genr8r := hkdf salt next info 64
    let next' := genr8r.take 32
    let key := (genr8r.drop 32).take 32
    .ok (next', ctr', (ctr', key))

theorem nextKeyInternal_ctr (hkdf : HkdfFn) (next next' : Bytes) (ctr ctr' : BitVec 32)
    (k : BitVec 32 × Bytes)
    (h : nextKeyInternal hkdf next ctr = .ok (next', ctr', k)) :
    ctr'.toNat = ctr.toNat + 1 := by
  unfold nextKeyInternal at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  rename_i hctr
  have hne : ctr ≠ 0xffffffff#32 := by simpa using hctr
  have hlt : ctr.toNat < 4294967295 := by
    have := ctr.isLt
    have : ctr.toNat ≠ 4294967295 := fun heq => hne (BitVec.eq_of_toNat_eq heq)
    omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `ChainEpochDirection::next_key(&mut self) -> (u32, Vec<u8>)` (`src/chain.rs:222–225`). -/
def nextKey (hkdf : HkdfFn) (self : ChainEpochDirection) :
    Except ChainPanic (ChainEpochDirection × (BitVec 32 × Bytes)) := do
  let (next', ctr', out) ← nextKeyInternal hkdf self.next self.ctr
  return ({ self with next := next', ctr := ctr' }, out)

/-- Inner `while at > self.ctr + 1` loop of `ChainEpochDirection::key` (`src/chain.rs:271–287`). -/
def keyAdvanceLoop (hkdf : HkdfFn) (self : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) : ChainResult ChainEpochDirection :=
  if _h : self.ctr.toNat + 1 < atIdx.toNat then
    match hnk : nextKeyInternal hkdf self.next self.ctr with
    | .error p => .error (.panic p)
    | .ok (next', ctr', k) =>
      have _hctr' : ctr'.toNat = self.ctr.toNat + 1 :=
        nextKeyInternal_ctr hkdf self.next next' self.ctr ctr' k hnk
      let maxOoo := params.maxOooKeysOrDefault
      if ctr'.toNat + maxOoo.toNat ≥ 2 ^ 32 then
        .error (.panic .ctrOverflow)
      else
        let prev' :=
          if ctr' + maxOoo ≥ atIdx then
            self.prev.add k params
          else
            self.prev
        keyAdvanceLoop hkdf { ctr := ctr', next := next', prev := prev' } atIdx params
  else if self.ctr == 0xffffffff#32 then
    -- Unreachable when `self.ctr < atIdx`, included for completeness of `self.ctr + 1` check.
    .error (.panic .ctrOverflow)
  else
    .ok self
termination_by atIdx.toNat - self.ctr.toNat
decreasing_by
  omega

/-- `ChainEpochDirection::key(&mut self, at: u32, params: &pqrpb::ChainParams) -> Result<Vec<u8>, Error>`
(`src/chain.rs:248–297`). -/
def key (hkdf : HkdfFn) (self : ChainEpochDirection) (atIdx : BitVec 32)
    (params : ChainParamsPB) : ChainResult (ChainEpochDirection × Bytes) :=
  if atIdx < self.ctr then do
    let (prev', out) ← self.prev.get atIdx self.ctr params
    return ({ self with prev := prev' }, out)
  else if atIdx == self.ctr then
    .error (.err (.keyAlreadyRequested atIdx))
  else
    if atIdx - self.ctr > params.maxJumpOrDefault then
      .error (.err (.keyJump self.ctr atIdx))
    else
      let maxOoo := params.maxOooKeysOrDefault
      if self.ctr.toNat + maxOoo.toNat ≥ 2 ^ 32 then
        .error (.panic .ctrOverflow)
      else do
        let self0 :=
          if atIdx > self.ctr + maxOoo then
            { self with prev := self.prev.clear }
          else
            self
        let self1 ← keyAdvanceLoop hkdf self0 atIdx params
        let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr params)
        let self2 := { self1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ←
          ChainResult.ofPanic (nextKeyInternal hkdf self2.next self2.ctr)
        return ({ self2 with next := next', ctr := ctr' }, outKey)

def intoPb (self : ChainEpochDirection) : EpochDirectionPB :=
  { ctr := self.ctr
    next := self.next
    prev := self.prev.data }

/-- `ChainEpochDirection::from_pb` (`src/chain.rs:307–316`), rejecting non-empty `next` of length
`≠ 32`. -/
def fromPb (pb : EpochDirectionPB) : Except Error ChainEpochDirection :=
  if !pb.next.isEmpty && pb.next.length != 32 then
    .error .stateDecode
  else
    .ok { ctr := pb.ctr, next := pb.next, prev := { data := pb.prev } }

def clearNext (self : ChainEpochDirection) : ChainEpochDirection :=
  { self with next := [] }

end ChainEpochDirection

/-! ## `ChainEpoch` and `Chain` (`src/chain.rs:106–125, 323–463`) -/

/-- Send and receive chains of a single epoch (`src/chain.rs:107–110`). -/
structure ChainEpoch where
  send : ChainEpochDirection
  recv : ChainEpochDirection
  deriving DecidableEq, Repr, Inhabited

/-- Full symmetric chain state (`src/chain.rs:113–121`). -/
structure Chain where
  dir : Direction
  currentEpoch : Epoch
  sendEpoch : Epoch
  links : List ChainEpoch
  nextRoot : Bytes
  params : ChainParamsPB
  deriving DecidableEq, Repr, Inhabited

def EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH : Nat := 1

/-- `"Signal PQ Ratchet V1 Chain  Start"` (`src/chain.rs:338`; two spaces before `Start`). -/
def chainStartInfo : Bytes :=
  asciiBytes "Signal PQ Ratchet V1 Chain  Start"

def chainAddEpochInfo : Bytes :=
  asciiBytes "Signal PQ Ratchet V1 Chain Add Epoch"

namespace Chain

def cedForDirection (genr8r : Bytes) (dir : Direction) : ChainEpochDirection :=
  ChainEpochDirection.new <|
    match dir with
    | .a2b => (genr8r.drop 32).take 32
    | .b2a => (genr8r.drop 64).take 32

/-- `Chain::new` (`src/chain.rs:333–354`). -/
def new (hkdf : HkdfFn) (initialKey : Bytes) (dir : Direction) (params : ChainParamsPB) :
    Except Error Chain :=
  let salt := List.replicate 32 0#8
  let genr8r := hkdf salt initialKey chainStartInfo 96
  let epoch0 : ChainEpoch :=
    { send := cedForDirection genr8r dir
      recv := cedForDirection genr8r dir.switch }
  .ok
    { dir := dir
      currentEpoch := 0#64
      sendEpoch := 0#64
      links := [epoch0]
      nextRoot := genr8r.take 32
      params := params }

/-- `Chain::add_epoch(&mut self, epoch_secret: EpochSecret)` (`src/chain.rs:356–375`).
* Panics with `.addEpochOverflow` if `self.current_epoch == u64::MAX` (`src/chain.rs:361`).
* Panics with `.addEpochMismatch` if `epoch_secret.epoch != self.current_epoch + 1`
  (`src/chain.rs:361`). -/
def addEpoch (hkdf : HkdfFn) (self : Chain) (epochSecret : EpochSecret) :
    Except ChainPanic Chain :=
  if self.currentEpoch == 0xffffffffffffffff#64 then
    .error .addEpochOverflow
  else if epochSecret.epoch != self.currentEpoch + 1#64 then
    .error .addEpochMismatch
  else
    let genr8r := hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96
    let newLink : ChainEpoch :=
      { send := cedForDirection genr8r self.dir
        recv := cedForDirection genr8r self.dir.switch }
    .ok
      { self with
        currentEpoch := epochSecret.epoch
        nextRoot := genr8r.take 32
        links := self.links ++ [newLink] }

/-- `Chain::epoch_idx(&mut self, epoch: Epoch) -> Result<usize, Error>` (`src/chain.rs:378–388`). -/
def epochIdx (self : Chain) (epoch : Epoch) : Except Error Nat :=
  if epoch > self.currentEpoch then
    .error (.epochOutOfRange epoch)
  else
    let back := (self.currentEpoch - epoch).toNat
    let linksLen := self.links.length
    if back ≥ linksLen then
      .error (.epochOutOfRange epoch)
    else
      .ok (linksLen - 1 - back)

/-- Clear `send.next` on the first `n` elements of `links` (`for i in 0..epoch_index` in
`Chain::send_key`, `src/chain.rs:403–406`). -/
def clearSendNextPrefix : Nat → List ChainEpoch → List ChainEpoch
  | 0, xs => xs
  | _ + 1, [] => []
  | n + 1, x :: xs => { x with send := x.send.clearNext } :: clearSendNextPrefix n xs

/-- Derive the next sending key `(index, key)` in `epoch`, dropping older epochs when the send epoch
advances. `Chain::send_key(&mut self, epoch: Epoch) -> Result<(u32, Vec<u8>), Error>`
(`src/chain.rs:390–414`). -/
def sendKey (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) :
    ChainResult (Chain × (BitVec 32 × Bytes)) :=
  if epoch < self.sendEpoch then
    .error (.err (.sendKeyEpochDecreased self.sendEpoch epoch))
  else do
    let epochIndex0 ← ChainResult.ofError (self.epochIdx epoch)
    let (self1, epochIndex) :=
      if self.sendEpoch != epoch then
        let dropCount := epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
        let epochIndex' := epochIndex0 - dropCount
        let links1 := self.links.drop dropCount
        let links2 := clearSendNextPrefix epochIndex' links1
        ({ self with sendEpoch := epoch, links := links2 }, epochIndex')
      else
        (self, epochIndex0)
    match self1.links[epochIndex]? with
    | none => .error (.panic .linksOutOfBounds)
    | some link => do
      let (send', out) ← ChainResult.ofPanic (link.send.nextKey hkdf)
      let links' := self1.links.set epochIndex { link with send := send' }
      return ({ self1 with links := links' }, out)

/-- Derive the receiving key for message `index` of `epoch`; epoch 0, index 0 yields the empty key.
`Chain::recv_key(&mut self, epoch: Epoch, index: u32) -> Result<Vec<u8>, Error>`
(`src/chain.rs:416–422`). -/
def recvKey (hkdf : HkdfFn) (self : Chain) (epoch : Epoch) (index : BitVec 32) :
    ChainResult (Chain × Bytes) :=
  if epoch == 0#64 && index == 0#32 then
    .ok (self, [])
  else do
    let epochIndex ← ChainResult.ofError (self.epochIdx epoch)
    match self.links[epochIndex]? with
    | none => .error (.panic .linksOutOfBounds)
    | some link => do
      let (recv', out) ← link.recv.key hkdf index self.params
      let links' := self.links.set epochIndex { link with recv := recv' }
      return ({ self with links := links' }, out)

def intoPb (self : Chain) : ChainPB :=
  { direction := self.dir.toI32
    currentEpoch := self.currentEpoch
    sendEpoch := self.sendEpoch
    links := self.links.map fun link =>
      { send := some link.send.intoPb
        recv := some link.recv.intoPb }
    nextRoot := self.nextRoot
    params := some self.params }

def linksFromPb : List ChainEpochPB → Except Error (List ChainEpoch)
  | [] => .ok []
  | link :: rest => do
    let sendPb ←
      match link.send with
      | some s => .ok s
      | none => .error .stateDecode
    let send ← ChainEpochDirection.fromPb sendPb
    let recvPb ←
      match link.recv with
      | some r => .ok r
      | none => .error .stateDecode
    let recv ← ChainEpochDirection.fromPb recvPb
    let tail ← linksFromPb rest
    return { send := send, recv := recv } :: tail

/-- `Chain::from_pb` (`src/chain.rs:444–462`). -/
def fromPb (pb : ChainPB) : Except Error Chain := do
  let dir ←
    match Direction.fromI32? pb.direction with
    | some d => .ok d
    | none => .error .stateDecode
  let links ← linksFromPb pb.links
  let params ←
    match pb.params with
    | some p => .ok p
    | none => .error .stateDecode
  return {
    dir := dir
    currentEpoch := pb.currentEpoch
    sendEpoch := pb.sendEpoch
    nextRoot := pb.nextRoot
    links := links
    params := params
  }

end Chain

/-! ## `chain_from_version_negotiation` and `chain_from` (`src/lib.rs:332–353`) -/

/-- `chain_from_version_negotiation` (`src/lib.rs:332–340`). -/
def chainFromVersionNegotiation (hkdf : HkdfFn) (vn : VersionNegotiationPB) :
    Except Error Chain := do
  let dir ←
    match Direction.fromI32? vn.direction with
    | some d => .ok d
    | none => .error .stateDecode
  let params ←
    match vn.chainParams with
    | some p => .ok p
    | none => .error .chainNotAvailable
  Chain.new hkdf vn.authKey dir params

/-- `chain_from` (`src/lib.rs:342–353`). -/
def chainFrom (hkdf : HkdfFn) (pb : Option ChainPB) (vn : Option VersionNegotiationPB) :
    Except Error Chain :=
  match pb with
  | some pb => Chain.fromPb pb
  | none =>
    match vn with
    | none => .error .chainNotAvailable
    | some vn => chainFromVersionNegotiation hkdf vn

/-! ## Executable guards (`src/chain.rs:465–728`) -/

section Guards

/-- Toy 32-bit mixing compression function used to instantiate `spqrHkdfWith` in guards. -/
 def testShaCompress (st : ShaState) (blk : Bytes) : ShaState :=
  let mix :=
    (blk.foldl
      (fun (acc, idx) (b : BitVec 8) =>
        (acc * 16777619#32 ^^^ (b.zeroExtend 32 <<< ((idx % 4) * 8)), idx + 1))
      (0x811c9dc5#32, 0)).1
  List.Vector.ofFn fun i : Fin 8 =>
    let w := st.get i
    (w.rotateLeft 7 + mix + BitVec.ofNat 32 (i.val * 0x9e3779b9)) ^^^ (w >>> 3)

 def testHkdf : HkdfFn :=
  spqrHkdfWith testShaCompress

 def sendMany (hkdf : HkdfFn) (c : Chain) (epoch : Epoch) :
    Nat → ChainResult (Chain × List (BitVec 32 × Bytes))
  | 0 => .ok (c, [])
  | n + 1 => do
    let (c', sk) ← c.sendKey hkdf epoch
    let (c'', rest) ← sendMany hkdf c' epoch n
    return (c'', sk :: rest)

 def recvAndCheckAll (hkdf : HkdfFn) (c : Chain) (epoch : Epoch) :
    List (BitVec 32 × Bytes) → ChainResult (Chain × Bool)
  | [] => .ok (c, true)
  | (idx, expected) :: rest => do
    let (c', actual) ← c.recvKey hkdf epoch idx
    let (c'', okRest) ← recvAndCheckAll hkdf c' epoch rest
    return (c'', (actual == expected && actual.length == 32) && okRest)

theorem guard_chain_params :
    ChainParams.default.maxJump = 25000#32 ∧
      ChainParams.default.maxOooKeys = 2000#32 ∧
      ChainParams.default.intoPb = { maxJump := 0#32, maxOooKeys := 0#32 } ∧
      ChainParams.default.intoPbTest = { maxJump := 0#32, maxOooKeys := 0#32 } ∧
      ({ maxJump := 10#32, maxOooKeys := 2000#32 : ChainParams }).intoPb =
        { maxJump := 10#32, maxOooKeys := 0#32 } ∧
      ChainParams.default.intoPb.maxJumpOrDefault = 25000#32 ∧
      ChainParams.default.intoPb.maxOooKeysOrDefault = 2000#32 ∧
      ChainParams.default.intoPb.trimSize = 2201 ∧
      ({ maxJump := 5#32, maxOooKeys := 3#32 : ChainParamsPB }).trimSize = 4 ∧
      ({ maxJump := 10#32, maxOooKeys := 10#32 : ChainParamsPB }).trimSize = 12 := by
  decide +kernel

/-- Translation of `test::directions_match` (`src/chain.rs:474–497`). -/
 def runDirectionsMatch : Bool :=
  match Chain.new testHkdf (asciiBytes "1") .a2b ChainParams.default.intoPb,
        Chain.new testHkdf (asciiBytes "1") .b2a ChainParams.default.intoPb with
  | .ok a2b, .ok b2a =>
    match a2b.sendKey testHkdf 0#64 with
    | .ok (a2b, sk1) =>
      match b2a.recvKey testHkdf 0#64 1#32 with
      | .ok (b2a, rk1) =>
        match a2b.addEpoch testHkdf { epoch := 1#64, secret := [2#8] },
              b2a.addEpoch testHkdf { epoch := 1#64, secret := [2#8] } with
        | .ok a2b, .ok b2a =>
          match a2b.sendKey testHkdf 1#64, b2a.recvKey testHkdf 1#64 1#32 with
          | .ok (a2b, sk2), .ok (b2a, rk2) =>
            match sendMany testHkdf a2b 1#64 8 with
            | .ok (a2b, _) =>
              match a2b.sendKey testHkdf 1#64, b2a.recvKey testHkdf 1#64 10#32 with
              | .ok (_, sk3), .ok (_, rk3) =>
                sk1.1 == 1#32 && sk1.2 == rk1 && sk1.2.length == 32 &&
                  sk2.1 == 1#32 && sk2.2 == rk2 && sk2.2 != sk1.2 &&
                  sk3.1 == 10#32 && sk3.2 == rk3 && sk3.2 != sk2.2
              | _, _ => false
            | _ => false
          | _, _ => false
        | _, _ => false
      | _ => false
    | _ => false
  | _, _ => false

theorem guard_directions_match : runDirectionsMatch = true := by
  decide +kernel

/-- Translation of `test::rejects_malformed_next_key_in_serialized_state` (`src/chain.rs:500–509`). -/
theorem guard_rejects_malformed_next_key :
    ChainEpochDirection.fromPb { next := List.replicate 31 0#8 } = .error .stateDecode ∧
      ChainEpochDirection.fromPb { next := List.replicate 33 0#8 } = .error .stateDecode ∧
      (ChainEpochDirection.fromPb { next := [] }).isOk = true ∧
      (ChainEpochDirection.fromPb { next := List.replicate 32 0#8 }).isOk = true := by
  decide +kernel

/-- Translation of `test::previously_returned_key` (`src/chain.rs:512–519`), testing both
`at == self.ctr` (`Ordering::Equal`) and `at < self.ctr` already removed from `KeyHistory`. -/
 def runPreviouslyReturnedKey : Bool :=
  match Chain.new testHkdf (asciiBytes "1") .a2b ChainParams.default.intoPb with
  | .ok a2b =>
    match a2b.recvKey testHkdf 0#64 2#32 with
    | .ok (a2b, k2) =>
      let dup2 := a2b.recvKey testHkdf 0#64 2#32
      match a2b.recvKey testHkdf 0#64 1#32 with
      | .ok (a2b, k1) =>
        let dup1 := a2b.recvKey testHkdf 0#64 1#32
        k2.length == 32 && k1.length == 32 && k1 != k2 &&
          dup2 == .error (.err (.keyAlreadyRequested 2#32)) &&
          dup1 == .error (.err (.keyAlreadyRequested 1#32))
      | _ => false
    | _ => false
  | _ => false

theorem guard_previously_returned_key : runPreviouslyReturnedKey = true := by
  decide +kernel

/-- Translation of `test::very_old_keys_are_trimmed` (`src/chain.rs:522–532`). -/
 def runVeryOldKeysAreTrimmed : Bool :=
  let params := ({ maxJump := 10#32, maxOooKeys := 10#32 : ChainParams }).intoPb
  match Chain.new testHkdf (asciiBytes "1") .a2b params with
  | .ok a2b =>
    match a2b.recvKey testHkdf 0#64 10#32 with
    | .ok (a2b, _) =>
      match a2b.recvKey testHkdf 0#64 12#32 with
      | .ok (a2b, _) =>
        let res1 := a2b.recvKey testHkdf 0#64 1#32
        match a2b.recvKey testHkdf 0#64 2#32 with
        | .ok (_, k2) =>
          res1 == .error (.err (.keyTrimmed 1#32)) && k2.length == 32
        | _ => false
      | _ => false
    | _ => false
  | _ => false

theorem guard_very_old_keys_are_trimmed : runVeryOldKeysAreTrimmed = true := by
  decide +kernel

/-- Translation of `test::out_of_order_keys` (`src/chain.rs:535–548`): send 12 keys on `a2b` and
receive them in a shuffled permutation `[7, 3, 12, 1, 9, 5, 11, 2, 8, 4, 10, 6]` on `b2a`. -/
 def runOutOfOrderKeys : Bool :=
  match Chain.new testHkdf (asciiBytes "1") .a2b ChainParams.default.intoPb,
        Chain.new testHkdf (asciiBytes "1") .b2a ChainParams.default.intoPb with
  | .ok a2b, .ok b2a =>
    match sendMany testHkdf a2b 0#64 12 with
    | .ok (_, sent) =>
      let order : List Nat := [6, 2, 11, 0, 8, 4, 10, 1, 7, 3, 9, 5]
      let shuffled := order.filterMap fun i => sent[i]?
      match recvAndCheckAll testHkdf b2a 0#64 shuffled with
      | .ok (_, okAll) => shuffled.length == 12 && okAll
      | _ => false
    | _ => false
  | _, _ => false

theorem guard_out_of_order_keys : runOutOfOrderKeys = true := by
  decide +kernel

/-- Translation of `test::clear_old_send_keys` (`src/chain.rs:551–564`) plus multi-epoch link
eviction (`EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1`, `src/chain.rs:395–407`). -/
 def runClearOldSendKeys : Bool :=
  match Chain.new testHkdf (asciiBytes "1") .a2b ChainParams.default.intoPb with
  | .ok a2b =>
    match a2b.sendKey testHkdf 0#64 with
    | .ok (a2b, _) =>
      match a2b.sendKey testHkdf 0#64 with
      | .ok (a2b, _) =>
        match a2b.addEpoch testHkdf { epoch := 1#64, secret := [2#8] } with
        | .ok a2b =>
          match a2b.sendKey testHkdf 1#64 with
          | .ok (a2b, _) =>
            let decreasedErr := a2b.sendKey testHkdf 0#64
            let epoch0Cleared :=
              match a2b.links[0]? with
              | some link0 => link0.send.next.isEmpty
              | none => false
            match a2b.addEpoch testHkdf { epoch := 2#64, secret := [3#8] } with
            | .ok a2b =>
              match a2b.sendKey testHkdf 2#64 with
              | .ok (a2b, _) =>
                let epoch0Evicted := a2b.recvKey testHkdf 0#64 1#32
                let epoch1Cleared :=
                  match a2b.links[0]? with
                  | some link1 => link1.send.next.isEmpty
                  | none => false
                decreasedErr == .error (.err (.sendKeyEpochDecreased 1#64 0#64)) &&
                  epoch0Cleared &&
                  a2b.links.length == 2 &&
                  epoch0Evicted == .error (.err (.epochOutOfRange 0#64)) &&
                  epoch1Cleared
              | _ => false
            | _ => false
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

theorem guard_clear_old_send_keys : runClearOldSendKeys = true := by
  decide +kernel

/-- Translation of `test::key_history_prop_test` (`src/chain.rs:588–642`). -/
 def runKeyHistoryTrace : Bool :=
  let params : ChainParamsPB := { maxOooKeys := 3#32, maxJump := 5#32 }
  let k (n : BitVec 8) : Bytes := List.replicate 32 n
  let kh0 := KeyHistory.new
  let kh1 := (((kh0.add (0#32, k 10#8) params).add (1#32, k 11#8) params).add
    (2#32, k 12#8) params)
  match kh1.gc 5#32 params with
  | .ok kh1Gc =>
    let kh2 := kh1Gc.add (3#32, k 13#8) params
    match kh2.gc 5#32 params with
    | .ok kh2Gc =>
      let trimmed0 := kh2Gc.get 0#32 5#32 params
      let trimmed1 := kh2Gc.get 1#32 5#32 params
      match kh2Gc.get 2#32 5#32 params with
      | .ok (kh3, out2) =>
        let dup2 := kh3.get 2#32 5#32 params
        match kh3.get 3#32 5#32 params with
        | .ok (kh4, out3) =>
          kh1Gc.data.length == 3 * 36 &&
            kh2Gc.data.length == 2 * 36 &&
            trimmed0 == .error (.err (.keyTrimmed 0#32)) &&
            trimmed1 == .error (.err (.keyTrimmed 1#32)) &&
            out2 == k 12#8 &&
            dup2 == .error (.err (.keyAlreadyRequested 2#32)) &&
            out3 == k 13#8 &&
            kh4.data.isEmpty
        | _ => false
      | _ => false
    | _ => false
  | _ => false

theorem guard_key_history_trace : runKeyHistoryTrace = true := by
  decide +kernel

/-- Translation of `test::ced_prop_test` (`src/chain.rs:665–727`). -/
 def runCedTrace : Bool :=
  let params : ChainParamsPB := { maxOooKeys := 3#32, maxJump := 5#32 }
  let ced0 := ChainEpochDirection.new (List.replicate 32 1#8)
  let tooHigh0 := ced0.key testHkdf 6#32 params
  match ced0.nextKey testHkdf with
  | .ok (ced1, (idx1, _)) =>
    match ced1.key testHkdf 3#32 params with
    | .ok (ced2, _) =>
      match ced2.key testHkdf 8#32 params with
      | .ok (ced3, _) =>
        let old2 := ced3.key testHkdf 2#32 params
        let old4 := ced3.key testHkdf 4#32 params
        match ced3.key testHkdf 5#32 params,
              ced3.key testHkdf 6#32 params,
              ced3.key testHkdf 7#32 params with
        | .ok (ced4, k5), .ok (_, k6), .ok (_, k7) =>
          let dup5 := ced4.key testHkdf 5#32 params
          tooHigh0 == .error (.err (.keyJump 0#32 6#32)) &&
            idx1 == 1#32 &&
            ced2.prev.data.length == 36 &&
            ced3.prev.data.length == 3 * 36 &&
            old2 == .error (.err (.keyTrimmed 2#32)) &&
            old4 == .error (.err (.keyTrimmed 4#32)) &&
            k5.length == 32 && k6.length == 32 && k7.length == 32 &&
            dup5 == .error (.err (.keyAlreadyRequested 5#32))
        | _, _, _ => false
      | _ => false
    | _ => false
  | _ => false

theorem guard_ced_trace : runCedTrace = true := by
  decide +kernel

 def runChainPbAndVersionNegotiation : Bool :=
  let vnOk : VersionNegotiationPB :=
    { authKey := asciiBytes "seed"
      direction := Direction.a2b.toI32
      minVersion := 1#32
      chainParams := some ChainParams.default.intoPb }
  let vnBadDir : VersionNegotiationPB := { vnOk with direction := 99#32 }
  let vnNoParams : VersionNegotiationPB := { vnOk with chainParams := none }
  match chainFrom testHkdf none (some vnOk) with
  | .ok c0 =>
    match c0.recvKey testHkdf 0#64 0#32 with
    | .ok (c0', emptyKey) =>
      let pb := c0'.intoPb
      let roundTrip := Chain.fromPb pb
      let fromPbCall := chainFrom testHkdf (some pb) none
      let errNone := chainFrom testHkdf none none
      let errBadDir := chainFromVersionNegotiation testHkdf vnBadDir
      let errNoParams := chainFromVersionNegotiation testHkdf vnNoParams
      let errEpochHigh := c0'.recvKey testHkdf 5#64 1#32
      emptyKey.isEmpty && c0' == c0 &&
        roundTrip == .ok c0' &&
        fromPbCall == .ok c0' &&
        errNone == .error .chainNotAvailable &&
        errBadDir == .error .stateDecode &&
        errNoParams == .error .chainNotAvailable &&
        errEpochHigh == .error (.err (.epochOutOfRange 5#64))
    | _ => false
  | _ => false

theorem guard_chain_pb_and_version_negotiation :
    runChainPbAndVersionNegotiation = true := by
  decide +kernel

/-- Explicit panic site guards (`src/chain.rs:149, 157, 191, 192, 230, 231, 266, 280, 361`). -/
theorem guard_chain_panics :
    (KeyHistory.gc { data := List.replicate (4 * 36) 0#8 } 2#32
      { maxOooKeys := 3#32, maxJump := 5#32 }) = .error .gcKeyUnderflow ∧
    (KeyHistory.gc { data := List.replicate (4 * 36) 0xff#8 ++ [1#8, 2#8] } 5#32
      { maxOooKeys := 3#32, maxJump := 5#32 }) = .error .gcSliceBounds ∧
    (KeyHistory.get { data := [1#8, 2#8, 3#8] } 1#32 2#32 ChainParams.default.intoPb) =
      .error (.panic .keyHistoryUnaligned) ∧
    (KeyHistory.get KeyHistory.new 0xfffffff0#32 0xffffffff#32 ChainParams.default.intoPb) =
      .error (.panic .keyHistoryAddOverflow) ∧
    (ChainEpochDirection.nextKeyInternal testHkdf [1#8] 0#32) = .error .nextKeyBadLen ∧
    (ChainEpochDirection.nextKeyInternal testHkdf (List.replicate 32 0#8) 0xffffffff#32) =
      .error .ctrOverflow ∧
    (ChainEpochDirection.key testHkdf
      { ctr := 0xfffffff0#32, next := List.replicate 32 0#8, prev := KeyHistory.new }
      0xfffffff5#32 { maxJump := 10#32, maxOooKeys := 32#32 }) =
      .error (.panic .ctrOverflow) ∧
    (ChainEpochDirection.key testHkdf
      { ctr := 0xffffffef#32, next := List.replicate 32 0#8, prev := KeyHistory.new }
      0xfffffff5#32 { maxJump := 10#32, maxOooKeys := 16#32 }) =
      .error (.panic .ctrOverflow) ∧
    (Chain.addEpoch testHkdf
      { dir := .a2b, currentEpoch := 0xffffffffffffffff#64, sendEpoch := 0#64,
        links := [], nextRoot := List.replicate 32 0#8, params := ChainParams.default.intoPb }
      { epoch := 0#64, secret := [1#8] }) = .error .addEpochOverflow ∧
    (Chain.addEpoch testHkdf
      { dir := .a2b, currentEpoch := 0#64, sendEpoch := 0#64,
        links := [], nextRoot := List.replicate 32 0#8, params := ChainParams.default.intoPb }
      { epoch := 2#64, secret := [1#8] }) = .error .addEpochMismatch := by
  decide +kernel

end Guards

end CryptoVerification.LibsignalSpqrV1
