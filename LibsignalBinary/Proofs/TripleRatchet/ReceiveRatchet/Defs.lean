/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Deserialize

/-!
# `TripleRatchet` Memory Layout and Receive-Ratchet Conversion Specifications

Defines the 264-byte `trAt` / `trResultAt` layout predicates for
`libsignal_protocol::triple_ratchet::TripleRatchet` and the specifications of
`TripleRatchet::from_session_state` (`0x1c60c`) and `TripleRatchet::apply_to_session_state` (`0x1cbf4`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters

/-! ## Symbol names -/

/-- `<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state` (image offset `0x1c60c`). -/
abbrev trFromName : String :=
  "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"

/-- `<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state` (image offset `0x1cbf4`). -/
abbrev trApplyName : String :=
  "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state"

/-- `<libsignal_core::curve::PublicKey>::deserialize` (`0x3db50`). -/
abbrev deserializeName : String :=
  "<libsignal_core::curve::PublicKey>::deserialize"

/-! ## `PublicKey::deserialize` callee hypothesis -/

/-- `PublicKey::deserialize` (`0x3db50`) meets `deserializeSpec b` on `tripleRatchetProgAtExt b ext`. -/
def DeserializeOkExt (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr deserializeName)
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec b)

/-- `PublicKey::deserialize` (`0x3db50`) meets `deserializeSpec b` on `tripleRatchetProgAt`. -/
def DeserializeOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  DeserializeOkExt b (tripleRatchetExterns C ctl abs)

/-! ## Stack budgets -/

/-- Stack budget for `TR::from_session_state`: 496-byte frame plus `dropVecChainStack`. -/
abbrev trFromStack : Nat := 496 + dropVecChainStack

/-- Stack budget for `TR::apply_to_session_state`: 224-byte frame plus `extHookStack`. -/
abbrev trApplyStack : Nat := 224 + extHookStack

/-! ## `TripleRatchet` layout predicate (264 bytes) -/

/-- Ghost layout of a 264-byte `TripleRatchet` in memory (`ratchet` at `+0x00..+0xb0` and `pqr_state` pin at `+0xb0..+0xc8`). -/
structure TrGhost where
  /-- Ghost layout of `ratchet: RatchetState` at `+0x00..+0xb0` (176 bytes). -/
  ratchet : RatchetGhost
  /-- Buffer pin `(cap, ptr)` of `pqr_state: Vec<u8>` at `+0xb0..+0xc8` (24 bytes). -/
  pq : VecPin

/-- Memory layout of a 264-byte `TripleRatchet` at `t` representing `tr` with ghost layout `G`:
* `+0x00..+0xb0` (176 B): `ratchet: RatchetState` (`ratchetAt A t G.ratchet tr.ratchet`), with
  clamped sender-chain private key (`Ratchet.clampScalar`);
* `+0xb0..+0xc8` (24 B): `pqr_state: Vec<u8>` (`vecU8At A (t + 0xb0) G.pq.cap G.pq.ptr tr.pqrState`);
* `+0xc8..+0xe8` (32 B): `local_identity_key: IdentityKey`;
* `+0xe8..+0x108` (32 B): `remote_identity_key: IdentityKey`. -/
def trAt (A : RustAlloc) (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
    ratchetAt A t G.ratchet tr.ratchet ∗
    vecU8At A (t + 0xb0#64) G.pq.cap G.pq.ptr tr.pqrState ∗
    ((t + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((t + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

/-- 264-byte `Result<TripleRatchet, SignalProtocolError>` at `r`: `trAt` on `Ok tr` (moving
`receiver_chains` and `pqr_state` from `G`), or `errResultAt A (utf8 "decrypt") 264 r e` on `Err e`. -/
def trResultAt (A : RustAlloc) (r : BitVec 64) (G : SessionGhost) :
    Except SignalProtocolError (TripleRatchet (List (BitVec 8))) → SepProp
  | .ok tr =>
    ∃∗ senderPad : List (BitVec 8),
      trAt A r ⟨⟨G.chainsCap, G.chainsPtr, G.chains, senderPad⟩, G.pq⟩ tr
  | .error e => errResultAt A (utf8 "decrypt") 264 r e

/-! ## `TripleRatchet::from_session_state` (`0x1c60c`) -/

/-- Updated `SessionGhost` after `TR::from_session_state`: `receiver_chains` (`+0x48`) and
`pq_ratchet_state` (`+0x78`) are replaced by empty `mem::take` headers (`{cap = 0, ptr = align, len = 0}`),
leaving all other fields unchanged (`G.AfterTryDecrypt false G.afterTrFrom`). -/
def _root_.CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost.afterTrFrom (G : SessionGhost) :
    SessionGhost :=
  { G with chainsCap := 0#64, chainsPtr := 8#64, chains := [], pq := ⟨0#64, 1#64⟩ }

/-- Ghost arguments of `TR::from_session_state`. -/
structure TrFromGhost where
  /-- `state: &mut SessionState` (`x0`). -/
  ss : BitVec 64
  /-- Initial ghost layout of `ss`. -/
  G : SessionGhost
  /-- Initial `SessionState` model value. -/
  st : SessionState (List (BitVec 8))
  /-- Sret buffer (`x8`, 264 bytes). -/
  ret : BitVec 64

/-- Pure model result and updated `SessionState` of `TripleRatchet.fromSessionState`. -/
def TrFromGhost.model (x : TrFromGhost) :
    Except SignalProtocolError (TripleRatchet (List (BitVec 8))) ×
      SessionState (List (BitVec 8)) :=
  Mut.exec TripleRatchet.fromSessionState x.st

/-- Specification of `<TripleRatchet>::from_session_state` (`0x1c60c`) in a loaded image `img`
with `self_session = false` (`w1 = 0`, `max_forward_jumps = 25000`). Moves `receiver_chains` and
`pq_ratchet_state` out of `x.ss` (`x.G.afterTrFrom`) and writes `trResultAt A x.ret x.G x.model.1`
to `x.ret` without allocating or panicking (dropping the moved buffers on missing `remote_identity`). -/
def trFromSpec (A : RustAlloc) (img : Obj.Image) : Spec TrFromGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = 0#32 ∧
          s.readReg64 .x8 = x.ret⌝ ∗
          sessionStateAt A x.ss x.G x.st ∗ memRegion x.ret 264 ∗ logOff img ∗
          stackAt s.sp trFromStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜x.G.AfterTryDecrypt false x.G.afterTrFrom ∧ sf.trace = s0.trace⌝ ∗
          sessionStateAt A x.ss x.G.afterTrFrom x.model.2 ∗
          trResultAt A x.ret x.G x.model.1 ∗ logOff img ∗
          stackAt s0.sp trFromStack ∗ A.pool }
    img

/-- `TR::from_session_state` meets `trFromSpec A img` on `tripleRatchetProgAtExt img.base ext`. -/
def TrFromOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr trFromName) (trFromSpec A img)

/-- `TR::from_session_state` meets `trFromSpec A img` on `tripleRatchetProgAt img.base`. -/
def TrFromOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  TrFromOkExt img A (tripleRatchetExterns C ctl abs)

/-! ## `TripleRatchet::apply_to_session_state` (`0x1cbf4`) -/

/-- Relation between initial `SessionGhost` `G`, `TrGhost` `trG`, and final `SessionGhost` `G'`
after `TR::apply_to_session_state`: preserves `localIk`, `remoteIk`, `alice`, `regIds`, `pending`,
and `kyber`, while moving `receiver_chains` and `pqr_state` from `trG` into `G'`. -/
def _root_.CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost.TrApplyRel (G : SessionGhost)
    (trG : TrGhost) (G' : SessionGhost) : Prop :=
  G.Keeps G' ∧ G'.pending = G.pending ∧ G'.kyber = G.kyber ∧
    G'.chainsCap = trG.ratchet.chainsCap ∧ G'.chainsPtr = trG.ratchet.chainsPtr ∧
    G'.chains = trG.ratchet.chains ∧ G'.pq = trG.pq

/-- Ghost arguments of `TR::apply_to_session_state`. -/
structure TrApplyGhost where
  /-- Pointer to `self: TripleRatchet` (`x0`, 264 bytes, consumed). -/
  t : BitVec 64
  /-- Ghost layout of `self`. -/
  trG : TrGhost
  /-- `TripleRatchet` model value. -/
  tr : TripleRatchet (List (BitVec 8))
  /-- `state: &mut SessionState` (`x1`, 344 bytes). -/
  ss : BitVec 64
  /-- Initial ghost layout of `ss`. -/
  G : SessionGhost
  /-- Initial `SessionState` model value. -/
  st : SessionState (List (BitVec 8))

/-- Specification of `<TripleRatchet>::apply_to_session_state` (`0x1cbf4`).
Consumes `trAt A x.t x.trG x.tr` (leaving `memRegion x.t 264`), updates `x.ss` to
`sessionStateAt A x.ss G' (x.tr.applyToSessionState x.st)` with `x.G.TrApplyRel x.trG G'`,
dropping replaced buffers and panicking only on allocator failure (`allocFailedIn`). -/
def trApplySpec (A : RustAlloc) : Spec TrApplyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.t ∧ s.readReg64 .x1 = x.ss⌝ ∗
      trAt A x.t x.trG x.tr ∗ sessionStateAt A x.ss x.G x.st ∗
      stackAt s.sp trApplyStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.TrApplyRel x.trG G'⌝ ∗
        sessionStateAt A x.ss G' (x.tr.applyToSessionState x.st)) ∗
      memRegion x.t 264 ∗ stackAt s0.sp trApplyStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `TR::apply_to_session_state` meets `trApplySpec A` on `tripleRatchetProgAtExt b ext`. -/
def TrApplyOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr trApplyName)
    (trApplySpec A)

/-- `TR::apply_to_session_state` meets `trApplySpec A` on `tripleRatchetProgAt b`. -/
def TrApplyOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  TrApplyOkExt b A (tripleRatchetExterns C ctl abs)

/-! ## Extended-stack (`extHookStack`) budgets and specifications -/

/-- `TR::from_session_state` frame (496 B) + `dropVecChainStackX` (16480 B). -/
abbrev trFromStackX : Nat := 496 + dropVecChainStackX

/-- `TR::apply_to_session_state` frame (224 B) + `dropVecChainStackX` (16480 B). -/
abbrev trApplyStackX : Nat := 224 + dropVecChainStackX

/-- `trFromSpec A img` at `trFromStackX`. -/
def trFromSpecX (A : RustAlloc) (img : Obj.Image) : Spec TrFromGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = 0#32 ∧
          s.readReg64 .x8 = x.ret⌝ ∗
          sessionStateAt A x.ss x.G x.st ∗ memRegion x.ret 264 ∗ logOff img ∗
          stackAt s.sp trFromStackX ∗ A.pool
      post := fun x s0 sf =>
        ⌜x.G.AfterTryDecrypt false x.G.afterTrFrom ∧ sf.trace = s0.trace⌝ ∗
          sessionStateAt A x.ss x.G.afterTrFrom x.model.2 ∗
          trResultAt A x.ret x.G x.model.1 ∗ logOff img ∗
          stackAt s0.sp trFromStackX ∗ A.pool }
    img

/-- `TR::from_session_state` meets `trFromSpecX A img` on `tripleRatchetProgAtExt img.base ext`. -/
def TrFromOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr trFromName) (trFromSpecX A img)

/-- `trApplySpec A` at `trApplyStackX`. -/
def trApplySpecX (A : RustAlloc) : Spec TrApplyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.t ∧ s.readReg64 .x1 = x.ss⌝ ∗
      trAt A x.t x.trG x.tr ∗ sessionStateAt A x.ss x.G x.st ∗
      stackAt s.sp trApplyStackX ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.TrApplyRel x.trG G'⌝ ∗
        sessionStateAt A x.ss G' (x.tr.applyToSessionState x.st)) ∗
      memRegion x.t 264 ∗ stackAt s0.sp trApplyStackX ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `TR::apply_to_session_state` meets `(trApplySpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def TrApplyOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr trApplyName)
    ((trApplySpecX A).inImage img)

end CryptoVerification.LibsignalTripleRatchet
