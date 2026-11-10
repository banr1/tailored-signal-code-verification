/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSpqr
public import Init.Data.String.Pattern.Basic
public import Init.Data.String.Pattern.String
public import Init.Data.String.Slice
public import Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetReprProofDefs
public import GeneratedLean.LibsignalSessionObj

/-!
# Proof-Side Triple-Ratchet Subroutine Contracts and Empty-State Statements

Defines in-image subroutine contracts (`decodeStateEmptySpec`, `otrFromSpec`, `otrApplySpec`,
`tryFromSpec`) and statement bundles (`TryDecrypt*RunStmt`, `Otr*RunStmt`, `TryFromRunStmt`,
`RecordDecrypt*RunStmt`) for `LibsignalBinary/Specifications/LibsignalTripleRatchet.lean`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet
open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-- `Result<Uuid, uuid::Error>`'s word 0 (a `u32`) for `Ok`: the niche `0xFFFFFFFF`; the UUID's 16
bytes follow at +4. 32 bytes, align 8 (`parse_from_service_id_string+0x40..+0x50`: `ldr w8, [sp,
#0x10]; cmn w8, #1; b.ne` to `None`, then `ldur q0, [sp, #0x14]`; layout replica: rustc 1.98.1
`aarch64-unknown-linux-gnu`, uuid 1.26.1 const-evaluated `Ok(Uuid::from_bytes(..))`). -/
def uuidOkTag : BitVec 32 := 0xFFFFFFFF#32

/-- Word 0 of `Err(uuid::Error(ErrorKind::ParseOther))` (the `u32` tag 6, same replica):
`Uuid::try_parse` returns this on every failure (`try_parse_ascii` maps any parse error to
`ParseOther`, uuid 1.26.1 `src/parser.rs:137–144`). -/
def uuidErrParseOther : BitVec 32 := 6#32

/-- `PqRatchetState.chain = None`: the word @0x30 (`spqr::send` `+0x1200: ldr x8, [sp, #0x60]`
on its copy at `sp + 0x30`; `+0x1204: cmn x8, #1`). -/
def pqChainNone : BitVec 64 := 0xFFFFFFFFFFFFFFFF#64

/-- `PqRatchetState.inner = None`: the word @0x80 (`spqr::send` `+0x9c: ldr x9, [sp, #0xb0]`;
`+0xac: cmn x9, #3`). -/
def pqInnerNone : BitVec 64 := 0xFFFFFFFFFFFFFFFD#64

/-- The 352-byte `Result<PqRatchetState, spqr::Error>` at `r` that `decode_state` returns on an
empty state (`spqr/src/lib.rs:495–501`: `Ok` with `inner`, `version_negotiation` and `chain` all
`None`), pinned only where its callers compare it: word 0 = `-1` (the `version_negotiation = None`
niche; not the `Err` niche, `spqr::send` `+0x5c`, and `< 1` as a signed word, `+0xc0: cmp x23, #1;
b.ge +0x388` would free a buffer of that many bytes); `chain = None` @0x30; `inner = None` @0x80
(the in-image code: `0x53ae0..0x53af0`, `str x8 (= -1), [x19]; str x8, [x19, #0x30]; str x9 (= -3),
[x19, #0x80]`). The other bytes are unspecified. -/
def decodeStateEmptyAt (r : BitVec 64) : SepProp :=
  (r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
    memRegion (r + 8#64) 40 ∗ ((r + 48#64) ↦₆₄ pqChainNone) ∗ memRegion (r + 56#64) 72 ∗
    ((r + 128#64) ↦₆₄ pqInnerNone) ∗ memRegion (r + 136#64) 216

/-- `spqr::decode_state(s = x0: &Vec<u8>)` (sret `x8`, 352 bytes; `spqr/src/lib.rs:495–505`)
on an empty state only: `decodeStateEmptyAt`, the header given back; it reads only the length
(`0x534c4: ldr x9, [x0, #0x10]; cbz x9`), allocates nothing and cannot panic (`onPanic` = the
default `False`). Note: `decode_state` is in-image code (`0x5349c`), so
this is a contract the proofs establish for it, not a hook; the empty-state proofs of `spqr::send`
and `spqr::recv` (`SpqrSendEmptyRunStmt`, `SpqrRecvEmptyRunStmt`) cross its call with it. Ghost
`(st, ret)`. -/
def decodeStateEmptySpec (A : RustAlloc) : Spec (VecArg × BitVec 64) where
  pre := fun (st, ret) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x8 = ret ∧ st.bytes = []⌝ ∗ st.at A ∗
      memRegion ret 352 ∗ stackAt s.sp extHookStack
  post := fun (st, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ st.at A ∗ decodeStateEmptyAt ret ∗ stackAt s0.sp extHookStack

/-- `spqrSendSpec` restricted to an empty state (`x.st.bytes = []`). -/
def spqrSendEmptySpec (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    Spec SendCall :=
  { spqrSendSpec A ctl S img with
    pre := fun x s => ⌜x.st.bytes = []⌝ ∗ (spqrSendSpec A ctl S img).pre x s }

/-- `SpqrSendOk` on an empty state, without assuming `SpqrSendOk`. For a model meeting
`SpqrModel.SendEmptyOk`, the in-image `spqr::send::<HookRng>` meets `spqrSendSpec` whenever the state
is empty. On that path it calls the in-image `spqr::decode_state` (`decodeStateEmptySpec`), then
`memcpy`, and `__rust_dealloc` only behind a test that `decodeStateEmptyAt` makes false (`+0xc0`);
no libcrux stub. -/
def SpqrSendEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.SendEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrSendName)
      (spqrSendEmptySpec A ctl S img)

/-- `spqrRecvSpec` restricted to an empty state (`st.bytes = []`). -/
def spqrRecvEmptySpec (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) :
    Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvSpec A S img with
    pre := fun x s => ⌜x.1.bytes = []⌝ ∗ (spqrRecvSpec A S img).pre x s }

/-- `SpqrRecvOk` on an empty state, without assuming `SpqrRecvOk`. For a model meeting
`SpqrModel.RecvEmptyOk`, the in-image `spqr::recv` meets `spqrRecvSpec` whenever the state is
empty, for every message. On that path the preamble check is inlined (`+0x28..+0x110`); if it
fails, `recv` writes `Err(MsgDecode)` (word 0 `-1`, discriminant byte 2 @8, `+0x114..+0x11c`) and
returns with no call. Otherwise it calls the in-image `spqr::decode_state` (`+0x144`,
`decodeStateEmptySpec`) and `memcpy` (`+0x194`, 320 bytes of the decoded state), tests only word
0, `chain` and `inner` of `decodeStateEmptyAt`, and writes the empty `Vec` (capacity 0, dangling
pointer 1) with no key (`+0x390..+0x39c`); it allocates and frees nothing. No libcrux stub is
reached. -/
def SpqrRecvEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrRecvName)
      (spqrRecvEmptySpec A S img)

/-- Ghost of an `OTR::from_session_state` call. -/
structure OtrFromGhost where
  /-- `state: &mut SessionState` (`x0`). -/
  ss : BitVec 64
  G : SessionGhost
  st : SessionState (List (BitVec 8))
  /-- The sret (`x8`, 200 bytes). -/
  ret : BitVec 64

/-- The session-model result and final state. -/
def OtrFromGhost.model (x : OtrFromGhost) :
    Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8))) ×
      SessionState (List (BitVec 8)) :=
  Mut.exec OutgoingTripleRatchet.fromSessionState x.st

/-- The binding spec of `OTR::from_session_state` (`triple_ratchet.rs:52–79`): `x0` = SS, sret
`x8`. SS holds the model's final state with a ghost that differs from `G` at most in the pq pin
(the pq state is taken; on the version / identity errors it is freed). `Ok`: the sret holds the
model's OTR whose pq `Vec` is SS's old one (moved, `G.pq`). -/
def otrFromSpec (A : RustAlloc) (img : Obj.Image) : Spec OtrFromGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret⌝ ∗ sessionStateAt A x.ss x.G x.st ∗
          memRegion x.ret 200 ∗ logOff img ∗ stackAt s.sp smallRootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G' : SessionGhost, ⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' x.model.2) ∗
        otrResultAt A x.ret x.G.pq x.model.1 ∗ logOff img ∗ stackAt s0.sp smallRootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜(x.model.1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Ghost of an `OTR::apply_to_session_state` call. -/
structure OtrApplyGhost where
  /-- `self: OutgoingTripleRatchet` by value (`x0` = a caller copy the callee consumes). -/
  o : BitVec 64
  pqCap : BitVec 64
  pqPtr : BitVec 64
  ot : OutgoingTripleRatchet (List (BitVec 8))
  /-- `state: &mut SessionState` (`x1`). -/
  ss : BitVec 64
  G : SessionGhost
  st : SessionState (List (BitVec 8))

/-- The binding spec of `OTR::apply_to_session_state` (`triple_ratchet.rs:81–84`): `x0` = the
OTR (consumed), `x1` = SS with a sender chain (the only use, after `from_session_state`). SS holds
the model's state; only the sender chain-key pin and the pq pin change (the OTR's pq `Vec` moves
in). -/
def otrApplySpec (A : RustAlloc) (img : Obj.Image) : Spec OtrApplyGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.o ∧ s.readReg64 .x1 = x.ss ∧ x.st.senderChain.isSome⌝ ∗
          otrAt A x.o x.pqCap x.pqPtr x.ot ∗ sessionStateAt A x.ss x.G x.st ∗ logOff img ∗
          stackAt s.sp smallRootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ G' : SessionGhost, ⌜x.G.AfterOutgoingRatchetApply G' ∧ G'.pq = ⟨x.pqCap, x.pqPtr⟩⌝ ∗
          sessionStateAt A x.ss G' (x.ot.applyToSessionState x.st)) ∗
        memRegion x.o 200 ∗ logOff img ∗ stackAt s0.sp smallRootStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Ghost of a parse call: the bytes (`x0`, `x1`) and the sret (`x8`, 120 bytes). -/
structure TryFromGhost where
  bytesA : BitVec 64
  bytes : List (BitVec 8)
  ret : BitVec 64

/-- The binding spec of `SignalMessage::try_from` (`protocol.rs:261–307`): the sret holds
`SignalMessage.tryFrom protoSignalCodec bytes` (using the concrete `prost` codec
`protoSignalCodec`), and the input bytes are given back. -/
def tryFromSpec (A : RustAlloc) (img : Obj.Image) : Spec TryFromGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff img ∗
          stackAt s.sp smallRootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ stackAt s0.sp smallRootStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Decrypt. For an image of `libsignalSessionImage` and abstract hooks meeting `TripleRatchetHooks`,
the compiled `try_decrypt_with_state::<HookRng>` meets `tryDecryptSpec`. Named hypotheses:
`SpqrRecvOk` and `TripleRatchetHooks.aesDec`. -/
def TryDecryptRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → SpqrRecvOk C A ctl S abs img → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img tryDecryptName)
      (tryDecryptSpec C A ctl uuidTryParse S img)

/-- Decrypt, empty post-quantum state (without `SpqrRecvOk`). For a model meeting
`SpqrModel.RecvEmptyOk` and a session whose pq state is empty, `try_decrypt_with_state::<HookRng>`
meets `tryDecryptSpec` without `SpqrRecvOk`: the `spqr::recv` call is crossed with
`SpqrRecvEmptyRunStmt`. Named hypothesis: `TripleRatchetHooks.aesDec`. -/
def TryDecryptEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img tryDecryptName)
      { tryDecryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜x.st.pqRatchetState = []⌝ ∗ (tryDecryptSpec C A ctl uuidTryParse S img).pre x s }

/-- Encrypt, step 1. `OTR::from_session_state` meets `otrFromSpec`. -/
def OtrFromRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img otrFromName) (otrFromSpec A img)

/-- Encrypt, step 2. `OTR::encrypt::<HookRng>` meets `otrEncryptSpec`. Named hypotheses:
`SpqrSendOk` and `TripleRatchetHooks.aesEnc`. -/
def OtrEncryptRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → SpqrSendOk C A ctl S abs img → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img otrEncryptName)
      (otrEncryptSpec C A ctl uuidTryParse S img)

/-- Encrypt, step 2, empty post-quantum state (without `SpqrSendOk`). For a model meeting
`SpqrModel.SendEmptyOk` and an OTR whose pq state is empty, `OTR::encrypt::<HookRng>` meets
`otrEncryptSpec` without `SpqrSendOk`: the `spqr::send` call is crossed with
`SpqrSendEmptyRunStmt`. Named hypothesis: `TripleRatchetHooks.aesEnc`. -/
def OtrEncryptEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.SendEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img otrEncryptName)
      { otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s => ⌜x.ot.pqrState = []⌝ ∗ (otrEncryptSpec C A ctl uuidTryParse S img).pre x s }

/-- Encrypt, step 3. `OTR::apply_to_session_state` meets `otrApplySpec`. -/
def OtrApplyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img otrApplyName) (otrApplySpec A img)

/-- Parse. `<SignalMessage as TryFrom<&[u8]>>::try_from` meets `tryFromSpec`. -/
def TryFromRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img tryFromName) (tryFromSpec A img)

/-- Decrypt from a record (`try_decrypt_from_record`). The `try_decrypt_from_record` region of
the compiled `message_decrypt_signal::<HookRng>` meets `recordDecryptSpec`. Named hypotheses:
`SpqrRecvOk` and `TripleRatchetHooks.aesDec`, as for `TryDecryptRunStmt`. -/
def RecordDecryptRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → SpqrRecvOk C A ctl S abs img → Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg img C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      (recordDecryptSpec C A ctl uuidTryParse S img)

/-- Decrypt from a record, empty post-quantum state (without `SpqrRecvOk`). As
`TryDecryptEmptyRunStmt`: for a model meeting `SpqrModel.RecvEmptyOk` and a current session whose
pq state is empty, the region meets `recordDecryptSpec` without `SpqrRecvOk`. Named hypothesis:
`TripleRatchetHooks.aesDec`. -/
def RecordDecryptEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg img C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      { recordDecryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜x.st.pqRatchetState = []⌝ ∗ (recordDecryptSpec C A ctl uuidTryParse S img).pre x s }

end CryptoVerification.LibsignalTripleRatchet
