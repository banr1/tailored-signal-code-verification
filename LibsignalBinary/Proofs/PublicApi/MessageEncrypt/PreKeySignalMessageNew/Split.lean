/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefs
public import LibsignalBinary.Proofs.Placed.PublicApiCodeSymA
public import LibsignalBinary.Proofs.Placed.PublicApiCodeSymB

/-!
# Seam Decomposition and `encoded_len` Specification for `PreKeySignalMessage::new`

Defines the 128-byte `wire::PreKeySignalMessage` stack predicate and `preKeyMsgEncodedLenSpec`
(`0x2da84`), together with the intermediate cut states `SeamA` (`+0x25c`, post-prologue/allocation)
and `SeamB` (`+0x4c4`, post-field-encoding) and segment-exit combinator `PreKeyMsgSegExit` for
`PreKeySignalMessage::new` (`0x15130`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

/-! ## Pure Model Helpers -/

def _root_.CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewCall.protoMsg
    (x : PreKeyMsgNewCall) : ProtoPreKeySignalMessage :=
  { registrationId := some x.regId
    preKeyId := x.preKeyId
    signedPreKeyId := some x.spk
    kyberPreKeyId := x.kp.map (·.preKeyId)
    kyberCiphertext := x.kp.map (·.ciphertext)
    baseKey := some x.baseKey.serialize
    identityKey := some x.ik.serialize
    message := some x.msg.serialized }

@[simp]
theorem model_serialized_eq (x : PreKeyMsgNewCall) :
    x.model.serialized = versionByte x.ver :: x.protoMsg.encode :=
  rfl

@[simp]
theorem model_serialized_length (x : PreKeyMsgNewCall) :
    x.model.serialized.length = x.protoMsg.encode.length + 1 :=
  rfl

/-! ## `PreKeySignalMessage::encoded_len` Specification (`0x2da84`) -/

abbrev preKeyMsgEncodedLenName : String :=
  "<libsignal_protocol::proto::wire::PreKeySignalMessage as prost::message::Message>::encoded_len"

abbrev preKeyMsgEncodedLenStack : Nat := 0x10

/-- Ghost `(cap, ptr)` pins for the four `Option<Vec<u8>>` fields of `wire::PreKeySignalMessage`. -/
structure WirePreKeySignalMessageGhost where
  kyberCt : VecPin
  bk : VecPin
  ik : VecPin
  msg : VecPin

/-- Stack layout of a 128-byte `libsignal_protocol::proto::wire::PreKeySignalMessage` at `a`
(`+0x00` `kyber_ciphertext`, `+0x18` `base_key`, `+0x30` `identity_key`, `+0x48` `message`,
`+0x60` `registration_id`, `+0x68` `pre_key_id`, `+0x70` `signed_pre_key_id`,
`+0x78` `kyber_pre_key_id`). -/
def wirePreKeySignalMessageAt (A : RustAlloc) (g : WirePreKeySignalMessageGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  optVecU8At A g.kyberCt a m.kyberCiphertext ∗
    optVecU8At A g.bk (a + 0x18#64) m.baseKey ∗
    optVecU8At A g.ik (a + 0x30#64) m.identityKey ∗
    optVecU8At A g.msg (a + 0x48#64) m.message ∗
    LibsignalPublicApiRepr.optU32At (a + 0x60#64) m.registrationId ∗
    LibsignalPublicApiRepr.optU32At (a + 0x68#64) m.preKeyId ∗
    LibsignalPublicApiRepr.optU32At (a + 0x70#64) m.signedPreKeyId ∗
    LibsignalPublicApiRepr.optU32At (a + 0x78#64) m.kyberPreKeyId

/-- Encoded byte length fits in `u64`, ruling out `panic_const_add_overflow` inside `encoded_len`. -/
def PreKeyMsgWireLengthsFit (m : ProtoPreKeySignalMessage) : Prop :=
  m.encode.length < 2 ^ 64

/-- Ghost input bundle for `<wire::PreKeySignalMessage as Message>::encoded_len`. -/
structure PreKeyMsgEncodedLenGhost where
  a : BitVec 64
  g : WirePreKeySignalMessageGhost
  m : ProtoPreKeySignalMessage

/-- Specification of `<wire::PreKeySignalMessage as prost::message::Message>::encoded_len`
(`0x2da84`): returns `x.m.encode.length` in `x0` while preserving `wirePreKeySignalMessageAt` and
the trace under `PreKeyMsgWireLengthsFit x.m`. -/
def preKeyMsgEncodedLenSpec (A : RustAlloc) : Spec PreKeyMsgEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ PreKeyMsgWireLengthsFit x.m⌝ ∗
      wirePreKeySignalMessageAt A x.g x.a x.m ∗ stackAt s.sp preKeyMsgEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 x.m.encode.length ∧ sf.trace = s0.trace⌝ ∗
      wirePreKeySignalMessageAt A x.g x.a x.m ∗ stackAt s0.sp preKeyMsgEncodedLenStack

def PreKeyMsgEncodedLenOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + 0x2db68#64) (preKeyMsgEncodedLenSpec A)

def PreKeyMsgEncodedLenOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs) (img.base + 0x2db68#64) (preKeyMsgEncodedLenSpec A)

def PreKeyMsgEncodedLenOk_ext (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + 0x2db68#64) (preKeyMsgEncodedLenSpec A)

/-! ## Seam States for `PreKeySignalMessage::new` (`0x15130`) -/

abbrev preKeyMsgNewEntry (img : Obj.Image) : BitVec 64 := img.base + 0x15130#64

/-- Seam (a) PC (`+0x25c`): immediately before protobuf tag 1 encoding. -/
abbrev preKeyMsgSeamAPC (img : Obj.Image) : BitVec 64 := preKeyMsgNewEntry img + 0x25c#64

/-- Seam (b) PC (`+0x4c4`): immediately after protobuf tag 1–8 encoding, before `into_boxed_slice`. -/
abbrev preKeyMsgSeamBPC (img : Obj.Image) : BitVec 64 := preKeyMsgNewEntry img + 0x4c4#64

abbrev preKeyMsgFrameSize : Nat := 0x170

abbrev preKeyMsgSubStack : Nat := preKeyMsgNewStack - preKeyMsgFrameSize

/-- Callee-saved registers spilled at `[sp0 - 96 .. sp0)`. -/
def preKeyMsgSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Ghost heap pointers and register/stack spills live across `SeamA` and `SeamB`. -/
structure PreKeyMsgFrameGhost where
  /-- Heap pointer of `serialized: Vec<u8>` at `sp + 0xe0`. -/
  serPtr : BitVec 64
  /-- Cloned `kyber_ciphertext` heap pointer at `[sp + 0x30]` (`1#64` when empty). -/
  kyberCopyPtr : BitVec 64
  /-- `baseKey.serialize` 33-byte box pointer in `x28`. -/
  bkSerPtr : BitVec 64
  /-- `ik.serialize` 33-byte box pointer at `[sp + 0x10]`. -/
  ikSerPtr : BitVec 64
  /-- Cloned `msg.serialized` heap pointer at `[sp + 0x00]`. -/
  msgCopyPtr : BitVec 64
  /-- 32-bit spill of `w0` at `[sp + 0x24]` (`ver32.setWidth 8 = x.ver`). -/
  ver32 : BitVec 32
  /-- 32-bit value in `w25` (`preKeyVal32 = v` when `x.preKeyId = some v`). -/
  preKeyVal32 : BitVec 32
  /-- 32-bit value at `[sp + 0x2c]` (`kyberId32 = k.preKeyId` when `x.kp = some k`). -/
  kyberId32 : BitVec 32

def optKyberCopyBuf (A : RustAlloc) (ptr : BitVec 64) : Option KyberPayload → SepProp
  | none => emp
  | some k => boxU8Buf A ptr k.ciphertext

def PreKeyMsgGhostWf (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) : Prop :=
  x.model.serialized.length < 2 ^ 42 ∧
    g.ver32.setWidth 8 = x.ver ∧
    (∀ v, x.preKeyId = some v → g.preKeyVal32 = v) ∧
    (∀ k, x.kp = some k → g.kyberId32 = k.preKeyId)

def preKeyMsgCommonRegs (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (s0 s : State) : Prop :=
  s.status = .Running ∧
    s.sp = s0.sp - 0x170#64 ∧
    s0.spAligned = true ∧
    s.spAligned = true ∧
    s.trace = s0.trace ∧
    s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    s.readReg64 .x19 =
      (match x.kp with
       | none => noneCap
       | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
    (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32) ∧
    (s.readReg64 .x21).setWidth 32 = x.spk ∧
    s.readReg64 .x22 = 33#64 ∧
    s.readReg64 .x24 = 33#64 ∧
    (s.readReg64 .x25).setWidth 32 = g.preKeyVal32 ∧
    s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
    s.readReg64 .x28 = g.bkSerPtr ∧
    calleeSavedVRegs s = calleeSavedVRegs s0

/-- Stack frame `[sp .. sp + 0x170)` (`sp = s0.sp - 0x170#64`) with `serialized: Vec<u8>` at
`sp + 0xe0` holding `serBytes` and matching length word `serBytes.length`. -/
def preKeyMsgFrameSlotsAt (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (s0 : State)
    (serBytes : List (BitVec 8)) : SepProp :=
  let sp := s0.sp - 0x170#64
  (sp ↦₆₄ g.msgCopyPtr) ∗
    ((sp + 0x08#64) ↦₆₄ x.ikA) ∗
    ((sp + 0x10#64) ↦₆₄ g.ikSerPtr) ∗
    ((sp + 0x18#64) ↦₃₂ x.regId) ∗
    memRegion (sp + 0x1c#64) 8 ∗
    ((sp + 0x24#64) ↦₃₂ g.ver32) ∗
    ((sp + 0x28#64) ↦₃₂ x.spk) ∗
    ((sp + 0x2c#64) ↦₃₂ g.kyberId32) ∗
    ((sp + 0x30#64) ↦₆₄ g.kyberCopyPtr) ∗
    ((sp + 0x38#64) ↦₆₄ x.bkA) ∗
    ((sp + 0x40#64) ↦₆₄ x.ret) ∗
    ((sp + 0x48#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
    ((sp + 0x4c#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
    ((sp + 0x50#64) ↦₆₄ x.msgA) ∗
    ((sp + 0x58#64) ↦₆₄ x.kyA) ∗
    memRegion (sp + 0x60#64) 128 ∗
    vecU8At A (sp + 0xe0#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr serBytes ∗
    memRegion (sp + 0xf8#64) 24 ∗
    preKeyMsgSavedRegs s0.sp s0

/-- `vecU8At` with an explicit length word `lenW` at `v + 16` (not necessarily `bs.length`). -/
def vecU8AtLen (A : RustAlloc) (v cap ptr lenW : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  vecHeader v cap ptr lenW ∗
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8AtLen_length (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8AtLen A v cap ptr (BitVec.ofNat 64 bs.length) bs = vecU8At A v cap ptr bs :=
  rfl

/-- Seam stack-frame layout (`preKeyMsgFrameSlotsAt` generalized to an explicit `lenW` at
`[sp + 0xf0]`): tag 8's nonempty Kyber ciphertext branch updates `x23` without storing the final
length word back to `[x29 - 0x20]`, and nothing after `SeamB` reads `[sp + 0xf0]`. -/
def preKeyMsgFrameSlotsAt' (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (s0 : State)
    (lenW : BitVec 64) (serBytes : List (BitVec 8)) : SepProp :=
  let sp := s0.sp - 0x170#64
  (sp ↦₆₄ g.msgCopyPtr) ∗
    ((sp + 0x08#64) ↦₆₄ x.ikA) ∗
    ((sp + 0x10#64) ↦₆₄ g.ikSerPtr) ∗
    ((sp + 0x18#64) ↦₃₂ x.regId) ∗
    memRegion (sp + 0x1c#64) 8 ∗
    ((sp + 0x24#64) ↦₃₂ g.ver32) ∗
    ((sp + 0x28#64) ↦₃₂ x.spk) ∗
    ((sp + 0x2c#64) ↦₃₂ g.kyberId32) ∗
    ((sp + 0x30#64) ↦₆₄ g.kyberCopyPtr) ∗
    ((sp + 0x38#64) ↦₆₄ x.bkA) ∗
    ((sp + 0x40#64) ↦₆₄ x.ret) ∗
    ((sp + 0x48#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
    ((sp + 0x4c#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
    ((sp + 0x50#64) ↦₆₄ x.msgA) ∗
    ((sp + 0x58#64) ↦₆₄ x.kyA) ∗
    memRegion (sp + 0x60#64) 128 ∗
    vecU8AtLen A (sp + 0xe0#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr lenW
      serBytes ∗
    memRegion (sp + 0xf8#64) 24 ∗
    preKeyMsgSavedRegs s0.sp s0

theorem preKeyMsgFrameSlotsAt_eq_vec (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (s0 : State)
    (serBytes : List (BitVec 8)) :
    preKeyMsgFrameSlotsAt' A x g s0 (BitVec.ofNat 64 serBytes.length) serBytes =
      preKeyMsgFrameSlotsAt A x g s0 serBytes :=
  rfl

theorem preKeyMsgFrameSlotsAt_one_eq_vec (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost)
    (s0 : State) :
    preKeyMsgFrameSlotsAt' A x g s0 1#64 [versionByte x.ver] =
      preKeyMsgFrameSlotsAt A x g s0 [versionByte x.ver] :=
  rfl

theorem preKeyMsgFrameSlotsAt_entails_exists (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost)
    (s0 : State) (serBytes : List (BitVec 8)) :
    preKeyMsgFrameSlotsAt A x g s0 serBytes ⊢ ∃∗ lenW, preKeyMsgFrameSlotsAt' A x g s0 lenW serBytes :=
  Entails.sepExists_right (BitVec.ofNat 64 serBytes.length) (Entails.refl _)

theorem exists_preKeyMsgFrameSlotsAt'_of_vec {A : RustAlloc} {x : PreKeyMsgNewCall} {g : PreKeyMsgFrameGhost}
    {s0 : State} {serBytes : List (BitVec 8)} {F : SepProp} {m : Memory}
    (h : m ⊨ preKeyMsgFrameSlotsAt A x g s0 serBytes ∗ F) :
    ∃ lenW, m ⊨ preKeyMsgFrameSlotsAt' A x g s0 lenW serBytes ∗ F :=
  ⟨BitVec.ofNat 64 serBytes.length, h⟩

def preKeyMsgHeapAt (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (s0 : State) : SepProp :=
  (s0.sp ↦₆₄ x.msgA) ∗
    optKyberAt A x.kyA x.kyPtr x.kp ∗
    (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
    (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗
    memRegion x.ret 248 ∗
    optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
    boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗
    boxU8Buf A g.ikSerPtr x.ik.serialize ∗
    boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
    A.pool ∗
    stackAt (s0.sp - 0x170#64) preKeyMsgSubStack

/-- Seam (a) state (`+0x25c`): prologue complete and `serialized` at `sp + 0xe0` initialized to
`[versionByte x.ver]`. -/
def SeamA (img : Obj.Image) (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = preKeyMsgSeamAPC img ∧
    PreKeyMsgGhostWf x g ∧
    preKeyMsgCommonRegs x g s0 s ∧
    (s.mem ⊨ preKeyMsgFrameSlotsAt' A x g s0 1#64 [versionByte x.ver] ∗ preKeyMsgHeapAt A x g s0 ∗ R)

/-- Seam (b) state (`+0x4c4`): tags 1–8 encoded into `serialized` (`x.model.serialized`), with
length in `x23 = x26` and stale/existential length word `lenW` at `[sp + 0xf0]`. -/
def SeamB (img : Obj.Image) (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost)
    (R : SepProp) (s0 s : State) : Prop :=
  s.pc = preKeyMsgSeamBPC img ∧
    PreKeyMsgGhostWf x g ∧
    preKeyMsgCommonRegs x g s0 s ∧
    s.readReg64 .x8 = x.bkA ∧
    s.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length ∧
    s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length ∧
    ∃ lenW, (s.mem ⊨ preKeyMsgFrameSlotsAt' A x g s0 lenW x.model.serialized ∗ preKeyMsgHeapAt A x g s0 ∗ R)

/-! ## Segment-Exit Combinator -/

/-- Segment exit inside `PreKeySignalMessage::new`: from `s`, execution reaches either a state
satisfying `next` or an OOM panic outcome of `preKeyMsgNewSpec A`. -/
def PreKeyMsgSegExit (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (x : PreKeyMsgNewCall) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
    ∃ sf, Steps (tripleRatchetProgAt img.base C ctl abs) s sf ∧
      (next sf ∨ SubroutineOutcome (preKeyMsgNewSpec A) x R s0 sf)

def PreKeyMsgSegExit_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (x : PreKeyMsgNewCall) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (trTrapProgAt img.base C abs).CodeLoaded s.mem →
    ∃ sf, Steps (trTrapProgAt img.base C abs) s sf ∧
      (next sf ∨ SubroutineOutcome (preKeyMsgNewSpec A) x R s0 sf)

theorem preKeyMsgSegExit_chain {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : PreKeyMsgSegExit img C A ctl abs x R s0 s next)
    (h2 : ∀ s', next s' →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (preKeyMsgNewSpec A) x R s0 s') :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (preKeyMsgNewSpec A) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

theorem preKeyMsgSegExit_chain_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : PreKeyMsgSegExit_trap img C A abs x R s0 s next)
    (h2 : ∀ s', next s' →
      reaches_outcome (trTrapProgAt img.base C abs) (preKeyMsgNewSpec A) x R s0 s') :
    reaches_outcome (trTrapProgAt img.base C abs) (preKeyMsgNewSpec A) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

def PreKeyMsgSegExit_ext (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (x : PreKeyMsgNewCall) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    ∃ sf, Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
      (next sf ∨ SubroutineOutcome (preKeyMsgNewSpec A) x R s0 sf)

theorem preKeyMsgSegExit_chain_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : PreKeyMsgSegExit_ext img A ext x R s0 s next)
    (h2 : ∀ s', next s' →
      reaches_outcome (tripleRatchetProgAtExt img.base ext) (preKeyMsgNewSpec A) x R s0 s') :
    reaches_outcome (tripleRatchetProgAtExt img.base ext) (preKeyMsgNewSpec A) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

theorem preKeyMsgSegExit_of_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hrun : ∀ sf, next sf → sf.status = .Running)
    (h : PreKeyMsgSegExit_trap img C A abs x R s0 s next) :
    PreKeyMsgSegExit img C A ctl abs x R s0 s next := by
  intro hL
  have hT := trapsOnly_trTrap_kit img.base C ctl abs
  obtain ⟨sf, hst, hnext | hout⟩ := h (ProofLib.Variant.CodeLoaded_of_trapsOnly hT hL)
  · exact ⟨sf, ProofLib.Variant.Steps.of_trapsOnly hT hst (.of_running (hrun sf hnext)), Or.inl hnext⟩
  · exact ⟨sf, ProofLib.Variant.Steps.of_trapsOnly hT hst (ProofLib.Variant.SubroutineOutcome.outcomeStatus hout), Or.inr hout⟩

/-! ## Relocatable Placement Proofs -/

open CryptoVerification.LibsignalPublicApi.Placed

abbrev PreKeyMsgEncodedLenPlacedOk [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_119 H) (blkPl_119).base (preKeyMsgEncodedLenSpec A)

abbrev preKeyMsgNewEntry_placed [LibsignalPlacement] : BitVec 64 := (blkPl_41).base

abbrev preKeyMsgSeamAPC_placed [LibsignalPlacement] : BitVec 64 :=
  preKeyMsgNewEntry_placed + 604#64

abbrev preKeyMsgSeamBPC_placed [LibsignalPlacement] : BitVec 64 :=
  preKeyMsgNewEntry_placed + 1220#64

def SeamA_placed [LibsignalPlacement] (A : RustAlloc) (x : PreKeyMsgNewCall)
    (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = preKeyMsgSeamAPC_placed ∧
    LibsignalCodeLoaded lsmpl s.mem ∧
    PreKeyMsgGhostWf x g ∧
    preKeyMsgCommonRegs x g s0 s ∧
    (s.mem ⊨ preKeyMsgFrameSlotsAt' A x g s0 1#64 [versionByte x.ver] ∗ preKeyMsgHeapAt A x g s0 ∗ R)

def SeamB_placed [LibsignalPlacement] (A : RustAlloc) (x : PreKeyMsgNewCall)
    (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = preKeyMsgSeamBPC_placed ∧
    LibsignalCodeLoaded lsmpl s.mem ∧
    PreKeyMsgGhostWf x g ∧
    preKeyMsgCommonRegs x g s0 s ∧
    s.readReg64 .x8 = x.bkA ∧
    s.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length ∧
    s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length ∧
    ∃ lenW, (s.mem ⊨ preKeyMsgFrameSlotsAt' A x g s0 lenW x.model.serialized ∗ preKeyMsgHeapAt A x g s0 ∗ R)

def PreKeyMsgSegExit_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (x : PreKeyMsgNewCall) (R : SepProp) (s0 s : State) (next : State → Prop) : Prop :=
  (lsProg_41 H).CodeLoaded s.mem →
    ∃ sf, Steps (lsProg_41 H) s sf ∧
      (next sf ∨ SubroutineOutcome (preKeyMsgNewSpec A) x R s0 sf)

theorem preKeyMsgSegExit_placed_chain [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : PreKeyMsgNewCall} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : PreKeyMsgSegExit_placed A H x R s0 s next)
    (h2 : ∀ s', next s' →
      reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec A) x R s0 s') :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec A) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
