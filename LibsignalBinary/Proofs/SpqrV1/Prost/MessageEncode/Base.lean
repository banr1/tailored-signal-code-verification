/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommon
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase

/-!
# Shared Base for 48-Byte `prost::encoding::message::encode` Monomorphizations

Defines symbol names, 48-byte stack-frame layouts, callee wrappers, and `Vec<Vec<u8>>` slice
decompositions shared across `prost::encoding::message::encode::<M, alloc::vec::Vec<u8>>`
for `PolynomialEncoder`, `ChainParams`, `PolynomialDecoder`, and `EpochDirection`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Symbol Names & Offsets -/

abbrev encodePolyEncoder1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#1]"

abbrev encodePolyEncoder2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"

abbrev encodeChainParams1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#1]"

abbrev encodeChainParams2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#2]"

abbrev encodePolyDecoder1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#1]"

abbrev encodePolyDecoder2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#2]"

abbrev encodeEpochDirection1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]"

abbrev encodeEpochDirection2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#2]"

@[simp, arm64_norm] theorem encodePolyEncoder1_fnOff :
    libsignalSessionCode.fnOff encodePolyEncoder1Name = 0x37774 :=
  libsignalSessionCode_fnOff_0x37774

@[simp, arm64_norm] theorem encodePolyEncoder2_fnOff :
    libsignalSessionCode.fnOff encodePolyEncoder2Name = 0x4d2dc :=
  libsignalSessionCode_fnOff_0x4d2dc

@[simp, arm64_norm] theorem encodeChainParams1_fnOff :
    libsignalSessionCode.fnOff encodeChainParams1Name = 0x37278 :=
  libsignalSessionCode_fnOff_0x37278

@[simp, arm64_norm] theorem encodeChainParams2_fnOff :
    libsignalSessionCode.fnOff encodeChainParams2Name = 0x4cd78 :=
  libsignalSessionCode_fnOff_0x4cd78

@[simp, arm64_norm] theorem encodePolyDecoder1_fnOff :
    libsignalSessionCode.fnOff encodePolyDecoder1Name = 0x37604 :=
  libsignalSessionCode_fnOff_0x37604

@[simp, arm64_norm] theorem encodePolyDecoder2_fnOff :
    libsignalSessionCode.fnOff encodePolyDecoder2Name = 0x4d14c :=
  libsignalSessionCode_fnOff_0x4d14c

@[simp, arm64_norm] theorem encodeEpochDirection1_fnOff :
    libsignalSessionCode.fnOff encodeEpochDirection1Name = 0x37850 :=
  libsignalSessionCode_fnOff_0x37850

@[simp, arm64_norm] theorem encodeEpochDirection2_fnOff :
    libsignalSessionCode.fnOff encodeEpochDirection2Name = 0x4d3c8 :=
  libsignalSessionCode_fnOff_0x4d3c8

/-! ## Pure Capacity & Varint Key Helpers -/

theorem cap_toNat_eq_of_beq {cap : BitVec 64} {n : Nat} (hn : n < 2 ^ 64)
    (h : (cap == BitVec.ofNat 64 n) = true) : cap.toNat = n := by
  have heq : cap = BitVec.ofNat 64 n := beq_iff_eq.mp h
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem lt_cap_toNat_of_beq_false {cap : BitVec 64} {n : Nat}
    (hle : n ≤ cap.toNat) (h : (cap == BitVec.ofNat 64 n) = false) :
    n < cap.toNat := by
  have hne : cap.toNat ≠ n := by
    intro heq
    apply Bool.eq_false_iff.mp h
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), heq]
  omega

theorem reserveCap_one_bounds {cap : BitVec 64} {n : Nat} (hcap : cap.toNat = n)
    (hfit : n + 10 < 2 ^ 62) :
    n + 1 ≤ reserveCap cap.toNat n 1 ∧
      reserveCap cap.toNat n 1 + 1 ≤ 2 ^ 63 ∧
      cap.toNat ≤ reserveCap cap.toNat n 1 ∧
      (BitVec.ofNat 64 (reserveCap cap.toNat n 1)).toNat = reserveCap cap.toNat n 1 := by
  refine ⟨by dsimp [reserveCap]; omega, by dsimp [reserveCap]; omega, by dsimp [reserveCap]; omega, ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [reserveCap]; omega)]

theorem protoEncodeKey_varint_1 :
    Proto.encodeKey 1#32 .varint = [8#8] := by decide

theorem protoEncodeKey_varint_2 :
    Proto.encodeKey 2#32 .varint = [16#8] := by decide

theorem protoEncodeKey_varint_4 :
    Proto.encodeKey 4#32 .varint = [32#8] := by decide

theorem protoEncodeKey_lengthDelimited_2 :
    Proto.encodeKey 2#32 .lengthDelimited = [18#8] := by decide

theorem protoEncodeKey_lengthDelimited_3 :
    Proto.encodeKey 3#32 .lengthDelimited = [26#8] := by decide

theorem protoEncodeUint32Field_zero (tag : BitVec 32) :
    Proto.encodeUint32Field tag 0#32 = [] := by
  simp [Proto.encodeUint32Field]

theorem protoEncodeUint32Field_1_of_ne_zero {v : BitVec 32} (h : v ≠ 0#32) :
    Proto.encodeUint32Field 1#32 v = [8#8] ++ LibsignalProtoCodec.encodeVarint (v.zeroExtend 64) := by
  have hbeq : (v == 0#32) = false := beq_false_of_ne h
  simp only [Proto.encodeUint32Field, hbeq, Bool.false_eq_true, ↓reduceIte,
    protoEncodeKey_varint_1, protoEncodeVarint_eq_codec]

theorem protoEncodeUint32Field_2_of_ne_zero {v : BitVec 32} (h : v ≠ 0#32) :
    Proto.encodeUint32Field 2#32 v = [16#8] ++ LibsignalProtoCodec.encodeVarint (v.zeroExtend 64) := by
  have hbeq : (v == 0#32) = false := beq_false_of_ne h
  simp only [Proto.encodeUint32Field, hbeq, Bool.false_eq_true, ↓reduceIte,
    protoEncodeKey_varint_2, protoEncodeVarint_eq_codec]

theorem protoEncodeBoolField_4_false :
    Proto.encodeBoolField 4#32 false = [] := rfl

theorem protoEncodeBoolField_4_true :
    Proto.encodeBoolField 4#32 true = [32#8, 1#8] := by decide

theorem orr_lsl3_two_eq_encodeKey_lengthDelimited (tag : BitVec 32) :
    LibsignalProtoCodec.encodeVarint ((2#32 ||| (tag <<< 3)).zeroExtend 64) =
      Proto.encodeKey tag .lengthDelimited := by
  simp only [Proto.encodeKey, Proto.WireType.toU32, protoEncodeVarint_eq_codec]
  congr 1
  rw [BitVec.or_comm]

/-! ## 48-Byte Stack Frame (`0x30` B) for `ChainParams`, `PolyEncoder`, `PolyDecoder` -/

/-- Total stack budget for 48-byte `message::encode` functions that only call `encode_varint` /
`do_reserve_and_handle`: `48 + (0x30 + resStack)`. -/
abbrev msgEnc48VarintStackOf (resStack : Nat) : Nat :=
  48 + (0x30 + resStack)

/-- Total stack budget for 48-byte `message::encode` functions that call `encode_repeated`:
`48 + encodeRepeatedStackOf resStack`. -/
abbrev msgEnc48RepeatedStackOf (resStack : Nat) : Nat :=
  48 + encodeRepeatedStackOf resStack

/-- Saved register frame at `[sp - 48, sp)` after prologue of a 48-byte `message::encode`
(`stp x29, x30, [sp, #-0x30]!`, `str x21, [sp, #0x10]`, `stp x20, x19, [sp, #0x20]`). -/
def msgEnc48SavedFrame (sp fp lr r21 v3 r20 r19 : BitVec 64) : SepProp :=
  ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
    ((sp - 32#64) ↦₆₄ r21) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
    ((sp - 16#64) ↦₆₄ r20) ∗ ((sp - 8#64) ↦₆₄ r19)

theorem stackAt_msgEnc48_varint {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (msgEnc48VarintStackOf resStack) =
      stackAt (sp - 48#64) (0x30 + resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
         ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
          ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
          ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
  have h1 := ProofLib.stackAt_split_cells sp (0x30 + resStack) 6 (by omega)
  have heq : 0x30 + resStack + 8 * 6 = msgEnc48VarintStackOf resStack := by
    dsimp [msgEnc48VarintStackOf]; omega
  rw [heq] at h1
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [h1, hc6]

theorem stackAt_msgEnc48_repeated {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (msgEnc48RepeatedStackOf resStack) =
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
         ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
          ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
          ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
  have h1 := ProofLib.stackAt_split_cells sp (encodeRepeatedStackOf resStack) 6
    (by dsimp [encodeRepeatedStackOf]; omega)
  have heq : encodeRepeatedStackOf resStack + 8 * 6 = msgEnc48RepeatedStackOf resStack := by
    dsimp [msgEnc48RepeatedStackOf]; omega
  rw [heq] at h1
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [h1, hc6]

/-- Split `stackAt sp (encodeRepeatedStackOf resStack)` (`80 + (0x30 + resStack)`) into
`memRegion (sp - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ stackAt sp (0x30 + resStack)`. -/
theorem stackAt_encodeRepeated_eq_varint {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (encodeRepeatedStackOf resStack) =
      memRegion (sp - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
        stackAt sp (0x30 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp (0x30 + resStack) 80 (by omega)
  have heq : (0x30 + resStack) + 80 = encodeRepeatedStackOf resStack := by
    dsimp [encodeRepeatedStackOf]; omega
  simpa only [heq] using h

/-- Split `stackAt sp (0x30 + resStack)` into
`memRegion (sp - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗ stackAt sp 16`. -/
theorem stackAt_varint_eq_stack16 {resStack : Nat} (hres : resStack + 48 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (0x30 + resStack) =
      memRegion (sp - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗
        stackAt sp 16 := by
  have h := ProofLib.stackAt_split_bottom sp 16 (32 + resStack) (by omega)
  have heq : 16 + (32 + resStack) = 0x30 + resStack := by omega
  simpa only [heq] using h

/-- Callee-saved registers `x22..x28` untouched by 48-byte `message::encode` (`x19..x21, fp, lr`
are saved on stack), together with `StepInv s0 s`. -/
def MsgEnc48CalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem MsgEnc48CalleeSaved.refl (s0 : State) : MsgEnc48CalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInv.refl s0⟩

theorem MsgEnc48CalleeSaved.trans {s0 s1 s2 : State}
    (h01 : MsgEnc48CalleeSaved s0 s1) (h12 : MsgEnc48CalleeSaved s1 s2) :
    MsgEnc48CalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
    h01.2.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2.2⟩

theorem MsgEnc48CalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : MsgEnc48CalleeSaved s1 s2 :=
  ⟨hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem MsgEnc48CalleeSaved.step {s0 s1 s2 : State}
    (h01 : MsgEnc48CalleeSaved s0 s1)
    (hx22 : s2.readReg64 (Reg.gpr 22#5) = s1.readReg64 (Reg.gpr 22#5))
    (hx23 : s2.readReg64 (Reg.gpr 23#5) = s1.readReg64 (Reg.gpr 23#5))
    (hx24 : s2.readReg64 (Reg.gpr 24#5) = s1.readReg64 (Reg.gpr 24#5))
    (hx25 : s2.readReg64 (Reg.gpr 25#5) = s1.readReg64 (Reg.gpr 25#5))
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInv s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm, calleeSavedVRegs_setPC]) :
    MsgEnc48CalleeSaved s0 s2 :=
  h01.trans ⟨hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs, hinv⟩

attribute [arm64_norm, wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

/-- Wrap a `Spec α` with `⌜MsgEnc48CalleeSaved s0 s⌝` in the precondition. -/
def withMsgEnc48CS {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜MsgEnc48CalleeSaved s0 s⌝ ∗ spec.pre x s }

theorem subroutine_ok_withMsgEnc48CS_ext {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withMsgEnc48CS s0 spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s hpc hrun hpre hsp
  rw [withMsgEnc48CS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (h.to_outcome x R s hpc hrun hpre.2 hsp).mono_outcome fun _ hout => hout

theorem subroutine_ok_withMsgEnc48CS_x {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (img : Obj.Image) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (withMsgEnc48CS s0 spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s hpc hrun hpre hsp
  rw [withMsgEnc48CS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.2.2.2.2.2.2.2.2 img hinv0, hpre.2⟩
  exact (h.to_outcome x R s hpc hrun hpre' hsp).mono_outcome fun _ hout => hout

/-- Standard panic postcondition for `message::encode` functions. -/
def msgEncOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem step_msg48_encode_varint_call {resStack : Nat} (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      MsgEnc48CalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ CryptoVerification.LibsignalProtoCodec.encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  refine SepWPp.call_cs (x := EncodeVarintGhost.mk val v curCap curPtr curBs) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withMsgEnc48CS, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CS, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)
    exact Entails.of_eq (by ac_rfl)

theorem step_msg48_do_reserve2_call {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)] at hm
    simp only [withMsgEnc48CS, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CS, doReserve2SpecOf, doReserveSpec, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, doReserve2SpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_msg48_do_reserve7_call {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)] at hm
    simp only [withMsgEnc48CS, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CS, doReserveSpecOf, doReserveSpec, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)]
    exact Entails.of_eq (by ac_rfl)

theorem stackAt_msgEnc48_varint_eq_bottom {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (msgEnc48VarintStackOf resStack) =
      memRegion (sp - BitVec.ofNat 64 (msgEnc48VarintStackOf resStack)) 48 ∗
        stackAt sp (0x30 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp (0x30 + resStack) 48 (by omega)
  have heq : (0x30 + resStack) + 48 = msgEnc48VarintStackOf resStack := by
    dsimp [msgEnc48VarintStackOf]; omega
  simpa only [heq] using h

theorem stackAt_msgEnc48_repeated_eq_bottom {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (msgEnc48RepeatedStackOf resStack) =
      memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗
        stackAt sp (encodeRepeatedStackOf resStack) := by
  have h := ProofLib.stackAt_split_bottom sp (encodeRepeatedStackOf resStack) 48
    (by dsimp [encodeRepeatedStackOf]; omega)
  have heq : encodeRepeatedStackOf resStack + 48 = msgEnc48RepeatedStackOf resStack := by
    dsimp [msgEnc48RepeatedStackOf]; omega
  simpa only [heq] using h

theorem msgEnc48SavedFrame_entails_cells (sp fp lr r21 v3 r20 r19 : BitVec 64) :
    msgEnc48SavedFrame sp fp lr r21 v3 r20 r19 ⊢
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) :=
  Entails.sepExists_right fp
    (Entails.sepExists_right lr
      (Entails.sepExists_right r21
        (Entails.sepExists_right v3
          (Entails.sepExists_right r20
            (Entails.sepExists_right r19 (Entails.refl _))))))

theorem stackAt_msgEnc48_varint_recombine {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (sp fp lr r21 v3 r20 r19 : BitVec 64) :
    stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19 ⊢
      stackAt sp (msgEnc48VarintStackOf resStack) := by
  rw [stackAt_msgEnc48_varint hres sp]
  exact sepConj_mono_right (msgEnc48SavedFrame_entails_cells sp fp lr r21 v3 r20 r19)

theorem stackAt_msgEnc48_repeated_recombine {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp fp lr r21 v3 r20 r19 : BitVec 64) :
    stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19 ⊢
      stackAt sp (msgEnc48RepeatedStackOf resStack) := by
  rw [stackAt_msgEnc48_repeated hres sp]
  exact sepConj_mono_right (msgEnc48SavedFrame_entails_cells sp fp lr r21 v3 r20 r19)

theorem step_msg48_encode_repeated_call {resStack : Nat} (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (encodeRepeatedSpecOf resStack A)))
    (tag : Nat) (base v curCap curPtr sp ret_pc : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29)
    (helems : elems.length < 2 ^ 58)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag)
    (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length)
    (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      MsgEnc48CalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((repeatedBytesSliceAt base elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  refine SepWPp.call_cs (x := EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) (F := F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withMsgEnc48CS, encodeRepeatedSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CS, encodeRepeatedSpecOf, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, encodeRepeatedSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)
    exact Entails.of_eq (by ac_rfl)

theorem step_msg48_encode_varint_tailcall {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hcc : CalleeSavedPreserved s0 s)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      MsgEnc48CalleeSaved s0 sf →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((vecU8At A v nextCap nextPtr (curBs ++ CryptoVerification.LibsignalProtoCodec.encodeVarint val) ∗
        A.pool ∗ stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact halign
  refine SepWPp.call_cs (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48VarintStackOf resStack)) 48 ∗ F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48VarintStackOf resStack) ∗
        (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') :=
      Satisfies.mono
        (sepConj_mono_left (stackAt_msgEnc48_varint_recombine hres sp fp lr r21 v3 r20 r19))
        hm0
    rw [stackAt_msgEnc48_varint_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CS, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CS, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28, hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres))
    rw [stackAt_msgEnc48_varint_eq_bottom hres sp]
    exact Entails.of_eq (by ac_rfl)

theorem step_msg48_encode_repeated_tailcall {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (encodeRepeatedSpecOf resStack A)))
    (tag : Nat) (base v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29)
    (helems : elems.length < 2 ^ 58)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag)
    (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length)
    (hx3 : s.readReg64 .x3 = v)
    (hcc : CalleeSavedPreserved s0 s)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      MsgEnc48CalleeSaved s0 sf →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((repeatedBytesSliceAt base elems ∗
        vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact halign
  refine SepWPp.call_cs (x := EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗ F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48RepeatedStackOf resStack) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') :=
      Satisfies.mono
        (sepConj_mono_left (stackAt_msgEnc48_repeated_recombine hres sp fp lr r21 v3 r20 r19))
        hm0
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CS, encodeRepeatedSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CS, encodeRepeatedSpecOf, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, encodeRepeatedSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28, hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres))
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp]
    exact Entails.of_eq (by ac_rfl)

/-! ## Decomposition of `Poly.vecVecU8PinnedAt` into `repeatedBytesSliceAt` -/

theorem vecU8At_eq_repeatedBytesElemAt_uncond (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      repeatedBytesElemAt a ptr bs ∗ Varint.vecU8ElemRestAt A a cap ptr bs := by
  by_cases hcap : cap = 0
  · subst hcap
    unfold vecU8At vecHeader repeatedBytesElemAt Varint.vecU8ElemRestAt
    simp only [↓reduceIte, sepConj_emp]
    have hcongr :
        (⌜bs.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ : SepProp) =
        ⌜bs.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ (ptr ↦ₛ bs) := by
      refine (sepConj_emp _).symm.trans (pure_sepConj_congr fun ⟨hle, _, _⟩ => ?_)
      have hbs : bs = [] := by
        cases bs with
        | nil => rfl
        | cons _ _ =>
          have h0 : (0 : BitVec 64).toNat = 0 := rfl
          rw [h0, List.length_cons] at hle; omega
      rw [hbs, pointsToBytes_nil]
    conv_lhs => rw [hcongr]
    ac_rfl
  · exact Varint.vecU8At_eq_repeatedBytesElemAt A a cap ptr bs (fun h => absurd h hcap)

/-- Remaining ownership of a `Vec<u8>` element at `addr` after extracting `repeatedBytesElemAt addr ptr bs`. -/
def vecU8ElemRestAt (A : RustAlloc) (addr ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, Varint.vecU8ElemRestAt A addr cap ptr bs

/-- Remaining ownership of a `Vec<Vec<u8>>` slice at `base` after extracting `repeatedBytesSliceAt base elems`. -/
def vecU8SliceRestAt (A : RustAlloc) (base : BitVec 64) :
    List (BitVec 64 × List (BitVec 8)) → SepProp
  | [] => emp
  | (ptr, bs) :: rest =>
      vecU8ElemRestAt A base ptr bs ∗ vecU8SliceRestAt A (base + 24#64) rest

theorem satisfies_vecU8_iff_repeatedBytesElemAt (A : RustAlloc) (addr : BitVec 64)
    (bs : List (BitVec 8)) (R : SepProp) (m : Memory) :
    (m ⊨ vecU8 A addr bs ∗ R) ↔
    ∃ ptr : BitVec 64, m ⊨ (repeatedBytesElemAt addr ptr bs ∗ vecU8ElemRestAt A addr ptr bs) ∗ R := by
  dsimp only [vecU8, vecU8ElemRestAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  constructor
  · rintro ⟨cap, ptr, hm⟩
    rw [vecU8At_eq_repeatedBytesElemAt_uncond A addr cap ptr bs] at hm
    exact ⟨ptr, cap, by convert hm using 1; try ac_rfl⟩
  · rintro ⟨ptr, cap, hm⟩
    refine ⟨cap, ptr, ?_⟩
    rw [vecU8At_eq_repeatedBytesElemAt_uncond A addr cap ptr bs]
    convert hm using 1; try ac_rfl

theorem satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt (A : RustAlloc) :
    ∀ (bss : List (List (BitVec 8))) (base : BitVec 64) (R : SepProp) (m : Memory),
      (m ⊨ arrayAt (fun bs addr => vecU8 A addr bs) 24 base bss ∗ R) ↔
      ∃ elems : List (BitVec 64 × List (BitVec 8)),
        elems.map Prod.snd = bss ∧
        (m ⊨ (repeatedBytesSliceAt base elems ∗ vecU8SliceRestAt A base elems) ∗ R)
  | [], base, R, m => by
      dsimp only [arrayAt]
      constructor
      · intro hm
        refine ⟨[], rfl, ?_⟩
        dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt]
        rwa [emp_sepConj]
      · rintro ⟨elems, heq, hm⟩
        cases elems with
        | nil =>
            dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt] at hm
            rwa [emp_sepConj] at hm
        | cons _ _ => cases heq
  | bs :: rest, base, R, m => by
      have h24 : (BitVec.ofNat 64 24 : BitVec 64) = 24#64 := rfl
      dsimp only [arrayAt]
      rw [h24, sepConj_assoc, satisfies_vecU8_iff_repeatedBytesElemAt]
      constructor
      · rintro ⟨ptr, hm⟩
        have hm' : m ⊨ arrayAt (fun bs addr => vecU8 A addr bs) 24 (base + 24#64) rest ∗
            ((repeatedBytesElemAt base ptr bs ∗ vecU8ElemRestAt A base ptr bs) ∗ R) := by
          convert hm using 1; ac_rfl
        obtain ⟨elems, heq, hm''⟩ :=
          (satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt A rest (base + 24#64) _ m).mp hm'
        refine ⟨(ptr, bs) :: elems, congrArg (bs :: ·) heq, ?_⟩
        dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt]
        convert hm'' using 1; ac_rfl
      · rintro ⟨elems_all, heq, hm⟩
        cases elems_all with
        | nil => cases heq
        | cons hd tl =>
            rcases hd with ⟨ptr, bs'⟩
            dsimp only [List.map] at heq
            injection heq with hbs htl
            subst bs'
            dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt] at hm
            refine ⟨ptr, ?_⟩
            have hm' : m ⊨ (repeatedBytesSliceAt (base + 24#64) tl ∗ vecU8SliceRestAt A (base + 24#64) tl) ∗
                ((repeatedBytesElemAt base ptr bs ∗ vecU8ElemRestAt A base ptr bs) ∗ R) := by
              convert hm using 1; ac_rfl
            have hm'' :=
              (satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt A rest (base + 24#64) _ m).mpr
                ⟨tl, htl, hm'⟩
            convert hm'' using 1; ac_rfl

/-- Full remaining ownership of `Poly.vecVecU8PinnedAt A pin v bss` after extracting
`(v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
 repeatedBytesSliceAt pin.ptr elems`. -/
def vecVecU8PinnedRestAt (A : RustAlloc) (pin : LibsignalSessionRepr.VecPin)
    (elems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  let bss := elems.map Prod.snd
  ⌜bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
  vecU8SliceRestAt A pin.ptr elems ∗
  (if pin.cap = 0 then emp
   else A.live pin.ptr (pin.cap.toNat * 24) 8 ∗
     memRegion (pin.ptr + BitVec.ofNat 64 (bss.length * 24)) ((pin.cap.toNat - bss.length) * 24))

theorem satisfies_vecVecU8PinnedAt_iff (A : RustAlloc) (pin : LibsignalSessionRepr.VecPin)
    (v : BitVec 64) (bss : List (List (BitVec 8))) (R : SepProp) (m : Memory) :
    (m ⊨ Poly.vecVecU8PinnedAt A pin v bss ∗ R) ↔
    ∃ elems : List (BitVec 64 × List (BitVec 8)),
      elems.map Prod.snd = bss ∧ bss.length * 24 < 2 ^ 63 ∧
      (m ⊨ ((v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
        repeatedBytesSliceAt pin.ptr elems ∗
        vecVecU8PinnedRestAt A pin elems) ∗ R) := by
  dsimp only [Poly.vecVecU8PinnedAt, vecAt, vecHeader, vecBuf, vecHeaderBytes]
  by_cases h0 : pin.cap = 0
  · simp only [h0, ↓reduceIte]
    constructor
    · intro hm
      have hm_p : m ⊨ ⌜bss.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗ emp ∗ R) := by
        convert hm using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hm_p
      obtain ⟨⟨hle, hlt, hne⟩, hm1⟩ := hm_p
      have hbss : bss = [] := by
        cases bss with
        | nil => rfl
        | cons _ _ =>
          have hz : (0 : BitVec 64).toNat = 0 := rfl
          rw [hz, List.length_cons] at hle; omega
      subst hbss
      refine ⟨[], rfl, by decide, ?_⟩
      dsimp only [vecVecU8PinnedRestAt, List.map, List.length, repeatedBytesSliceAt, vecU8SliceRestAt]
      simp only [h0, ↓reduceIte]
      have hp : (0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0) = True :=
        eq_true ⟨hle, hlt, hne⟩
      simp only [hp, pure_true, emp_sepConj, sepConj_emp] at hm1 ⊢
      convert hm1 using 1; ac_rfl
    · rintro ⟨elems, heq, _, hm⟩
      dsimp only [vecVecU8PinnedRestAt] at hm
      simp only [h0, ↓reduceIte, heq] at hm
      have hm_p : m ⊨ ⌜bss.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          ((v ↦₆₄ 0) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
            repeatedBytesSliceAt pin.ptr elems ∗ vecU8SliceRestAt A pin.ptr elems ∗ emp ∗ R) := by
        convert hm using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hm_p
      obtain ⟨⟨hle, hlt, hne⟩, hm1⟩ := hm_p
      have hbss : bss = [] := by
        cases bss with
        | nil => rfl
        | cons _ _ =>
          have hz : (0 : BitVec 64).toNat = 0 := rfl
          rw [hz, List.length_cons] at hle; omega
      subst hbss
      cases elems with
      | nil =>
          dsimp only [repeatedBytesSliceAt, vecU8SliceRestAt] at hm1
          have hp : (([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0) = True :=
            eq_true ⟨hle, hlt, hne⟩
          simp only [hp, pure_true, emp_sepConj, sepConj_emp] at hm1 ⊢
          convert hm1 using 1; ac_rfl
      | cons _ _ => cases heq
  · simp only [h0, ↓reduceIte]
    constructor
    · intro hm
      have hm_p : m ⊨ ⌜bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 pin.ptr bss ∗
            ((v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗
              ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              A.live pin.ptr (pin.cap.toNat * 24) 8 ∗
              memRegion (pin.ptr + BitVec.ofNat 64 (bss.length * 24)) ((pin.cap.toNat - bss.length) * 24) ∗ R)) := by
        convert hm using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hm_p
      obtain ⟨⟨hle, hlt, hne⟩, hm2⟩ := hm_p
      have hbss24 : bss.length * 24 < 2 ^ 63 := by omega
      obtain ⟨elems, heq, hm3⟩ :=
        (satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt A bss pin.ptr _ m).mp hm2
      refine ⟨elems, heq, hbss24, ?_⟩
      dsimp only [vecVecU8PinnedRestAt]
      simp only [h0, ↓reduceIte, heq]
      have hp : (bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0) = True :=
        eq_true ⟨hle, hlt, hne⟩
      simp only [hp, pure_true, emp_sepConj]
      convert hm3 using 1; ac_rfl
    · rintro ⟨elems, heq, _, hm⟩
      dsimp only [vecVecU8PinnedRestAt] at hm
      simp only [h0, ↓reduceIte, heq] at hm
      have hm_p : m ⊨ ⌜bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          ((repeatedBytesSliceAt pin.ptr elems ∗ vecU8SliceRestAt A pin.ptr elems) ∗
            ((v ↦₆₄ pin.cap) ∗ ((v + 8#64) ↦₆₄ pin.ptr) ∗
              ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              A.live pin.ptr (pin.cap.toNat * 24) 8 ∗
              memRegion (pin.ptr + BitVec.ofNat 64 (bss.length * 24)) ((pin.cap.toNat - bss.length) * 24) ∗ R)) := by
        convert hm using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hm_p
      obtain ⟨⟨hle, hlt, hne⟩, hm2⟩ := hm_p
      have hm3 :=
        (satisfies_arrayAt_vecU8_iff_repeatedBytesSliceAt A bss pin.ptr _ m).mpr ⟨elems, heq, hm2⟩
      have hp : (bss.length ≤ pin.cap.toNat ∧ pin.cap.toNat * 24 < 2 ^ 63 ∧ pin.ptr ≠ 0) = True :=
        eq_true ⟨hle, hlt, hne⟩
      simp only [hp, pure_true, emp_sepConj]
      convert hm3 using 1; ac_rfl

end CryptoVerification.SpqrV1.Prost.MessageEncode

