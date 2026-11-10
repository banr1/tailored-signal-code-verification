/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `spqr::v1::chunked::send_ct::send_ct2_encoder` (`0x5e730`, `85` instructions)

**Checked by Lean.** Verifies `send_ct2_encoder_ok_4K` under `AllocContracts4K`,
`send_ct2_encoder_ok_ext` under `AllocContracts`, and `.inImage img` / `StatesRecvContractsAx` lifts.
-/

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Recv
  (growToCalleeExt sub_ok_inImage_of_sub_ok_ax sub_ok_inImage_growToCalleeExt_ax)
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [-simp, -arm64_norm] sendCt2Encoder_fnOff libsignalSessionCode_fnOff_0x5e730
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Instruction Decode Tree (`0x63b28..0x63c78`) -/

gen_decodes libsignalSessionCode_tree spqrSendCt2EncoderBin [
  0x5e730 → 0x5e880
]

/-! ## 2. Stack Frame, Address Normalization, and Slice/Buffer Helpers -/

@[local arm64_norm, local wp_norm] theorem sp_sub_80_sub_432 (sp : BitVec 64) :
    (sp - 80#64) - 432#64 = sp - 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_432 (sp : BitVec 64) :
    (sp - 512#64) + 432#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_8 (sp : BitVec 64) :
    (sp - 512#64) + 8#64 = sp - 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_16 (sp : BitVec 64) :
    (sp - 512#64) + 16#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_24 (sp : BitVec 64) :
    (sp - 512#64) + 24#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_512_add_32 (sp : BitVec 64) :
    (sp - 512#64) + 32#64 = sp - 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_504_add_8 (sp : BitVec 64) :
    (sp - 504#64) + 8#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_504_add_16 (sp : BitVec 64) :
    (sp - 504#64) + 16#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_496_add_8 (sp : BitVec 64) :
    (sp - 496#64) + 8#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_8 (sp : BitVec 64) :
    (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_16 (sp : BitVec 64) :
    (sp - 80#64) + 16#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_24 (sp : BitVec 64) :
    (sp - 80#64) + 24#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_32 (sp : BitVec 64) :
    (sp - 80#64) + 32#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_40 (sp : BitVec 64) :
    (sp - 80#64) + 40#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_48 (sp : BitVec 64) :
    (sp - 80#64) + 48#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_56 (sp : BitVec 64) :
    (sp - 80#64) + 56#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_64 (sp : BitVec 64) :
    (sp - 80#64) + 64#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_72 (sp : BitVec 64) :
    (sp - 80#64) + 72#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_80 (sp : BitVec 64) :
    (sp - 80#64) + 80#64 = sp := by bv_omega

/-- Saved callee-saved registers at `s0.sp - 80#64 .. s0.sp - 8#64` (`[s0.sp - 56#64]` holds `d56`). -/
def sendCt2SavedCells (s0 : State) (d56 : BitVec 64) : SepProp :=
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ d56) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem fold_sendCt2SavedCells (s0 : State) (d56 : BitVec 64) :
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
    ((s0.sp - 56#64) ↦₆₄ d56) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    sendCt2SavedCells s0 d56 :=
  Entails.refl _

theorem sendCt2SavedCells_entails_memRegion_80 (s0 : State) (d56 : BitVec 64) :
    sendCt2SavedCells s0 d56 ⊢ memRegion (s0.sp - 80#64) 80 := by
  have heq : sendCt2SavedCells s0 d56 =
      wordsAt (s0.sp - 80#64)
        [s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x28, d56,
         s0.readReg64 .x24, s0.readReg64 .x23, s0.readReg64 .x22, s0.readReg64 .x21,
         s0.readReg64 .x20, s0.readReg64 .x19] := by
    unfold sendCt2SavedCells
    simp only [wordsAt_10, arm64_norm]
  rw [heq]
  exact wordsAt_entails_memRegion _ (s0.sp - 80#64) 80 rfl

theorem stackAt_sendCt2Encoder_split (sp : BitVec 64) :
    stackAt sp sendCt2EncoderStack =
      stackAt (sp - 512#64) encodeBytesStackX ∗
      memRegion (sp - 512#64) 8 ∗
      cells (sp - 504#64) 3 ∗
      memRegion (sp - 480#64) 400 ∗
      cells (sp - 80#64) 10 := by
  change memRegion (sp - 17456#64) 17456 =
    memRegion (sp - 512#64 - 16944#64) 16944 ∗
    memRegion (sp - 512#64) 8 ∗
    cells (sp - 504#64) 3 ∗
    memRegion (sp - 480#64) 400 ∗
    cells (sp - 80#64) 10
  have hsub : sp - 512#64 - 16944#64 = sp - 17456#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_cells (sp - 504#64) 3 (by decide),
      ← ProofLib.memRegion_cells (sp - 80#64) 10 (by decide),
      ProofLib.memRegion_split' (b := sp - 17456#64) (n := 16944) (k := 512) (b' := sp - 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 512#64) (n := 8) (k := 504) (b' := sp - 504#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 504#64) (n := 24) (k := 480) (b' := sp - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 480#64) (n := 400) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide)]

theorem stackAt_512_recompose (s0 : State) (w0 w1 w2 d56 : BitVec 64) :
    stackAt (s0.sp - 512#64) encodeBytesStackX ∗
      memRegion (s0.sp - 512#64) 8 ∗
      (((s0.sp - 504#64) ↦₆₄ w0) ∗ ((s0.sp - 496#64) ↦₆₄ w1) ∗ ((s0.sp - 488#64) ↦₆₄ w2)) ∗
      memRegion (s0.sp - 480#64) 400 ∗
      sendCt2SavedCells s0 d56 ⊢
    stackAt s0.sp sendCt2EncoderStack := by
  have h3 :
      (((s0.sp - 504#64) ↦₆₄ w0) ∗ ((s0.sp - 496#64) ↦₆₄ w1) ∗ ((s0.sp - 488#64) ↦₆₄ w2)) ⊢
      memRegion (s0.sp - 504#64) 24 := by
    have heq :
        (((s0.sp - 504#64) ↦₆₄ w0) ∗ ((s0.sp - 496#64) ↦₆₄ w1) ∗ ((s0.sp - 488#64) ↦₆₄ w2)) =
        wordsAt (s0.sp - 504#64) [w0, w1, w2] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2] (s0.sp - 504#64) 24 rfl
  have h10 := sendCt2SavedCells_entails_memRegion_80 s0 d56
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono h3 (sepConj_mono_right h10)))) ?_
  change memRegion (s0.sp - 512#64 - 16944#64) 16944 ∗
      (memRegion (s0.sp - 512#64) 8 ∗ (memRegion (s0.sp - 504#64) 24 ∗
        (memRegion (s0.sp - 480#64) 400 ∗ memRegion (s0.sp - 80#64) 80))) ⊢
    memRegion (s0.sp - 17456#64) 17456
  have hsub : s0.sp - 512#64 - 16944#64 = s0.sp - 17456#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 400) (k := 80) (b' := s0.sp - 80#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 504#64) (n := 24) (k := 480) (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 512#64) (n := 8) (k := 504) (b' := s0.sp - 504#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 17456#64) (n := 16944) (k := 512) (b' := s0.sp - 512#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_encodeBytesX_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encodeBytesStackX ⊢
    memRegion (fsp - 16944#64) 12848 ∗ stackAt fsp allocHookStack := by
  change memRegion (fsp - 16944#64) 16944 ⊢
    memRegion (fsp - 16944#64) 12848 ∗ memRegion (fsp - 4096#64) 4096
  rw [ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 12848) (k := 4096) (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_encodeBytesX_from_allocHook (fsp : BitVec 64) :
    memRegion (fsp - 16944#64) 12848 ∗ stackAt fsp allocHookStack ⊢
    stackAt fsp encodeBytesStackX := by
  change memRegion (fsp - 16944#64) 12848 ∗ memRegion (fsp - 4096#64) 4096 ⊢
    memRegion (fsp - 16944#64) 16944
  rw [← ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 12848) (k := 4096) (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_encodeBytesX_to_doReserve (fsp : BitVec 64) :
    stackAt fsp encodeBytesStackX ⊢
    memRegion (fsp - 16944#64) 12736 ∗ stackAt fsp doReserveStack := by
  change memRegion (fsp - 16944#64) 16944 ⊢
    memRegion (fsp - 16944#64) 12736 ∗ memRegion (fsp - 4208#64) 4208
  rw [ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 12736) (k := 4208) (b' := fsp - 4208#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_encodeBytesX_from_doReserve (fsp : BitVec 64) :
    memRegion (fsp - 16944#64) 12736 ∗ stackAt fsp doReserveStack ⊢
    stackAt fsp encodeBytesStackX := by
  change memRegion (fsp - 16944#64) 12736 ∗ memRegion (fsp - 4208#64) 4208 ⊢
    memRegion (fsp - 16944#64) 16944
  rw [← ProofLib.memRegion_split' (b := fsp - 16944#64) (n := 12736) (k := 4208) (b' := fsp - 4208#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_sendCt2Encoder_to_allocHook (sp : BitVec 64) :
    stackAt sp sendCt2EncoderStack ⊢
    memRegion (sp - 17456#64) 13360 ∗ stackAt sp allocHookStack := by
  change memRegion (sp - 17456#64) 17456 ⊢
    memRegion (sp - 17456#64) 13360 ∗ memRegion (sp - 4096#64) 4096
  rw [ProofLib.memRegion_split' (b := sp - 17456#64) (n := 13360) (k := 4096) (b' := sp - 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_sendCt2Encoder_from_allocHook (sp : BitVec 64) :
    memRegion (sp - 17456#64) 13360 ∗ stackAt sp allocHookStack ⊢
    stackAt sp sendCt2EncoderStack := by
  change memRegion (sp - 17456#64) 13360 ∗ memRegion (sp - 4096#64) 4096 ⊢
    memRegion (sp - 17456#64) 17456
  rw [← ProofLib.memRegion_split' (b := sp - 17456#64) (n := 13360) (k := 4096) (b' := sp - 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- `encodeBytesSpec A` entails `encodeBytesSpecX A` by framing the unused bottom stack region. -/
theorem encodeBytesSpecX_of_encodeBytesSpec' {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (encodeBytesSpec A)) :
    subroutine_ok P addr (encodeBytesSpecX A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hle : encodeBytesStack ≤ encodeBytesStackX := by decide
  have hsplit : stackAt s0.sp encodeBytesStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
        (encodeBytesStackX - encodeBytesStack) ∗
        stackAt s0.sp encodeBytesStack := by
    have h1 := stackAt_split_bottom s0.sp encodeBytesStack
      (encodeBytesStackX - encodeBytesStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
      (encodeBytesStackX - encodeBytesStack) ∗ R
  have hpre' : s0.mem ⊨ (encodeBytesSpec A).pre x s0 ∗ R' := by
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine (h.to_outcome x R' s0 hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpost ⊢
    have h1 : (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
          (encodeBytesStackX - encodeBytesStack) ∗ R) ⊢
        (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      rw [sepConj_assoc, sepConj_assoc, ← sepConj_assoc anyHeap]
      exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))
    exact Satisfies.mono h1 hpost
  · dsimp only [encodeBytesSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem slice_and_vecU8Tail_eq_doReserveBuf (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (h0 : cap = 0#64 → bs = []) :
    (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs =
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8Tail
  by_cases hc : cap = 0#64
  · subst hc
    rw [h0 rfl]
    simp [pointsToBytes_nil]
  · have hcb : (cap == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcb, Bool.false_eq_true, ↓reduceIte]
    ac_rfl

theorem polyEncoderAt_split_tag (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    ∃ tag : BitVec 64, (tag = 0#64 ∨ tag = 1#64) ∧
      ∃ rest : SepProp, polyEncoderAt A a enc = (a ↦₆₄ tag) ∗ rest := by
  unfold polyEncoderAt encoderStateAt
  cases enc.s with
  | points pts =>
    dsimp only [polyEncoderPointsTag]
    exact ⟨0#64, Or.inl rfl,
      ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
        pointListOf A (a + polyEncoderVecsOff) pts ∗
        ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
        memRegion (a + polyEncoderPadOff) polyEncoderPadSize, by ac_rfl⟩
  | polys polys =>
    dsimp only [polyEncoderPolysTag]
    exact ⟨1#64, Or.inr rfl,
      ⌜polys.length = NUM_POLYS⌝ ∗ polyListOf A (a + polyEncoderVecsOff) polys ∗
        ((a + polyEncoderIdxOff) ↦₃₂ enc.idx) ∗
        memRegion (a + polyEncoderPadOff) polyEncoderPadSize, by ac_rfl⟩

/-! ## 3. Framed Call Rules (`call_memcpy_relocate_cs`, `call_doReserve7Raw`, `call_encodeBytesX`) -/

/-- Framed `memcpy` call rule that relocates any `Relocatable n F` predicate from `src` to `dst`,
leaving `memRegion src n` at `src`, and forwards `CalleeSavedPreserved s sf`. -/
theorem call_memcpy_relocate_cs {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.fold (relocate_pre_entails hrel dst src Frame) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.fold (relocate_post_entails dst src hlen Frame) (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed call rule for `doReserveRawSpec A` (`0x530a0`). -/
theorem call_doReserve7Raw {A : RustAlloc} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (doReserveRawSpec A))
    (v cap ptr : BitVec 64) (bs : Bytes) (additional : Nat)
    (hlen : bs.length ≤ cap.toNat) (hptr : ptr ≠ 0#64)
    (h0 : cap = 0#64 → bs = [])
    (hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = v)
    (hx1 : (s.readReg64 Reg.x1).toNat = bs.length)
    (hx2 : (s.readReg64 Reg.x2).toNat = additional)
    (hx3 : s.readReg64 Reg.x3 = 1#64)
    (hx4 : s.readReg64 Reg.x4 = 1#64)
    (hsplit : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs ∗
      A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      let newCap := reserveCap cap.toNat bs.length additional
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      p' ≠ 0#64 →
      SepWP prog next_pc sf
        (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' newCap 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨v, cap, ptr, bs, additional⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [doReserveRawSpec]
    rw [hsp, ← slice_and_vecU8Tail_eq_doReserveBuf A cap ptr bs h0]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [doReserveRawSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    wp_pull_exists; rename_i p'
    wp_focus_pure; intro hp'
    have hassoc :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame =
        (v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf p' hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hp'

/-- Framed call rule for `encodeBytesSpecX A` (`0x6b6b8`) when `encodeBytesResult msg = .ok outEnc`. -/
theorem call_encodeBytesX {A : RustAlloc} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (encodeBytesSpecX A))
    (out msgA : BitVec 64) (msg : Bytes) (outEnc : PolyEncoder)
    (henc : encodeBytesResult msg = .ok outEnc) (hlen_lt : msg.length < 2 ^ 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = out)
    (hx0 : s.readReg64 Reg.x0 = msgA)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 msg.length)
    (hsplit : P = (memRegion out 400 ∗ (msgA ↦ₛ msg) ∗
      A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨out, false, msgA, msg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [encodeBytesSpecX, polyEncoderSize, bytesAt]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hlen_lt⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [encodeBytesSpecX]
    rw [henc, resultPolyEncoderAt, hsp, sepConj_assoc]
    change SepWPp prog (s0.readReg64 Reg.lr) sf
      (⌜sf.trace = s.trace⌝ ∗
        ((polyEncoderAt A out outEnc ∗
          ((msgA ↦ₛ msg) ∗ (A.pool ∗ stackAt sp_call encodeBytesStackX))) ∗ Frame)) post _
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyEncoderAt A out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame =
        (polyEncoderAt A out outEnc ∗
          ((msgA ↦ₛ msg) ∗ (A.pool ∗ stackAt sp_call encodeBytesStackX))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed call rule for `rustAllocSpec A` (`__rust_alloc`). -/
theorem call_rustAlloc {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustAllocSpec A))
    (size align : Nat) (hlay : LayoutOk size align)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size)
    (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        (((if sf.readReg64 .x0 = 0 then
            ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else
            ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size) ∗
          A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (size, align)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit] at hm
    dsimp only [rustAllocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustAllocSpec]
    rw [hsp, htrace]
    have hassoc :
        (A.pool ∗ stackAt sp_call allocHookStack ∗
          (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)) ∗ Frame =
        (((if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size) ∗
          A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) := by ac_rfl
    rw [hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf

private theorem call_memcpy_relocate_cs_4K {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withStack sessionMemcpyRegionSpec encodeBytesStackX))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((F dst ∗ memRegion src n) ∗ (stackAt sp_call encodeBytesStackX ∗ Frame)) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit, show (memRegion dst n ∗ F src ∗ stackAt sp_call encodeBytesStackX) ∗ Frame =
      (memRegion dst n ∗ F src) ∗ (stackAt sp_call encodeBytesStackX ∗ Frame) by sep_frame]
  refine SepWP.fold
    (relocate_pre_entails hrel dst src (stackAt sp_call encodeBytesStackX ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists; rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by
      dsimp only [withStack, sessionMemcpyRegionSpec] at h
      exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using h)).1)
    (fun _ _ _ _ h => by
      dsimp only [withStack, sessionMemcpyRegionSpec] at h
      exact ((satisfies_pure_sepConj _ _ _).mp (by simpa only [sepConj_assoc] using h)).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp, hlen, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_frame)) hm⟩
  · dsimp only [withStack, sessionMemcpyRegionSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hreord :
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt sp_call encodeBytesStackX ∗
          (relocatedHeap F bs ∗ Frame) =
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ relocatedHeap F bs ∗
          (stackAt sp_call encodeBytesStackX ∗ Frame) := by sep_frame
    rw [hreord]
    refine SepWP.fold
      (relocate_post_entails dst src hlen (stackAt sp_call encodeBytesStackX ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 4. Encoder Generation & Buffer Deallocation (`entry + 100#64` = `0x5e6b0`) -/

private theorem send_ct2_encoder_finish_4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (henc_call : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName + 31632#64) (encodeBytesSpecX A))
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        (bv% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "memcpy")))
      (withStack sessionMemcpyRegionSpec encodeBytesStackX))
    (hdealloc : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        (bv% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_dealloc"))) (rustDeallocSpec A))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (outEnc : PolyEncoder)
    (cap ptr w24 d56 : BitVec 64)
    (henc_res : encodeBytesResult (ct2 ++ mac) = .ok outEnc)
    (hlen_le : (ct2 ++ mac).length ≤ 1048576)
    (hcap_le : (ct2 ++ mac).length ≤ cap.toNat)
    (hcap_lt : cap.toNat < 2 ^ 63)
    {s0 s : State} {P R : SepProp}
    (_hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr sendCt2EncoderName + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 512#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 mac.length)
    (hx21 : s.readReg64 .x21 = ptr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ct2.length)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
       (ptr ↦ₛ (ct2 ++ mac)) ∗ vecU8Tail A cap ptr (ct2 ++ mac) ∗
       ((s0.sp - 504#64) ↦₆₄ cap) ∗ ((s0.sp - 496#64) ↦₆₄ ptr) ∗
       ((s0.sp - 488#64) ↦₆₄ w24) ∗ memRegion (s0.sp - 512#64) 8 ∗
       memRegion (s0.sp - 480#64) 400 ∗ sendCt2SavedCells s0 d56 ∗
       A.pool ∗ stackAt (s0.sp - 512#64) encodeBytesStackX) ∗ emp) :
    SepWPp (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗ polyEncoderAt A outA outEnc ∗
            (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗ A.pool ∗
            stackAt s0.sp sendCt2EncoderStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  rw [hP, sepConj_emp]
  have hfn : libsignalSessionCode.fnOff sendCt2EncoderName = 0x5e730 :=
    sendCt2Encoder_fnOff
  code_fetches CryptoVerification.libsignalSessionCode spqrSendCt2EncoderBin b
    (Rust.withPanics ext) hfn 0x5e730 340
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, sendCt2EncoderName,
    BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "spqr::v1::chunked::send_ct::send_ct2_encoder" = entry
  examples_hide_fetches
  have hadd_len :
      BitVec.ofNat 64 ct2.length + BitVec.ofNat 64 mac.length =
        BitVec.ofNat 64 (ct2 ++ mac).length := by
    rw [List.length_append, BitVec.ofNat_add]
  have hlen_lt64 : (ct2 ++ mac).length < 2 ^ 64 := by omega
  apply SepWPp.of_sepWP (mid := entry + 31632#64)
  wp_steps
  refine call_encodeBytesX henc_call
    (s0.sp - 480#64) ptr (ct2 ++ mac) outEnc henc_res hlen_lt64
    (ret_pc := entry + 120#64) (sp_call := s0.sp - 512#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x8, arm64_norm, hsp])
    (by simp only [Reg.x0, arm64_norm, hx21])
    (by simp only [Reg.x1, arm64_norm, hx22, hx20, hadd_len])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx22, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  obtain ⟨tag, htag01, encRest, henc_split⟩ := polyEncoderAt_split_tag A (s0.sp - 480#64) outEnc
  rcases htag01 with rfl | rfl
  · wp_conv_pre => rw [henc_split]
    wp_steps
    wp_conv_pre => rw [← henc_split]
    refine call_memcpy_relocate_cs_4K hmemcpy (s0 := s0)
      (Relocatable.of_polyEncoderAt A outEnc) outA (s0.sp - 480#64)
      (ret_pc := entry + 148#64) (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
      (by simp only [Reg.x0, arm64_norm, hx19_1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm])
      (by (conv => lhs; simp only [sepConj_assoc]); sep_focus)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
    simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
    refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A cap ptr (ct2 ++ mac) hcap_le hcap_lt)
      (by sep_focus) ?_
    dsimp only [vecCapPtrDealloc, sendCt2SavedCells]
    by_cases hcap0 : (cap == 0#64) = true <;>
      simp only [hcap0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · have hcap_eq0 : cap = 0#64 := eq_of_beq hcap0
      subst hcap_eq0
      wp_steps
      refine SepWP.fold (stackAt_512_recompose s0 0#64 ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      wp_done
    · have hcap_ne0 : cap ≠ 0#64 := ne_of_beq_false (Bool.eq_false_iff.mpr hcap0)
      have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero fun h0 =>
        hcap_ne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hlay_dealloc : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
      wp_steps
      refine SepWP.fold (stackAt_512_recompose s0 cap ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      refine SepWP.fold (stackAt_sendCt2Encoder_to_allocHook s0.sp) (by sep_focus) ?_
      wp_apply
      refine SepWP.fold (stackAt_sendCt2Encoder_from_allocHook s0.sp) (by sep_focus) ?_
      wp_done
  · wp_conv_pre => rw [henc_split]
    wp_steps
    wp_conv_pre => rw [← henc_split]
    refine call_memcpy_relocate_cs_4K hmemcpy (s0 := s0)
      (Relocatable.of_polyEncoderAt A outEnc) outA (s0.sp - 480#64)
      (ret_pc := entry + 148#64) (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
      (by simp only [Reg.x0, arm64_norm, hx19_1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm])
      (by (conv => lhs; simp only [sepConj_assoc]); sep_focus)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
    simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
    refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A cap ptr (ct2 ++ mac) hcap_le hcap_lt)
      (by sep_focus) ?_
    dsimp only [vecCapPtrDealloc, sendCt2SavedCells]
    by_cases hcap0 : (cap == 0#64) = true <;>
      simp only [hcap0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · have hcap_eq0 : cap = 0#64 := eq_of_beq hcap0
      subst hcap_eq0
      wp_steps
      refine SepWP.fold (stackAt_512_recompose s0 0#64 ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      wp_done
    · have hcap_ne0 : cap ≠ 0#64 := ne_of_beq_false (Bool.eq_false_iff.mpr hcap0)
      have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero fun h0 =>
        hcap_ne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hlay_dealloc : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
      wp_steps
      refine SepWP.fold (stackAt_512_recompose s0 cap ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      refine SepWP.fold (stackAt_sendCt2Encoder_to_allocHook s0.sp) (by sep_focus) ?_
      wp_apply
      refine SepWP.fold (stackAt_sendCt2Encoder_from_allocHook s0.sp) (by sep_focus) ?_
      wp_done

/-! ## 5. MAC Reserve & Copy (`entry + 208#64` = `0x5e71c`) -/

private theorem send_ct2_encoder_mac_4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdr7 : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName + 18446744073709483384#64) (doReserveRawSpec A))
    (henc_call : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName + 31632#64) (encodeBytesSpecX A))
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        (bv% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "memcpy")))
      (withStack sessionMemcpyRegionSpec encodeBytesStackX))
    (hdealloc : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        (bv% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_dealloc"))) (rustDeallocSpec A))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (outEnc : PolyEncoder)
    (cap ptr d56 : BitVec 64)
    (henc_res : encodeBytesResult (ct2 ++ mac) = .ok outEnc)
    (hlen_le : (ct2 ++ mac).length ≤ 1048576)
    (hcap_eq : cap.toNat = ct2.length)
    (hptr_ne : ptr ≠ 0#64)
    {s0 s : State} {P R : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr sendCt2EncoderName + 208#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 512#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 mac.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ct2.length)
    (hx23 : s.readReg64 .x23 = macPtr)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
       (ptr ↦ₛ ct2) ∗ vecU8Tail A cap ptr ct2 ∗
       ((s0.sp - 504#64) ↦₆₄ cap) ∗ ((s0.sp - 496#64) ↦₆₄ ptr) ∗
       ((s0.sp - 488#64) ↦₆₄ BitVec.ofNat 64 ct2.length) ∗
       memRegion (s0.sp - 512#64) 8 ∗ memRegion (s0.sp - 480#64) 400 ∗
       sendCt2SavedCells s0 d56 ∗ A.pool ∗
       stackAt (s0.sp - 512#64) encodeBytesStackX) ∗ emp) :
    SepWPp (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗ polyEncoderAt A outA outEnc ∗
            (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗ A.pool ∗
            stackAt s0.sp sendCt2EncoderStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  rw [hP, sepConj_emp]
  have h_finish := send_ct2_encoder_finish_4K henc_call hmemcpy hdealloc
  have hfn : libsignalSessionCode.fnOff sendCt2EncoderName = 0x5e730 :=
    sendCt2Encoder_fnOff
  code_fetches CryptoVerification.libsignalSessionCode spqrSendCt2EncoderBin b
    (Rust.withPanics ext) hfn 0x5e730 340
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, sendCt2EncoderName,
    BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "spqr::v1::chunked::send_ct::send_ct2_encoder" = entry
  examples_hide_fetches
  have hlen_app : (ct2 ++ mac).length = ct2.length + mac.length := List.length_append
  have hct2_lt : ct2.length < 2 ^ 64 := by omega
  have hmac_lt : mac.length < 2 ^ 64 := by omega
  have hct2_toNat : (BitVec.ofNat 64 ct2.length).toNat = ct2.length := Nat.mod_eq_of_lt hct2_lt
  have hmac_toNat : (BitVec.ofNat 64 mac.length).toNat = mac.length := Nat.mod_eq_of_lt hmac_lt
  have h0_imp : cap = 0#64 → ct2 = [] := fun hc0 => by
    subst hc0; exact List.eq_nil_of_length_eq_zero hcap_eq.symm
  let newCap := reserveCap cap.toNat ct2.length mac.length
  have hnew_bound : newCap + 1 ≤ 2 ^ 63 := by dsimp [newCap, reserveCap]; omega
  have hnew_ge : ct2.length + mac.length ≤ newCap := by dsimp [newCap, reserveCap]; omega
  have hnew_pos : 0 < newCap := by dsimp [newCap, reserveCap]; omega
  have hnew_lt63 : newCap < 2 ^ 63 := by omega
  have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := Nat.mod_eq_of_lt (by omega)
  have hnew_ne0 : BitVec.ofNat 64 newCap ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hnew_toNat] at this
    change newCap = 0 at this; omega
  apply SepWPp.of_sepWP (mid := entry + 18446744073709483384#64)
  wp_steps
  refine SepWP.fold (stackAt_encodeBytesX_to_doReserve (s0.sp - 512#64)) (by sep_focus) ?_
  refine call_doReserve7Raw hdr7
    (s0.sp - 504#64) cap ptr ct2 mac.length
    (by omega) hptr_ne h0_imp hnew_bound
    (ret_pc := entry + 232#64) (next_pc := entry + 100#64) (sp_call := s0.sp - 512#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp])
    (by simp only [Reg.x1, arm64_norm, hx22, hct2_toNat])
    (by simp only [Reg.x2, arm64_norm, hx20, hmac_toNat])
    (by simp only [Reg.x3, arm64_norm])
    (by simp only [Reg.x4, arm64_norm])
    (by sep_focus)
    (fun sf1 p' hpc1 hrun1 hsp1 hcs1 htr1 hp'_ne => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx22, hx23, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (stackAt_encodeBytesX_from_doReserve (s0.sp - 512#64)) (by sep_focus) ?_
  have hmem_split :
      memRegion (p' + BitVec.ofNat 64 ct2.length) (newCap - ct2.length) ⊢
      memRegion (p' + BitVec.ofNat 64 ct2.length) mac.length ∗
      memRegion (p' + BitVec.ofNat 64 (ct2 ++ mac).length) (newCap - (ct2 ++ mac).length) := by
    rw [ProofLib.memRegion_split'
      (b := p' + BitVec.ofNat 64 ct2.length) (n := mac.length)
      (k := newCap - (ct2 ++ mac).length) (b' := p' + BitVec.ofNat 64 (ct2 ++ mac).length)
      (by omega) (by rw [List.length_append, BitVec.ofNat_add, BitVec.add_assoc]) (by omega)]
    exact Entails.refl _
  refine SepWP.fold hmem_split (by sep_focus) ?_
  wp_steps; wp_apply; wp_steps
  have hjoin_mac :
      A.live p' newCap 1 ∗ (p' ↦ₛ ct2) ∗ ((p' + BitVec.ofNat 64 ct2.length) ↦ₛ mac) ∗
        memRegion (p' + BitVec.ofNat 64 (ct2 ++ mac).length) (newCap - (ct2 ++ mac).length) ⊢
      (p' ↦ₛ (ct2 ++ mac)) ∗ vecU8Tail A (BitVec.ofNat 64 newCap) p' (ct2 ++ mac) := by
    have hcb : (BitVec.ofNat 64 newCap == 0#64) = false := beq_false_of_ne hnew_ne0
    unfold vecU8Tail
    simp only [hcb, Bool.false_eq_true, ↓reduceIte, hnew_toNat, pointsToBytes_append]
    exact Entails.of_eq (by sep_frame)
  refine SepWP.fold hjoin_mac (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  exact h_finish outA ct2Ptr macPtr ct2 mac outEnc
    (BitVec.ofNat 64 newCap) p' (BitVec.ofNat 64 ct2.length) d56
    henc_res hlen_le (by rw [hnew_toNat]; omega) (by rw [hnew_toNat]; omega)
    hsp0_align hfsp_align
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, hsp1, *])
    (by simp only [Reg.x19, arm64_norm, hx19_1, *])
    (by simp only [Reg.x20, arm64_norm, hx20_1, *])
    (by simp only [Reg.x21, arm64_norm, *])
    (by simp only [Reg.x22, arm64_norm, *])
    (by simp only [Reg.x25, arm64_norm, hx25_1, *])
    (by simp only [Reg.x26, arm64_norm, hx26_1, *])
    (by simp only [Reg.x27, arm64_norm, hx27_1, *])
    (by simp only [arm64_norm, htr1, *])
    (by simp only [arm64_norm, hvregs_1, *])
    (by sep_focus)

/-! ## 6. Main Theorems: `send_ct2_encoder_ok_4K`, `send_ct2_encoder_ok_ext`, `.inImage`, & `ax` -/

private theorem send_ct2_encoder_ok_core {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        BitVec.ofNat 64 (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_no_alloc_shim_is_unstable_v2")))
      noAllocShimSpec)
    (halloc : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        BitVec.ofNat 64 (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_alloc")))
      (rustAllocSpec A))
    (hdealloc : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        BitVec.ofNat 64 (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        BitVec.ofNat 64 (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "memcpy")))
      (withStack sessionMemcpyRegionSpec encodeBytesStackX))
    (hdr7_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name) (doReserveRawSpec A))
    (henc : EncodeBytesOkExt b A ext) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A) := by
  have hfn : libsignalSessionCode.fnOff sendCt2EncoderName = 0x5e730 :=
    sendCt2Encoder_fnOff
  have haerr : (leavesProgAtExt b ext).externAt?
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName +
        BitVec.ofNat 64 (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "alloc::raw_vec::handle_error"))) =
        some Rust.panicked :=
    panic_at_handle_error_ext b ext sendCt2EncoderName
      (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "alloc::raw_vec::handle_error"))
      (by
        change libsignalSessionCode.fnOff sendCt2EncoderName +
          (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "alloc::raw_vec::handle_error")) =
          libsignalSessionCode.fnOff "alloc::raw_vec::handle_error"
        rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hdr7 : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName + 18446744073709483384#64)
      (doReserveRawSpec A) := by
    have hrel : (leavesProgAtExt b ext).fnAddr sendCt2EncoderName =
        (leavesProgAtExt b ext).fnAddr doReserve7Name + BitVec.ofNat 64 68232 :=
      Program.fnAddr_rel (k := 68232) (b := b) (X := Rust.withPanics ext)
        libsignalSessionCode_fnOff_0x4dca8 hfn (by decide)
    refine sub_ok_of_addr_eq ?_ hdr7_fn
    dsimp only [leavesProgAtExt, contractProg, tripleRatchetProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  have henc_call : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName + 31632#64)
      (encodeBytesSpecX A) := by
    have hrel := fnAddr_fwd_eq (c := libsignalSessionCode)
      (f1 := sendCt2EncoderName) (f2 := encodeBytesName)
      (o1 := 0x5e730) (o2 := 0x662c0) (d := 31632)
      (b := b) (X := Rust.withPanics ext)
      hfn encodeBytes_fnOff rfl
    rw [hrel]
    exact encodeBytesSpecX_of_encodeBytesSpec' henc
  code_fetches CryptoVerification.libsignalSessionCode spqrSendCt2EncoderBin b
    (Rust.withPanics ext) hfn 0x5e730 340
  clear hfn
  unfold sendCt2EncoderSpec
  conv => arg 3; arg 1; ext x s; simp only [stackAt_sendCt2Encoder_split]
  cells_unfold
  wpp_init x s0
  conv => arg 6; ext sf P_f; rw [sepConj_assoc]
  obtain ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ := x
  have h_finish := send_ct2_encoder_finish_4K henc_call hmemcpy hdealloc
  have h_mac := send_ct2_encoder_mac_4K hdr7 henc_call hmemcpy hdealloc
  dsimp only [leavesProgAtExt, contractProg, tripleRatchetProgAtExt, sendCt2EncoderName,
    BitVec.ofNat_eq_ofNat, CryptoVerification.LibsignalTripleRatchet.Expand.esp] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "spqr::v1::chunked::send_ct::send_ct2_encoder" = entry
  examples_hide_fetches
  obtain ⟨henc_res, hlen_le⟩ := encodeBytesResult_of_expectEncodeBytes_ok
    ‹Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc›
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := ‹(s0.sp &&& 15#64 == 0#64) = true›
  have hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 512#64 hsp0_align (by decide)
  have hlen_app : (ct2 ++ mac).length = ct2.length + mac.length := List.length_append
  by_cases hct2_nil : ct2 = []
  · subst hct2_nil
    have hct2_z : (BitVec.ofNat 64 ([] : Bytes).length == 0#64) = true := rfl
    have henc_nil :
        emp ⊢ ((1#64 : BitVec 64) ↦ₛ ([] : Bytes)) ∗ vecU8Tail A 0#64 1#64 [] := by
      unfold vecU8Tail; simp [pointsToBytes_nil]; exact Entails.refl emp
    by_cases hmac_nil : mac = []
    · subst hmac_nil
      have hmac_z : (BitVec.ofNat 64 ([] : Bytes).length == 0#64) = true := rfl
      apply SepWPp.of_sepWP (mid := entry + 100#64)
      wp_steps
      refine SepWP.fold (Entails.trans (Entails.of_eq (emp_sepConj _).symm)
        (sepConj_mono_left henc_nil)) (sepConj_emp _).symm ?_
      rw [sepConj_emp]
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      exact h_finish outA ct2Ptr macPtr [] [] outEnc 0#64 1#64 0#64 _
        henc_res hlen_le (by decide) (by decide) hsp0_align hfsp_align
        (by wp_norm_goal) (by wp_norm_lhs) (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [List.append_nil]; sep_focus)
    · have hmac_pos : 0 < mac.length := List.length_pos_iff.mpr hmac_nil
      have hmac_ne0 : BitVec.ofNat 64 mac.length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change mac.length = 0 at this; omega
      have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = false := beq_false_of_ne hmac_ne0
      apply SepWPp.of_sepWP (mid := entry + 208#64)
      wp_steps
      refine SepWP.fold (Entails.trans (Entails.of_eq (emp_sepConj _).symm)
        (sepConj_mono_left henc_nil)) (sepConj_emp _).symm ?_
      rw [sepConj_emp]
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      exact h_mac outA ct2Ptr macPtr [] mac outEnc 0#64 1#64 _
        henc_res hlen_le rfl (by decide) hsp0_align hfsp_align
        (by wp_norm_goal) (by wp_norm_lhs) (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *]) (by simp only [Reg.x23, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by sep_focus)
  · have hct2_pos : 0 < ct2.length := List.length_pos_iff.mpr hct2_nil
    have hct2_toNat : (BitVec.ofNat 64 ct2.length).toNat = ct2.length := Nat.mod_eq_of_lt (by omega)
    have hct2_ne0 : BitVec.ofNat 64 ct2.length ≠ 0#64 := by
      intro h0; have := congrArg BitVec.toNat h0; rw [hct2_toNat] at this
      change ct2.length = 0 at this; omega
    have hct2_z : (BitVec.ofNat 64 ct2.length == 0#64) = false := beq_false_of_ne hct2_ne0
    have hlay_ct2 : LayoutOk ct2.length 1 := ⟨hct2_pos, ⟨0, rfl⟩, by omega⟩
    apply SepWPp.of_sepWP (mid := entry + 68#64)
    wp_steps; wp_apply; wp_steps
    refine SepWP.fold (stackAt_encodeBytesX_to_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
    refine call_rustAlloc halloc ct2.length 1 hlay_ct2
      (s0 := s0) (ret_pc := entry + 68#64) (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hfsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, hct2_toNat, *]) (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus) (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    by_cases hoom : sf1.readReg64 (Reg.gpr 0#5) = 0
    · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_elim fun htr_oom => ?_
      apply SepWPp.of_sepWP
        (mid := entry + (bv% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "alloc::raw_vec::handle_error")))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, htr_ok⟩ => ?_
      have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
      have hjoin_ct2 :
          A.live (sf1.readReg64 (Reg.gpr 0#5)) ct2.length 1 ∗
            (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ ct2) ⊢
          (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ ct2) ∗
            vecU8Tail A (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) ct2 := by
        unfold vecU8Tail
        simp only [hct2_z, Bool.false_eq_true, ↓reduceIte, hct2_toNat, Nat.sub_self,
          ProofLib.memRegion_zero, sepConj_emp]
        exact Entails.of_eq (sepConj_comm _ _)
      by_cases hmac_nil : mac = []
      · have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = true := by subst hmac_nil; rfl
        apply SepWPp.of_sepWP (mid := entry + 100#64)
        refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
        wp_steps; wp_apply; wp_steps
        conv => arg 4; rw [hsp1]
        subst hmac_nil
        refine SepWP.fold hjoin_ct2 (by sep_focus) ?_
        refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        exact h_finish outA ct2Ptr macPtr ct2 [] outEnc
          (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) (BitVec.ofNat 64 ct2.length) _
          henc_res hlen_le (by rw [List.append_nil, hct2_toNat]) (by rw [hct2_toNat]; omega)
          hsp0_align hfsp_align (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, arm64_norm, *]) (by simp only [Reg.x19, arm64_norm, *])
          (by simp only [Reg.x20, arm64_norm, *]) (by simp only [Reg.x21, arm64_norm, *])
          (by simp only [Reg.x22, arm64_norm, *]) (by simp only [Reg.x25, arm64_norm, *])
          (by simp only [Reg.x26, arm64_norm, *]) (by simp only [Reg.x27, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [List.append_nil]; sep_focus)
      · have hmac_pos : 0 < mac.length := List.length_pos_iff.mpr hmac_nil
        have hmac_ne0 : BitVec.ofNat 64 mac.length ≠ 0#64 := by
          intro h0; have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          change mac.length = 0 at this; omega
        have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = false := beq_false_of_ne hmac_ne0
        apply SepWPp.of_sepWP (mid := entry + 208#64)
        refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
        wp_steps; wp_apply; wp_steps
        conv => arg 4; rw [hsp1]
        refine SepWP.fold hjoin_ct2 (by sep_focus) ?_
        refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        exact h_mac outA ct2Ptr macPtr ct2 mac outEnc
          (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) _
          henc_res hlen_le hct2_toNat hoom hsp0_align hfsp_align
          (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, arm64_norm, *]) (by simp only [Reg.x19, arm64_norm, *])
          (by simp only [Reg.x20, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
          (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x25, arm64_norm, *])
          (by simp only [Reg.x26, arm64_norm, *]) (by simp only [Reg.x27, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)

/-- `spqr::v1::chunked::send_ct::send_ct2_encoder` (`0x5e64c`, 85 instructions) satisfies
    `sendCt2EncoderSpec A` on `tripleRatchetProgAtExt b ext` under `AllocContracts4K`. -/
theorem send_ct2_encoder_ok_4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (henc : EncodeBytesOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A) := by
  have hfn : libsignalSessionCode.fnOff sendCt2EncoderName = 0x5e730 := sendCt2Encoder_fnOff
  exact send_ct2_encoder_ok_core
    (hA.shim_ok_at sendCt2EncoderName
      (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]))
    (hA.alloc_ok_at sendCt2EncoderName
      (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_alloc"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")]))
    (hA.dealloc_ok_at sendCt2EncoderName
      (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_dealloc"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")]))
    (hA.session_memcpy_region_ok_at sendCt2EncoderName
      (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "memcpy"))
      (hookStack := encodeBytesStackX) (by decide) (by decide)
      (by rw [hfn, libsignalSessionCode_fnOff_memcpy]))
    (do_reserve_7_raw_ok_ext_4k hA) henc

/-- `spqr::v1::chunked::send_ct::send_ct2_encoder` (`0x5e64c`, 85 instructions) satisfies
    `sendCt2EncoderSpec A` on `leavesProgAtExt b ext` under `AllocContracts`. -/
theorem send_ct2_encoder_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (henc : EncodeBytesOkExt b A ext) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A) := by
  have hfn : libsignalSessionCode.fnOff sendCt2EncoderName = 0x5e730 := sendCt2Encoder_fnOff
  exact send_ct2_encoder_ok_core
    (hA.shim_ok_at sendCt2EncoderName
      (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]))
    (hA.alloc_ok_at sendCt2EncoderName
      (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_alloc"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")]))
    (hA.dealloc_ok_at sendCt2EncoderName
      (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "__rustc::__rust_dealloc"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")]))
    (subroutine_ok_withStack_of_subroutine_ok
      (hA.session_memcpy_region_ok_at sendCt2EncoderName
        (num% (ls_rel% "spqr::v1::chunked::send_ct::send_ct2_encoder" "memcpy"))
        (by rw [hfn, libsignalSessionCode_fnOff_memcpy]))
      encodeBytesStackX)
    (do_reserve_7_raw_ok_ext hA) henc

/-- Native-stack (`sendCt2EncoderStack = 17456` B) `.inImage img` contract for `send_ct2_encoder`
    under `AllocContracts4K`. -/
theorem send_ct2_encoder_ok_inImage {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext)
    (henc : EncodeBytesOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((sendCt2EncoderSpec A).inImage img) :=
  sub_ok_inImage_of_sub_ok_ax img (send_ct2_encoder_ok_4K hA henc)

/-- `StatesRecvContractsAx.sendCt2Encoder_ok` (Field 10, `35936` B grown stack)
    under `AllocContracts4K`. -/
theorem send_ct2_encoder_ok_ax {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext)
    (henc : EncodeBytesOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((growToCalleeExt sendCt2EncoderStack (sendCt2EncoderSpec A)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax sendCt2EncoderStack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (send_ct2_encoder_ok_inImage hA henc)

end CryptoVerification.SpqrV1.States.Leaves
