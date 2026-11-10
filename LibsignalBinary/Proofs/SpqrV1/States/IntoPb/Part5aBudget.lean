/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5a
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5a: Arm 8 (`States.ekReceivedCt1Sampled`)

Verifies `states_into_pb_ekReceivedCt1Sampled` (Arm 8, tag `10`, jump table index `8` -> `+1644`)
under `RustCliAllocBudget M`, `BudgetLimits`, and `EkReceivedCt1SampledEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (PolyEncoder States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (EkReceivedCt1Sampled)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  optProtoInnerStateAt optProtoInnerStateSize
)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt polyEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb (
  authenticatorHeap ekReceivedScratchCells epilogueStagingCells
  memRegion_1424_split_epilogue memRegion_ekReceived_scratch_split outWords28
  protoPolynomialEncoderHeap stackAt_encoderIntoPb_eq_allocHook
  statesIntoPbJumpTableAt statesIntoPbName statesIntoPbSavedCells
  statesIntoPbStack vecU8CloneTail vecU8Heap
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (
  EncoderIntoPbAllocEnv EncoderIntoPbEnv EncoderIntoPbOkExt
  fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudgetAux (
  ekReceivedCt1Sampled_step_60_to_1760 ekReceivedCt1Sampled_step_1760_to_2252_wp
  ekReceivedCt1Sampled_step_2252_to_2324 ekReceivedCt1Sampled_step_2324_to_2340_wp
  ekReceivedCt1Sampled_step_2340_to_1544
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (
  ct1CloneEvents ct1DeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux (
  Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv
  chunkedEkReceivedCt1Sampled_expose ct1CloneAndDropEnv_of_dealloc
  ekReceivedCt1SampledEnv_of_parts ekReceivedScratchCells_entails_memRegions
  fitsEvents_clone_of_ct1CloneAndDropEnv outWords28_entails_ekReceivedCt1Sampled
  stA_ekReceivedCt1Sampled_entails_928 statesIntoPbEkReceivedCt1SampledSpec
  statesIntoPbVariantSpecOfEnv states_into_pb_epilogue_vm
  states_into_pb_prologue_60_vm sub_ok_encoderIntoPb_raw
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux (
  Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv
  ekReceivedCt1SampledEnv_of_parts statesIntoPbVariantSpecOfEnv
  statesIntoPbEkReceivedCt1SampledSpec
)
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudgetAux (
  ekReceivedCt1Sampled_step_60_to_1760 ekReceivedCt1Sampled_step_1760_to_2252_wp
  ekReceivedCt1Sampled_step_1760_to_2252 ekReceivedCt1Sampled_step_2252_to_2324
  ekReceivedCt1Sampled_step_2324_to_2340_wp ekReceivedCt1Sampled_step_2324_to_2340
  ekReceivedCt1Sampled_step_2340_to_1544
)

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem sepWPp_of_states_into_pb_exit_budget
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (h : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢
            optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
            memRegion stA chunkedStatesSize ∗
            statesIntoPbJumpTableAt b ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesIntoPbVariantSpecOfEnv M A lim F b stateVal Env).post ((out, stA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpecOfEnv M A lim F b stateVal Env).onPanic ((out, stA), st) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨⟨evs, henv, hPf⟩, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesIntoPbVariantSpecOfEnv]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, henv⟩, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by sep_ac_rfl))) hmem_f⟩

/-- Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`, jump table index `8` -> `+1644`). -/
theorem states_into_pb_ekReceivedCt1Sampled
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (henc : EncoderIntoPbOkExt b M A lim ext)
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbEkReceivedCt1SampledSpec M A lim F b s) := by
  have henc_raw := sub_ok_encoderIntoPb_raw henc
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbEkReceivedCt1SampledSpec, statesIntoPbVariantSpecOfEnv,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align, hfits⟩, hmem⟩
  have hfits_cd : FitsEnv M lim st (Ct1CloneAndDropEnv s.uc.ct1) := hfits.seq_left
  have hfits_clone : FitsEvents M lim st (ct1CloneEvents s.uc.ct1) :=
    fitsEvents_clone_of_ct1CloneAndDropEnv hfits_cd
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ekReceivedCt1Sampled s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_budget st s0 s0 out stA
    (.ekReceivedCt1Sampled s) (EkReceivedCt1SampledEnv s) _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedEkReceivedCt1Sampled_expose A.repAlloc stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro a0
  apply SepWP.exists_elim; intro a1
  apply SepWP.exists_elim; intro a2
  apply SepWP.exists_elim; intro a3
  apply SepWP.exists_elim; intro a4
  apply SepWP.exists_elim; intro a5
  apply SepWP.exists_elim; intro es0
  apply SepWP.exists_elim; intro es1
  apply SepWP.exists_elim; intro es2
  apply SepWP.exists_elim; intro ek0
  apply SepWP.exists_elim; intro ek1
  apply SepWP.exists_elim; intro ek2
  apply SepWP.exists_elim; intro cap_ct1
  apply SepWP.exists_elim; intro ptr_ct1
  rw [show memRegion out optProtoInnerStateSize ∗
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stA ↦₆₄ 10#64) ∗
      polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
      ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
      ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
      vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
      memRegion (stA + 536#64) 392 ∗
      statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 10#64) ∗
       (statesIntoPbJumpTableAt b ∗
        memRegion out optProtoInnerStateSize ∗
        polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
        ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
        ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
        ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
        ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
        vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
        memRegion (stA + 536#64) 392 ∗ A.pool lim st s0)) by sep_ac_rfl]
  apply SepWP.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60_vm s0 out stA 10#64
    (statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392 ∗ A.pool lim st s0)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.seq hpro ?_
  intro s1 P1 hpc1 hrun1 ⟨hvm1, hP1, _hacp1, hsp1, hx29_1, hx28_1, hx27_1, hx26_1,
    hx20_1, hx19_1, hx8_1, htr1⟩
  rw [← A.pool_of_vmPreserved hvm1] at hP1
  refine SepWP.weaken_pre hP1 ?_
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  refine SepWP.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ 10#64) ∗
          (statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
           ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
           ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
           vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
           memRegion (stA + 536#64) 392 ∗ A.pool lim st s1) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           (stA ↦₆₄ 10#64) ∗
           statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
           ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
           ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
           vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
           memRegion (stA + 536#64) 392 ∗ A.pool lim st s1) by sep_ac_rfl]
      exact sepConj_mono_left (Entails.trans h1424 (memRegion_1424_split_epilogue s0.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w8
  apply SepWP.exists_elim; intro w16
  apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w32
  apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w48
  apply SepWP.exists_elim; intro w64
  apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w80
  apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w96
  apply SepWP.exists_elim; intro w104
  apply SepWP.exists_elim; intro w112
  apply SepWP.exists_elim; intro w120
  apply SepWP.exists_elim; intro w128
  apply SepWP.exists_elim; intro w136
  apply SepWP.exists_elim; intro w144
  apply SepWP.exists_elim; intro w152
  apply SepWP.exists_elim; intro w160
  apply SepWP.exists_elim; intro w168
  apply SepWP.exists_elim; intro w176
  apply SepWP.exists_elim; intro w184
  apply SepWP.exists_elim; intro w192
  apply SepWP.exists_elim; intro w200
  apply SepWP.exists_elim; intro w208
  apply SepWP.exists_elim; intro w216
  have hscratch_split :
      ∀ (Rest : SepProp),
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗ Rest ⊢
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        (∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
         ∃∗ t4 : BitVec 64, ∃∗ t5 : BitVec 64, ∃∗ t6 : BitVec 64, ∃∗ t7 : BitVec 64,
         ∃∗ t8 : BitVec 64, ∃∗ t9 : BitVec 64, ∃∗ t10 : BitVec 64, ∃∗ t11 : BitVec 64,
         ∃∗ t12 : BitVec 64, ∃∗ t13 : BitVec 64, ∃∗ t14 : BitVec 64, ∃∗ t15 : BitVec 64,
         ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
         ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
         ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
           ekReceivedScratchCells s0.sp
             t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
             u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
           memRegion (s0.sp - 1232#64) 56 ∗
           memRegion (s0.sp - 1176#64) 696 ∗
           memRegion (s0.sp - 432#64) 128 ∗
           memRegion (s0.sp - 208#64) 112) ∗ Rest := by
    intro Rest
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160) ∗ Rest by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left (memRegion_ekReceived_scratch_split s0.sp))
  refine SepWP.weaken_pre (hscratch_split _) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro t0
  apply SepWP.exists_elim; intro t1
  apply SepWP.exists_elim; intro t2
  apply SepWP.exists_elim; intro t3
  apply SepWP.exists_elim; intro t4
  apply SepWP.exists_elim; intro t5
  apply SepWP.exists_elim; intro t6
  apply SepWP.exists_elim; intro t7
  apply SepWP.exists_elim; intro t8
  apply SepWP.exists_elim; intro t9
  apply SepWP.exists_elim; intro t10
  apply SepWP.exists_elim; intro t11
  apply SepWP.exists_elim; intro t12
  apply SepWP.exists_elim; intro t13
  apply SepWP.exists_elim; intro t14
  apply SepWP.exists_elim; intro t15
  apply SepWP.exists_elim; intro u0
  apply SepWP.exists_elim; intro u1
  apply SepWP.exists_elim; intro u2
  apply SepWP.exists_elim; intro u3
  apply SepWP.exists_elim; intro u4
  apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro v0
  apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v5
  have hstep2 := ekReceivedCt1Sampled_step_60_to_1760 s0 s1 out stA
    a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392 ∗ A.pool lim st s1)
    hb_align hsp0_align hlen hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep2) ?_
  intro s2 P2 hpc2 hrun2 ⟨hvm2, hP2, _hacp2, hsp2, hx29_2, hx19_2, hx20_2, hx21_2,
    hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩
  rw [← A.pool_of_vmPreserved hvm2] at hP2
  refine SepWP.weaken_pre hP2 ?_
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  have hstep3 := ekReceivedCt1Sampled_step_1760_to_2252_wp hA s0 s2 st out stA
    cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     ekReceivedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
       u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hfits_clone hsp0_align hlen hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx23_2 hx24_2
    hx26_2 hx27_2 hx28_2 htr2
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep3) ?_
  intro s3 P3 hpc3 hrun3 ⟨ptr_new, hP3, hsp3, hx29_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, htr3⟩
  refine SepWP.weaken_pre hP3 ?_
  have hstep4 := ekReceivedCt1Sampled_step_2252_to_2324 hA s0 s3
    (M.stepEvents (ct1CloneEvents s.uc.ct1) st)
    out stA cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx26_3 hx27_3 hx28_3 htr3
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep4) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, _hacp4, hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx22_4,
    hx27_4, hx28_4, htr4⟩
  let evs_cd := ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1
  have hst_cd :
      M.stepEvents (ct1DeallocEvents cap_ct1) (M.stepEvents (ct1CloneEvents s.uc.ct1) st) =
      M.stepEvents evs_cd st :=
    (M.stepEvents_append (ct1CloneEvents s.uc.ct1) (ct1DeallocEvents cap_ct1) st).symm
  have hcd : Ct1CloneAndDropEnv s.uc.ct1 evs_cd :=
    ct1CloneAndDropEnv_of_dealloc s.uc.ct1 cap_ct1
  have hfits_enc : FitsEnv M lim (M.stepEvents evs_cd st) (EncoderIntoPbAllocEnv s.sending_ct1) :=
    fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv (hfits.seq_right hcd)
  rw [hst_cd] at hP4
  refine SepWP.weaken_pre hP4 ?_
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  have hstep5 := ekReceivedCt1Sampled_step_2324_to_2340_wp henc_raw s0 s4
    (M.stepEvents evs_cd st) out stA ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.sending_ct1
    (((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     ekReceivedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
       es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hfits_enc hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hx20_4 hx21_4 hx22_4 hx27_4 hx28_4 htr4
  refine SepWP.seq
    (SepWP.weaken_pre (by rw [← hrecomb_stack]; exact Entails.of_eq (by sep_ac_rfl)) hstep5) ?_
  intro s5 P5 hpc5 hrun5 ⟨evs_enc, e0, e1, e2, e3, e4, e5, e6, henc_env, _hacp5, hP5,
    hsp5, hx29_5, hx19_5, hx20_5, hx21_5, hx22_5, hx27_5, hx28_5, htr5⟩
  let evs_tot := evs_cd ++ evs_enc
  have hst_tot :
      M.stepEvents evs_enc (M.stepEvents evs_cd st) = M.stepEvents evs_tot st :=
    (M.stepEvents_append evs_cd evs_enc st).symm
  have htot_env : EkReceivedCt1SampledEnv s evs_tot :=
    ekReceivedCt1SampledEnv_of_parts hcd henc_env
  rw [hst_tot] at hP5
  refine SepWP.weaken_pre hP5 ?_
  have hstep6 := ekReceivedCt1Sampled_step_2340_to_1544 s0 s5 out stA ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    e0 e1 e2 e3 e4 e5 e6
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     memRegion (stA + 8#64) polyEncoderSize ∗
     A.pool lim (M.stepEvents evs_tot st) s5 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5 hx27_5 hx28_5 htr5
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep6) ?_
  intro s6 P6 hpc6 hrun6 ⟨hvm6, hP6, _hacp6, hsp6, hx29_6, hx19_6, hx21_6, hx22_6, htr6⟩
  rw [← A.pool_of_vmPreserved hvm6] at hP6
  refine SepWP.weaken_pre hP6 ?_
  have hscratch := ekReceivedScratchCells_entails_memRegions s0.sp
    es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5 s.uc.epoch
    es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
  have hstA := stA_ekReceivedCt1Sampled_entails_928 stA
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
  have hpre_epi :
      ekReceivedScratchCells s0.sp
        es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
        a0 a1 a2 a3 a4 a5 s.uc.epoch
        es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
       ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
       ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
       ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
      epilogueStagingCells s0.sp
        es0 es1 es2 ek0 ek1 ek2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        w192 w200 w208 w216 ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       memRegion (stA + 8#64) polyEncoderSize ∗
       A.pool lim (M.stepEvents evs_tot st) s6 ∗
       stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 10#64) ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
       memRegion (stA + 536#64) 392) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        es0 es1 es2 ek0 ek1 ek2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        w192 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b ∗ A.pool lim (M.stepEvents evs_tot st) s6) := by
    refine Entails.trans (Entails.of_eq (show _ =
      (ekReceivedScratchCells s0.sp
         es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
         a0 a1 a2 a3 a4 a5 s.uc.epoch
         es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112) ∗
      ((stA ↦₆₄ 10#64) ∗
       memRegion (stA + 8#64) polyEncoderSize ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (stA + 536#64) 392) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         es0 es1 es2 ek0 ek1 ek2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch e0 e1 e2 e3 e4 e5 e6
         w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTableAt b ∗ A.pool lim (M.stepEvents evs_tot st) s6) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hep := states_into_pb_epilogue_vm s0 s6 out
    es0 es1 es2 ek0 ek1 ek2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch e0 e1 e2 e3 e4 e5 e6
    w192 w200 w208 w216
    (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool lim (M.stepEvents evs_tot st) s6)
    hsp0_align hpc6 hrun6 hsp6 hx29_6 hx19_6 htr6
  rw [hx22_6, hx21_6] at hep
  refine SepWP.mono (SepWP.weaken_pre hpre_epi hep) ?_
  intro sf Pf _ _ ⟨hvm_f, hPf, _hacp_f, hsp_f, hcs_f, htr_f⟩
  refine ⟨⟨evs_tot, htot_env, ?_⟩, hsp_f, hcs_f, htr_f⟩
  rw [A.pool_of_vmPreserved hvm_f]
  refine Entails.trans hPf ?_
  have hout := outWords28_entails_ekReceivedCt1Sampled A.repAlloc out
    es0 es1 es2 ek0 ek1 ek2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    w192 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       0x8000000000000008#64
       es0 es1 es2 ek0 ek1 ek2
       (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
       a0 a1 a2 a3 a4 a5 s.uc.epoch
       e0 e1 e2 e3 e4 e5 e6
       w192 w200 w208 w216 ∗
     protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗
     A.pool lim (M.stepEvents evs_tot st) s6 ∗
     stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudget
