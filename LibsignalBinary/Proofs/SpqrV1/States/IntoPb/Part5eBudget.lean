/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5e
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5e: Arm 7 (`States.ct1Sampled`)

Verifies Arm 7 (`States.ct1Sampled`, `PolyEncoder` tag `0` or `1`, jump table index `7`,
`+0 -> +60 -> +828 -> +1712 -> +2028 -> +2100 -> +2116 -> +2128 -> +1544 -> ret`) under
`RustCliAllocBudget M`, `BudgetLimits`, and `Ct1SampledEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   ekReceivedScratchCells epilogueStagingCells memRegion_1424_split_epilogue
   memRegion_ekReceived_scratch_split outWords28 protoPolynomialDecoderHeap
   protoPolynomialEncoderHeap stackAt_encoderIntoPb_eq_allocHook
   statesIntoPbJumpTableAt statesIntoPbName statesIntoPbSavedCells
   statesIntoPbStack vecU8CloneTail vecU8Heap)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv DecoderIntoPbOkExt
   fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv EncoderIntoPbOkExt
   fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbVariantSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
  (sepWPp_of_states_into_pb_exit_of_env states_into_pb_epilogue
   states_into_pb_prologue_60 sub_ok_decoderIntoPb_raw sub_ok_encoderIntoPb_raw)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1CloneEvents ct1DeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudget
  (ct1Sampled_step_60_to_1712 ct1Sampled_step_1712_to_2028_wp
   ct1Sampled_step_2028_to_2100 ct1Sampled_step_2100_to_2116_wp
   ct1Sampled_step_2116_to_2128_wp ct1Sampled_step_2128_to_1544)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (Ct1CloneAndDropEnv Ct1SampledEnv chunkedCt1Sampled_expose
   ct1CloneAndDropEnv_of_dealloc ct1SampledEnv_of_parts
   ct1SampledScratchCells_entails_memRegions fitsEvents_clone_of_ct1CloneAndDropEnv
   outWords28_entails_ct1Sampled polyEncoderAt_eq_tag_tail polyEncoderTag
   polyEncoderTailAt stA_ct1Sampled_entails_928)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (Ct1SampledEnv ct1SampledEnv_of_parts)

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

abbrev statesIntoPbCt1SampledSpec
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64)
    (s : Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantSpecOfEnv M A lim F b (.ct1Sampled s) (Ct1SampledEnv s)

set_option maxHeartbeats 800000 in
/-- Envelope-parametric `subroutine_ok` for `<States>::into_pb` on `.ct1Sampled s`
    (Arm 7, `PolyEncoder` tag `0` or `1`, jump table index `7` -> `+828`). -/
theorem states_into_pb_ct1Sampled_of_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : AllocContractsBudget b M A lim ext)
    (henc : EncoderIntoPbOkExt b M A lim ext)
    (hdec : DecoderIntoPbOkExt b M A lim ext)
    (s : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct1SampledEnv s evs → Env evs) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.ct1Sampled s) Env) := by
  have henc_raw := sub_ok_encoderIntoPb_raw henc
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align, hfits_outer⟩, hmem⟩
  have hfits_ct1 : FitsEnv M lim st (Ct1SampledEnv s) :=
    FitsEnv.mono hEnv hfits_outer
  have hfits_cd : FitsEnv M lim st (Ct1CloneAndDropEnv s.uc.ct1) :=
    hfits_ct1.seq_left
  have hfits_clone : FitsEvents M lim st (ct1CloneEvents s.uc.ct1) :=
    fitsEvents_clone_of_ct1CloneAndDropEnv hfits_cd
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ct1Sampled s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_of_env st s0 s0 out stA (.ct1Sampled s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedCt1Sampled_expose A.repAlloc stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro a0
  apply SepWP.exists_elim; intro a1
  apply SepWP.exists_elim; intro a2
  apply SepWP.exists_elim; intro a3
  apply SepWP.exists_elim; intro a4
  apply SepWP.exists_elim; intro a5
  apply SepWP.exists_elim; intro hdr0
  apply SepWP.exists_elim; intro hdr1
  apply SepWP.exists_elim; intro hdr2
  apply SepWP.exists_elim; intro es0
  apply SepWP.exists_elim; intro es1
  apply SepWP.exists_elim; intro es2
  apply SepWP.exists_elim; intro cap_ct1
  apply SepWP.exists_elim; intro ptr_ct1
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
    (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗
     A.pool lim st s0 ∗
     (statesIntoPbJumpTableAt b ∗
      memRegion out optProtoInnerStateSize ∗
      polyEncoderTailAt A.repAlloc stA s.sending_ct1 ∗
      ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
      ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
      ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
      ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
      ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)) by
    dsimp only [authenticatorHeap, vecU8Heap, vecU8CloneTail]
    sep_ac_rfl)) ?_
  apply SepWP.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60 A lim st s0 out stA (polyEncoderTag s.sending_ct1)
    (statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderTailAt A.repAlloc stA s.sending_ct1 ∗
     ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)
    hsp0_align hpc hrun hx8 hx0
  refine seq_clean_wp hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  have henc_rejoin :
      (stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗ polyEncoderTailAt A.repAlloc stA s.sending_ct1 =
      polyEncoderAt A.repAlloc stA s.sending_ct1 :=
    (polyEncoderAt_eq_tag_tail A.repAlloc stA s.sending_ct1).symm
  refine SepWP.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗
          A.pool lim st s1 ∗
          (statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderTailAt A.repAlloc stA s.sending_ct1 ∗
           ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
           ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
           ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
           ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
           ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
           polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           ((stA ↦₆₄ polyEncoderTag s.sending_ct1) ∗ polyEncoderTailAt A.repAlloc stA s.sending_ct1) ∗
           statesIntoPbJumpTableAt b ∗
           memRegion out optProtoInnerStateSize ∗
           ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
           ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
           ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
           ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
           ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
           polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗ A.pool lim st s1) by
        dsimp only [authenticatorHeap, vecU8Heap, vecU8CloneTail]
        sep_ac_rfl,
        henc_rejoin]
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
  rw [ProofLib.memRegion_split' (b := s0.sp - 1176#64) (n := 40) (k := 656)
        (b' := s0.sp - 1136#64) rfl (by bv_omega) (by decide)]
  have hstep1b_vm := ct1Sampled_step_60_to_1712 s0 s1 out stA s.sending_ct1
    a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (A.pool lim st s1 ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 40 ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc stA s.sending_ct1 ∗
     polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)
    hb_align hsp0_align hlen hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  have hstep1b := SepWP.mono
    (post' := fun s2 P2 =>
      (P2 ⊢
        statesIntoPbJumpTableAt b ∗
        ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
        ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
        ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
        ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
        ekReceivedScratchCells s0.sp
          a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
          u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
        (A.pool lim st s2 ∗
         memRegion (s0.sp - 1232#64) 56 ∗
         memRegion (s0.sp - 1176#64) 40 ∗
         memRegion (s0.sp - 1136#64) 656 ∗
         memRegion (s0.sp - 432#64) 128 ∗
         memRegion (s0.sp - 208#64) 112 ∗
         stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
         epilogueStagingCells s0.sp
           w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
           w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
         statesIntoPbSavedCells s0 ∗
         memRegion out optProtoInnerStateSize ∗
         polyEncoderAt A.repAlloc stA s.sending_ct1 ∗
         polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
         ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
         ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
         (ptr_ct1 ↦ₛ s.uc.ct1) ∗
         vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
         vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)) ∧
      (s2.sp = s0.sp - 1520#64 ∧
       s2.readReg64 .x29 = s0.sp - 96#64 ∧
       s2.readReg64 .x19 = out ∧
       s2.readReg64 .x20 = stA ∧
       s2.readReg64 .x22 = BitVec.ofNat 64 s.uc.ct1.length ∧
       s2.readReg64 .x23 = cap_ct1 ∧
       s2.readReg64 .x24 = ptr_ct1 ∧
       s2.readReg64 .x26 = s0.sp - 480#64 ∧
       s2.readReg64 .x27 = s0.sp - 1360#64 ∧
       s2.readReg64 .x28 = s.uc.epoch ∧
       TraceCalleeSaved s2 s0))
    hstep1b_vm
    fun s2 P2 _ _ ⟨hvm2, hP2, _hacp2, hregs2⟩ =>
      ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs2⟩
  refine SepWP.weaken_pre
    (Entails.of_eq (by dsimp only [authenticatorHeap, vecU8Heap, vecU8CloneTail]; sep_ac_rfl))
    (seq_clean_wp hstep1b fun s2 hpc2 hrun2
      ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩ => ?_)
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  have hstep2 := ct1Sampled_step_1712_to_2028_wp hA s0 s2 st out stA cap_ct1 ptr_ct1
    s.uc.epoch s.uc.ct1
    (((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     ekReceivedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
       u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 40 ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc stA s.sending_ct1 ∗
     polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)
    hfits_clone hsp0_align hlen hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2
    hx26_2 hx27_2 hx28_2 htr2
  refine SepWP.weaken_pre
    (Entails.of_eq (by dsimp only [authenticatorHeap, vecU8Heap, vecU8CloneTail]; sep_ac_rfl))
    (SepWP.seq hstep2 fun s3 _P3 hpc3 hrun3
      ⟨ptr_new, hP3, hsp3, hx29_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
       hx26_3, hx27_3, hx28_3, htr3⟩ =>
      SepWP.weaken_pre hP3 ?_)
  have hstep3 := ct1Sampled_step_2028_to_2100 hA s0 s3
    (M.stepEvents (ct1CloneEvents s.uc.ct1) st) out stA
    cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 40 ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc stA s.sending_ct1 ∗
     polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx26_3 hx27_3 hx28_3 htr3
  refine SepWP.weaken_pre
    (Entails.of_eq (by dsimp only [authenticatorHeap, vecU8Heap, vecCapPtrDealloc]; sep_ac_rfl))
    (seq_clean_wp hstep3 fun s4 hpc4 hrun4
      ⟨_hacp4, hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx22_4, hx27_4, hx28_4, htr4⟩ => ?_)
  let evs_cd : List AllocEvent := ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1
  have hcd_env : Ct1CloneAndDropEnv s.uc.ct1 evs_cd :=
    ct1CloneAndDropEnv_of_dealloc s.uc.ct1 cap_ct1
  have hstep_cd : M.stepEvents (ct1DeallocEvents cap_ct1)
      (M.stepEvents (ct1CloneEvents s.uc.ct1) st) = M.stepEvents evs_cd st :=
    (M.stepEvents_append (ct1CloneEvents s.uc.ct1) (ct1DeallocEvents cap_ct1) st).symm
  rw [hstep_cd]
  have hfits_ed : FitsEnv M lim (M.stepEvents evs_cd st)
      (SeqEnv (EncoderIntoPbEnv s.sending_ct1) (DecoderIntoPbEnv s.receiving_ek)) :=
    hfits_ct1.seq_right hcd_env
  have hfits_enc : FitsEnv M lim (M.stepEvents evs_cd st) (EncoderIntoPbAllocEnv s.sending_ct1) :=
    fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv hfits_ed.seq_left
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  have hstep4 := ct1Sampled_step_2100_to_2116_wp henc_raw s0 s4 (M.stepEvents evs_cd st)
    out stA ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.sending_ct1
    (((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     ekReceivedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
       hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1176#64) 40 ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     polyDecoderAt A.repAlloc (stA + 528#64) s.receiving_ek ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)
    hfits_enc hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hx20_4 hx21_4 hx22_4 hx27_4 hx28_4 htr4
  refine SepWP.weaken_pre
    (by rw [← hrecomb_stack]; exact Entails.of_eq (by dsimp only [authenticatorHeap, vecU8Heap]; sep_ac_rfl))
    (SepWP.seq hstep4 fun s5 _P5 hpc5 hrun5
      ⟨evs_enc, e0, e1, e2, e3, e4, e5, e6, henv_enc, _hacp5, hP5,
       hsp5, hx29_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx27_5, hx28_5, htr5⟩ =>
      SepWP.weaken_pre hP5 ?_)
  have hfits_dec : FitsEnv M lim (M.stepEvents evs_enc (M.stepEvents evs_cd st))
      (DecoderIntoPbAllocEnv s.receiving_ek) :=
    fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv (hfits_ed.seq_right henv_enc)
  have hstep5 := ct1Sampled_step_2116_to_2128_wp hdec_raw s0 s5
    (M.stepEvents evs_enc (M.stepEvents evs_cd st))
    out stA ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.receiving_ek
    ((((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
      ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
      ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
      ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
     protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     memRegion stA polyEncoderSize ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     ekReceivedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
       hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)
    hfits_dec hsp0_align hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5
    hx23_5 hx27_5 hx28_5 htr5
  refine SepWP.weaken_pre
    (Entails.of_eq (by dsimp only [authenticatorHeap, vecU8Heap]; sep_ac_rfl))
    (SepWP.seq hstep5 fun s6 _P6 hpc6 hrun6
      ⟨evs_dec, d0, d1, d2, d3, d4, henv_dec, _hacp6, hP6,
       hsp6, hx29_6, hx19_6, hx21_6, hx22_6, hx27_6, hx28_6, htr6⟩ =>
      SepWP.weaken_pre hP6 ?_)
  let evs_tot : List AllocEvent := evs_cd ++ (evs_enc ++ evs_dec)
  have htot_env : Ct1SampledEnv s evs_tot :=
    ct1SampledEnv_of_parts hcd_env henv_enc henv_dec
  have hstep_tot :
      M.stepEvents evs_dec (M.stepEvents evs_enc (M.stepEvents evs_cd st)) =
      M.stepEvents evs_tot st := by
    dsimp only [evs_tot]
    rw [M.stepEvents_append evs_cd (evs_enc ++ evs_dec) st,
        M.stepEvents_append evs_enc evs_dec (M.stepEvents evs_cd st)]
  rw [hstep_tot]
  have hstep6_vm := ct1Sampled_step_2128_to_1544 s0 s6 out ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    e0 e1 e2 e3 e4 e5 e6
    d0 d1 d2 d3 d4
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (A.pool lim (M.stepEvents evs_tot st) s6 ∗
     protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     memRegion (stA + 528#64) polyDecoderSize ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     memRegion stA polyEncoderSize ∗
     ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
     ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
     ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
     ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1136#64) 656 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     statesIntoPbJumpTableAt b ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)
    hsp0_align hpc6 hrun6 hsp6 hx29_6 hx19_6 hx21_6 hx22_6 hx27_6 hx28_6 htr6
  have hstep6 := SepWP.mono
    (post' := fun s7 P7 =>
      (P7 ⊢
        ekReceivedScratchCells s0.sp
          hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) t7
          (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
          hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
        (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
         ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
         ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
         ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
        (((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
         ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
         ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
        epilogueStagingCells s0.sp
          hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
          (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
          s.uc.epoch e0 e1 e2 e3 e4 e5 e6
          d0 d1 d2 d3 d4 ∗
        (A.pool lim (M.stepEvents evs_tot st) s7 ∗
         protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
         memRegion (stA + 528#64) polyDecoderSize ∗
         stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
         protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
         memRegion stA polyEncoderSize ∗
         ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
         ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
         vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
           (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
         ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
         ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
         ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
         ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
         ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
         memRegion (s0.sp - 1136#64) 656 ∗
         memRegion (s0.sp - 432#64) 128 ∗
         memRegion (s0.sp - 208#64) 112 ∗
         statesIntoPbSavedCells s0 ∗
         statesIntoPbJumpTableAt b ∗
         memRegion out optProtoInnerStateSize ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
         vecU8Heap A.repAlloc es0 es1 es2 s.uc.es)) ∧
      (s7.sp = s0.sp - 1520#64 ∧
       s7.readReg64 .x29 = s0.sp - 96#64 ∧
       s7.readReg64 .x19 = out ∧
       s7.readReg64 .x21 = ptr_new ∧
       s7.readReg64 .x22 = hdr0 ∧
       TraceCalleeSaved s7 s0))
    hstep6_vm
    fun s7 P7 _ _ ⟨hvm7, hP7, _hacp7, hregs7⟩ =>
      ⟨by rw [A.pool_of_vmPreserved hvm7]; exact hP7, hregs7⟩
  refine SepWP.weaken_pre
    (Entails.of_eq (by dsimp only [authenticatorHeap, vecU8Heap]; sep_ac_rfl))
    (seq_clean_wp hstep6 fun s7 hpc7 hrun7 ⟨hsp7, hx29_7, hx19_7, hx21_7, hx22_7, htr7⟩ => ?_)
  have hscratch := ct1SampledScratchCells_entails_memRegions s0.sp
    hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) t7
    (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
    hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    d0 d1 d2 d3 d4
  have hstA := stA_ct1Sampled_entails_928 stA
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
  have hpre_epi :
      ekReceivedScratchCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) t7
        (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
        hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
       ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
       ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
       ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
      (((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
       ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
       ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
      epilogueStagingCells s0.sp
        hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
        (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        d0 d1 d2 d3 d4 ∗
      (A.pool lim (M.stepEvents evs_tot st) s7 ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       memRegion (stA + 528#64) polyDecoderSize ∗
       stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       memRegion stA polyEncoderSize ∗
       ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
       ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
       ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
       ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1136#64) 656 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       statesIntoPbSavedCells s0 ∗
       statesIntoPbJumpTableAt b ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
        (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        d0 d1 d2 d3 d4 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      A.pool lim (M.stepEvents evs_tot st) s7 ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b) := by
    refine Entails.trans (Entails.of_eq (show _ =
      (ekReceivedScratchCells s0.sp
         hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) t7
         (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       (((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
        ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
        ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
       memRegion (s0.sp - 1136#64) 656 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112) ∗
      (memRegion stA polyEncoderSize ∗
       ((stA + 400#64) ↦₆₄ a0) ∗ ((stA + 408#64) ↦₆₄ a1) ∗ ((stA + 416#64) ↦₆₄ a2) ∗
       ((stA + 424#64) ↦₆₄ a3) ∗ ((stA + 432#64) ↦₆₄ a4) ∗ ((stA + 440#64) ↦₆₄ a5) ∗
       ((stA + 448#64) ↦₆₄ hdr0) ∗ ((stA + 456#64) ↦₆₄ hdr1) ∗ ((stA + 464#64) ↦₆₄ hdr2) ∗
       ((stA + 472#64) ↦₆₄ es0) ∗ ((stA + 480#64) ↦₆₄ es1) ∗ ((stA + 488#64) ↦₆₄ es2) ∗
       ((stA + 496#64) ↦₆₄ cap_ct1) ∗ ((stA + 504#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 512#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 520#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (stA + 528#64) polyDecoderSize) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
         (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch e0 e1 e2 e3 e4 e5 e6
         d0 d1 d2 d3 d4 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       A.pool lim (M.stepEvents evs_tot st) s7 ∗
       protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTableAt b) by dsimp only [authenticatorHeap, vecU8Heap]; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by dsimp only [authenticatorHeap, vecU8Heap]; sep_ac_rfl)
  have hep := states_into_pb_epilogue A lim (M.stepEvents evs_tot st) s0 s7 out
    hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length)
    (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch e0 e1 e2 e3 e4 e5 e6
    d0 d1 d2 d3 d4
    (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b)
    hsp0_align hpc7 hrun7 hsp7 hx29_7 hx19_7 htr7
  rw [hx22_7, hx21_7] at hep
  refine SepWP.weaken_pre hpre_epi
    (SepWP.mono hep fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret, _⟩ =>
      ⟨⟨evs_tot, hEnv evs_tot htot_env, ?_⟩, hsp_ret, hcs_ret, htr_ret⟩)
  refine Entails.trans hPf ?_
  have hout := outWords28_entails_ct1Sampled A.repAlloc out
    hdr0 hdr1 hdr2 es0 es1 es2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    d0 d1 d2 d3 d4 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       hdr0 hdr1 hdr2 es0 es1 es2 (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
       e0 e1 e2 e3 e4 e5 e6
       d0 d1 d2 d3 d4 ∗
     protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗
     A.pool lim (M.stepEvents evs_tot st) s_ret ∗
     stackAt s0.sp statesIntoPbStack) by dsimp only [authenticatorHeap, vecU8Heap]; sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq rfl)

/-- Verifies `<States>::into_pb` on `.ct1Sampled s`
    (Arm 7, `PolyEncoder` tag `0` or `1`, jump table index `7` -> `+828`). -/
theorem states_into_pb_ct1Sampled
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (henc : EncoderIntoPbOkExt b M A lim ext)
    (hdec : DecoderIntoPbOkExt b M A lim ext)
    (s : Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbCt1SampledSpec M A lim F b s) :=
  states_into_pb_ct1Sampled_of_env hA henc hdec s (fun _ h => h)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eBudget
