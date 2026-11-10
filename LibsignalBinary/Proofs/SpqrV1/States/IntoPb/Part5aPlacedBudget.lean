/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5a Placed: Arm 8 (`States.ekReceivedCt1Sampled`)

Provides `SpqrBoundedEvs` bounds bridges for `<PolyEncoder>::into_pb` and `EkReceivedCt1SampledEnv`,
and verifies Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`, jump table index `8` -> `+1644`)
on Block `334` under `RustCliAllocBudget M` in plain and `withLsCodeLoaded` forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (GF16 PolyEncoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (EkReceivedCt1Sampled)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt polyEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (authenticatorHeap ekReceivedScratchCells epilogueStagingCells
   memRegion_1424_split_epilogue memRegion_ekReceived_scratch_split outWords28
   protoPolynomialEncoderHeap stackAt_encoderIntoPb_eq_allocHook
   statesIntoPbJumpTablePlacedAt statesIntoPbSavedCells statesIntoPbStack
   vecU8CloneTail vecU8Heap)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbAllocEvents
   encoderIntoPbSlotEvents encoderIntoPbSpec encoderIntoPbVecs
   fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (sepWPp_of_states_into_pb_exit_placed statesIntoPbVariantPlacedSpec
   statesIntoPbVariantPlacedSpecOfEnv states_into_pb_epilogue_placed
   states_into_pb_prologue_60_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (StatesIntoPbAllocPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudgetAux
  (ekReceivedCt1Sampled_step_1760_to_2252_wp_placed
   ekReceivedCt1Sampled_step_2252_to_2324_placed
   ekReceivedCt1Sampled_step_2324_to_2340_wp_placed
   ekReceivedCt1Sampled_step_2340_to_1544_placed
   ekReceivedCt1Sampled_step_60_to_1760_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1CloneEvents ct1DeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
  (spqrBoundedEvs_ct1CloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv
   chunkedEkReceivedCt1Sampled_expose ct1CloneAndDropEnv_of_dealloc
   ekReceivedCt1SampledEnv_of_parts ekReceivedScratchCells_entails_memRegions
   fitsEvents_clone_of_ct1CloneAndDropEnv outWords28_entails_ekReceivedCt1Sampled
   stA_ekReceivedCt1Sampled_entails_928)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv
   ekReceivedCt1SampledEnv_of_parts)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudgetAux
  (ekReceivedCt1Sampled_step_60_to_1760_placed
   ekReceivedCt1Sampled_step_1760_to_2252_wp_placed
   ekReceivedCt1Sampled_step_1760_to_2252_placed
   ekReceivedCt1Sampled_step_2252_to_2324_placed
   ekReceivedCt1Sampled_step_2324_to_2340_wp_placed
   ekReceivedCt1Sampled_step_2324_to_2340_placed
   ekReceivedCt1Sampled_step_2340_to_1544_placed)

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. `SpqrBoundedEvs` Bounds Bridges for `<PolyEncoder>::into_pb` & Arm 8 -/

private theorem spqrBoundedEvs_rustAllocEvents_384_8 :
    SpqrBoundedEvs 1 384 (rustAllocEvents 384 8) := by
  have hcond : (8 ≤ 16 ∧ 8 ≤ 384) := ⟨by decide, by decide⟩
  simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, Nat.le_refl 384, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem spqrBoundedEvs_encoderIntoPbSlotEvents (cs : List GF16) {maxReq : Nat}
    (hmax : 2 * cs.length ≤ MallocngMaxAllocSize)
    (hreq : 2 * cs.length ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (encoderIntoPbSlotEvents cs) := by
  unfold encoderIntoPbSlotEvents
  cases cs with
  | nil =>
    exact SpqrBoundedEvs.nil 1 maxReq
  | cons c rest =>
    have h1 : 1 ≤ 2 * (c :: rest).length := by simp only [List.length_cons]; omega
    have hcond : (1 ≤ 16 ∧ 1 ≤ 2 * (c :: rest).length) := ⟨by decide, h1⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      rustAllocEvents, hcond, and_self]
    refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem spqrBoundedEvs_flatMap_encoderSlots {maxReq : Nat} :
    ∀ (xss : List (List GF16)),
      (∀ cs ∈ xss, 2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq) →
      SpqrBoundedEvs xss.length maxReq (xss.flatMap encoderIntoPbSlotEvents)
  | [], _ => SpqrBoundedEvs.nil 0 maxReq
  | cs :: xss, h => by
    simp only [List.flatMap_cons, List.length_cons]
    have hcs := h cs List.mem_cons_self
    have htl := spqrBoundedEvs_flatMap_encoderSlots xss
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h1 := spqrBoundedEvs_encoderIntoPbSlotEvents cs hcs.1 hcs.2
    have happ := SpqrBoundedEvs.append h1 htl
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_of_eq (Nat.max_self maxReq)) happ

theorem encoderIntoPbEnv_imp_spqrBoundedEvs {enc : PolyEncoder}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 2 + (encoderIntoPbVecs enc).length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs enc,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (henv : EncoderIntoPbEnv enc evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with ⟨evs_alloc, evs_free, rfl, rfl, hfree⟩
  have ho : SpqrBoundedEvs 1 maxReq (rustAllocEvents 384 8) :=
    SpqrBoundedEvs.mono (Nat.le_refl 1) h384 spqrBoundedEvs_rustAllocEvents_384_8
  have hsl : SpqrBoundedEvs (encoderIntoPbVecs enc).length maxReq
      ((encoderIntoPbVecs enc).flatMap encoderIntoPbSlotEvents) :=
    spqrBoundedEvs_flatMap_encoderSlots (encoderIntoPbVecs enc) hslots
  have hfr : SpqrBoundedEvs 0 maxReq evs_free :=
    SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree)
  unfold encoderIntoPbAllocEvents
  have h12 := SpqrBoundedEvs.append ho ho
  have h123 := SpqrBoundedEvs.append h12 hsl
  have htot := SpqrBoundedEvs.append h123 hfr
  exact SpqrBoundedEvs.mono (by omega) (by omega) htot

theorem ct1CloneAndDropEnv_imp_spqrBoundedEvs {ct1 : List (BitVec 8)}
    {maxReq : Nat} {evs : List AllocEvent}
    (hct1_max : ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : ct1.length ≤ maxReq)
    (henv : Ct1CloneAndDropEnv ct1 evs) :
    SpqrBoundedEvs 1 maxReq evs := by
  rcases henv with rfl | ⟨evs_cl, evs_fr, rfl, rfl, hfree⟩
  · exact SpqrBoundedEvs.mono (Nat.le_refl 1) hct1_req (spqrBoundedEvs_ct1CloneEvents ct1 hct1_max)
  · have hcl : SpqrBoundedEvs 1 maxReq (ct1CloneEvents ct1) :=
      SpqrBoundedEvs.mono (Nat.le_refl 1) hct1_req (spqrBoundedEvs_ct1CloneEvents ct1 hct1_max)
    have hfr : SpqrBoundedEvs 0 maxReq evs_fr :=
      SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree)
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hcl hfr)

theorem ekReceivedCt1SampledEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 3 + (encoderIntoPbVecs s.sending_ct1).length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (henv : EkReceivedCt1SampledEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with hcd | ⟨evs_cd, evs_enc, rfl, hcd, henc⟩
  · exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl _)
      (ct1CloneAndDropEnv_imp_spqrBoundedEvs hct1_max hct1_req hcd)
  · have h1 := ct1CloneAndDropEnv_imp_spqrBoundedEvs hct1_max hct1_req hcd
    have h2 := encoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hslots henc
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append h1 h2)

/-! ## 2. Relocatable Block-`334` Main Theorems for Arm 8 (`States.ekReceivedCt1Sampled`) -/

/-- Envelope-parametric relocatable Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`,
    jump table index `8` -> `+1644` in Block `334`). -/
theorem states_into_pb_ekReceivedCt1Sampled_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, EkReceivedCt1SampledEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ekReceivedCt1Sampled s) Env) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfits_env⟩, hmem⟩
  have hfits : FitsEnv M lim st (EkReceivedCt1SampledEnv s) := FitsEnv.mono hEnv hfits_env
  have hfits_cd : FitsEnv M lim st (Ct1CloneAndDropEnv s.uc.ct1) := hfits.seq_left
  have hfits_clone : FitsEvents M lim st (ct1CloneEvents s.uc.ct1) :=
    fitsEvents_clone_of_ct1CloneAndDropEnv hfits_cd
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ekReceivedCt1Sampled s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · dsimp only [statesIntoPbJumpTablePlacedAt,
      CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt] at hmem ⊢
    simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_placed st s0 s0 out stA
    (.ekReceivedCt1Sampled s) Env _ R ?_
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
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 10#64) ∗ A.pool lim st s0 ∗
       (statesIntoPbJumpTablePlacedAt ∗
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
        memRegion (stA + 536#64) 392)) by sep_ac_rfl]
  apply SepWP.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 10#64
    (statesIntoPbJumpTablePlacedAt ∗
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
     memRegion (stA + 536#64) 392)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.seq hpro ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx29_1, hx28_1, hx27_1, hx26_1,
    hx20_1, hx19_1, hx8_1, htr1, _hvm1⟩
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
          (stA ↦₆₄ 10#64) ∗ A.pool lim st s1 ∗
          (statesIntoPbJumpTablePlacedAt ∗
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
           memRegion (stA + 536#64) 392) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           (stA ↦₆₄ 10#64) ∗
           statesIntoPbJumpTablePlacedAt ∗
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
  have hstep2 := ekReceivedCt1Sampled_step_60_to_1760_placed (ext := ext) s0 s1 out stA
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
    hsp0_align hlen hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep2) ?_
  intro s2 P2 hpc2 hrun2 ⟨hvm2, hP2, _hacp2, hsp2, hx29_2, hx19_2, hx20_2, hx21_2,
    hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩
  rw [← A.pool_of_vmPreserved hvm2] at hP2
  refine SepWP.weaken_pre hP2 ?_
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  have hstep3 := ekReceivedCt1Sampled_step_1760_to_2252_wp_placed hA s0 s2 st out stA
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
     statesIntoPbJumpTablePlacedAt ∗
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
  have hstep4 := ekReceivedCt1Sampled_step_2252_to_2324_placed hA s0 s3
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
     statesIntoPbJumpTablePlacedAt ∗
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
  have hstep5 := ekReceivedCt1Sampled_step_2324_to_2340_wp_placed henc_raw s0 s4
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
     statesIntoPbJumpTablePlacedAt ∗
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
  have hstep6 := ekReceivedCt1Sampled_step_2340_to_1544_placed (ext := ext) s0 s5 out stA ptr_new
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
     statesIntoPbJumpTablePlacedAt ∗
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
       statesIntoPbJumpTablePlacedAt ∗
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
      A.pool lim (M.stepEvents evs_tot st) s6 ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTablePlacedAt) := by
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
       A.pool lim (M.stepEvents evs_tot st) s6 ∗
       protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hep := states_into_pb_epilogue_placed (ext := ext) A lim (M.stepEvents evs_tot st)
    s0 s6 out
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
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc6 hrun6 hsp6 hx29_6 hx19_6 htr6
  rw [hx22_6, hx21_6] at hep
  refine SepWP.mono (SepWP.weaken_pre hpre_epi hep) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, _hvm_f⟩
  refine ⟨⟨evs_tot, hEnv evs_tot htot_env, ?_⟩, hsp_f, hcs_f, htr_f⟩
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
     statesIntoPbJumpTablePlacedAt ∗
     A.pool lim (M.stepEvents evs_tot st) sf ∗
     stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

/-- Tight `EkReceivedCt1SampledEnv` relocatable `subroutine_ok` for Arm 8 (`States.ekReceivedCt1Sampled`). -/
theorem states_into_pb_ekReceivedCt1Sampled_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F
        (.ekReceivedCt1Sampled s) (EkReceivedCt1SampledEnv s)) :=
  states_into_pb_ekReceivedCt1Sampled_of_env_placed hA henc_raw s (fun _ h => h)

/-- Default `statesIntoPbVariantPlacedSpec` (`SpqrBoundedEvs 64 (2 * |encodeRaw| + 1024)`)
    relocatable `subroutine_ok` for Arm 8 (`States.ekReceivedCt1Sampled`) under explicit
    payload/slot size bounds. -/
theorem states_into_pb_ekReceivedCt1Sampled_of_bounds_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hcnt : 3 + (encoderIntoPbVecs s.sending_ct1).length ≤ 64)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤
      2 * (V1State.encodeRaw (States.ekReceivedCt1Sampled (P := spqrPolyApi) s).into_pb).length + 1024)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
      2 * cs.length ≤ MallocngMaxAllocSize ∧
      2 * cs.length ≤
        2 * (V1State.encodeRaw (States.ekReceivedCt1Sampled (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec M A lim F (.ekReceivedCt1Sampled s)) :=
  states_into_pb_ekReceivedCt1Sampled_of_env_placed hA henc_raw s
    (fun _ => ekReceivedCt1SampledEnv_imp_spqrBoundedEvs hcnt (by omega) hct1_max hct1_req hslots)

theorem states_into_pb_ekReceivedCt1Sampled_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, EkReceivedCt1SampledEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ekReceivedCt1Sampled s) Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ekReceivedCt1Sampled_of_env_placed hA henc_raw s hEnv)

theorem states_into_pb_ekReceivedCt1Sampled_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F
          (.ekReceivedCt1Sampled s) (EkReceivedCt1SampledEnv s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ekReceivedCt1Sampled_env_placed hA henc_raw s)

theorem states_into_pb_ekReceivedCt1Sampled_of_bounds_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hcnt : 3 + (encoderIntoPbVecs s.sending_ct1).length ≤ 64)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤
      2 * (V1State.encodeRaw (States.ekReceivedCt1Sampled (P := spqrPolyApi) s).into_pb).length + 1024)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
      2 * cs.length ≤ MallocngMaxAllocSize ∧
      2 * cs.length ≤
        2 * (V1State.encodeRaw (States.ekReceivedCt1Sampled (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F (.ekReceivedCt1Sampled s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ekReceivedCt1Sampled_of_bounds_placed
      hA henc_raw s hcnt hct1_max hct1_req hslots)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget
