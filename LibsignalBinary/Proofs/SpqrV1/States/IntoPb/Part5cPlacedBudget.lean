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
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5c Placed: Arm 9 (`States.ct1Acknowledged`)

Provides relocatable `[LibsignalPlacement]` `call_memcpy_keep_relocate` helpers over
`sessionMemcpyRegionBudgetSpec` and verifies Arm 9 (`States.ct1Acknowledged`, tag `11`,
jump table index `9` -> `+360`) on Block `334` under `RustCliAllocBudget M` in plain and
`withLsCodeLoaded` forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement libsignalSessionCode lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolyDecoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Acknowledged)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize protoPolynomialDecoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (Relocatable TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   chunkedCt1Acknowledged_expose ct1AcknowledgedScratchCells
   ct1AcknowledgedScratchCells_entails_memRegions epilogueStagingCells
   memRegion_1424_split_epilogue memRegion_ct1Acknowledged_scratch_split
   memcpy_keep_relocate_recombine memcpy_keep_relocate_split outWords28
   outWords28_entails_ct1Acknowledged protoPolynomialDecoderHeap relocatedHeap
   stA_ct1Acknowledged_entails_928 stackAt_encoderIntoPb_eq_allocHook
   statesIntoPbJumpTablePlacedAt statesIntoPbSavedCells statesIntoPbStack
   vecU8CloneTail vecU8Heap)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open CryptoVerification.SpqrV1.States.IntoPb.Relocatable
  (words12 words4_polyDecoderAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (sepWPp_of_states_into_pb_exit_placed statesIntoPbVariantPlacedSpec
   statesIntoPbVariantPlacedSpecOfEnv states_into_pb_epilogue_placed
   states_into_pb_prologue_60_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (call_decoderIntoPb_expose_wp_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (StatesIntoPbAllocPlacedBudget sessionMemcpyRegion_ok_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1CloneEvents ct1DeallocEvents freeOnlyEvs_ct1DeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bPlacedBudget
  (ct1Acknowledged_step_1812_to_1900_placed
   ct1Acknowledged_step_1904_to_1544_placed
   ct1Acknowledged_step_376_to_424_placed
   ct1Acknowledged_step_424_to_1812_wp_placed
   ct1Acknowledged_step_60_to_372_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
  (Ct1AcknowledgedEnv ct1AcknowledgedEnv_imp_spqrBoundedEvs
   fitsEnv_decoder_of_ct1AcknowledgedEnv
   fitsEvents_ct1Clone_of_ct1AcknowledgedEnv
   nonFreeCount_ct1AcknowledgedEnv_le spqrBoundedEvs_ct1CloneEvents
   spqrBoundedEvs_decoderIntoPbSlotEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
  (Ct1AcknowledgedEnv fitsEvents_ct1Clone_of_ct1AcknowledgedEnv
   fitsEnv_decoder_of_ct1AcknowledgedEnv spqrBoundedEvs_ct1CloneEvents
   spqrBoundedEvs_decoderIntoPbSlotEvents nonFreeCount_ct1AcknowledgedEnv_le
   ct1AcknowledgedEnv_imp_spqrBoundedEvs)

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

private theorem seq_vm_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## 1. Relocatable `call_memcpy_keep_relocate` Helpers -/

/-- Total-correctness (`SepWP`) relocatable call helper for `lsρ "memcpy"`
    (`sessionMemcpyRegionBudgetSpec`), keeping `F src` (`szKeep` bytes) at `src`, relocating
    `G (src + off)` (`szReloc` bytes) to `dst + off`, and transporting `A.pool lim st` via
    `VmPreserved`. -/
theorem call_memcpy_keep_relocate_wp_placed [LibsignalPlacement]
    {M : AllocCostModel} {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {szKeep szReloc szTotal : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 szKeep)
    (hsum : szKeep + szReloc = szTotal)
    (hF : Relocatable szKeep F)
    (hG : Relocatable szReloc G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = lsρ "memcpy")
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = szTotal)
    (hsplit : P = (memRegion dst szTotal ∗ (F src ∗ G (src + off)) ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      VmPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc sf
        ((((memRegion dst szKeep ∗ G (dst + off)) ∗
           (F src ∗ memRegion (src + off) szReloc)) ∗ A.pool lim st sf) ∗ Frame)
        post) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc s P post := by
  have hpre_split :
      P ⊢ ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = szKeep ∧ bs2.length = szReloc ∧ (bs1 ++ bs2).length = szTotal⌝ ∗
        ((memRegion dst szTotal ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
         (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ A.pool lim st s ∗ Frame)) := by
    rw [hsplit]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (memcpy_keep_relocate_split hoff hsum hF hG dst src)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs1
    apply Entails.sepExists_elim; intro bs2
    refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre_split ?_
  refine SepWP.exists_elim fun bs1 => SepWP.exists_elim fun bs2 => ?_
  refine SepWP.pure_elim fun ⟨hlen1, hlen2, hlen12⟩ => ?_
  refine SepWP.call_subroutine_frame hmemcpy_raw (x := (dst, src, bs1 ++ bs2))
    (F := relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen12]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜VmPreserved s sf⌝ ∗ ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s.trace⌝ ∗
      (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
        relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
       A.pool lim st s ∗ Frame) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun hvm => SepWP.pure_elim fun ⟨_hx0_sf, htr_sf⟩ => ?_
    rw [← A.pool_transport lim st s sf hvm]
    have hrec := memcpy_keep_relocate_recombine (F := F) (G := G) hoff hlen1 hlen2 dst src
    refine SepWP.weaken_pre (Entails.trans (sepConj_mono_left hrec) (Entails.of_eq (show _ =
      ((((memRegion dst szKeep ∗ G (dst + off)) ∗
         (F src ∗ memRegion (src + off) szReloc)) ∗ A.pool lim st sf) ∗ Frame) by sep_ac_rfl))) ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hvm
      ⟨htr_sf.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩
  · intro _ _ _ ho
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

theorem call_memcpy_keep_relocate_placed [LibsignalPlacement]
    {M : AllocCostModel} {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {szKeep szReloc szTotal : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 szKeep)
    (hsum : szKeep + szReloc = szTotal)
    (hF : Relocatable szKeep F)
    (hG : Relocatable szReloc G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsρ "memcpy")
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = szTotal)
    (hsplit : P = (memRegion dst szTotal ∗ (F src ∗ G (src + off)) ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      VmPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        ((((memRegion dst szKeep ∗ G (dst + off)) ∗
           (F src ∗ memRegion (src + off) szReloc)) ∗ A.pool lim st sf) ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q Qp := by
  refine SepWPp.seq_frozen (mid := ret_pc) (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  refine call_memcpy_keep_relocate_wp_placed hmemcpy_raw A lim st hoff hsum hF hG dst src
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hsplit ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf hvm_sf htr_sf
  exact SepWP.done hpc_sf hrun_sf fun _ =>
    hnext sf hpc_sf hrun_sf hsp_sf hcs_sf hvm_sf htr_sf

/-! ## 2. Arm 9 (`States.ct1Acknowledged`, tag `11`) Relocatable Main Theorems -/

set_option maxHeartbeats 800000 in
/-- Envelope-parametric relocatable `subroutine_ok` for `<States>::into_pb` (Block `334`) on Arm 9
    (`States.ct1Acknowledged`, tag `11`, jump table index `9` -> `+360`,
    `+0 -> +60 -> +360 -> +376 -> +424 -> +1812 -> +1884 -> +1904 -> +1544 -> ret`),
    valid for any `Env` containing `Ct1AcknowledgedEnv s`. -/
theorem states_into_pb_ct1Acknowledged_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct1AcknowledgedEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct1Acknowledged s) Env) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfit⟩, hmem⟩
  have hfit_ct1 : FitsEnv M lim st (Ct1AcknowledgedEnv s) := FitsEnv.mono hEnv hfit
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ct1Acknowledged s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · dsimp only [statesIntoPbJumpTablePlacedAt,
      CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt] at hmem ⊢
    simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_placed st s0 s0 out stA (.ct1Acknowledged s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedCt1Acknowledged_expose A.repAlloc stA s))) ?_
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
  have hfits_clone : FitsEvents M lim st (ct1CloneEvents s.uc.ct1) :=
    fitsEvents_ct1Clone_of_ct1AcknowledgedEnv cap_ct1 hfit_ct1
  have hfit_dec : FitsEnv M lim
      (M.stepEvents (ct1DeallocEvents cap_ct1) (M.stepEvents (ct1CloneEvents s.uc.ct1) st))
      (DecoderIntoPbAllocEnv s.receiving_ek) :=
    fitsEnv_decoder_of_ct1AcknowledgedEnv cap_ct1 hfit_ct1
  rw [show memRegion out optProtoInnerStateSize ∗
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stA ↦₆₄ 11#64) ∗
      ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2) ∗
      ((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392 ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 11#64) ∗ A.pool lim st s0 ∗
       (statesIntoPbJumpTablePlacedAt ∗
        memRegion out optProtoInnerStateSize ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
         ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
         ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
        (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
         ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
         ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
        vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
        memRegion (stA + 536#64) 392)) by sep_ac_rfl]
  apply SepWP.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 11#64
    (statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc hrun hx8 hx0
  refine seq_clean_wp hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _hvm1⟩
  have hsplit_1424 : memRegion (s0.sp - 1520#64) 1424 =
      memRegion (s0.sp - 1520#64) 8 ∗ memRegion (s0.sp - 1512#64) 1416 :=
    ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [hsplit_1424]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  refine SepWP.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ 11#64) ∗ A.pool lim st s1 ∗
          (statesIntoPbJumpTablePlacedAt ∗
           memRegion out optProtoInnerStateSize ∗
           (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
            ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
            ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
           (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
            ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
            ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
            polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
           memRegion (stA + 536#64) 392) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           (stA ↦₆₄ 11#64) ∗
           statesIntoPbJumpTablePlacedAt ∗
           memRegion out optProtoInnerStateSize ∗
           (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
            ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
            ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
           (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
            ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
            ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
            polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
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
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
         ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
         ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
         ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
         ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64, ∃∗ v8 : BitVec 64,
         ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
         ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
         ∃∗ y0 : BitVec 64, ∃∗ y1 : BitVec 64, ∃∗ y2 : BitVec 64,
         ∃∗ y3 : BitVec 64, ∃∗ y4 : BitVec 64, ∃∗ y5 : BitVec 64,
           ct1AcknowledgedScratchCells s0.sp
             u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
             w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
           memRegion (s0.sp - 1360#64) 528 ∗
           memRegion (s0.sp - 832#64) 352 ∗
           memRegion (s0.sp - 432#64) 8 ∗
           memRegion (s0.sp - 352#64) 40 ∗
           memRegion (s0.sp - 312#64) 8 ∗
           memRegion (s0.sp - 208#64) 48 ∗
           memRegion (s0.sp - 112#64) 16) ∗ Rest := by
    intro Rest
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160) ∗ Rest by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left (memRegion_ct1Acknowledged_scratch_split s0.sp))
  refine SepWP.weaken_pre (hscratch_split _) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
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
  apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v8
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro y0
  apply SepWP.exists_elim; intro y1
  apply SepWP.exists_elim; intro y2
  apply SepWP.exists_elim; intro y3
  apply SepWP.exists_elim; intro y4
  apply SepWP.exists_elim; intro y5
  have hpre1 := ct1Acknowledged_step_60_to_372_placed (ext := ext) s0 s1 out stA
    (epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     ct1AcknowledgedScratchCells s0.sp
       u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
       w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
     memRegion (s0.sp - 1360#64) 528 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392 ∗ A.pool lim st s1)
    hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine seq_vm_wp (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hpre1) ?_
  intro s2 hpc2 hrun2 hvm2
    ⟨_hacp2, hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx20_2, hx19_2, htr2⟩
  rw [← A.pool_transport lim st s1 s2 hvm2]
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    ((a + 48#64) ↦₆₄ hdr0) ∗ ((a + 56#64) ↦₆₄ hdr1) ∗ ((a + 64#64) ↦₆₄ hdr2) ∗
    ((a + 72#64) ↦₆₄ es0) ∗ ((a + 80#64) ↦₆₄ es1) ∗ ((a + 88#64) ↦₆₄ es2)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ cap_ct1) ∗ ((a + 8#64) ↦₆₄ ptr_ct1) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
    ((a + 24#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (a + 32#64) s.receiving_ek
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
       ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) := by
    dsimp only [F_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 96#64) =
      (((stA + 104#64) ↦₆₄ cap_ct1) ∗ ((stA + 112#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 120#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 128#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A.repAlloc (stA + 136#64) s.receiving_ek) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 96#64) =
      (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
       ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A.repAlloc (s0.sp - 1232#64) s.receiving_ek) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 96#64 = stA + 104#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_wp_placed hmemcpy A lim st
    (szKeep := 96) (szReloc := 432) (szTotal := 528) (off := 96#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (words12 a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2)
    (words4_polyDecoderAt A.repAlloc cap_ct1 ptr_ct1
      (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.receiving_ek)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      statesIntoPbJumpTablePlacedAt ∗
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      ct1AcknowledgedScratchCells s0.sp
        u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
        w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
      memRegion (s0.sp - 832#64) 352 ∗
      memRegion (s0.sp - 432#64) 8 ∗
      memRegion (s0.sp - 352#64) 40 ∗
      memRegion (s0.sp - 312#64) 8 ∗
      memRegion (s0.sp - 208#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 11#64) ∗
      memRegion out optProtoInnerStateSize ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 _hvm3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hstep2 := ct1Acknowledged_step_376_to_424_placed (ext := ext) s0 s3 out stA
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 v6 v7 v8
    w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5
    (memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A.repAlloc (s0.sp - 1232#64) s.receiving_ek ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTablePlacedAt ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392 ∗ A.pool lim st s3)
    hsp0_align hlen hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx20_3 hx19_3 htr3
  refine seq_vm_wp (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep2) ?_
  intro s4 hpc4 hrun4 hvm4
    ⟨_hacp4, hsp4, hx29_4, hx28_4, hx27_4, hx26_4, hx24_4, hx23_4,
     hx21_4, hx20_4, hx19_4, htr4⟩
  rw [← A.pool_transport lim st s3 s4 hvm4]
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  have hstep3 := ct1Acknowledged_step_424_to_1812_wp_placed hA s0 s4 st out stA cap_ct1 ptr_ct1
    s.uc.epoch s.uc.ct1
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
     ct1AcknowledgedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
       w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5 ∗
     memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A.repAlloc (s0.sp - 1232#64) s.receiving_ek ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTablePlacedAt ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hfits_clone hsp0_align hlen hpc4 hrun4 hsp4 hx29_4 hx28_4 hx27_4 hx26_4 hx24_4 hx23_4
    hx21_4 hx20_4 hx19_4 htr4
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep3) ?_
  intro s5 _Pm5 hpc5 hrun5
    ⟨ptr_new, hPm5, hsp5, hx29_5, hx28_5, hx27_5, hx26_5,
     hx24_5, hx23_5, hx22_5, hx21_5, hx20_5, hx19_5, htr5⟩
  refine SepWP.weaken_pre hPm5 ?_
  have hstep4 := ct1Acknowledged_step_1812_to_1900_placed hA s0 s5
    (M.stepEvents (ct1CloneEvents s.uc.ct1) st)
    out stA cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    v0 v1 v2 v3 v4 v5 v6 v7 v8
    w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 y4 y5
    (vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
     memRegion (s0.sp - 1360#64) 96 ∗
     polyDecoderAt A.repAlloc (s0.sp - 1232#64) s.receiving_ek ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTablePlacedAt ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 352#64) 40 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc5 hrun5 hsp5 hx29_5 hx28_5 hx27_5 hx26_5 hx24_5 hx23_5
    hx22_5 hx21_5 hx20_5 hx19_5 htr5
  refine seq_clean_wp (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep4) ?_
  intro s6 hpc6 hrun6
    ⟨_hacp6, hsp6, hlr6, hx0_6, hx1_6, hx29_6, hx27_6, hx26_6, hx22_6, hx21_6, hx19_6, htr6⟩
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  refine call_decoderIntoPb_expose_wp_placed hdec
    (M.stepEvents (ct1DeallocEvents cap_ct1) (M.stepEvents (ct1CloneEvents s.uc.ct1) st))
    (s0.sp - 352#64) (s0.sp - 1232#64) s.receiving_ek
    (Frame :=
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
       ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
      ct1AcknowledgedScratchCells s0.sp
        a0 a1 a2 a3 a4 a5 v0 v1 v2 v3 v4 v5 v6 v7 v8
        hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
      vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
        (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
      (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
       ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
      memRegion (s0.sp - 1360#64) 96 ∗
      memRegion (stA + 104#64) 432 ∗
      statesIntoPbJumpTablePlacedAt ∗
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      memRegion (s0.sp - 832#64) 352 ∗
      memRegion (s0.sp - 432#64) 8 ∗
      memRegion (s0.sp - 312#64) 8 ∗
      memRegion (s0.sp - 208#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 11#64) ∗
      memRegion out optProtoInnerStateSize ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
      memRegion (stA + 536#64) 392)
    hpc6 hrun6 hsp6 hfsp_align hlr6 htr6 hx0_6 hx1_6 hfit_dec
    (by
      rw [← hrecomb_stack]
      dsimp only [protoPolynomialDecoderSize]
      sep_ac_rfl)
    fun s7 evs_dec d0 d1 d2 d3 d4 hpc7 hrun7 hsp7 hcs7 _hacp7 htr7 henv_dec => ?_
  have hx19_7 : s7.readReg64 .x19 = out := hcs7.1.trans hx19_6
  have hx21_7 : s7.readReg64 .x21 = BitVec.ofNat 64 s.uc.ct1.length := hcs7.2.2.1.trans hx21_6
  have hx22_7 : s7.readReg64 .x22 = ptr_new := hcs7.2.2.2.1.trans hx22_6
  have hx26_7 : s7.readReg64 .x26 = s0.sp - 480#64 := hcs7.2.2.2.2.2.2.2.1.trans hx26_6
  have hx27_7 : s7.readReg64 .x27 = s.uc.epoch := hcs7.2.2.2.2.2.2.2.2.1.trans hx27_6
  have hx29_7 : s7.readReg64 .x29 = s0.sp - 96#64 := hcs7.2.2.2.2.2.2.2.2.2.2.1.trans hx29_6
  simp only [arm64_norm]
  have hstep5 := ct1Acknowledged_step_1904_to_1544_placed (ext := ext) s0 s7 out ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
    d0 d1 d2 d3 d4
    v0 v1 v2 v3 v4 v5 v6 v7 v8
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     memRegion (s0.sp - 1232#64) polyDecoderSize ∗
     A.pool lim
       (M.stepEvents evs_dec
         (M.stepEvents (ct1DeallocEvents cap_ct1)
           (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s7 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
      ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
     memRegion (s0.sp - 1360#64) 96 ∗
     memRegion (stA + 104#64) 432 ∗
     statesIntoPbJumpTablePlacedAt ∗
     memRegion (s0.sp - 832#64) 352 ∗
     memRegion (s0.sp - 432#64) 8 ∗
     memRegion (s0.sp - 312#64) 8 ∗
     memRegion (s0.sp - 208#64) 48 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 11#64) ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc7 hrun7 hsp7 hx29_7 hx27_7 hx26_7 hx22_7 hx21_7 hx19_7 htr7
  refine seq_vm_wp (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep5) ?_
  intro s8 hpc8 hrun8 hvm8 ⟨_hacp8, hsp8, hx29_8, hx19_8, hx21_8, hx22_8, htr8⟩
  rw [← A.pool_transport lim
    (M.stepEvents evs_dec
      (M.stepEvents (ct1DeallocEvents cap_ct1)
        (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s7 s8 hvm8]
  have hscratch := ct1AcknowledgedScratchCells_entails_memRegions s0.sp
    hdr0 hdr1 hdr2 es0 es1 es2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
    hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    d0 d1 d2 d3 d4
  have hstA := stA_ct1Acknowledged_entails_928 stA
    a0 a1 a2 a3 a4 a5 hdr0 hdr1 hdr2 es0 es1 es2
  have hpre_epi :
      ct1AcknowledgedScratchCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
        hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
       ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
       ((s0.sp - 320#64) ↦₆₄ d4)) ∗
      epilogueStagingCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch d0 d1 d2 d3 d4 w176 w184
        w192 w200 w208 w216 ∗
      (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       memRegion (s0.sp - 1232#64) polyDecoderSize ∗
       A.pool lim
         (M.stepEvents evs_dec
           (M.stepEvents (ct1DeallocEvents cap_ct1)
             (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s8 ∗
       stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       memRegion (stA + 104#64) 432 ∗
       statesIntoPbJumpTablePlacedAt ∗
       memRegion (s0.sp - 832#64) 352 ∗
       memRegion (s0.sp - 432#64) 8 ∗
       memRegion (s0.sp - 312#64) 8 ∗
       memRegion (s0.sp - 208#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 11#64) ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       memRegion (stA + 536#64) 392) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        hdr0 hdr1 hdr2 es0 es1 es2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch d0 d1 d2 d3 d4 w176 w184
        w192 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      A.pool lim
        (M.stepEvents evs_dec
          (M.stepEvents (ct1DeallocEvents cap_ct1)
            (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s8 ∗
      (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTablePlacedAt) := by
    dsimp only [polyDecoderSize] at *
    refine Entails.trans (Entails.of_eq (show _ =
      (ct1AcknowledgedScratchCells s0.sp
         hdr0 hdr1 hdr2 es0 es1 es2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5 s.uc.epoch
         hdr0 hdr1 hdr2 es0 es1 es2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1264#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 1256#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1248#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((s0.sp - 1240#64) ↦₆₄ s.uc.epoch)) ∗
       (((s0.sp - 352#64) ↦₆₄ d0) ∗ ((s0.sp - 344#64) ↦₆₄ d1) ∗
        ((s0.sp - 336#64) ↦₆₄ d2) ∗ ((s0.sp - 328#64) ↦₆₄ d3) ∗
        ((s0.sp - 320#64) ↦₆₄ d4)) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       memRegion (s0.sp - 1232#64) 400 ∗
       memRegion (s0.sp - 832#64) 352 ∗
       memRegion (s0.sp - 432#64) 8 ∗
       memRegion (s0.sp - 312#64) 8 ∗
       memRegion (s0.sp - 208#64) 48 ∗
       memRegion (s0.sp - 112#64) 16) ∗
      ((stA ↦₆₄ 11#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
        ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ hdr0) ∗ ((stA + 64#64) ↦₆₄ hdr1) ∗ ((stA + 72#64) ↦₆₄ hdr2) ∗
        ((stA + 80#64) ↦₆₄ es0) ∗ ((stA + 88#64) ↦₆₄ es1) ∗ ((stA + 96#64) ↦₆₄ es2)) ∗
       memRegion (stA + 104#64) 432 ∗
       memRegion (stA + 536#64) 392) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         hdr0 hdr1 hdr2 es0 es1 es2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch d0 d1 d2 d3 d4 w176 w184
         w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       A.pool lim
         (M.stepEvents evs_dec
           (M.stepEvents (ct1DeallocEvents cap_ct1)
             (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) s8 ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hep := states_into_pb_epilogue_placed (ext := ext) A lim
    (M.stepEvents evs_dec
      (M.stepEvents (ct1DeallocEvents cap_ct1)
        (M.stepEvents (ct1CloneEvents s.uc.ct1) st)))
    s0 s8 out
    hdr0 hdr1 hdr2 es0 es1 es2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch d0 d1 d2 d3 d4 w176 w184
    w192 w200 w208 w216
    (protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc8 hrun8 hsp8 hx29_8 hx19_8 htr8
  rw [hx22_8, hx21_8] at hep
  refine SepWP.mono (SepWP.weaken_pre hpre_epi hep)
    fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf, _hvmf⟩ => ?_
  refine ⟨⟨(ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1) ++ evs_dec,
    hEnv _ ⟨ct1DeallocEvents cap_ct1, evs_dec, rfl,
      freeOnlyEvs_ct1DeallocEvents cap_ct1, henv_dec⟩, ?_⟩,
    hspf, hcsf, htrf⟩
  rw [M.stepEvents_append, M.stepEvents_append]
  refine Entails.trans hPf ?_
  have hout := outWords28_entails_ct1Acknowledged A.repAlloc out
    hdr0 hdr1 hdr2 es0 es1 es2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    d0 d1 d2 d3 d4
    w176 w184 w192 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       0x8000000000000009#64
       hdr0 hdr1 hdr2 es0 es1 es2
       (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
       a0 a1 a2 a3 a4 a5 s.uc.epoch
       d0 d1 d2 d3 d4 w176 w184
       w192 w200 w208 w216 ∗
     protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc hdr0 hdr1 hdr2 s.uc.hdr ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗
     A.pool lim
       (M.stepEvents evs_dec
         (M.stepEvents (ct1DeallocEvents cap_ct1)
           (M.stepEvents (ct1CloneEvents s.uc.ct1) st))) sf ∗
     stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

theorem states_into_pb_ct1Acknowledged_of_env_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct1AcknowledgedEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct1Acknowledged s) Env) :=
  states_into_pb_ct1Acknowledged_of_env_placed hA hdec (sessionMemcpyRegion_ok_placed hA) s hEnv

/-- Tight `Ct1AcknowledgedEnv` relocatable `subroutine_ok` for Arm 9 (`States.ct1Acknowledged`). -/
theorem states_into_pb_ct1Acknowledged_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F
        (.ct1Acknowledged s) (Ct1AcknowledgedEnv s)) :=
  states_into_pb_ct1Acknowledged_of_env_placed hA hdec hmemcpy s (fun _ h => h)

/-- Tight `Ct1AcknowledgedEnv` relocatable `subroutine_ok` for Arm 9 (`States.ct1Acknowledged`),
    projecting `memcpy` directly from `StatesIntoPbAllocPlacedBudget`. -/
theorem states_into_pb_ct1Acknowledged_env_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F
        (.ct1Acknowledged s) (Ct1AcknowledgedEnv s)) :=
  states_into_pb_ct1Acknowledged_env_placed hA hdec (sessionMemcpyRegion_ok_placed hA) s

/-- Default `statesIntoPbVariantPlacedSpec` (`SpqrBoundedEvs 64 (2 * |encodeRaw| + 1024)`)
    relocatable `subroutine_ok` for Arm 9 (`States.ct1Acknowledged`) under explicit payload/slot
    size bounds. -/
theorem states_into_pb_ct1Acknowledged_of_bounds_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + s.receiving_ek.pts.length ≤ 64)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤
      2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧
      4 * sl.vec.length ≤
        2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec M A lim F (.ct1Acknowledged s)) :=
  states_into_pb_ct1Acknowledged_of_env_placed hA hdec hmemcpy s
    (fun _ => ct1AcknowledgedEnv_imp_spqrBoundedEvs hcnt (by omega) hct1_max hct1_req hpts)

theorem states_into_pb_ct1Acknowledged_of_bounds_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + s.receiving_ek.pts.length ≤ 64)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤
      2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧
      4 * sl.vec.length ≤
        2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec M A lim F (.ct1Acknowledged s)) :=
  states_into_pb_ct1Acknowledged_of_bounds_placed hA hdec (sessionMemcpyRegion_ok_placed hA)
    s hcnt hct1_max hct1_req hpts

theorem states_into_pb_ct1Acknowledged_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct1AcknowledgedEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct1Acknowledged s) Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct1Acknowledged_of_env_placed hA hdec hmemcpy s hEnv)

theorem states_into_pb_ct1Acknowledged_of_env_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct1AcknowledgedEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct1Acknowledged s) Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct1Acknowledged_of_env_of_alloc_placed hA hdec s hEnv)

theorem states_into_pb_ct1Acknowledged_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F
          (.ct1Acknowledged s) (Ct1AcknowledgedEnv s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct1Acknowledged_env_placed hA hdec hmemcpy s)

theorem states_into_pb_ct1Acknowledged_env_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F
          (.ct1Acknowledged s) (Ct1AcknowledgedEnv s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct1Acknowledged_env_of_alloc_placed hA hdec s)

theorem states_into_pb_ct1Acknowledged_of_bounds_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + s.receiving_ek.pts.length ≤ 64)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤
      2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧
      4 * sl.vec.length ≤
        2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F (.ct1Acknowledged s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct1Acknowledged_of_bounds_placed
      hA hdec hmemcpy s hcnt hct1_max hct1_req hpts)

theorem states_into_pb_ct1Acknowledged_of_bounds_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (hdec : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + s.receiving_ek.pts.length ≤ 64)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤
      2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧
      4 * sl.vec.length ≤
        2 * (V1State.encodeRaw (States.ct1Acknowledged (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F (.ct1Acknowledged s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct1Acknowledged_of_bounds_of_alloc_placed
      hA hdec s hcnt hct1_max hct1_req hpts)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cPlacedBudget
