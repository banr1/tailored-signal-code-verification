/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `initialize_bob_session` (Block `75`) at SPQR V1

Allocator-budget (`RustCliAllocBudget M`) relocatable proofs of `initialize_bob_session` (Block `75`)
at SPQR V1, composing `InitBobCutPlacedBudget` (`Pqxdh::accept` at Block `79`), the budget-threaded
`spqr::initial_state` seam (`lsmpl.base 327`), and `InitBobPlacedBudget` under `InitBobV1EnvOfEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification (LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement LibsignalHooks
  LibsignalPlacement blkPl_75 libsignalFrozen_of_keepsFrozen lsLogFilterAddr lsMemcpySym
  lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl lsProg_75)
open CryptoVerification.RustHeap (vecHeader vecU8)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded sessionMemcpyRegionSpec
  sessionShimSpec withLsCodeRoLoaded withLsFrozen)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput Bytes DRKey Primitives StructuralPrims
  WellSizedAcceptKeysInput bv_sub_add_lit' bytesToBv8 encodeEC pqxdhEntryStack)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (PrimitivesMatchCrypto acceptKeys_some_lengths
  bobFrameAtSpqr bobParamsFieldsAt bobSession344Bv8V1 bobSpqrCutCells initBobSavedRegs
  pqxdhAcceptFieldsAt_split pqxdhAcceptOptFieldsAt pqxdhAcceptRestAt stackAt_initBob_entry
  withBobMemInv)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (stageP2bStack)
open CryptoVerification.Cli.E2E.V1 (bobSpqrCutCells_eq_paramsAt bobSpqrParams bobSpqrVecBuf
  bobV1_stack_extra bobV1_stack_join vecU8At_eq_header_bobBuf)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost initialStateResultAt
  initialStateStack initialStateValue paramsAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget SeqEnv VmPreserved rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpyBudgetSpec
  framelessMemcpySpec noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec
  sessionShimBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (pqxdhAcceptOptFieldsFrozenPlacedSpec
  pqxdhAcceptOptFieldsInnerPlacedSpec pqxdhAcceptOptFieldsPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget (
  PqxdhPlacedHookContracts hookSat_noAllocShimBudget_of_rustAllocShimVm)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (
  initBob_to_spqr_full_memInv_placed_of_accept)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget (InitBobSessionBuildEnv
  fitsEnv_initBobSessionBuildEnv_iff initBobSessionBuildEvents initBob_epilogue_placed
  initBob_session_build_placed_of_session)
open LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget (
  pqxdhAccept_opt_fields_full_placed_ok_of_block)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv
  initialStatePlacedSpec initialStatePlacedSpecOfEnv initialStatePlacedSpecX
  initialStatePlacedSpecXOfEnv)

/-! ## `spqr::initial_state` budget seam and combined envelope (`InitBobV1Env`) -/

/-- `InitialStateGhost` witness passed by `initialize_bob_session` (Block `75`) to
`spqr::initial_state` (`lsmpl.base 327`) at entry stack pointer `sp0`. -/
def bobSpqrGhost (sp0 : BitVec 64) (pqrKey : Bytes) : InitialStateGhost :=
  ⟨sp0 - 488#64, sp0 - 768#64, sp0 - 576#64, bobSpqrParams pqrKey⟩

/-- Envelope-parametric allocation event predicate for `initialize_bob_session` (Block `75`) on the
SPQR V1 accepting path: `Pqxdh::accept`, followed by `spqr::initial_state`, followed by
`InitBobSessionBuildEnv`. -/
def InitBobV1EnvOfEnv
    (AcceptEnv : AcceptKeysInput → List AllocEvent → Prop)
    (InitEnv : InitialStateGhost → List AllocEvent → Prop)
    (sp0 : BitVec 64) (inp : AcceptKeysInput) (pqrKey : Bytes) :
    List AllocEvent → Prop :=
  SeqEnv (AcceptEnv inp) (SeqEnv (InitEnv (bobSpqrGhost sp0 pqrKey)) InitBobSessionBuildEnv)

/-- Concrete allocation event envelope for `initialize_bob_session` (Block `75`) at SPQR V1,
instantiating `AcceptOptFieldsEnv P` and `InitialStateEnv F`. -/
def InitBobV1Env (P : Primitives) (F : ShaCompress)
    (sp0 : BitVec 64) (inp : AcceptKeysInput) (pqrKey : Bytes) :
    List AllocEvent → Prop :=
  InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) (InitialStateEnv F) sp0 inp pqrKey

/-- Envelope-parametric relocatable inner `Spec` of `spqr::initial_state` (Block `327`). -/
abbrev spqrInitialStatePlacedInnerSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (InitEnv : InitialStateGhost → List AllocEvent → Prop) :
    Spec (InitialStateGhost × M.σ) :=
  initialStatePlacedSpecOfEnv M A lim F InitEnv

abbrev spqrInitialStatePlacedInnerSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (InitialStateGhost × M.σ) :=
  initialStatePlacedSpec M A lim F

/-- Envelope-parametric plain `subroutine_ok` seam for `spqr::initial_state` at `lsmpl.base 327`. -/
def InitialStatePlacedOkOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (InitEnv : InitialStateGhost → List AllocEvent → Prop) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_75 H) (lsmpl.base 327)
    (spqrInitialStatePlacedInnerSpecOfEnv M A lim F InitEnv)

abbrev InitialStatePlacedOk [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (H : LibsignalHooks) : Prop :=
  InitialStatePlacedOkOfEnv M A lim F (InitialStateEnv F) H

/-- Envelope-parametric `withBobMemInv Φ`-guarded `subroutine_ok` seam for `spqr::initial_state` at
`lsmpl.base 327` on `lsProg_75 H`. -/
def InitialStateMemInvPlacedOkOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (Φ : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (InitEnv : InitialStateGhost → List AllocEvent → Prop)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_75 H) (lsmpl.base 327)
    (withBobMemInv Φ (spqrInitialStatePlacedInnerSpecOfEnv M A lim F InitEnv))

abbrev InitialStateMemInvPlacedOk [LibsignalPlacement]
    (M : AllocCostModel) (Φ : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (H : LibsignalHooks) : Prop :=
  InitialStateMemInvPlacedOkOfEnv M Φ A lim F (InitialStateEnv F) H

theorem initialStateMemInvPlacedOkOfEnv_eq_specXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (InitEnv : InitialStateGhost → List AllocEvent → Prop) (H : LibsignalHooks) :
    InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv H =
      subroutine_ok (lsProg_75 H) (lsmpl.base 327)
        (initialStatePlacedSpecXOfEnv M A lim F InitEnv) := rfl

theorem initialStateMemInvPlacedOk_eq_specX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (H : LibsignalHooks) :
    InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F H =
      subroutine_ok (lsProg_75 H) (lsmpl.base 327)
        (initialStatePlacedSpecX M A lim F) := rfl

theorem initialStateMemInvPlacedOkOfEnv_of_plain [LibsignalPlacement]
    {M : AllocCostModel} (Φ : Memory → Prop) {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {InitEnv : InitialStateGhost → List AllocEvent → Prop} {H : LibsignalHooks}
    (h : InitialStatePlacedOkOfEnv M A lim F InitEnv H) :
    InitialStateMemInvPlacedOkOfEnv M Φ A lim F InitEnv H := by
  refine subroutine_ok_mono h (fun _ _ _ hm => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withBobMemInv] at hm
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hm
  exact hm.2

theorem initialStateMemInvPlacedOk_of_plain [LibsignalPlacement]
    {M : AllocCostModel} (Φ : Memory → Prop) {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {H : LibsignalHooks}
    (h : InitialStatePlacedOk M A lim F H) :
    InitialStateMemInvPlacedOk M Φ A lim F H :=
  initialStateMemInvPlacedOkOfEnv_of_plain Φ h

theorem initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {InitEnv : InitialStateGhost → List AllocEvent → Prop} {H : LibsignalHooks}
    (h : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv H) :
    InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv H := by
  refine subroutine_ok_mono h (fun _ _ _ hm => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withBobMemInv] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hm ⊢
  exact ⟨⟨LibsignalCodeLoaded.of_codeLoaded hm.1.2, hm.1.1⟩, hm.2⟩

theorem initialStateFrozenPlacedOk_of_codeRoLoaded [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {H : LibsignalHooks}
    (h : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F H) :
    InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F H :=
  initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded h

/-! ## Spatial and hook-weakening helpers -/

theorem hookSat_sessionShimBudget_of_noAllocShimBudget {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec) :
    HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec := by
  refine HookSat.mono h fun u R s0 hp => ⟨u, R, hp, fun sf hq => ?_⟩
  dsimp only [noAllocShimBudgetSpec, sessionShimBudgetSpec, sessionShimSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hq.1.2, hq.1.1, hq.2⟩

theorem hookSat_framelessMemcpy_of_sessionMemcpyRegionBudget {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    HookSat H lsMemcpySym framelessMemcpySpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hp => ?_
  dsimp only [framelessMemcpySpec, framelessMemcpyBudgetSpec,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hp ⊢
  refine ⟨(dst, src, bs), R, by simpa only [sepConj_assoc] using hp, fun sf hq => ?_⟩
  dsimp only [framelessMemcpySpec, framelessMemcpyBudgetSpec,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨hvm, hq'⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq'
  rcases hq' with ⟨⟨hx0f, htr⟩, hmem⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0f, htr, hvm⟩, by rwa [← sepConj_assoc] at hmem⟩

private theorem hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm_local {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hp => ?_
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
    memcpyRegionSpec, allocMemcpyVmSpec] at hp ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), R, ?_, fun sf hq => ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, by rwa [sepConj_assoc]⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0f, hacp, hvm⟩, hm'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0f, hacp.2.1⟩, by rwa [← sepConj_assoc]⟩

private def bobFrameRestPlaced (sp0 : BitVec 64) (pq ck : Bytes) : SepProp :=
  ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗
  ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗ ((sp0 - 672#64) ↦₃₂ 0#32) ∗
  memRegion (sp0 - 668#64) 12 ∗ ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
  memRegion (sp0 - 544#64) 56 ∗
  ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
  ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288

private theorem bobFrameAtSpqr_entails_placed (sp0 : BitVec 64) (rk pq ck : Bytes)
    (hrk : rk.length = 32) :
    bobFrameAtSpqr sp0 rk pq ck ⊢
      memRegion (sp0 - 768#64) 32 ∗ bobFrameRestPlaced sp0 pq ck := by
  unfold bobFrameAtSpqr bobFrameRestPlaced
  have hlen : (bytesToBv8 rk).length = 32 := by simp [bytesToBv8, hrk]
  have hm : ((sp0 - 768#64) ↦ₛ bytesToBv8 rk) ⊢ memRegion (sp0 - 768#64) 32 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp0 - 768#64) (bytesToBv8 rk)
  exact sepConj_mono_left hm

private theorem sub488_merge_placed (sp0 : BitVec 64) (pq ck : Bytes)
    (hpq : pq.length = 32) (hck : ck.length = 32) :
    paramsAt (sp0 - 488#64) (sp0 - 576#64) (bobSpqrParams pq) ∗
    ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288 ⊢
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 := by
  have hpq_len : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have hck_len : (bytesToBv8 ck).length = 32 := by simp [bytesToBv8, hck]
  have h104 :
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (bobSpqrParams pq) ∗
      ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
      ((sp0 - 388#64) ↦₃₂ 0#32) ⊢ memRegion (sp0 - 488#64) 104 := by
    unfold paramsAt bobSpqrParams
    simp only [hpq_len, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    rw [ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 8) (k := 96)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 8) (k := 88)
        (b' := sp0 - 472#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 472#64) (n := 4) (k := 84)
        (b' := sp0 - 468#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 468#64) (n := 4) (k := 80)
        (b' := sp0 - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 464#64) (n := 4) (k := 76)
        (b' := sp0 - 460#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 460#64) (n := 4) (k := 72)
        (b' := sp0 - 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 456#64) (n := 4) (k := 68)
        (b' := sp0 - 452#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 452#64) (n := 32) (k := 36)
        (b' := sp0 - 420#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 420#64) (n := 32) (k := 4)
        (b' := sp0 - 388#64) rfl (by bv_omega) (by decide)]
    have hm_pq : ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 452#64) 32 := by
      rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 452#64) (bytesToBv8 pq)
    have hm_ck : ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 420#64) 32 := by
      rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 420#64) (bytesToBv8 ck)
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono (pointsTo32_entails_memRegion _ _)
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono hm_pq
                    (sepConj_mono hm_ck
                      (pointsTo32_entails_memRegion _ _)))))))))
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  have hrearr :
      paramsAt (sp0 - 488#64) (sp0 - 576#64) (bobSpqrParams pq) ∗
      ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
      ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288 =
      (paramsAt (sp0 - 488#64) (sp0 - 576#64) (bobSpqrParams pq) ∗
       ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
       ((sp0 - 388#64) ↦₃₂ 0#32)) ∗ memRegion (sp0 - 384#64) 288 := by ac_rfl
  rw [hrearr]
  exact sepConj_mono_left h104

private theorem sub768_merge_280_placed (sp0 : BitVec 64) (rk pq ck : Bytes)
    (hrk : rk.length = 32) (hpq : pq.length = 32) (hck : ck.length = 32) :
    memRegion (sp0 - 768#64) 32 ∗
    ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 672#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 668#64) 12 ∗
    ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ∗
    ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
    ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ∗ memRegion (sp0 - 544#64) 56 ⊢
      memRegion (sp0 - 768#64) 280 := by
  have hrk_len : (bytesToBv8 rk).length = 32 := by simp [bytesToBv8, hrk]
  have hpq_len : (bytesToBv8 pq).length = 32 := by simp [bytesToBv8, hpq]
  have hck_len : (bytesToBv8 ck).length = 32 := by simp [bytesToBv8, hck]
  rw [ProofLib.memRegion_split' (b := sp0 - 768#64) (n := 32) (k := 248)
      (b' := sp0 - 736#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 736#64) (n := 32) (k := 216)
      (b' := sp0 - 704#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 704#64) (n := 32) (k := 184)
      (b' := sp0 - 672#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 672#64) (n := 4) (k := 180)
      (b' := sp0 - 668#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 668#64) (n := 12) (k := 168)
      (b' := sp0 - 656#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 656#64) (n := 32) (k := 136)
      (b' := sp0 - 624#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 624#64) (n := 32) (k := 104)
      (b' := sp0 - 592#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 592#64) (n := 4) (k := 100)
      (b' := sp0 - 588#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 588#64) (n := 12) (k := 88)
      (b' := sp0 - 576#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 576#64) (n := 32) (k := 56)
      (b' := sp0 - 544#64) rfl (by bv_omega) (by decide)]
  have hm_pq736 : ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 736#64) 32 := by
    rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 736#64) (bytesToBv8 pq)
  have hm_ck704 : ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 704#64) 32 := by
    rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 704#64) (bytesToBv8 ck)
  have hm_rk656 : ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ⊢ memRegion (sp0 - 656#64) 32 := by
    rw [← hrk_len]; exact pointsToBytes_entails_memRegion (sp0 - 656#64) (bytesToBv8 rk)
  have hm_ck624 : ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ⊢ memRegion (sp0 - 624#64) 32 := by
    rw [← hck_len]; exact pointsToBytes_entails_memRegion (sp0 - 624#64) (bytesToBv8 ck)
  have hm_pq576 : ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ⊢ memRegion (sp0 - 576#64) 32 := by
    rw [← hpq_len]; exact pointsToBytes_entails_memRegion (sp0 - 576#64) (bytesToBv8 pq)
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono hm_pq736
      (sepConj_mono hm_ck704
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono hm_rk656
              (sepConj_mono hm_ck624
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (Entails.refl _)
                    (sepConj_mono hm_pq576
                      (Entails.refl _))))))))))

private theorem stack_final_eq_placed (sp0 : BitVec 64) :
    memRegion (sp0 - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
    stackAt (sp0 - 768#64) pqxdhEntryStack ∗
    memRegion (sp0 - 768#64) 280 ∗
    memRegion (sp0 - 488#64) 344 ∗
    memRegion (sp0 - 144#64) 48 ∗
    memRegion (sp0 - 96#64) 96 =
      stackAt sp0 (stageP2bStack + 0x700) := by
  have hsplit :
      memRegion (sp0 - 488#64) 344 ∗ memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 488#64) 104 ∗ memRegion (sp0 - 384#64) 288 := by
    rw [(ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 344) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)).symm,
      ProofLib.memRegion_split' (b := sp0 - 488#64) (n := 104) (k := 288)
        (b' := sp0 - 384#64) rfl (by bv_omega) (by decide)]
  rw [bobV1_stack_extra sp0, stackAt_initBob_entry sp0,
    ← (ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
      memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12),
    ← sepConj_assoc (memRegion (sp0 - 488#64) 344), hsplit]
  ac_rfl

private theorem sepWPp_seq_placed {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm hQ R hmm (hsteps.codeLoaded hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

private theorem call_spqr_memInv_budget {α : Type} {prog : Program} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hcall : subroutine_ok prog entry (withBobMemInv Φ spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, (s.mem ⊨ P ∗ (F ∗ R)) → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ (withBobMemInv Φ spec).onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ (withBobMemInv Φ spec).onPanic x s sf ∗ R') →
      Qp sf ((withBobMemInv Φ spec).onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withBobMemInv]) :
    SepWPp prog ret s (P ∗ F) Q Qp := by
  have hmid :
      SepWPp prog ret_pc s (P ∗ F)
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm R' _ hoom_post => ?_)
    · intro R hm
      rw [sepConj_assoc] at hm
      dsimp only [withBobMemInv]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hΦ, hpre R hm⟩
    · dsimp only [withBobMemInv] at hoom_post
      rw [hoom sm] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := hmid R hm hL
  rcases hout with
    ⟨hpcm, hrunm, P_m, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm
        (hkf s.mem sm.mem hΦ hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

/-! ## Postcondition and SPQR V1 budget-threaded `initialize_bob_session` -/

/-- Budget-threaded postcondition of `initialize_bob_session` (Block `75`) at SPQR V1, advancing
`A.pool lim st s0` by some event trace `evs` satisfying `InitBobV1EnvOfEnv`. -/
abbrev BobSessionV1Post [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (AcceptEnv : AcceptKeysInput → List AllocEvent → Prop)
    (InitEnv : InitialStateGhost → List AllocEvent → Prop)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ∃ (evs : List AllocEvent)
    (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
     ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
    InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey evs ∧
    localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
    baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
    chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
      (outPtr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
        spqrCap spqrBufPtr
        (BitVec.ofNat 64 (initialStateValue F (bobSpqrParams drKey.pqrKey)).length)
        ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
      bobSpqrVecBuf A.repAlloc spqrCap spqrBufPtr
        (initialStateValue F (bobSpqrParams drKey.pqrKey)) ∗
      bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
      (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
      (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗ A.live ratchetPubBoxPtr 33 1 ∗
      (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
      (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp (stageP2bStack + 0x700) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ Frame) ∧
    sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

set_option maxHeartbeats 1200000 in
/-- Relocatable `withBobMemInv Φ` budget-threaded proof of `initialize_bob_session` (Block `75`) at
SPQR V1 when `acceptKeys P inp = some drKey`, parameterized over `h_accept` (`lsmpl.base 79`) and
`hinit` (`lsmpl.base 327`). -/
theorem initializeBobSession_ok_v1_memInv_placed_of_accept_of_session
    [LibsignalPlacement] {M : AllocCostModel} {P : Primitives}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Φ : Memory → Prop} {Qp : State → SepProp → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hΦ_cl : ∀ m, Φ m → LibsignalCodeLoaded lsmpl m)
    (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv)))
    (hinit : InitialStateMemInvPlacedOkOfEnv M Φ A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hΦ0 : Φ s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F AcceptEnv InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame)
      Qp := by
  have ⟨hlen_rk, hlen_pq, hlen_ck⟩ := acceptKeys_some_lengths hWF hacc
  have ⟨_, _, hlen_spkSk, _, _, _, _, hlen_ikA, hlen_ekA, _⟩ := h_9
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned] using hsp_align
  have hfits1 : FitsEnv M lim st (AcceptEnv inp) := hfits.seq_left
  let Frame1 : SepProp :=
    memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame
  have hpb3 := initBob_to_spqr_full_memInv_placed_of_accept (Qp := Qp) hkf hWF h_accept s0 st inp
    ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame1
    hΦ0 hfits1 hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc
  refine sepWPp_seq_placed
    (SepWPp.weaken_pre
      (Entails.of_eq (by dsimp only [Frame1]; rw [bobV1_stack_extra s0.sp]; ac_rfl))
      hpb3) ?_
  intro s1 P1 hpc1 hrun1
    ⟨⟨evs1, hevs1, hent1⟩, hΦ1, _, hsp1,
     hx0_1, hx8_1, hx19_1, hx20_1, hx21_1, hx23_1, hx27_1, hx30_1, htr1, hvregs1⟩
  let st1 : M.σ := M.stepEvents evs1 st
  let gx : InitialStateGhost := bobSpqrGhost s0.sp drKey.pqrKey
  have hfits2 : FitsEnv M lim st1 (InitEnv gx) := (hfits.seq_right hevs1).seq_left
  let FrameCall : SepProp :=
    ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
    ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
    (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
    ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    bobFrameRestPlaced s0.sp drKey.pqrKey drKey.chainKey ∗
    (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
    pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
    ((argPtr + 297#64) ↦₈ 0#8) ∗
    memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗ Frame
  have hent1_call : P1 ⊢
      (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (bobSpqrParams drKey.pqrKey) ∗
       ((s0.sp - 576#64) ↦ₛ (bobSpqrParams drKey.pqrKey).authKey) ∗
       memRegion (s0.sp - 768#64) 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim st1 s1 ∗ stackAt s1.sp initialStateStack) ∗ FrameCall := by
    refine Entails.trans hent1 ?_
    dsimp only [Frame1, FrameCall, st1]
    rw [bobSpqrCutCells_eq_paramsAt s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey
      drKey.chainKey spkBPk inp.spkBSk hlen_pq, hsp1]
    have hrearr :
        (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (bobSpqrParams drKey.pqrKey) ∗
         ((s0.sp - 576#64) ↦ₛ (bobSpqrParams drKey.pqrKey).authKey) ∗
         ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
         ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
         (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
         ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)) ∗
        bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
        (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
        pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
        ((argPtr + 297#64) ↦₈ 0#8) ∗ memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool lim (M.stepEvents evs1 st) s1 ∗
        (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) =
        bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
        (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
         stackAt (s0.sp - 768#64) pqxdhEntryStack) ∗
        (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (bobSpqrParams drKey.pqrKey) ∗
         ((s0.sp - 576#64) ↦ₛ (bobSpqrParams drKey.pqrKey).authKey) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs1 st) s1 ∗
         ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
         ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
         (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
         ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
         pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
         ((argPtr + 297#64) ↦₈ 0#8) ∗ memRegion outPtr 344 ∗
         initBobSavedRegs s0.sp s0 ∗ Frame) := by ac_rfl
    rw [hrearr, bobV1_stack_join s0.sp]
    exact Entails.trans
      (sepConj_mono_left
        (bobFrameAtSpqr_entails_placed s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey hlen_rk))
      (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hent1_call ?_
  have hsp1_align : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]; revert hsp0_align; bv_bits
  refine call_spqr_memInv_budget hkf hΦ1 hinit (x := (gx, st1)) (F := FrameCall)
    hpc1 hrun1 hsp1_align hx30_1
    (fun R hm => ?_)
    (fun _ _ _ _ hex => (not_satisfies_false_sepConj hex).elim)
    (fun _ _ ⟨_, hpan⟩ => (not_satisfies_false_sepConj hpan).elim)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hΦ2 => ?_)
  · dsimp only [spqrInitialStatePlacedInnerSpecOfEnv, initialStatePlacedSpecOfEnv,
      bobSpqrGhost, bobSpqrParams, gx]
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hx8_1, hpqr_ne, ?_, hfits2⟩, hm⟩
    simp [bytesToBv8, hlen_pq]
  · dsimp only [spqrInitialStatePlacedInnerSpecOfEnv, initialStatePlacedSpecOfEnv,
      initialStateResultAt, vecU8, bobSpqrGhost, gx]
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs2 => ?_
    rw [hsp1, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr2, hevs2⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by
      simp only [vecU8At_eq_header_bobBuf, vecHeader,
        sepExists_sepConj_left, sepExists_sepConj_right,
        bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      rfl)) ?_
    refine SepWPp.exists_elim fun spqrCap => SepWPp.exists_elim fun spqrBufPtr => ?_
    obtain ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, _, _, _, hx27_2, _, _, hvregs2⟩ := hcs2
    let st2 : M.σ := M.stepEvents evs2 st1
    have hfits3 : FitsEvents M lim st2 initBobSessionBuildEvents :=
      fitsEnv_initBobSessionBuildEnv_iff.mp ((hfits.seq_right hevs1).seq_right hevs2)
    let v := initialStateValue F (bobSpqrParams drKey.pqrKey)
    let spqrLen := BitVec.ofNat 64 v.length
    let Frame2 : SepProp :=
      bobSpqrVecBuf A.repAlloc spqrCap spqrBufPtr v ∗
      ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
      ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
      ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
      memRegion (s0.sp - 588#64) 12 ∗
      ((s0.sp - 576#64) ↦ₛ (bobSpqrParams drKey.pqrKey).authKey) ∗
      memRegion (s0.sp - 544#64) 56 ∗ memRegion (s0.sp - 144#64) 48 ∗
      pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
      ((argPtr + 297#64) ↦₈ 0#8) ∗ initBobSavedRegs s0.sp s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame
    have hent2 :
        paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (bobSpqrParams drKey.pqrKey) ∗
        ((s0.sp - 576#64) ↦ₛ (bobSpqrParams drKey.pqrKey).authKey) ∗
        ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
        ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
        bobSpqrVecBuf A.repAlloc spqrCap spqrBufPtr v ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim st2 s2 ∗ stackAt (s0.sp - 768#64) initialStateStack ∗ FrameCall ⊢
        ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
        ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
        ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
        ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
        ((s0.sp - 592#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 488#64) 344 ∗
        (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
        ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
        (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
        ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
        memRegion outPtr 344 ∗
        stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool lim st2 s2 ∗ Frame2 := by
      dsimp only [FrameCall, Frame2, bobFrameRestPlaced]
      rw [← bobV1_stack_join s0.sp,
        pqxdhAcceptFieldsAt_split argPtr pqskPtr ctSlicePtr ctBufPtr inp]
      have hrearr :
          paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (bobSpqrParams drKey.pqrKey) ∗
          ((s0.sp - 576#64) ↦ₛ (bobSpqrParams drKey.pqrKey).authKey) ∗
          ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
          ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
          bobSpqrVecBuf A.repAlloc spqrCap spqrBufPtr v ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st2 s2 ∗
          (memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
           stackAt (s0.sp - 768#64) pqxdhEntryStack) ∗
          (((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
           ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           (((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
            ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗ ((s0.sp - 672#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 668#64) 12 ∗ ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 588#64) 12 ∗ memRegion (s0.sp - 544#64) 56 ∗
            ((s0.sp - 452#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
            ((s0.sp - 420#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
            ((s0.sp - 388#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 384#64) 288) ∗
           (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
           (((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
            pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp) ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗ memRegion outPtr 344 ∗
           initBobSavedRegs s0.sp s0 ∗ Frame) =
          (paramsAt (s0.sp - 488#64) (s0.sp - 576#64) (bobSpqrParams drKey.pqrKey) ∗
           ((s0.sp - 452#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 420#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 388#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 384#64) 288) ∗
          (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
           ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
           ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
           (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
           ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
           (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
           ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           memRegion outPtr 344 ∗
           stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool lim st2 s2 ∗
           bobSpqrVecBuf A.repAlloc spqrCap spqrBufPtr v ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ (bobSpqrParams drKey.pqrKey).authKey) ∗
           memRegion (s0.sp - 544#64) 56 ∗
           pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗ initBobSavedRegs s0.sp s0 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) := by
        ac_rfl
      rw [hrearr]
      exact Entails.trans
        (sepConj_mono_left (sub488_merge_placed s0.sp drKey.pqrKey drKey.chainKey hlen_pq hlen_ck))
        (Entails.of_eq (by ac_rfl))
    have hpb1 := initBob_session_build_placed_of_session (Qp := Qp) hshim halloc hdealloc hmemcpy
      s0 s2 st2 argPtr ratchetKeyPairPtr outPtr spqrCap spqrBufPtr spqrLen
      ikBPk inp.hdr.ikAPk inp.hdr.ekAPk spkBPk inp.spkBSk drKey.rootKey drKey.chainKey Frame2
      (hΦ_cl s2.mem hΦ2) hfits3
      h_10 hlen_ikA hlen_ekA h_11 hlen_spkSk hlen_rk hlen_ck
      hsp0_align hrun2 hpc2 (hsp2.trans hsp1)
      (hx19_2.trans hx19_1) (hx20_2.trans hx20_1) (hx21_2.trans hx21_1)
      (hx23_2.trans hx23_1) (hx27_2.trans hx27_1) (htr2.trans htr1) (hvregs2.trans hvregs1)
    refine sepWPp_seq_placed (SepWPp.weaken_pre hent2 hpb1) ?_
    intro s3 P3 hpc3 hrun3
      ⟨localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
       ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
       pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
       hlik, hrik, hrk_box, hbk, hrp, hrpriv, hck_box,
       hent3, _, _, _, hsp3, htr3, hvregs3⟩
    let evsFull : List AllocEvent := evs1 ++ (evs2 ++ initBobSessionBuildEvents)
    have hevsFull : InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey evsFull :=
      SeqEnv.append hevs1 (SeqEnv.append hevs2 (rfl : InitBobSessionBuildEnv initBobSessionBuildEvents))
    have hstFull : M.stepEvents initBobSessionBuildEvents st2 = M.stepEvents evsFull st := by
      dsimp only [evsFull, st2, st1]; simp only [AllocCostModel.stepEvents_append]
    let sessBytes := bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
      spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
    let FrameEpi : SepProp :=
      (outPtr ↦ₛ sessBytes) ∗
      bobSpqrVecBuf A.repAlloc spqrCap spqrBufPtr v ∗
      bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
      (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
      (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗ A.live ratchetPubBoxPtr 33 1 ∗
      (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
      (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
      stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
      memRegion (s0.sp - 768#64) 280 ∗ memRegion (s0.sp - 488#64) 344 ∗
      memRegion (s0.sp - 144#64) 48 ∗ A.pool lim (M.stepEvents evsFull st) s3 ∗ Frame
    have hent3_epi : P3 ⊢ initBobSavedRegs s0.sp s0 ∗ FrameEpi := by
      refine Entails.trans hent3 ?_
      dsimp only [Frame2, FrameEpi, sessBytes, bobParamsFieldsAt, bobSpqrParams]
      rw [hstFull, pqxdhAcceptFieldsAt_split argPtr pqskPtr ctSlicePtr ctBufPtr inp]
      have hrearr :
          (outPtr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
            spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
            pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
          memRegion (s0.sp - 768#64) 32 ∗
          ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
          ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
          ((s0.sp - 592#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 488#64) 344 ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
          ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
          (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
          ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
          (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
          (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
          (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
          (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
          (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗ A.live ratchetPubBoxPtr 33 1 ∗
          (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
          (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
          stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool lim (M.stepEvents evsFull st) s3 ∗
          (bobSpqrVecBuf A.repAlloc spqrCap spqrBufPtr v ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           memRegion (s0.sp - 544#64) 56 ∗ memRegion (s0.sp - 144#64) 48 ∗
           pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
           ((argPtr + 297#64) ↦₈ 0#8) ∗ initBobSavedRegs s0.sp s0 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗ Frame) =
          (memRegion (s0.sp - 768#64) 32 ∗
           ((s0.sp - 736#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           ((s0.sp - 704#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 672#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 668#64) 12 ∗
           ((s0.sp - 656#64) ↦ₛ bytesToBv8 drKey.rootKey) ∗
           ((s0.sp - 624#64) ↦ₛ bytesToBv8 drKey.chainKey) ∗
           ((s0.sp - 592#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 588#64) 12 ∗
           ((s0.sp - 576#64) ↦ₛ bytesToBv8 drKey.pqrKey) ∗
           memRegion (s0.sp - 544#64) 56) ∗
          (initBobSavedRegs s0.sp s0 ∗
           (outPtr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
             spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
             pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
           bobSpqrVecBuf A.repAlloc spqrCap spqrBufPtr v ∗
           ((argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            (((argPtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
             ((argPtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
             pqxdhAcceptRestAt argPtr pqskPtr ctSlicePtr ctBufPtr inp) ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
            ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)) ∗
           (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
           (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
           (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
           (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
           (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗ A.live ratchetPubBoxPtr 33 1 ∗
           (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
           (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           memRegion (s0.sp - 768#64 - BitVec.ofNat 64 initialStateStack) 0x700 ∗
           stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
           memRegion (s0.sp - 488#64) 344 ∗ memRegion (s0.sp - 144#64) 48 ∗
           A.pool lim (M.stepEvents evsFull st) s3 ∗ Frame) := by ac_rfl
      rw [hrearr]
      exact Entails.trans
        (sepConj_mono_left
          (sub768_merge_280_placed s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey
            hlen_rk hlen_pq hlen_ck))
        (Entails.of_eq (by ac_rfl))
    have hpb2 := initBob_epilogue_placed (H := H) s0 s3 FrameEpi hsp0_align hrun3 hpc3 hsp3 hvregs3
    refine SepWPp.of_sepWP_ret
      (SepWP.weaken_pre hent3_epi
        (SepWP.mono hpb2 (fun sf Pf _ _ ⟨hPf, hrun_f, hpc_f, hsp_f, hcs_f, hvm_f, htr_f⟩ => ?_)))
    refine ⟨evsFull, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hevsFull, hlik, hrik, hrk_box, hbk, hrp, hrpriv, hck_box,
      Entails.trans hPf (Entails.of_eq (by
        dsimp only [FrameEpi, sessBytes, spqrLen, v]
        rw [← A.pool_transport lim (M.stepEvents evsFull st) s3 sf hvm_f,
          ← stack_final_eq_placed s0.sp]
        ac_rfl)),
      hrun_f, hpc_f, hsp_f, hcs_f, htr_f.trans htr3⟩

theorem initializeBobSession_ok_v1_memInv_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop} {H : LibsignalHooks}
    {Φ : Memory → Prop} {Qp : State → SepProp → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hΦ_cl : ∀ m, Φ m → LibsignalCodeLoaded lsmpl m) (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (withBobMemInv Φ (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv)))
    (hinit : InitialStateMemInvPlacedOkOfEnv M Φ A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hΦ0 : Φ s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F AcceptEnv InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_memInv_placed_of_accept_of_session hkf hΦ_cl hWF
    (hookSat_sessionShimBudget_of_noAllocShimBudget
      (hookSat_noAllocShimBudget_of_rustAllocShimVm hshim))
    halloc hdealloc (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm_local hmemcpy)
    h_accept hinit s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
    outPtr drKey Frame hΦ0 hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11
    hacc

/-! ## `withLsCodeRoLoaded` and `withLsFrozen` specializations -/

theorem initializeBobSession_ok_v1_placed_of_accept_of_session [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop} (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F AcceptEnv InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_memInv_placed_of_accept_of_session
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk) (fun _ h => h.1)
    hWF hshim halloc hdealloc hmemcpy h_accept hinit s0 st inp ikBPk spkBPk argPtr pqskPtr
    ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame hcro hfits hrun hpc hsp_align hpqr_ne
    h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

theorem initializeBobSession_ok_v1_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop} (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F AcceptEnv InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_memInv_placed_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk) (fun _ h => h.1)
    hWF hshim halloc hdealloc hmemcpy h_accept hinit s0 st inp ikBPk spkBPk argPtr pqskPtr
    ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame hcro hfits hrun hpc hsp_align hpqr_ne
    h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

theorem initializeBobSession_ok_v1_frozen_placed_of_accept_of_session [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop} (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim AcceptEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F AcceptEnv InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_memInv_placed_of_accept_of_session
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk)
    (fun _ h => LibsignalCodeLoaded.of_codeLoaded h.2)
    hWF hshim halloc hdealloc hmemcpy h_accept hinit s0 st inp ikBPk spkBPk argPtr pqskPtr
    ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame hfr hfits hrun hpc hsp_align hpqr_ne
    h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

theorem initializeBobSession_ok_v1_frozen_placed_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop} (hWF : StructuralPrims P)
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim AcceptEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F AcceptEnv InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_memInv_placed_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk)
    (fun _ h => LibsignalCodeLoaded.of_codeLoaded h.2)
    hWF hshim halloc hdealloc hmemcpy h_accept hinit s0 st inp ikBPk spkBPk argPtr pqskPtr
    ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame hfr hfits hrun hpc hsp_align hpqr_ne
    h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-! ## Closed `[LibsignalFullPlacement]` corollaries -/

/-- Closed `[LibsignalFullPlacement]` budget-threaded SPQR V1 `initialize_bob_session` (Block `75`),
discharging `Pqxdh::accept` (`lsmpl.base 79`) internally (`InitEnv`-parametric). -/
theorem initializeBobSession_ok_v1_full_placed_of_env_of_session [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P) (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st
      (InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F (AcceptOptFieldsEnv P) InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_frozen_placed_of_accept_of_session hWF
    (hookSat_sessionShimBudget_of_noAllocShimBudget hH.noAllocShim)
    hH.alloc hH.dealloc hmemcpy
    (pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH
      (hookSat_framelessMemcpy_of_sessionMemcpyRegionBudget hmemcpy))
    hinit s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

theorem initializeBobSession_ok_v1_full_placed_of_session [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P) (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1Env P F s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F (AcceptOptFieldsEnv P) (InitialStateEnv F) s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_full_placed_of_env_of_session hWF hP hH hmemcpy hinit
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

theorem initializeBobSession_ok_v1_full_placed_of_env_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P) (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st
      (InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F (AcceptOptFieldsEnv P) InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_full_placed_of_env_of_session hWF hP hH
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm_local hmemcpy) hinit
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- Closed `[LibsignalFullPlacement]` budget-threaded SPQR V1 `initialize_bob_session` (Block `75`)
under `allocMemcpyVmSpec` at concrete envelope `InitBobV1Env P F`. -/
theorem initializeBobSession_ok_v1_full_placed_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P) (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1Env P F s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F (AcceptOptFieldsEnv P) (InitialStateEnv F) s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_full_placed_of_env_std hWF hP hH hmemcpy hinit
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

end LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
