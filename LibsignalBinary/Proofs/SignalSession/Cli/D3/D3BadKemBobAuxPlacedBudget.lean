/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxA
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxB
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Bad-KEM Error Ownership (`Pqxdh::accept` & `initialize_bob_session`)

Budget-threaded `[LibsignalPlacement]` / `[LibsignalFullPlacement]` owned-error contracts for
`Pqxdh::accept` (Block `79`) and `initialize_bob_session` (Block `75`) when
`pkVecTag? 8#8 1568 ctBytes = none` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  IsLsBlockProg LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  blkPl_75 blkPl_79 libsignalFrozen_of_keepsFrozen libsignalSessionLib
  lsLogFilterAddr lsMemcpySym lsProg_75 lsProg_79 lsmpl
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded extract_withLsFrozen withLsCodeRoLoaded withLsFrozen
)
open CryptoVerification.LibsignalTripleRatchet.Keys (lsRustAllocSym lsRustNoAllocShimSym)
open CryptoVerification.LibsignalPublicApi.StoreKit (speWordsAt)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Primitives StructuralPrims WellSizedAcceptKeysInput
  bv_add_neg64 bv_sub_add_lit' bv_sub_sub_lit
  pqxdhEntryStack
  readReg_setMem_setPC_pre readReg_setPC_pre
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  PrimitivesMatchCrypto acceptRustDeallocSym
  cells6_sub764_merge cells12_sub96_merge
  ls_subroutine_ok_withLsFrozen_of_block
  memRegion_280_none_split memRegion_344_none_split
  stackAt_initBob_entry sub488_none_104_merge
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget (
  ecPubKeyIsCanonical_placed_ok_cl
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  acceptCalculateAgreementPlacedBaseSpec ecPubKeyIsCanonicalCallSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget (
  PqxdhPlacedHookContracts
  hookSat_framelessMemcpy_of_allocMemcpyVm
  hookSat_noAllocShimBudget_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget (
  pqxdhVecAppendElementsFastSpec vecAppendElements_fast_placed_ok_cl
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  AcceptBadKemGhost InitBobBadKemGhost
  bobParamsBadKemFieldsAt initBobBadKemErrOwnedAt initBobBadKemErrOwnedAt_merge
  pkVecTag? pqxdhAcceptBadKemErrOwnedAt pqxdhAcceptBadKemFieldsAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxA (
  pqxdhAcceptBadKemErrOwnedOpkNoneInnerPlacedSpec
  pqxdhAccept_badKem_err_owned_opk_none_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxB (
  pqxdhAcceptBadKemErrOwnedOpkSomeInnerPlacedSpec
  pqxdhAccept_badKem_err_owned_opk_some_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec noAllocShimSpec)

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

export D3BadKemBobAuxPlacedBudgetAuxA (
  acceptBadKemEvents
  AcceptBadKemEnv
  fitsEnv_acceptBadKemEnv_iff
  pqxdhAcceptBadKemErrOwnedInnerPlacedSpec
  pqxdhAcceptBadKemErrOwnedPlacedSpec
  pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
)

/-! ## 1. Combined Block-`79` Contract & Cross-Block Wrappers -/

/-- Budget-threaded owned-error rejecting contract for `Pqxdh::accept` (Block `79`) when
`pkVecTag? 8#8 1568 g.ctBytes = none`. -/
theorem pqxdhAccept_badKem_err_owned_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
        A lim (AcceptBadKemEnv P)) := by
  have hnone := pqxdhAccept_badKem_err_owned_opk_none_placed_ok hWF h_canon h_agree
    h_shim h_alloc h_dealloc h_memcpy
  have hsome := pqxdhAccept_badKem_err_owned_opk_some_placed_ok hWF h_canon h_agree h_vec_append
    h_shim h_alloc h_dealloc h_memcpy
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hfr, hpre_inner⟩ := extract_withLsFrozen hpre
  cases hopk : x.1.inp.opkBSk?
  · refine hnone.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsFrozen, pqxdhAcceptBadKemErrOwnedOpkNoneInnerPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hopk, hpre_inner⟩
  · refine hsome.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsFrozen, pqxdhAcceptBadKemErrOwnedOpkSomeInnerPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp [hopk], hpre_inner⟩

theorem pqxdhAccept_badKem_err_owned_placed_ok_of_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
        A lim (AcceptBadKemEnv P)) :=
  pqxdhAccept_badKem_err_owned_placed_ok hWF h_canon h_agree h_vec_append
    (hookSat_noAllocShimBudget_of_rustAllocShimVm h_shim) h_alloc h_dealloc
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

theorem pqxdhAccept_badKem_err_owned_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
        A lim (AcceptBadKemEnv P)) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (pqxdhAccept_badKem_err_owned_placed_ok hWF h_canon h_agree h_vec_append
      h_shim h_alloc h_dealloc h_memcpy)

theorem pqxdhAccept_badKem_err_owned_placed_ok_of_block_std [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
        A lim (AcceptBadKemEnv P)) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (pqxdhAccept_badKem_err_owned_placed_ok_of_std hWF h_canon h_agree h_vec_append
      h_shim h_alloc h_dealloc h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`Pqxdh::accept` (Block `79`) on Bad-KEM lifted to any `callerProg` at `lsmpl.base 79`. -/
theorem pqxdhAccept_badKem_err_owned_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
        A lim (AcceptBadKemEnv P)) :=
  pqxdhAccept_badKem_err_owned_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    (vecAppendElements_fast_placed_ok_cl h_memcpy)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy

theorem pqxdhAccept_badKem_err_owned_full_placed_ok_of_block_std [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
        A lim (AcceptBadKemEnv P)) :=
  pqxdhAccept_badKem_err_owned_full_placed_ok_of_block hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-! ## 2. Budget-Threaded `initialize_bob_session` (Block `75`) Specs & Proofs on Bad-KEM -/

/-- Budget-threaded inner specification of `initialize_bob_session` (Block `75`) when
`pkVecTag? 8#8 1568 g.ctBytes = none`, exposing `initBobBadKemErrOwnedAt A.repAlloc g.outPtr`. -/
def initializeBobSessionBadKemErrOwnedInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobBadKemGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      g.ctBytes.length < 2 ^ 63 ∧
      pkVecTag? 8#8 1568 g.ctBytes = none ∧
      FitsEnv M lim st (AcceptErrEnv g.inp)⌝ ∗
    bobParamsBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ctBytes g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AcceptErrEnv g.inp evs⌝ ∗
      bobParamsBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
        g.inp g.ctBytes g.ikBPk g.spkBPk g.sameAccountByte ∗
      (initBobBadKemErrOwnedAt A.repAlloc g.outPtr ∗ anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp (768 + pqxdhEntryStack) ∗
      A.pool lim (M.stepEvents evs st) sf

def initializeBobSessionBadKemErrOwnedPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobBadKemGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv)

def initializeBobSessionBadKemErrOwnedFrozenPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobBadKemGhost × M.σ) :=
  withLsFrozen lsmpl (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv)

private abbrev withBobErrMemInv {α : Type} (Φ : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜Φ s0.mem⌝ }

private theorem call_bobErrMemInv_frame {α : Type} {prog : Program} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hcall : subroutine_ok prog entry (withBobErrMemInv Φ spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withBobErrMemInv]) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm R' _ hoom_post => ?_)
    · intro R hm
      dsimp only [withBobErrMemInv]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hΦ, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩
    · dsimp only [withBobErrMemInv] at hoom_post
      rw [hoom sm] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := hmid R hm hL
  rcases hout with
    ⟨hpcm, hrunm, P_m, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out
  · have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hkf s.mem sm.mem hΦ hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

private theorem sepWP_instantiate_post_exists_outer {α : Type _} {prog : Program}
    {target_pc : BitVec 64} {s : State} {P R : SepProp} {Q : State → α → SepProp}
    {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ∃∗ a, Q sf a) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (Entails.sepExists_intro w) (h1 hm), h2⟩

set_option maxHeartbeats 1200000 in
/-- Memory-invariant budget-threaded owned-error rejecting contract for `initialize_bob_session`
(Block `75`) on Bad-KEM. -/
theorem initializeBobSession_badKem_errOwned_memInv_placed_ok_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {H : LibsignalHooks} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      ({ D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv with
          pre := fun x s0 =>
            (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec
              A lim AcceptErrEnv).pre x s0 ∗ ⌜Φ s0.mem⌝ })) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      ({ initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv with
          pre := fun x s0 =>
            (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv).pre x s0 ∗
              ⌜Φ s0.mem⌝ }) := by
  unfold initializeBobSessionBadKemErrOwnedInnerPlacedSpec bobParamsBadKemFieldsAt
  wpp_init x s0
  obtain ⟨⟨inp, ctBytes, ikBPk, spkBPk, sameAccountByte, argPtr, pqskPtr, ctSlicePtr, ctBufPtr,
    ratchetKeyPairPtr, outPtr⟩, st⟩ := x
  dsimp only at *
  have hΦ0 : Φ s0.mem := by assumption
  subst argPtr ratchetKeyPairPtr outPtr
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.seq_frozen (Φ := Φ) hkf hΦ0 (mid := lsmpl.base 79)
  wp_steps_sync_pool (lsmpl.base 79)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hΦ1
  refine call_bobErrMemInv_frame
    (spec := D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv)
    hkf hΦ1 h_accept
    (ret_pc := (blkPl_75).base + 56#64)
    (x := (⟨inp, ctBytes, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr,
      s0.sp - 488#64⟩, st))
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
    (by wp_norm_lhs)
    rfl
    (by simp only [arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ hm => by
      dsimp only [D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec] at hm
      rw [satisfies_pure_sepConj] at hm
      exact hm.1)
    (fun _ _ hm => by
      dsimp only [D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec] at hm
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 _hΦ2 => ?_)
  dsimp only [D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedInnerPlacedSpec,
    pqxdhAcceptBadKemErrOwnedAt] at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28
       hcs1_29 hcs1_vregs
  conv =>
    arg 4
    simp only [speWordsAt, sepExists_sepConj_left, sepExists_sepConj_right,
      bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub,
      arm64_norm, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.exists_elim fun errTag => ?_
  refine SepWPp.exists_elim fun w2 => ?_
  refine SepWPp.exists_elim fun w3 => ?_
  refine SepWPp.exists_elim fun w4 => ?_
  refine SepWPp.exists_elim fun w5 => ?_
  refine SepWPp.exists_elim fun w6 => ?_
  refine SepWPp.pure_left fun ⟨⟨htr1, hevs⟩, herrTag⟩ => ?_
  apply SepWPp.of_sepWP_ret
  rw [memRegion_280_none_split s0.sp,
      memRegion_344_none_split (s0.readReg64 (.gpr 8#5))]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  refine SepWP.fold
    (initBobBadKemErrOwnedAt_merge A.repAlloc (s0.readReg64 (.gpr 8#5))
      errTag w2 w3 w4 w5 w6 herrTag)
    (by sep_focus) ?_
  refine SepWP.fold (cells6_sub764_merge s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_280_none_split s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (sub488_none_104_merge s0.sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine SepWP.fold (cells12_sub96_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_initBob_entry s0.sp).symm) (by sep_focus) ?_
  apply sepWP_instantiate_post_exists_outer evs
  wp_done

theorem initializeBobSession_badKem_errOwned_placed_ok_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedPlacedSpec A lim AcceptErrEnv)) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedPlacedSpec A lim AcceptErrEnv) :=
  initializeBobSession_badKem_errOwned_memInv_placed_ok_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk) h_accept

theorem initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (D3BadKemBobAuxPlacedBudgetAuxA.pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec A lim AcceptErrEnv)) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim AcceptErrEnv) :=
  initializeBobSession_badKem_errOwned_memInv_placed_ok_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk) h_accept

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`initialize_bob_session` (Block `75`) on Bad-KEM. -/
theorem initializeBobSession_badKem_errOwned_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept
    (pqxdhAccept_badKem_err_owned_full_placed_ok_of_block hWF hP hH h_memcpy)

theorem initializeBobSession_badKem_errOwned_full_placed_ok_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A lim (AcceptBadKemEnv P)) :=
  initializeBobSession_badKem_errOwned_full_placed_ok hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget
