/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::clone` Base Helpers (Block `80`)

Specializes `SerContractsXPlaced M A lim H` stub contracts and Block `82 → 80` `Chain::clone`
bridges onto `lsProg_80 H`, and provides `VmPreserved`-aware `SepWPpLsCl` stepping and `A.pool`
transport combinators for `SessionStructure::clone`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseXBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl lsρ
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
  withLsCodeLoaded withLsCl withMemEq
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (sepWPp_pure_2nd)
open CryptoVerification.E2E.Record.Placed (
  blkPl_80 blkPl_82 lsProg_80 lsProg_82
)
open CryptoVerification.E2E.Record.Serialization (SessionCloneGhost)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  RustLayoutOk FitsEvents rustAllocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget (
  sepWPp_of_sepWP_lscl_vm_sc sc_transport_pool scNoPanicPost sc_noPanic_of_false
  maxReq_le_mallocngMaxAllocSize_of_fitsEnv sessionCloneEnv_segCloneEvents
  fitsEvents_segCloneEvents_of_fitsEnv
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced sessionCloneSpecX
  shim_placed_ok_at_stateX alloc_placed_ok_at_stateX
  allocNoOom_placed_ok_at_stateX memcpy_placed_ok_at_stateX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (SepWPpLsCl)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget (
  protoChainCloneSpecX chainCloneSpecX senderChainCloneSpecX
  ProtoChainCloneLocal1PlacedOkX ChainCloneLocal1PlacedOkX SenderChainCloneLocal1PlacedOkX
)

/-! ## Re-exported stack decomposition and `SessionCloneEnv` bridges -/

abbrev scSubStackX : Nat :=
  CryptoVerification.E2E.Record.Serialization.SessionCloneAux.scSubStackX

abbrev stackAt_sessionClone_eq_x :=
  @CryptoVerification.E2E.Record.Serialization.SessionCloneAux.stackAt_sessionClone_eq_x

abbrev maxReq_le_mallocngMaxAllocSize_of_fitsEnv_x :=
  @maxReq_le_mallocngMaxAllocSize_of_fitsEnv

abbrev sessionCloneEnv_segCloneEvents_x :=
  @sessionCloneEnv_segCloneEvents

abbrev fitsEvents_segCloneEvents_of_fitsEnv_x :=
  @fitsEvents_segCloneEvents_of_fitsEnv

/-! ## Extern stub bridges and call helpers on Block `80` -/

theorem sc_shim_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl session2ShimBudgetSpecX) :=
  hC.alloc.shim (callerProg := lsProg_80 H)

theorem sc_alloc_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)) :=
  hC.alloc.alloc (callerProg := lsProg_80 H)

theorem sc_allocNoOom_call_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {s : State} (hC : SerContractsXPlaced M A lim H)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym)
      (withMemEq s.mem
        (rustCliAllocNoOomSpecWithStack M A lim false extHookStack)) :=
  hC.alloc.allocNoOom_call (callerProg := lsProg_80 H) hcl

theorem sc_memcpy_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)) :=
  hC.memcpy (callerProg := lsProg_80 H)

theorem sc_shim_placed_ok_at_stateX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {s : State} (hC : SerContractsXPlaced M A lim H)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustNoAllocShimSym)
      { pre := fun (_ : Unit) s' =>
          ⌜s'.mem = s.mem⌝ ∗ stackAt s'.sp extHookStack
        post := fun (_ : Unit) s0 sf =>
          ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp extHookStack } :=
  shim_placed_ok_at_stateX (sc_shim_placed_ok_at_x hC) hcl

theorem sc_alloc_placed_ok_at_stateX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {s : State} (hC : SerContractsXPlaced M A lim H)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym)
      { pre := fun (size, align, st) s' =>
          ⌜s'.mem = s.mem ∧
            (s'.readReg64 .x0).toNat = size ∧ (s'.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align ∧ LsRetAddr624 (s'.readReg64 .lr)⌝ ∗
          A.pool lim st s' ∗ stackAt s'.sp extHookStack
        post := (rustCliAllocBudgetSpecWithStack M A lim false extHookStack).post
        onOom := (rustCliAllocBudgetSpecWithStack M A lim false extHookStack).onOom } :=
  alloc_placed_ok_at_stateX (sc_alloc_placed_ok_at_x hC) hcl

theorem sc_allocNoOom_placed_ok_at_stateX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {s : State} (hC : SerContractsXPlaced M A lim H)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym)
      { pre := fun (size, align, st) s' =>
          ⌜s'.mem = s.mem ∧
            (s'.readReg64 .x0).toNat = size ∧ (s'.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align ∧ FitsEvents M lim st (rustAllocEvents size align) ∧
            LsRetAddr624 (s'.readReg64 .lr)⌝ ∗
          A.pool lim st s' ∗ stackAt s'.sp extHookStack
        post := (rustCliAllocNoOomSpecWithStack M A lim false extHookStack).post } :=
  allocNoOom_placed_ok_at_stateX (callerProg := lsProg_80 H) hC.alloc hcl

theorem sc_memcpy_placed_ok_at_stateX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {s : State} (hC : SerContractsXPlaced M A lim H)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym)
      { pre := fun ((dst, src, bs) : BitVec 64 × BitVec 64 × List (BitVec 8)) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = dst ∧ s'.readReg64 .x1 = src ∧
            (s'.readReg64 .x2).toNat = bs.length⌝ ∗
          memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s'.sp extHookStack
        post := (sessionMemcpyBudgetSpec extHookStack).post } :=
  memcpy_placed_ok_at_stateX (sc_memcpy_placed_ok_at_x hC) hcl

/-! ## Block `82 → 80` `Chain::clone` callee bridges -/

theorem sc_chainClone_placed_ok_at_x [LibsignalPlacement] {H : LibsignalHooks}
    {α : Type} (spec : Spec α)
    (hcc : subroutine_ok (lsProg_82 H) (blkPl_82).base (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base (withLsCodeLoaded lsmpl spec) :=
  CryptoVerification.E2E.Record.Serialization.SessionCloneAux.sc_chainClone_placed_ok_at_x spec hcc

theorem sc_protoChainClone_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hpcc : ProtoChainCloneLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (protoChainCloneSpecX M A lim)) :=
  sc_chainClone_placed_ok_at_x (protoChainCloneSpecX M A lim) hpcc

theorem sc_chainCloneSpec_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hcc : ChainCloneLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (chainCloneSpecX M A lim)) :=
  sc_chainClone_placed_ok_at_x (chainCloneSpecX M A lim) hcc

theorem sc_senderChainClone_placed_ok_at_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hscc : SenderChainCloneLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (senderChainCloneSpecX M A lim)) :=
  sc_chainClone_placed_ok_at_x (senderChainCloneSpecX M A lim) hscc

/-! ## Stepping, `A.pool` transport, and panic-postcondition combinators -/

abbrev sepWPp_of_sepWP_lscl_vm_sc_x := @sepWPp_of_sepWP_lscl_vm_sc

/-- Lift a `VmPreserved` `SepWP` basic block directly into `SepWPpLsCl`. -/
theorem SepWPpLsCl.of_sepWP_vm {pl : MultiPlacement} {prog : Program}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → SepWPpLsCl pl prog ret sm Pm Q Qp))) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  fun hcl => sepWPp_of_sepWP_lscl_vm_sc hcl h

abbrev sc_transport_pool_x := @sc_transport_pool

theorem sc_transport_pool_bind_x {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {ret : BitVec 64}
    {s_old s : State} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s_old s)
    (h : ∀ s_cur : State, s_cur = s → SepWPp prog ret s_cur (A.pool lim st s_cur ∗ Rest) Q Qp) :
    SepWPp prog ret s (A.pool lim st s_old ∗ Rest) Q Qp :=
  sc_transport_pool hvm (h s rfl)

theorem sc_transport_pool_lscl_x {pl : MultiPlacement} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {prog : Program}
    {ret : BitVec 64} {s_old s : State} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s_old s)
    (h : SepWPpLsCl pl prog ret s (A.pool lim st s ∗ Rest) Q Qp) :
    SepWPpLsCl pl prog ret s (A.pool lim st s_old ∗ Rest) Q Qp :=
  fun hcl => sc_transport_pool hvm (h hcl)

theorem sc_transport_pool_bind_lscl_x {pl : MultiPlacement} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {prog : Program}
    {ret : BitVec 64} {s_old s : State} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s_old s)
    (h : ∀ s_cur : State, s_cur = s →
      SepWPpLsCl pl prog ret s_cur (A.pool lim st s_cur ∗ Rest) Q Qp) :
    SepWPpLsCl pl prog ret s (A.pool lim st s_old ∗ Rest) Q Qp :=
  sc_transport_pool_lscl_x hvm (h s rfl)

theorem sepWPpLsCl_pure_2nd_x {pl : MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State} {φ : Prop} {P Q_post : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpLsCl pl prog ret s (P ∗ Q_post) Q Qp) :
    SepWPpLsCl pl prog ret s (P ∗ ⌜φ⌝ ∗ Q_post) Q Qp :=
  fun hcl => sepWPp_pure_2nd fun hφ => h hφ hcl

abbrev scNoPanicPostX : State → SepProp → Prop := scNoPanicPost

abbrev sc_noPanic_of_false_x := @sc_noPanic_of_false

/-- Canonical panic postcondition for `subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl` on
`sessionCloneSpecX M A lim` (`onPanic = ⌜False⌝`). -/
abbrev scPanicPostX {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : SessionCloneGhost × M.σ) (Fr R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (sessionCloneSpecX M A lim).onPanic x s0 sf ∗ R)

theorem sc_panic_of_false_x {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : SessionCloneGhost × M.σ} {Fr R F : SepProp} {s0 : State}
    (sf : State) (_hpan : sf.status = .Panicked) :
    scPanicPostX A lim x Fr R s0 sf (⌜False⌝ ∗ F) := by
  intro hm
  rw [sepConj_assoc] at hm
  exact False.elim (not_satisfies_false_sepConj hm)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseXBudget
