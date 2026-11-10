/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Callee and Pool-Sync Helpers for Budget `SignalMessage::compute_mac`

Stack-parameterized `VmPreserved` and `RustCliAllocBudget` callee contracts, `LsClInv`
transport lemmas, and `sync_call_pool` tactic for `ComputeBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto PublicKey ShaCompress)
open CryptoGames.HMAC (ShaState chunks64 keyToBytes32 toBEBytes)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lsmpl withLsCodeLoaded
)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded LsClInv LsSymState
  NewFromSliceGhost PublicKeySerializeCall RegsSaved
  boxU8Buf compress256Spec extHookStack hmacCoreAt hmacInnerInit hmacOuterInit
  hmacStateAt hmacWords64At hmacWords64At_eq
  newFromSliceSpec newFromSliceStack
  publicKeySerializeStack publicKeySerializeStackX
  regsSaved_of_calleeSavedPreserved session2Compress256Spec session2MemsetSpec
  sessionMemcpyRegionSpec sessionMemsetRegionSpec withLsCodeRoLoaded
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  VmPreserved fitsEvents_append rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  PublicKeySerializeEnv framelessMemcpyBudgetSpec publicKeySerializeEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustDeallocExternSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (
  ComputeMacEnv computeMacEvents fitsEnv_computeMac_iff
)

/-! ## `LsClInv` lift lemmas and state-parameterized join -/

theorem subroutine_ok_withLsClState_of_lscl [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog addr
      (spec.withLsClState (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, withLsCodeLoaded, LsSymState] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hpre.1.1, hpre.2⟩

theorem subroutine_ok_withLsClState_of_lscro [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog addr
      (spec.withLsClState (LsClState := fun s => LibsignalCodeRoLoaded lsmpl s.mem)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, withLsCodeRoLoaded, LsSymState] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hpre.1.1, hpre.2⟩

theorem subroutine_ok_withLsClState_of_plain {LsClState : State → Prop} {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr spec) :
    subroutine_ok prog addr (spec.withLsClState (LsClState := LsClState)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, LsSymState] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem subroutine_ok_lscl_of_withLsClState [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr
      (spec.withLsClState (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem))) :
    subroutine_ok prog addr (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, withLsCodeLoaded, LsSymState] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpre.1, trivial⟩, hpre.2⟩

theorem subroutine_ok_lscro_of_withLsClState [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr
      (spec.withLsClState (LsClState := fun s => LibsignalCodeRoLoaded lsmpl s.mem))) :
    subroutine_ok prog addr (withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, withLsCodeRoLoaded, LsSymState] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpre.1, trivial⟩, hpre.2⟩

theorem of_sepWP_lscl {LsClState : State → Prop} [hInv : LsClInv LsClState]
    {prog : Program} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LsClState s) (_hsym : LsSymState)
    (h : SepWP prog mid s P (fun sm Pm =>
      LsClState sm → LsSymState → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hInv.of_keepsFrozen hF hsteps.keepsFrozen) trivial R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem seq_lscl_compute {LsClState : State → Prop} [hInv : LsClInv LsClState]
    {prog : Program} (mid : BitVec 64) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : LsClState s) (_hsym : LsSymState)
    (h : SepWP prog mid s P (fun sm Pm =>
      LsClState sm → LsSymState → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · rcases (hnext (hInv.of_keepsFrozen hF hsteps.keepsFrozen) trivial).elim
        hmm (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hpost⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hpost⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- State-dependent join-point combinator allowing `A.pool lim st sm` inside the join invariant. -/
theorem sepWPp_with_join_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (P_join : State → SepProp) (Inv : State → Prop)
    (hbody : ∀ sm, Inv sm → SepWPp prog ret sm (P_join sm) Q Qp)
    (hbranches : (∀ {sm P'}, Inv sm → (P' ⊢ P_join sm) → SepWPp prog ret sm P' Q Qp) →
      SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hbranches fun hinv hent => SepWPp.weaken_pre hent (hbody _ hinv)

/-! ## Allocator envelope decomposition for `computeMacEvents` -/

theorem fitsComputeMac_parts {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st ComputeMacEnv) :
    let st1 := M.stepEvents publicKeySerializeEvents st
    let st2 := M.stepEvents (rustDeallocEvents 33 1) st1
    let st3 := M.stepEvents publicKeySerializeEvents st2
    let st4 := M.stepEvents (rustDeallocEvents 33 1) st3
    FitsEnv M lim st PublicKeySerializeEnv ∧
      FitsEnv M lim st2 PublicKeySerializeEnv ∧
      st4 = M.stepEvents computeMacEvents st := by
  rw [fitsEnv_computeMac_iff] at h
  dsimp only [computeMacEvents] at h
  have ⟨h12, h34⟩ := (fitsEvents_append M lim _ _ st).mp h
  have ⟨h1, _⟩ := (fitsEvents_append M lim _ _ st).mp h12
  rw [M.stepEvents_append] at h34
  have ⟨h3, _⟩ := (fitsEvents_append M lim _ _ _).mp h34
  refine ⟨FitsEnv.eq_iff.mpr h1, FitsEnv.eq_iff.mpr h3, ?_⟩
  dsimp only [computeMacEvents]
  simp only [M.stepEvents_append]

/-! ## `VmPreserved` and budget callee contracts -/

/-- `VmPreserved`-strengthened `newFromSliceSpec F`. -/
abbrev newFromSliceBudgetSpec (F : ShaCompress) : Spec NewFromSliceGhost :=
  withVmPreserved (newFromSliceSpec F)

/-- `VmPreserved`-strengthened `compress256Spec F`. -/
abbrev compress256BudgetSpec (F : ShaCompress) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) :=
  withVmPreserved (compress256Spec F)

def newFromSlicePkStackBudgetSpecAt (F : ShaCompress) (pkStack : Nat) :
    Spec NewFromSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.keyA ∧
      (s.readReg64 .x2).toNat = x.key.length ∧ x.key.length ≤ 64⌝ ∗
      memRegion x.ret 0x98 ∗ (x.keyA ↦ₛ x.key) ∗
      stackAt s.sp pkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (x.ret ↦₆₄ 0#64) ∗ hmacCoreAt F (x.ret + 8#64) x.key [] ∗
      (x.keyA ↦ₛ x.key) ∗
      stackAt s0.sp pkStack

abbrev newFromSlicePkStackBudgetSpec (F : ShaCompress) : Spec NewFromSliceGhost :=
  newFromSlicePkStackBudgetSpecAt F publicKeySerializeStack

abbrev newFromSlicePkStackBudgetSpecX (F : ShaCompress) : Spec NewFromSliceGhost :=
  newFromSlicePkStackBudgetSpecAt F publicKeySerializeStackX

private theorem stackAt_pk_eq_nfs_aux (sp : BitVec 64) :
    stackAt sp publicKeySerializeStack =
      stackAt sp newFromSliceStack ∗ memRegion (sp - 4128#64) 3584 := by
  simp only [stackAt, publicKeySerializeStack, newFromSliceStack]
  rw [show (4096 + 32 : Nat) = 3584 + 544 by decide,
    memRegion_split _ 3584 544 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (3584 + 544) = sp - 4128#64 := by bv_arith
  have e2 : sp - 4128#64 + BitVec.ofNat 64 3584 = sp - BitVec.ofNat 64 544 := by bv_arith
  rw [e1, e2, sepConj_comm]

private theorem stackAt_pkX_eq_nfs_aux (sp : BitVec 64) :
    stackAt sp publicKeySerializeStackX =
      stackAt sp newFromSliceStack ∗ memRegion (sp - 16416#64) 15872 := by
  simp only [stackAt, publicKeySerializeStackX, extHookStack, newFromSliceStack]
  rw [show (2 ^ 14 + 32 : Nat) = 15872 + 544 by decide,
    memRegion_split _ 15872 544 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (15872 + 544) = sp - 16416#64 := by bv_arith
  have e2 : sp - 16416#64 + BitVec.ofNat 64 15872 = sp - BitVec.ofNat 64 544 := by bv_arith
  rw [e1, e2, sepConj_comm]

theorem newFromSlice_placed_budget_ok [LibsignalPlacement] (C : Crypto)
    {prog : Program} {addr : BitVec 64}
    (hnew : subroutine_ok prog addr (withLsCodeLoaded lsmpl (newFromSliceBudgetSpec C.F))) :
    subroutine_ok prog addr
      ((newFromSlicePkStackBudgetSpec C.F).withLsClState
        (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem)) := by
  have hnew' := subroutine_ok_withLsClState_of_lscl hnew
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome hnew' x (memRegion (s0.sp - 4128#64) 3584 ∗ R) s0 hpc hrun
    (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec,
      newFromSlicePkStackBudgetSpec, newFromSlicePkStackBudgetSpecAt,
      stackAt_pk_eq_nfs_aux, sepConj_assoc] using hpre) hsp fun sf hraw => ?_
  rcases hraw with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withLsClState, newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec,
      newFromSlicePkStackBudgetSpec, newFromSlicePkStackBudgetSpecAt,
      stackAt_pk_eq_nfs_aux, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hpan)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hex)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hoom)).elim

theorem newFromSlice_placed_budget_ok_x [LibsignalPlacement] (C : Crypto)
    {prog : Program} {addr : BitVec 64}
    (hnew : subroutine_ok prog addr (withLsCodeLoaded lsmpl (newFromSliceBudgetSpec C.F))) :
    subroutine_ok prog addr
      ((newFromSlicePkStackBudgetSpecX C.F).withLsClState
        (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem)) := by
  have hnew' := subroutine_ok_withLsClState_of_lscl hnew
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome hnew' x (memRegion (s0.sp - 16416#64) 15872 ∗ R) s0 hpc hrun
    (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec,
      newFromSlicePkStackBudgetSpecX, newFromSlicePkStackBudgetSpecAt,
      stackAt_pkX_eq_nfs_aux, sepConj_assoc] using hpre) hsp fun sf hraw => ?_
  rcases hraw with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withLsClState, newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec,
      newFromSlicePkStackBudgetSpecX, newFromSlicePkStackBudgetSpecAt,
      stackAt_pkX_eq_nfs_aux, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hpan)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hex)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hoom)).elim

theorem newFromSlice_placed_cro_budget_ok [LibsignalPlacement] (C : Crypto)
    {prog : Program} {addr : BitVec 64}
    (hnew : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec C.F))) :
    subroutine_ok prog addr
      ((newFromSlicePkStackBudgetSpec C.F).withLsClState
        (LsClState := fun s => LibsignalCodeRoLoaded lsmpl s.mem)) := by
  have hnew' := subroutine_ok_withLsClState_of_lscro hnew
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome hnew' x (memRegion (s0.sp - 4128#64) 3584 ∗ R) s0 hpc hrun
    (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec,
      newFromSlicePkStackBudgetSpec, newFromSlicePkStackBudgetSpecAt,
      stackAt_pk_eq_nfs_aux, sepConj_assoc] using hpre) hsp fun sf hraw => ?_
  rcases hraw with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withLsClState, newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec,
      newFromSlicePkStackBudgetSpec, newFromSlicePkStackBudgetSpecAt,
      stackAt_pk_eq_nfs_aux, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hpan)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hex)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [Spec.withLsClState, newFromSliceBudgetSpec,
      withVmPreserved, newFromSliceSpec, sepConj_assoc] using hoom)).elim

def session2MemcpyPkStackBudgetSpecAt (pkStack : Nat) (sp_cur : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      s0.sp = sp_cur⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt sp_cur pkStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt sp_cur pkStack

def session2Compress256BudgetSpec (F : ShaCompress) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := (session2Compress256Spec F).pre
  post := fun (stA, st, blkA, blk, _n) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (stA ↦ₛ shaStateBytes ((chunks64 blk).foldl F st)) ∗ (blkA ↦ₛ blk)

theorem session2Compress256Budget_of_compress256Budget {F : ShaCompress}
    {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr (compress256BudgetSpec F)) :
    subroutine_ok prog addr (session2Compress256BudgetSpec F) := by
  refine subroutine_ok_outcome_intro fun ⟨stA, st, blkA, blk, n⟩ R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h (stA, st, blkA, blk, n) R s0 hpc hrun
    (by simpa only [compress256BudgetSpec, withVmPreserved, compress256Spec,
      session2Compress256BudgetSpec, session2Compress256Spec, sepConj_assoc] using hpre)
    hsp fun sf hraw => ?_
  rcases hraw with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [compress256BudgetSpec, withVmPreserved, compress256Spec,
      session2Compress256BudgetSpec, session2Compress256Spec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl (by simpa only [compress256BudgetSpec, withVmPreserved,
      compress256Spec, session2Compress256BudgetSpec] using hpan))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [compress256BudgetSpec, withVmPreserved,
      compress256Spec, session2Compress256BudgetSpec] using hex)))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [compress256BudgetSpec, withVmPreserved,
      compress256Spec, session2Compress256BudgetSpec] using hoom)))

def session2Compress256PkStackBudgetSpecAt (F : ShaCompress) (pkStack : Nat) (sp_cur : BitVec 64) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, blk, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧
      (s0.readReg64 .x2).toNat = n ∧ blk.length = 64 * n ∧ s0.sp = sp_cur⌝ ∗
      (stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ₛ blk) ∗ stackAt sp_cur pkStack
  post := fun (stA, st, blkA, blk, _n) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (stA ↦ₛ shaStateBytes ((chunks64 blk).foldl F st)) ∗ (blkA ↦ₛ blk) ∗
      stackAt sp_cur pkStack

def session2MemsetBudgetSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := session2MemsetSpec.pre
  post := fun (dst, val, n) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ List.replicate n val)

theorem session2MemsetBudget_of_sessionMemsetRegionBudget {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr sessionMemsetRegionBudgetSpec) :
    subroutine_ok prog addr session2MemsetBudgetSpec := by
  refine subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [session2MemsetBudgetSpec, session2MemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hpre' : s0.mem ⊨ sessionMemsetRegionBudgetSpec.pre (dst, val, n) s0 ∗ R := by
    simp only [sessionMemsetRegionBudgetSpec, sessionMemsetRegionSpec,
      ProofLib.memsetRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, ?_, hx2, by rw [← hx2]; exact Nat.le_of_lt (s0.readReg64 .x2).isLt⟩, hmem⟩
    rw [← hx1]; dsimp [State.readReg32]; bv_bits
  refine subroutine_ok.mono_outcome h (dst, val, n) R s0 hpc hrun hpre' hsp fun sf hraw => ?_
  rcases hraw with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [sessionMemsetRegionBudgetSpec, sessionMemsetRegionSpec,
      ProofLib.memsetRegionSpec, session2MemsetBudgetSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl (by simpa only [sessionMemsetRegionBudgetSpec, withVmPreserved,
      sessionMemsetRegionSpec, ProofLib.memsetRegionSpec, session2MemsetBudgetSpec] using hpan))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [sessionMemsetRegionBudgetSpec, withVmPreserved,
      sessionMemsetRegionSpec, ProofLib.memsetRegionSpec, session2MemsetBudgetSpec] using hex)))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [sessionMemsetRegionBudgetSpec, withVmPreserved,
      sessionMemsetRegionSpec, ProofLib.memsetRegionSpec, session2MemsetBudgetSpec] using hoom)))

def session2MemsetPkStackBudgetSpecAt (pkStack : Nat) (sp_cur : BitVec 64) :
    Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (dst, val, n) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ (s0.readReg64 .x1).truncate 8 = val ∧
      (s0.readReg64 .x2).toNat = n ∧ s0.sp = sp_cur⌝ ∗
      memRegion dst n ∗ stackAt sp_cur pkStack
  post := fun (dst, val, n) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ List.replicate n val) ∗ stackAt sp_cur pkStack

/-! ## Budget `PublicKey::serialize` and `__rust_dealloc` helpers -/

def publicKeySerializeBudgetSpecAt (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (pkStack : Nat) : Spec (PublicKeySerializeCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ FitsEnv M lim st PublicKeySerializeEnv⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool lim st s ∗ stackAt s.sp pkStack
  post := fun (x, st) s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A.repAlloc (sf.readReg64 .x0) x.pk.serialize ∗
      A.pool lim (M.stepEvents publicKeySerializeEvents st) sf ∗ stackAt s0.sp pkStack

def publicKeySerializeSpecKeepPlacedBudgetAt {LsClState : State → Prop}
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (pkStack : Nat) :
    Spec (PublicKeySerializeCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜(LsClState s ∧ LsSymState) ∧ s.readReg64 .x0 = x.self ∧
      FitsEnv M lim st PublicKeySerializeEnv⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool lim st s ∗ stackAt s.sp pkStack
  post := fun (x, st) s0 sf =>
    ⌜LsClState sf ∧ LsSymState⌝ ∗
      (publicKeySerializeBudgetSpecAt M A lim pkStack).post (x, st) s0 sf
  onPanic := (publicKeySerializeBudgetSpecAt M A lim pkStack).onPanic
  onExit := (publicKeySerializeBudgetSpecAt M A lim pkStack).onExit
  onOom := (publicKeySerializeBudgetSpecAt M A lim pkStack).onOom

theorem publicKeySerializeKeepPlacedBudgetAt_of_lscl {LsClState : State → Prop}
    [hInv : LsClInv LsClState] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {pkStack : Nat}
    (h : subroutine_ok prog entry
      ((publicKeySerializeBudgetSpecAt M A lim pkStack).withLsClState (LsClState := LsClState))) :
    subroutine_ok prog entry
      (publicKeySerializeSpecKeepPlacedBudgetAt (LsClState := LsClState) M A lim pkStack) := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp hcode => ?_
  have hpre' : s0.mem ⊨
      ((publicKeySerializeBudgetSpecAt M A lim pkStack).withLsClState
        (LsClState := LsClState)).pre (x, st) s0 ∗ R := by
    simp only [publicKeySerializeSpecKeepPlacedBudgetAt, Spec.withLsClState,
      publicKeySerializeBudgetSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩
  have hinv : LsClState s0 ∧ LsSymState := by
    simp only [Spec.withLsClState, publicKeySerializeBudgetSpecAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpre'
    exact hpre'.1
  obtain ⟨sf, hsteps, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome h (x, st) R s0 hpc hrun hpre' hsp hcode
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [publicKeySerializeSpecKeepPlacedBudgetAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hInv.of_keepsFrozen hinv.1 hsteps.keepsFrozen, trivial⟩, hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem call_pk_serialize_placed_budget_at {LsClState : State → Prop} [LsClInv LsClState]
    {prog : Program} {ret callee : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {pkStack : Nat}
    {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog callee
      ((publicKeySerializeBudgetSpecAt M A lim pkStack).withLsClState (LsClState := LsClState)))
    (ret_pc sp_cur keyA : BitVec 64) (key : PublicKey) (st : M.σ)
    (hfits : FitsEnv M lim st PublicKeySerializeEnv)
    (hP : P = ((keyA ↦ₛ key.bytes.toList) ∗ A.pool lim st s ∗
      stackAt sp_cur pkStack) ∗ F)
    (hside : LsClState s ∧ LsSymState ∧
      s.pc = callee ∧ s.status = .Running ∧ s.spAligned = true ∧
      s.sp = sp_cur ∧ s.readReg64 Reg.lr = ret_pc ∧ s.trace = s0.trace ∧
      s.readReg64 (Reg.gpr 0#5) = keyA)
    (hnext : ∀ (sf : State),
      LsClState sf → LsSymState →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_cur → RegsSaved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 → sf.readReg64 (Reg.gpr 1#5) = 33#64 →
      sf.trace = s0.trace →
      SepWPp prog ret sf
        ((keyA ↦ₛ key.bytes.toList) ∗
          A.repAlloc.live (sf.readReg64 (Reg.gpr 0#5)) key.serialize.length 1 ∗
          (sf.readReg64 (Reg.gpr 0#5) ↦ₛ key.serialize) ∗
          A.pool lim (M.stepEvents publicKeySerializeEvents st) sf ∗
          stackAt sp_cur pkStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)) := by
  rcases hside with ⟨hF_s, hsym_s, hpc, hrun, hsp, hsp_cur, hlr, htr, hφ⟩
  have hφ' : (LsClState s ∧ LsSymState) ∧ s.readReg64 (Reg.gpr 0#5) = keyA ∧
      FitsEnv M lim st PublicKeySerializeEnv :=
    ⟨⟨hF_s, hsym_s⟩, hφ, hfits⟩
  refine SepWPp.call_frame (x := (⟨keyA, key⟩, st))
    (publicKeySerializeKeepPlacedBudgetAt_of_lscl hcall) hpc hrun hsp hlr
    (by simp only [publicKeySerializeSpecKeepPlacedBudgetAt,
      publicKeySerializeBudgetSpecAt, hsp_cur, Reg.x0])
    hφ' hP
    (fun sf code R' _ hm => by
      dsimp only [publicKeySerializeSpecKeepPlacedBudgetAt, publicKeySerializeBudgetSpecAt] at hm
      exact not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      dsimp only [publicKeySerializeSpecKeepPlacedBudgetAt, publicKeySerializeBudgetSpecAt] at hm
      rw [sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    (fun sf hpcm hrunm hspm hcsm => ?_)
  have hne : key.serialize ≠ [] := by simp [PublicKey.serialize]
  conv =>
    arg 4
    simp only [publicKeySerializeSpecKeepPlacedBudgetAt, publicKeySerializeBudgetSpecAt,
      boxU8Buf, hne, ite_false, hsp_cur, Reg.x0, Reg.x1, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hF_sf, hsym_sf⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hx1, htr'⟩ => ?_
  conv =>
    arg 4
    rw [sepConj_left_comm (keyA ↦ₛ key.bytes.toList)]
  refine SepWPp.pure_elim fun ⟨hx0, _⟩ => ?_
  exact hnext sf hF_sf hsym_sf hpcm hrunm (hspm.trans hsp_cur)
    (regsSaved_of_calleeSavedPreserved hcsm) hx0 hx1 (htr'.trans htr)

open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

def rustDeallocPkStackBudgetSpecAt [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (pkStack : Nat) :
    Spec ((BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((p, bs), st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = 1 ∧
      bs.length = 33 ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.repAlloc.live p bs.length 1 ∗ (p ↦ₛ bs) ∗ stackAt s.sp pkStack
  post := fun ((_, _), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents 33 1) st) sf ∗ stackAt s0.sp pkStack

theorem dealloc_pkStack_placed_budget_ok [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {pkStack : Nat}
    (hdeel : subroutine_ok prog addr (rustDeallocExternSpecWithStack M A lim pkStack)) :
    subroutine_ok prog addr (rustDeallocPkStackBudgetSpecAt M A lim pkStack) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨p, bs⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [rustDeallocPkStackBudgetSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs, hlr⟩, hmem⟩
  rw [hbs] at hx1 hmem
  have hpre' : s0.mem ⊨
      (rustDeallocExternSpecWithStack M A lim pkStack).pre (p, 33, 1, st) s0 ∗ R := by
    simp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    have hlay : RustLayoutOk 33 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
    refine ⟨⟨hx0, hx1, hx2, hlay, hlr⟩, ?_⟩
    have hm : s0.mem ⊨ (p ↦ₛ bs) ∗
        (A.pool lim st s0 ∗ A.repAlloc.live p 33 1 ∗ stackAt s0.sp pkStack ∗ R) := by
      refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hmem
      sep_ac_rfl
    have hm2 := Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion p bs)) hm
    rw [hbs] at hm2
    refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hm2
    sep_ac_rfl
  refine subroutine_ok.mono_outcome hdeel (p, 33, 1, st) R s0 hpc hrun hpre' hsp fun sf hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
    rustDeallocPkStackBudgetSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

/-! ## Representation, stack-framing, and pool-sync helpers -/

theorem hmacStateAt_eq_words64_aux (a : BitVec 64) (innerSt : ShaState) (nBlocks : Nat)
    (outerSt : ShaState) (tail : List (BitVec 8)) :
    hmacStateAt a innerSt nBlocks outerSt tail =
      ∃∗ pad : List (BitVec 8),
        ⌜tail.length < 64 ∧ pad.length = 63 - tail.length⌝ ∗
        hmacWords64At a innerSt nBlocks outerSt tail pad := by
  unfold hmacStateAt
  rw [memRegion_eq_exists_bytes (a + BitVec.ofNat 64 tail.length) (63 - tail.length) (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun pad => ?_)
  have hlhs :
      ⌜tail.length < 64⌝ ∗ (a ↦ₛ tail) ∗
        (⌜pad.length = 63 - tail.length⌝ ∗ ((a + BitVec.ofNat 64 tail.length) ↦ₛ pad)) ∗
        ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
        ((a + 0x40#64) ↦ₛ shaStateBytes innerSt) ∗
        ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
        ((a + 0x68#64) ↦ₛ shaStateBytes outerSt) ∗
        ((a + 0x88#64) ↦₆₄ 1#64) =
      ⌜tail.length < 64⌝ ∗ ⌜pad.length = 63 - tail.length⌝ ∗
        ((a ↦ₛ tail) ∗ ((a + BitVec.ofNat 64 tail.length) ↦ₛ pad) ∗
          ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
          ((a + 0x40#64) ↦ₛ shaStateBytes innerSt) ∗
          ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
          ((a + 0x68#64) ↦ₛ shaStateBytes outerSt) ∗
          ((a + 0x88#64) ↦₆₄ 1#64)) := by sep_ac_rfl
  rw [hlhs, pure_sepConj, pure_sepConj, pure_sepConj]
  ext h
  refine ⟨fun ⟨ht, hp, hm⟩ => ⟨⟨ht, hp⟩, ?_⟩, fun ⟨⟨ht, hp⟩, hm⟩ => ⟨ht, hp, ?_⟩⟩
  · rwa [hmacWords64At_eq a innerSt nBlocks outerSt ht hp]
  · rwa [← hmacWords64At_eq a innerSt nBlocks outerSt ht hp]

theorem hmacCoreAt_nil_eq_words64_aux (F : ShaCompress) (a : BitVec 64)
    (key : List (BitVec 8)) :
    hmacCoreAt F a key [] =
      ∃∗ pad : { l : List (BitVec 8) // l.length = 63 },
        hmacWords64At a (hmacInnerInit F key) 1 (hmacOuterInit F key) [] pad.1 := by
  rw [hmacCoreAt, hmacStateAt_eq_words64_aux]
  simp only [List.length_nil, Nat.sub_zero]
  exact ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun pad =>
      Entails.pure_left fun ⟨_, hp⟩ =>
        Entails.sepExists_right ⟨pad, hp⟩ (Entails.refl _))
    (Entails.sepExists_elim fun ⟨pad, hp⟩ =>
      Entails.sepExists_right pad (Entails.pure_right ⟨by decide, hp⟩ (Entails.refl _)))

theorem hmacStateAt_eq_words64_sub_aux (a : BitVec 64) (innerSt : ShaState) (nBlocks : Nat)
    (outerSt : ShaState) (tail : List (BitVec 8)) (ht : tail.length < 64) :
    hmacStateAt a innerSt nBlocks outerSt tail =
      ∃∗ pad : { l : List (BitVec 8) // l.length = 63 - tail.length },
        hmacWords64At a innerSt nBlocks outerSt tail pad.1 := by
  rw [hmacStateAt_eq_words64_aux]
  exact ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun pad =>
      Entails.pure_left fun ⟨_, hp⟩ =>
        Entails.sepExists_right ⟨pad, hp⟩ (Entails.refl _))
    (Entails.sepExists_elim fun ⟨pad, hp⟩ =>
      Entails.sepExists_right pad (Entails.pure_right ⟨ht, hp⟩ (Entails.refl _)))

theorem keyToBytes32_length_aux (k : BitVec 256) :
    (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

theorem toBEBytes_len_aux {w : Nat} (n : Nat) (x : BitVec w) :
    (toBEBytes n x).length = n := by
  simp [toBEBytes]

theorem framelessMemcpyBudget_of_sessionMemcpyRegionBudget {prog : Program}
    {addr : BitVec 64}
    (h : subroutine_ok prog addr sessionMemcpyRegionBudgetSpec) :
    subroutine_ok prog addr framelessMemcpyBudgetSpec := by
  refine subroutine_ok_mono h ?_ ?_
  · rintro ⟨dst, src, bs⟩ R s0 hp
    dsimp only [framelessMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, ProofLib.memcpyRegionSpec] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · rintro ⟨dst, src, bs⟩ R s0 sf hq
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      ProofLib.memcpyRegionSpec, framelessMemcpyBudgetSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩

theorem memcpy_pkStack_placed_budget_ok {LsClState : State → Prop}
    {prog : Program} {addr : BitVec 64} {pkStack : Nat} (sp_cur : BitVec 64)
    (hmemcpy : subroutine_ok prog addr framelessMemcpyBudgetSpec) :
    subroutine_ok prog addr
      ((session2MemcpyPkStackBudgetSpecAt pkStack sp_cur).withLsClState
        (LsClState := LsClState)) :=
  subroutine_ok_withLsClState_of_plain
    (subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => by
      simp only [session2MemcpyPkStackBudgetSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
      refine subroutine_ok.mono_outcome hmemcpy (dst, src, bs) (stackAt sp_cur pkStack ∗ R) s0
        hpc hrun
        (by simpa only [framelessMemcpyBudgetSpec, sepConj_assoc, satisfies_pure_sepConj]
          using ⟨⟨hx0, hx1, hx2⟩, hmem⟩) hsp fun _ hraw => ?_
      unfold SubroutineOutcome at hraw ⊢
      simpa only [framelessMemcpyBudgetSpec, session2MemcpyPkStackBudgetSpecAt,
        satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw)

theorem compress256_pkStack_placed_budget_ok {LsClState : State → Prop}
    {prog : Program} {addr : BitVec 64} {F : ShaCompress} {pkStack : Nat} (sp_cur : BitVec 64)
    (hcompress : subroutine_ok prog addr (session2Compress256BudgetSpec F)) :
    subroutine_ok prog addr
      ((session2Compress256PkStackBudgetSpecAt F pkStack sp_cur).withLsClState
        (LsClState := LsClState)) :=
  subroutine_ok_withLsClState_of_plain
    (subroutine_ok_outcome_intro fun ⟨stA, st, blkA, blk, n⟩ R s0 hpc hrun hpre hsp => by
      simp only [session2Compress256PkStackBudgetSpecAt, sepConj_assoc, satisfies_pure_sepConj]
        at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hblk, _⟩, hmem⟩
      refine subroutine_ok.mono_outcome hcompress (stA, st, blkA, blk, n)
        (stackAt sp_cur pkStack ∗ R) s0 hpc hrun
        (by simpa only [session2Compress256BudgetSpec, session2Compress256Spec,
          sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2, hblk⟩, hmem⟩)
        hsp fun _ hraw => ?_
      unfold SubroutineOutcome at hraw ⊢
      simpa only [session2Compress256BudgetSpec, session2Compress256PkStackBudgetSpecAt,
        satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw)

theorem memset_pkStack_placed_budget_ok {LsClState : State → Prop}
    {prog : Program} {addr : BitVec 64} {pkStack : Nat} (sp_cur : BitVec 64)
    (hmemset' : subroutine_ok prog addr session2MemsetBudgetSpec) :
    subroutine_ok prog addr
      ((session2MemsetPkStackBudgetSpecAt pkStack sp_cur).withLsClState
        (LsClState := LsClState)) :=
  subroutine_ok_withLsClState_of_plain
    (subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => by
      simp only [session2MemsetPkStackBudgetSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
      refine subroutine_ok.mono_outcome hmemset' (dst, val, n) (stackAt sp_cur pkStack ∗ R) s0
        hpc hrun
        (by simpa only [session2MemsetBudgetSpec, session2MemsetSpec,
          sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2⟩, hmem⟩)
        hsp fun _ hraw => ?_
      unfold SubroutineOutcome at hraw ⊢
      simpa only [session2MemsetBudgetSpec, session2MemsetPkStackBudgetSpecAt,
        satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw)

theorem rewrap_compress256_lscl {LsClState : State → Prop}
    {prog : Program} {addr : BitVec 64} {F : ShaCompress} {pkStack : Nat} {sp_cur : BitVec 64}
    (h : subroutine_ok prog addr
      ({ pre := fun (x : BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) s =>
          ⌜(LsClState s ∧ LsSymState) ∧
              s.readReg64 (Reg.gpr 0#5) = x.1 ∧
              s.readReg64 (Reg.gpr 1#5) = x.2.2.1 ∧
              (s.readReg64 (Reg.gpr 2#5)).toNat = x.2.2.2.2 ∧
              x.2.2.2.1.length = 64 * x.2.2.2.2 ∧ s.sp = sp_cur⌝ ∗
            x.1 ↦ₛ shaStateBytes x.2.1 ∗ x.2.2.1 ↦ₛ x.2.2.2.1 ∗ stackAt sp_cur pkStack
         post := fun x s0 sf =>
          ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
            x.1 ↦ₛ shaStateBytes (List.foldl F x.2.1 (chunks64 x.2.2.2.1)) ∗
            x.2.2.1 ↦ₛ x.2.2.2.1 ∗ stackAt sp_cur pkStack } :
        Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat))) :
    subroutine_ok prog addr
      ((session2Compress256PkStackBudgetSpecAt F pkStack sp_cur).withLsClState
        (LsClState := LsClState)) := by
  refine subroutine_ok_outcome_intro fun ⟨stA, st, blkA, blk, n⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withLsClState, session2Compress256PkStackBudgetSpecAt,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hLs, hregs, hmem⟩
  refine subroutine_ok.mono_outcome h (stA, st, blkA, blk, n) R s0 hpc hrun
    (by simpa only [sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hLs, hregs⟩, hmem⟩) hsp
    fun _ hout => ?_
  unfold SubroutineOutcome at hout ⊢
  simpa only [Spec.withLsClState, session2Compress256PkStackBudgetSpecAt] using hout

theorem rewrap_memset_lscl {LsClState : State → Prop}
    {prog : Program} {addr : BitVec 64} {pkStack : Nat} {sp_cur : BitVec 64}
    (h : subroutine_ok prog addr
      ({ pre := fun (x : BitVec 64 × BitVec 8 × Nat) s =>
          ⌜(LsClState s ∧ LsSymState) ∧
              s.readReg64 (Reg.gpr 0#5) = x.1 ∧
              BitVec.truncate 8 (s.readReg64 (Reg.gpr 1#5)) = x.2.1 ∧
              (s.readReg64 (Reg.gpr 2#5)).toNat = x.2.2 ∧ s.sp = sp_cur⌝ ∗
            memRegion x.1 x.2.2 ∗ stackAt sp_cur pkStack
         post := fun x s0 sf =>
          ⌜sf.readReg64 (Reg.gpr 0#5) = x.1 ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
            x.1 ↦ₛ List.replicate x.2.2 x.2.1 ∗ stackAt sp_cur pkStack } :
        Spec (BitVec 64 × BitVec 8 × Nat))) :
    subroutine_ok prog addr
      ((session2MemsetPkStackBudgetSpecAt pkStack sp_cur).withLsClState
        (LsClState := LsClState)) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withLsClState, session2MemsetPkStackBudgetSpecAt,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hLs, hregs, hmem⟩
  refine subroutine_ok.mono_outcome h (dst, val, n) R s0 hpc hrun
    (by simpa only [sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hLs, hregs⟩, hmem⟩) hsp
    fun _ hout => ?_
  unfold SubroutineOutcome at hout ⊢
  simpa only [Spec.withLsClState, session2MemsetPkStackBudgetSpecAt] using hout

public meta section

open Lean Meta Elab Tactic in
/-- Normalize nested `State.setMem` and transport `A.pool lim st s_call` to `A.pool lim st sf`
inside a `SepWP` or `SepWPp` goal using the most recent `VmPreserved` postcondition hypothesis. -/
elab "sync_call_pool" : tactic => do
  evalTactic (← `(tactic| try simp only [Arm64.State.setMem_setMem] at *))
  let g ← getMainGoal
  g.withContext do
    let gTy := (← instantiateMVars (← g.getType)).consumeMData
    let isWpp := gTy.isAppOfArity ``ProofLib.SepWPp 7
    let gState := (gTy.getArg! 2).consumeMData
    for decl in (← getLCtx).decls.toList.reverse do
      if let some d := decl then
        if !d.isImplementationDetail then
          let ty := (← instantiateMVars d.type).consumeMData
          let id := mkIdent d.userName
          if ty.isAppOfArity ``LibsignalBinary.Heap.VmPreserved 2 then
            if ← isDefEq (ty.getArg! 1) gState then
              if isWpp then
                evalTactic (← `(tactic|
                  refine ProofLib.SepWPp.transport_budgetPool $id (hnext := ?_)))
              else
                evalTactic (← `(tactic|
                  refine ProofLib.SepWP.transport_budgetPool $id (hnext := ?_)))
              return
          else if ty.isAppOfArity ``And 2 then
            let r1 := (ty.getArg! 1).consumeMData
            if r1.isAppOfArity ``LibsignalBinary.Heap.VmPreserved 2 then
              if ← isDefEq (r1.getArg! 1) gState then
                if isWpp then
                  evalTactic (← `(tactic| (
                    have := ($id).1
                    refine ProofLib.SepWPp.transport_budgetPool ($id).2 (hnext := ?_))))
                else
                  evalTactic (← `(tactic| (
                    have := ($id).1
                    refine ProofLib.SepWP.transport_budgetPool ($id).2 (hnext := ?_))))
                return
            else if r1.isAppOfArity ``And 2 then
              let r2 := (r1.getArg! 1).consumeMData
              if r2.isAppOfArity ``LibsignalBinary.Heap.VmPreserved 2 then
                if ← isDefEq (r2.getArg! 1) gState then
                  if isWpp then
                    evalTactic (← `(tactic| (
                      have := ($id).1
                      have := ($id).2.1
                      refine ProofLib.SepWPp.transport_budgetPool ($id).2.2 (hnext := ?_))))
                  else
                    evalTactic (← `(tactic| (
                      have := ($id).1
                      have := ($id).2.1
                      refine ProofLib.SepWP.transport_budgetPool ($id).2.2 (hnext := ?_))))
                  return
    throwError "sync_call_pool: no VmPreserved hypothesis found in context"

end

end LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux
