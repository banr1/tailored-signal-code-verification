/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1Budget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Shared Budget & `VmPreserved` Combinators for `EpochDirection::encode` (`[local#1, 2]`)

Provides `VecU8ReserveChain` / `VecU8EncodeEnv` step combinators, the `noAllocEnforcedLimits` /
`withVmAnchor` zero-allocation `VmPreserved` anchor, and core-to-full / exact-capacity bridges
for `EpochDirection::encode` (`Blocks 154 & 317`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionAuxBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement blkPl_148 blkPl_292 lsProg_148 lsProg_292 lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost StepInvPlaced)
open CryptoVerification.SpqrV1.Auth (authEncodeStackOf)
open CryptoVerification.SpqrV1.ProtoRepr (epochDirectionPBPinnedAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodeEpochDirectionPinnedGhost encodeEpochDirectionMsg)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents RustCliAllocBudget
   VmPreserved rustAllocEvents rustReallocEvents zeroBudgetLimits fitsEvents_append)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (pushBytesStep pushBytesStep_snd_eq reserveStep reserveStep_of_need_doReserveEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8EncodeEnv VecU8ReserveChain fitsEnv_vecU8EncodeEnv_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (EncodeEpochDirectionPinnedEnv encodeEpochDirectionPinnedExactVmSpecOf
   encodeEpochDirectionPinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserve2SpecOf doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeVarintDetSpecOf vecU8ReserveChain_pushBytesStep vecU8ReserveChain_reserveStep)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1Budget
  (encodeVarint2_det_placed_ok_of_doReserve)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
  (encodeVarint4_det_placed_ok_of_doReserve)

/-! ## 1. `VmPreserved` Symmetry & `SepWPp` Placed Stepping Bridges -/

theorem vmPreserved_symm {s s' : State} (h : VmPreserved s s') : VmPreserved s' s :=
  h.symm

theorem sepWPp_of_sepWP_cs_placed_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext hvmp (StepInvPlaced.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem sepWP_done_tpidr_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    ProofLib.SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  ProofLib.SepWP.done hpc hrun ⟨htp, hpost⟩

/-! ## 2. `VecU8ReserveChain` / `VecU8EncodeEnv` Step Combinators -/

theorem fitsEvents_and_step_of_chain {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {c0 c1 finalLen : Nat} {evs : List AllocEvent}
    (hEnv : FitsEnv M lim st (VecU8EncodeEnv c0 finalLen))
    (hchain : VecU8ReserveChain c0 c1 finalLen evs) :
    FitsEvents M lim st evs ∧
      FitsEnv M lim (M.stepEvents evs st) (VecU8EncodeEnv c1 finalLen) := by
  refine ⟨hEnv evs ⟨c1, hchain⟩, ?_⟩
  rintro evs' ⟨cOut, hchain'⟩
  have htot := hEnv (evs ++ evs') ⟨cOut, hchain.trans (Nat.le_refl _) hchain'⟩
  exact ((fitsEvents_append M lim evs evs' st).mp htot).2

theorem vecU8ReserveChain_encodeVarint {val v curCap curPtr nextCap : BitVec 64}
    {curBs : List (BitVec 8)} {finalLen : Nat}
    (hle : curBs.length + (encodeVarint val).length ≤ finalLen)
    (hdet : nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1) :
    VecU8ReserveChain curCap.toNat nextCap.toNat finalLen
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) := by
  have hc := vecU8ReserveChain_pushBytesStep (encodeVarint val).length curCap.toNat curBs.length
    finalLen hle
  rw [← hdet, pushBytesStep_snd_eq] at hc
  exact hc

theorem fitsEvents_encodeVarint_of_env {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {val v curCap curPtr : BitVec 64} {curBs : List (BitVec 8)} {finalLen : Nat}
    (hEnv : FitsEnv M lim st (VecU8EncodeEnv curCap.toNat finalLen))
    (hle : curBs.length + (encodeVarint val).length ≤ finalLen) :
    FitsEvents M lim st (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) := by
  have hc := vecU8ReserveChain_pushBytesStep (encodeVarint val).length curCap.toNat curBs.length
    finalLen hle
  rw [pushBytesStep_snd_eq] at hc
  exact (fitsEvents_and_step_of_chain hEnv hc).1

theorem vecU8ReserveChain_doReserve (v curCap curPtr : BitVec 64)
    (curBs : List (BitVec 8)) (additional finalLen : Nat)
    (hneed : ¬ (curBs.length + additional ≤ curCap.toNat))
    (hle : curBs.length + additional ≤ finalLen)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63) :
    VecU8ReserveChain curCap.toNat
      (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)).toNat finalLen
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) := by
  have hc := vecU8ReserveChain_reserveStep (cap := curCap.toNat) (len := curBs.length)
    (additional := additional) (finalLen := finalLen) hle
  rw [reserveStep_of_need_doReserveEvents v curCap curPtr curBs additional hneed] at hc
  have htoNat : (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)).toNat =
      reserveCap curCap.toNat curBs.length additional := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rwa [htoNat]

/-! ## 3. Enforced Zero-Allocation Anchor (`noAllocEnforcedLimits` & `withVmAnchor`) -/

/-- Enforced `BudgetLimits` rejecting every allocation event (`staticBytes = 1 > physCap = 0`),
forcing `do_reserve_and_handle` preconditions to be vacuous while keeping `enforced = true`. -/
def noAllocEnforcedLimits : BudgetLimits :=
  { staticCount := 0, staticBytes := 1, physCap := 0, enforced := true }

theorem not_fitsEvent_noAllocEnforcedLimits (M : AllocCostModel) (st : M.σ) (ev : AllocEvent) :
    ¬ FitsEvent M noAllocEnforcedLimits st ev := by
  rintro ⟨_, _, hram, _⟩
  dsimp only [noAllocEnforcedLimits] at hram
  omega

theorem not_fitsEvents_doReserveEvents_noAllocEnforced (M : AllocCostModel) (st : M.σ)
    (x : DoReserveCall) :
    ¬ FitsEvents M noAllocEnforcedLimits st (doReserveEvents x) := by
  unfold doReserveEvents
  split_ifs
  · unfold rustAllocEvents
    dsimp only
    split_ifs <;> intro h <;> exact not_fitsEvent_noAllocEnforcedLimits M st _ h.1
  · unfold rustReallocEvents
    dsimp only
    split_ifs <;> intro h <;> exact not_fitsEvent_noAllocEnforcedLimits M st _ h.1

/-- Augment `A` with pure `⌜VmPreserved s₀ s⌝` when `lim.enforced = true`, reusing `A.live` and
`A.block_valid` directly. -/
def withVmAnchor {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim₀ : BudgetLimits) (s₀ : State) : RustCliAllocBudget M where
  pool := fun lim st s =>
    if lim.enforced then ⌜VmPreserved s₀ s⌝ ∗ A.pool lim₀ st s
    else A.pool zeroBudgetLimits st s
  live := A.live
  block_valid := A.block_valid
  pool_transport := by
    intro lim st s s' hvmp
    split_ifs with henf
    · have hp : (⌜VmPreserved s₀ s'⌝ : SepProp) = ⌜VmPreserved s₀ s⌝ :=
        congrArg SepProp.pure
          (propext ⟨fun h => h.trans (vmPreserved_symm hvmp), fun h => h.trans hvmp⟩)
      rw [hp, A.pool_transport lim₀ st s s' hvmp]
    · exact A.pool_transport zeroBudgetLimits st s s' hvmp
  pool_zero_transport := fun st s s' hpp => A.pool_zero_transport st s s' hpp

@[simp] theorem withVmAnchor_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim₀ : BudgetLimits) (s₀ : State) :
    (withVmAnchor A lim₀ s₀).repAlloc = A.repAlloc :=
  rfl

theorem withVmAnchor_pool_noAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim₀ : BudgetLimits) (s₀ : State) (st : M.σ) (s : State) :
    (withVmAnchor A lim₀ s₀).pool noAllocEnforcedLimits st s =
      (⌜VmPreserved s₀ s⌝ ∗ A.pool lim₀ st s) :=
  rfl

theorem doReserve2_noAllocEnforced_ok [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {fn_pc : BitVec 64} (A : RustCliAllocBudget M) :
    subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A noAllocEnforcedLimits)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 _ _ hpre _ => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  have hpre2 := hpre.2
  simp only [doReserve2SpecOf, sepConj_assoc, satisfies_pure_sepConj] at hpre2
  exact absurd ((fitsEnv_doReserve_iff x).mp hpre2.1.2.2.2.2)
    (not_fitsEvents_doReserveEvents_noAllocEnforced M st x)

theorem doReserve7_noAllocEnforced_ok [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {fn_pc : BitVec 64} (A : RustCliAllocBudget M) :
    subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A noAllocEnforcedLimits)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 _ _ hpre _ => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  have hpre2 := hpre.2
  simp only [doReserveSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hpre2
  exact absurd ((fitsEnv_doReserve_iff x).mp hpre2.1.2.2.2.2.2.2)
    (not_fitsEvents_doReserveEvents_noAllocEnforced M st x)

theorem encodeVarint2_det_noAllocEnforced_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_148 H) (blkPl_148).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A noAllocEnforcedLimits)) :=
  encodeVarint2_det_placed_ok_of_doReserve hres A noAllocEnforcedLimits H
    (doReserve2_noAllocEnforced_ok A)

theorem encodeVarint4_det_noAllocEnforced_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_292 H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A noAllocEnforcedLimits)) :=
  encodeVarint4_det_placed_ok_of_doReserve hres A noAllocEnforcedLimits H
    (doReserve7_noAllocEnforced_ok A)

/-! ## 4. Core-to-Full `encodeEpochDirectionPinnedSpecOf` & Exact-Capacity Bridges -/

/-- Core specification of `encode<EpochDirection>` (pinned) before strengthening the spare-capacity
postcondition with `VmPreserved s0 sf` via `withVmAnchor`. -/
def encodeEpochDirectionPinnedCoreSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeEpochDirectionPinnedGhost × M.σ) where
  pre := (encodeEpochDirectionPinnedSpecOf resStack A lim).pre
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜EncodeEpochDirectionPinnedEnv x evs ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            evs = [])⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

theorem subroutine_ok_encodeEpochDirectionPinned_of_core [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {fn_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hcore_full : subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedCoreSpecOf resStack A lim)))
    (hcore_spare : ∀ s0 : State, subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl
        (encodeEpochDirectionPinnedCoreSpecOf resStack (withVmAnchor A lim s0)
          noAllocEnforcedLimits))) :
    subroutine_ok prog fn_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hspare : x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat
  · have hpre_anchor : s0.mem ⊨
        (withLsCodeLoaded lsmpl
          (encodeEpochDirectionPinnedCoreSpecOf resStack (withVmAnchor A lim s0)
            noAllocEnforcedLimits)).pre (x, st) s0 ∗ R := by
      dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedCoreSpecOf,
        encodeEpochDirectionPinnedSpecOf] at hpre ⊢
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨hcl0, hpre⟩
      refine ⟨hcl0, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hw0, hx1, hx2, _, _⟩, hmem⟩
      refine ⟨⟨hw0, hx1, hx2, Or.inl hspare,
        fitsEnv_vecU8EncodeEnv_of_spare M noAllocEnforcedLimits st hspare⟩, ?_⟩
      rw [withVmAnchor_repAlloc, withVmAnchor_pool_noAlloc]
      have hmem' : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            (vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
              (A.pool lim st s0 ∗ (stackAt s0.sp (authEncodeStackOf resStack) ∗ R)))) := by
        rw [satisfies_pure_sepConj]
        exact ⟨VmPreserved.refl s0, hmem⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'
    refine (hcore_spare s0).mono_outcome (x, st) R s0 hpc hrun hpre_anchor hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedCoreSpecOf,
        encodeEpochDirectionPinnedSpecOf] at hq ⊢
      simp only [withVmAnchor_repAlloc, withVmAnchor_pool_noAlloc,
        sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨evs, cap', ptr', htr, hmem⟩
      have hmem_reord : sf.mem ⊨
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ⌜EncodeEpochDirectionPinnedEnv x evs ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              evs = [])⌝ ∗
          ⌜VmPreserved s0 sf⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_reord
      rcases hmem_reord with ⟨⟨hge, hpres⟩, ⟨hev, hnil⟩, hvmp, hmem_clean⟩
      have hev_nil : evs = [] := hnil hspare
      subst hev_nil
      simp only [AllocCostModel.stepEvents] at hmem_clean
      refine ⟨[], cap', ptr', htr, ?_⟩
      have hout_mem : sf.mem ⊨
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ⌜EncodeEpochDirectionPinnedEnv x [] ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              ([] : List AllocEvent) = [] ∧ VmPreserved s0 sf)⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
            A.pool lim st sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨⟨hge, hpres⟩, ⟨hev, fun _ => ⟨rfl, hvmp⟩⟩, hmem_clean⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hout_mem
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim
  · refine hcore_full.mono_outcome (x, st) R s0 hpc hrun hpre hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedCoreSpecOf,
        encodeEpochDirectionPinnedSpecOf] at hq ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨evs, cap', ptr', htr, hmem⟩
      have hmem_reord : sf.mem ⊨
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ⌜EncodeEpochDirectionPinnedEnv x evs ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              evs = [])⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_reord
      rcases hmem_reord with ⟨hcp, ⟨hev, _⟩, hmem_clean⟩
      refine ⟨evs, cap', ptr', htr, ?_⟩
      have hout_mem : sf.mem ⊨
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ⌜EncodeEpochDirectionPinnedEnv x evs ∧
            (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
              evs = [] ∧ VmPreserved s0 sf)⌝ ∗
          (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨hcp, ⟨hev, fun h => absurd h hspare⟩, hmem_clean⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hout_mem
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim

/-- Derive `encodeEpochDirectionPinnedExactVmSpecOf` (with `A.pool lim st s` in frame) from
`encodeEpochDirectionPinnedSpecOf` on spare-capacity inputs. -/
theorem subroutine_ok_encodeEpochDirectionPinnedExact_of_budget {resStack : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st : M.σ)
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (encodeEpochDirectionPinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry
      { pre := fun x s =>
          (encodeEpochDirectionPinnedExactVmSpecOf resStack A.repAlloc).pre x s ∗ A.pool lim st s
        post := fun x s0 sf =>
          (encodeEpochDirectionPinnedExactVmSpecOf resStack A.repAlloc).post x s0 sf ∗
            A.pool lim st sf } := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodeEpochDirectionPinnedExactVmSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hle⟩, hrest⟩
  have hEnv : FitsEnv M lim st (EncodeEpochDirectionPinnedEnv x) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hle
  have hpreB : s0.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [encodeEpochDirectionPinnedSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hx1, hx2, Or.inl hle, hEnv⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  refine h.mono_outcome (x, st) R s0 hpc hrun hpreB hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeEpochDirectionPinnedSpecOf] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨evs, cap', ptr', htr, hq_mem0⟩
    have hq_reord : sf.mem ⊨
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        ⌜EncodeEpochDirectionPinnedEnv x evs ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp (authEncodeStackOf resStack) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem0
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hq_reord
    rcases hq_reord with ⟨⟨_, hcp⟩, ⟨_, hev⟩, hq_mem⟩
    rcases hcp hle with ⟨rfl, rfl⟩
    rcases hev hle with ⟨rfl, hvm⟩
    simp only [AllocCostModel.stepEvents] at hq_mem
    dsimp only [encodeEpochDirectionPinnedExactVmSpecOf]
    have hgoal : sf.mem ⊨
        ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
        (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
         vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
         stackAt s0.sp (authEncodeStackOf resStack) ∗ A.pool lim st sf ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hvm, htr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionAuxBudget
