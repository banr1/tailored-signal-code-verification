/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetState
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionRecord::set_session_state` (Block `48`)

Verifies `<SessionRecord>::set_session_state` against `setSessionStateSpec M A lim` under
`[LibsignalPlacement]` over `RustCliAllocBudget M` across both `cur = none` (`evs = []`) and
`cur = some _` (`FreeOnlyEvs evs`) branches.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetStateBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey SessionState)
open CryptoVerification (
  LibsignalPlacement LibsignalCodeLoaded lsmpl
  blkPC_6 blkPl_6 blkPC_48 blkPl_48 lsρ lsMemcpySym
  ls_hook_ok_of_mem ls_subroutine_ok_of_block
  withLsCodeLoaded extract_withLsCodeLoaded
  subroutine_ok_withLsCodeLoaded_of_plain sepWP_seq_lscl
)
open CryptoVerification.RustHeap (RustAlloc vecAt vecHeader vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost noneCap optSenderChainAt optTailVecAt sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet (
  framelessMemcpySpec sessionMemcpyRegionSpec
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost SetSessionStateGhost
  dropSessionStructureLocal1Stack setSessionStateStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal1Spec setSessionStateSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Private Framing & Unfolding Helpers -/

private theorem stackAt_setSessionState (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := stackAt_split_cells sp dropSessionStructureLocal1Stack 4 (by decide)
  change stackAt sp setSessionStateStack =
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗ cells (sp - 32#64) 4 at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, hc4]
  simp only [sepExists_sepConj_right]

private theorem pointsTo64_memRegion_336_eq_344 (r : BitVec 64) :
    (∃∗ v : BitVec 64, ((r + 24#64) ↦₆₄ v)) ∗ memRegion (r + 32#64) 336 =
      memRegion (r + 24#64) 344 := by
  have h := memRegion_split (r + 24#64) 8 336 (by decide)
  have hadd : r + 24#64 + 8#64 = r + 32#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [show (8 + 336 : Nat) = 344 by rfl, hadd, memRegion_eight] at h
  exact h.symm

private theorem pointsTo64_memRegion_336_entails_344 (r v : BitVec 64) :
    ((r + 24#64) ↦₆₄ v) ∗ memRegion (r + 32#64) 336 ⊢ memRegion (r + 24#64) 344 := by
  rw [← pointsTo64_memRegion_336_eq_344 r]
  exact sepConj_mono_left (Entails.sepExists_intro v)

private theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht
  omega

private def vecGhostTailAt (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_unfold_cap (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt]
  sep_ac_rfl

private def sessionStateAfterLocalIk (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = Except.ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = Except.ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.remoteIk (ss + 24#64) ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 96#64) ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗
  optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 336#64) ↦ₛ G.regIds)

private theorem sessionStateAt_unfold_cap (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostTailAt A G.localIk ss ∗
      sessionStateAfterLocalIk A ss G st := by
  unfold sessionStateAt sessionStateAfterLocalIk
  rw [vecGhostAt_unfold_cap]
  sep_ac_rfl

private def dropSessionStructureLocal1HeadSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, stB) s =>
    ⌜s.readReg64 .x0 = x.ss ∧
      x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧
      x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt A.repAlloc x.G.localIk x.ss ∗
      sessionStateAfterLocalIk A.repAlloc x.ss x.G x.st ∗
      A.pool lim stB s ∗ stackAt s.sp dropSessionStructureLocal1Stack
  post := fun (x, stB) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs stB) sf ∗
        stackAt s0.sp dropSessionStructureLocal1Stack

private theorem drop_session_structure_local1_placed_head_at_state [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {s : State}
    (hdrop1 : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog entry
      { pre := fun (x, stB) s' =>
          ⌜s'.mem = s.mem ∧ s'.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s'.readReg64 .lr) ∧
            x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
            x.G.localIk.cap.toNat < 2 ^ 63 ∧
            x.G.localIk.ptr ≠ 0⌝ ∗
          (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt A.repAlloc x.G.localIk x.ss ∗
          sessionStateAfterLocalIk A.repAlloc x.ss x.G x.st ∗
          A.pool lim stB s' ∗ stackAt s'.sp dropSessionStructureLocal1Stack
        post := (dropSessionStructureLocal1HeadSpec M A lim).post } := by
  refine subroutine_ok_outcome_intro fun ⟨x, stB⟩ R s0 hpc hrun hm hsp => ?_
  refine hdrop1.mono_outcome (x, stB) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded, dropSessionStructureLocal1Spec] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hx0, hlr, hlen, hcap, hptr⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sessionStateAt_unfold_cap, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj]
  refine ⟨⟨hx0, hlr⟩, ?_⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hlen, hcap, hptr⟩, by simpa only [sepConj_assoc] using hspatial⟩

/-! ## 2. Relocatable `[LibsignalPlacement]` Budget Proofs (Block `48`) -/

def setSessionStateNoneSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((record, src, bs), stB) s =>
    ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
      ((record + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (record + 0x20#64) 336 ∗
      (src ↦ₛ bs) ∗ A.pool lim stB s ∗ stackAt s.sp setSessionStateStack
  post := fun ((record, src, bs), stB) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs ∧ evs = []⌝ ∗
        ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
        A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp setSessionStateStack

def setSessionStateSomeSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × SessionGhost × SessionState (List (BitVec 8)) × List (BitVec 8)) × M.σ) where
  pre := fun ((record, src, G, ss, bs), stB) s =>
    ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
      sessionStateAt A.repAlloc (record + 0x18#64) G ss ∗
      (src ↦ₛ bs) ∗ A.pool lim stB s ∗ stackAt s.sp setSessionStateStack
  post := fun ((record, src, _G, _ss, bs), stB) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
        A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp setSessionStateStack

theorem set_session_state_none_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hmemcpy_in : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsρ lsMemcpySym) (withVmPreserved framelessMemcpySpec)) :
    subroutine_ok ((blkPC_48).rebase (blkPl_48).base H) (blkPl_48).base
      (setSessionStateNoneSpec A lim) := by
  have hmemcpy := hmemcpy_in
  dsimp only [withVmPreserved, framelessMemcpySpec, memcpyRegionSpec] at hmemcpy
  refine subroutine_ok_of_sepWP fun ⟨⟨record, src, bs⟩, stB⟩ R s0 hpc hrun hpre hsp0 => ?_
  simp only [setSessionStateNoneSpec, noneCap, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hbs⟩, hmem⟩
  refine ⟨((record + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (record + 0x20#64) 336 ∗
    (src ↦ₛ bs) ∗ A.pool lim stB s0 ∗ stackAt s0.sp setSessionStateStack,
    R, by simpa [sepConj_assoc] using hmem, ?_⟩
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  refine SepWP.fold (pointsTo64_memRegion_336_entails_344 record 0xffffffffffffffff#64)
    (by sep_focus) ?_
  have h24 : record + 24#64 = record + 0x18#64 := rfl
  wp_simp_pre only [h24]
  wp_call hmemcpy (record + 0x18#64, src, bs)
  have htr_mc : sf.trace = s0.trace := by assumption
  have hsp_mc : sf.sp = s0.sp := by simp only [wp_norm, arm64_norm, *]
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  refine SepWP.done (by simp_all) (by simp_all) ⟨fun hm => ?_, ?_, ?_⟩
  · refine Satisfies.mono (sepConj_mono_left ?_) hm
    refine Entails.sepExists_right ([] : List AllocEvent) ?_
    refine Entails.pure_right ⟨htr_mc, by simp [FreeOnlyEvs], rfl⟩ ?_
    rw [M.stepEvents_nil]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [wp_norm, arm64_norm, *]
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

set_option maxHeartbeats 800000 in
theorem set_session_state_some_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hmemcpy_in : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsρ lsMemcpySym) (withVmPreserved framelessMemcpySpec))
    (hdrop1_in : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsmpl.base 6) (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim))) :
    subroutine_ok ((blkPC_48).rebase (blkPl_48).base H) (blkPl_48).base
      (withLsCodeLoaded lsmpl (setSessionStateSomeSpec A lim)) := by
  have hmemcpy := hmemcpy_in
  dsimp only [withVmPreserved, framelessMemcpySpec, memcpyRegionSpec] at hmemcpy
  refine subroutine_ok_of_sepWP fun ⟨⟨record, src, G, ss, bs⟩, stB⟩ R s0 hpc hrun hpre hsp0 => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [setSessionStateSomeSpec, sessionStateAt_unfold_cap,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hbs⟩, ⟨hlen, hcap, hptr⟩, hmem⟩
  refine ⟨((record + 0x18#64) ↦₆₄ G.localIk.cap) ∗
    vecGhostTailAt A.repAlloc G.localIk (record + 0x18#64) ∗
    sessionStateAfterLocalIk A.repAlloc (record + 0x18#64) G ss ∗
    (src ↦ₛ bs) ∗ A.pool lim stB s0 ∗ stackAt s0.sp setSessionStateStack,
    R, by simpa [sepConj_assoc] using hmem, ?_⟩
  rw [stackAt_setSessionState s0.sp]
  simp only [sepExists_sepConj_right]
  refine SepWP.exists_elim fun v0 => SepWP.exists_elim fun v1 =>
    SepWP.exists_elim fun v2 => SepWP.exists_elim fun v3 => ?_
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap
  apply sepWP_seq_lscl (mid := lsmpl.base 6) hcl0
  wp_steps_sync_pool (lsmpl.base 6)
  simp only [State.setMem_setMem]
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl1
  have hdrop1 := drop_session_structure_local1_placed_head_at_state hdrop1_in hcl1
  dsimp only [dropSessionStructureLocal1HeadSpec] at hdrop1
  wp_call hdrop1 (⟨record + 0x18#64, G, ss⟩, stB)
  have htr_dr : sf.trace = s0.trace := by assumption
  have hfree : FreeOnlyEvs w := by assumption
  have hsp_dr : sf.sp = s0.sp - 32#64 := by simp only [wp_norm, arm64_norm, *]
  wp_simp_pre only [hsp_dr]
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  wp_call hmemcpy (record + 0x18#64, src, bs)
  have htr_mc : sf_1.trace = sf.trace := by assumption
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  refine SepWP.done (by simp_all) (by simp_all) ⟨fun hm => ?_, ?_, ?_⟩
  · refine Satisfies.mono (sepConj_mono_left ?_) hm
    refine Entails.sepExists_right w ?_
    refine Entails.pure_right ⟨htr_mc.trans htr_dr, hfree⟩ ?_
    rw [stackAt_setSessionState s0.sp]
    have hstk :
        stackAt (s0.sp - 32#64) dropSessionStructureLocal1Stack ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19) ⊢
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          stackAt (s0.sp - 32#64) dropSessionStructureLocal1Stack ∗
          ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
          ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) :=
      Entails.sepExists_right (s0.readReg64 Reg.x29)
        (Entails.sepExists_right (s0.readReg64 Reg.lr)
          (Entails.sepExists_right (s0.readReg64 Reg.x20)
            (Entails.sepExists_right (s0.readReg64 Reg.x19) (Entails.refl _))))
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk)))
    exact Entails.of_eq (by
      dsimp only [Reg.x19, Reg.x20, Reg.lr, Reg.x29]
      sep_ac_rfl)
  · simp only [wp_norm, arm64_norm, *]
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem set_session_state_placed_ok_of_memcpy [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsρ lsMemcpySym) (withVmPreserved sessionMemcpyRegionSpec))
    (hdrop1 : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsmpl.base 6) (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim))) :
    subroutine_ok ((blkPC_48).rebase (blkPl_48).base H) (blkPl_48).base
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) := by
  apply subroutine_ok_outcome_intro
  intro ⟨⟨record, src, cur, bs⟩, stB⟩ R s0 hpc hrun hpre hsp
  rcases cur with _ | ⟨G, ss⟩
  · have hnone := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (set_session_state_none_placed_ok (A := A) (lim := lim) hmemcpy)
    refine hnone.mono_outcome ((record, src, bs), stB) R s0 hpc hrun
      (by simpa only [withLsCodeLoaded, setSessionStateSpec, setSessionStateNoneSpec,
        sepConj_assoc] using hpre)
      hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, setSessionStateSpec]
      dsimp only [withLsCodeLoaded, setSessionStateNoneSpec] at hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1.1, hpost.1.2.1, fun _ => hpost.1.2.2⟩, hpost.2⟩
    · exact Or.inr hrest
  · refine (set_session_state_some_placed_ok hmemcpy hdrop1).mono_outcome
      ((record, src, G, ss, bs), stB) R s0 hpc hrun
      (by simpa only [withLsCodeLoaded, setSessionStateSpec, setSessionStateSomeSpec,
        sepConj_assoc] using hpre)
      hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, setSessionStateSpec]
      dsimp only [withLsCodeLoaded, setSessionStateSomeSpec] at hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1.1, hpost.1.2, fun h => nomatch h⟩, hpost.2⟩
    · exact Or.inr hrest

/-- Block `48`: `<SessionRecord>::set_session_state` meets `setSessionStateSpec M A lim`
    under `[LibsignalPlacement]`. -/
theorem set_session_state_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hmemcpy : HookSat H lsMemcpySym (withVmPreserved sessionMemcpyRegionSpec))
    (hdrop1 : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (blkPl_6).base (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim))) :
    subroutine_ok ((blkPC_48).rebase (blkPl_48).base H) (blkPl_48).base
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) :=
  set_session_state_placed_ok_of_memcpy
    (ls_hook_ok_of_mem hmemcpy)
    (ls_subroutine_ok_of_block hdrop1)

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetStateBudget
