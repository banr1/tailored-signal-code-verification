/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.PrologueSplit

/-!
# Budget-Threaded Prologue and Dispatch of `RatchetState::consume_message_key`

Proves `ProloguePastPlacedSpec`, `PrologueTooFarPlacedSpec`, and `PrologueAdvanceEntryPlacedSpec`
(Block 24) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.PrologueSplitBudget

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkLib_eq_24 blkPC_24 blkPl_24 lsmpl
)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalSession (
  CmkLoopRegs CmkTakeRegs CmkTooFarRegs ConsumeMessageKeyGhost
  cmkDummyImg cmkEntry_placed cmkEpiloguePC_placed cmkLoopHeap_placed_eq cmkLoopPC_placed
  cmkPreLoopHeap_placed_eq cmkTakePC_placed cmkTooFarPC_placed logFilterAddr_cmkDummyImg
)
open CryptoVerification.LibsignalSession.PrologueSplit (
  bv_sub_sub_lit cmkPre_placed_unpack
  prologueSplitActive prologueSplitActive_entails_loopHeap
  prologueSplitActive_entails_preLoopHeap prologueSplitPassiveFrame
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved rustAllocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (tpidrEl0_applyWriteback)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkEnv CmkLoopState_placed CmkTakeState_placed CmkTooFarState_placed
  PrologueAdvanceEntryPlacedSpec ProloguePastPlacedSpec PrologueTooFarPlacedSpec
  cmkEnv_tooFar cmkPlacedSpec
)

section WP

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_sub_lit CryptoVerification.LibsignalSession.PrologueSplit.bv_sub_add_lit

set_option maxHeartbeats 800000 in
theorem prologueSplit_past_wp_placed_vm [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx8 : s0.readReg64 .x8 = x.ret) (hlt : x.counter < x.ck.index) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) cmkTakePC_placed s0
      (prologueSplitActive cmkDummyImg x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        VmPreserved s0 sf ∧
        P_f = prologueSplitActive cmkDummyImg x s0 v368 x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkTakeRegs x s0 sf) := by
  by_vm_steps (
    unfold cmkTakePC_placed
    unfold cmkEntry_placed at hpc ⊢
    have hsp480 : (s0.sp - 480#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
    have h_not_ule : ¬(BitVec.ule x.ck.index x.counter = true) := by
      simp [BitVec.ule_iff_toNat_le, BitVec.lt_def] at hlt ⊢; omega
    dsimp only [prologueSplitActive]
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨by simp, rfl, rfl, rfl, rfl, rfl, ?_⟩
    unfold CmkTakeRegs
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  )

set_option maxHeartbeats 800000 in
theorem prologueSplit_tooFar_wp_placed_vm [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx4 : (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType)
    (hx8 : s0.readReg64 .x8 = x.ret) (hle : x.ck.index ≤ x.counter) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) cmkTooFarPC_placed s0
      (prologueSplitActive cmkDummyImg x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        VmPreserved s0 sf ∧
        P_f = prologueSplitActive cmkDummyImg x s0 v368 x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkTooFarRegs x s0 sf) := by
  by_vm_steps (
    unfold cmkTooFarPC_placed
    unfold cmkEntry_placed at hpc ⊢
    have hsp480 : (s0.sp - 480#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
    have h_ule : BitVec.ule x.ck.index x.counter = true := by
      simp [BitVec.ule_iff_toNat_le, BitVec.le_def] at hle ⊢; omega
    dsimp only [prologueSplitActive]
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨by simp, rfl, rfl, rfl, rfl, rfl, ?_⟩
    unfold CmkTooFarRegs
    exact ⟨hx2, hx4, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  )

set_option maxHeartbeats 800000 in
theorem prologueSplit_advance_wp_placed_vm [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry_placed) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hmax : x.st.maxForwardJumps < 2 ^ 64)
    (hle : x.ck.index ≤ x.counter)
    (hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps) :
    let targetPC := if x.ck.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
    SepWP ((blkPC_24).rebase (blkPl_24).base H) targetPC s0
      (prologueSplitActive cmkDummyImg x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        VmPreserved s0 sf ∧
        P_f = prologueSplitActive cmkDummyImg x s0 x.ret x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index ((x.counter - x.ck.index).zeroExtend 64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkLoopRegs x x.ck s0 sf ∧
        (targetPC = cmkLoopPC_placed → sf.readReg64 .x19 = 1#64)) := by
  intro targetPC
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 (mid := targetPC)
  intro _m_strip
  unfold cmkEntry_placed at hpc
  have hpc' : (s0.setMem _m_strip).pc = (blkPl_24).base := hpc
  have hrun' : (s0.setMem _m_strip).status = .Running := hrun
  have hsp480 : ((s0.setMem _m_strip).sp - 480#64) &&& 15#64 = 0#64 :=
    beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
  have hx0' : (s0.setMem _m_strip).readReg64 .x0 = x.self := hx0
  have hx1' : (s0.setMem _m_strip).readReg64 .x1 = x.theirA := hx1
  have hx2' : (s0.setMem _m_strip).readReg64 .x2 = x.ckA := hx2
  have hx3' : ((s0.setMem _m_strip).readReg64 .x3).setWidth 32 = x.counter := hx3
  have hx8' : (s0.setMem _m_strip).readReg64 .x8 = x.ret := hx8
  have h_ule : BitVec.ule x.ck.index x.counter = true := by
    simp [BitVec.ule_iff_toNat_le, BitVec.le_def] at hle ⊢; omega
  have h_jump_ule :
      BitVec.ule (BitVec.zeroExtend 64 (x.counter - x.ck.index))
        (BitVec.ofNat 64 x.st.maxForwardJumps) = true := by
    have := (x.counter - x.ck.index).isLt
    rw [BitVec.ule_iff_toNat_le, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  dsimp only [targetPC]
  by_cases hck_lt : x.ck.index < x.counter
  · simp only [hck_lt, ↓reduceIte]
    unfold cmkLoopPC_placed cmkEntry_placed
    have h_not_ck_ule : ¬(BitVec.ule x.counter x.ck.index = true) := by
      simp [BitVec.ule_iff_toNat_le, BitVec.lt_def] at hck_lt ⊢; omega
    dsimp only [prologueSplitActive]
    rw [logFilterAddr_cmkDummyImg]
    by_cases h25000 : BitVec.ule (x.counter - x.ck.index) 25000#32 = true
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
      refine SepWP.done rfl (by simp [hrun]) ⟨_hnsp.toVmPreserved (by simp),
        rfl, rfl, rfl, rfl, rfl, ?_, fun _ => rfl⟩
      unfold CmkLoopRegs
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
      refine SepWP.done rfl (by simp [hrun]) ⟨_hnsp.toVmPreserved (by simp),
        rfl, rfl, rfl, rfl, rfl, ?_, fun _ => rfl⟩
      unfold CmkLoopRegs
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hck_lt, ↓reduceIte]
    unfold cmkEpiloguePC_placed cmkLoopPC_placed cmkEntry_placed
    have h_loop_ne : (blkPl_24).base + bv% (1244) ≠ (blkPl_24).base + bv% (820) := by
      intro h
      have h2 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2
      omega
    have h_ck_ule : BitVec.ule x.counter x.ck.index = true := by
      simp [BitVec.ule_iff_toNat_le, BitVec.le_def, BitVec.lt_def] at hle hck_lt ⊢; omega
    dsimp only [prologueSplitActive]
    rw [logFilterAddr_cmkDummyImg]
    by_cases h25000 : BitVec.ule (x.counter - x.ck.index) 25000#32 = true
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
      refine SepWP.done rfl (by simp [hrun]) ⟨_hnsp.toVmPreserved (by simp),
        rfl, rfl, rfl, rfl, rfl, ?_, fun h => absurd h h_loop_ne⟩
      unfold CmkLoopRegs
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
      refine SepWP.done rfl (by simp [hrun]) ⟨_hnsp.toVmPreserved (by simp),
        rfl, rfl, rfl, rfl, rfl, ?_, fun h => absurd h h_loop_ne⟩
      unfold CmkLoopRegs
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end WP

/-- Budget-threaded placed prologue dispatch to `cmkTakePC_placed`. -/
theorem prologueSplit_past_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    ProloguePastPlacedSpec F A lim H := by
  intro x st_init R s0 hpc hrun hsp hpre hlt hL
  dsimp only [cmkPlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hFits, hpre⟩
  obtain ⟨hcl, hx0, hx1, hx2, hx3, _, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    cmkPre_placed_unpack hpre
  have hwp := prologueSplit_past_wp_placed_vm H x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hlt
  rcases hwp.elim hm hL with
    ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, P_f, hm_sf, hvm, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hseam : SeamBudget M lim (CmkEnv x) st_init st_init FreeOnlyEvs :=
    (SeamBudget.init hFits).weaken fun evs hfree => by simp [CmkEnv, hlt, hfree]
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hseam, hpc_sf, ?_, hregs_sf, ?_⟩⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← A.atState_eq_of_vmPreserved lim st_init hvm, ← sepConj_assoc] at hm_sf
    rw [cmkPreLoopHeap_placed_eq]
    exact Satisfies.mono
      (sepConj_mono_left (prologueSplitActive_entails_preLoopHeap
        (A.atState lim st_init sf) cmkDummyImg x s0 v368 x.counter
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328 hchains hpad hmax))
      hm_sf

/-- Budget-threaded placed prologue dispatch to `cmkTooFarPC_placed`. -/
theorem prologueSplit_tooFar_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    PrologueTooFarPlacedSpec F A lim H := by
  intro x st_init R s0 hpc hrun hsp hpre hle hjump hL
  dsimp only [cmkPlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hFits, hpre⟩
  obtain ⟨hcl, hx0, hx1, hx2, hx3, hx4, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    cmkPre_placed_unpack hpre
  have hwp := prologueSplit_tooFar_wp_placed_vm H x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx4 hx8 hle
  rcases hwp.elim hm hL with
    ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, P_f, hm_sf, hvm, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hseam : SeamBudget M lim (CmkEnv x) st_init st_init (fun evs => evs = rustAllocEvents 36 1) :=
    (SeamBudget.init hFits).weaken fun evs heq => (cmkEnv_tooFar hle hjump).mpr heq
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hseam, hpc_sf, ?_, hregs_sf, ?_⟩⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← A.atState_eq_of_vmPreserved lim st_init hvm, ← sepConj_assoc] at hm_sf
    rw [cmkPreLoopHeap_placed_eq]
    exact Satisfies.mono
      (sepConj_mono_left (prologueSplitActive_entails_preLoopHeap
        (A.atState lim st_init sf) cmkDummyImg x s0 v368 x.counter
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328 hchains hpad hmax))
      hm_sf

/-- Budget-threaded placed prologue dispatch to `cmkLoopPC_placed` or `cmkEpiloguePC_placed`. -/
theorem prologueSplit_advance_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    PrologueAdvanceEntryPlacedSpec F A lim H := by
  intro x st_init R s0 hpc hrun hsp hpre hle hj targetPC hL
  dsimp only [cmkPlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hFits, hpre⟩
  obtain ⟨hcl, hx0, hx1, hx2, hx3, _, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    cmkPre_placed_unpack hpre
  have hwp := prologueSplit_advance_wp_placed_vm H x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hmax hle hj
  rcases hwp.elim hm hL with
    ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, P_f, hm_sf, hvm, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf, hx19_sf⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hseam : SeamBudget M lim (CmkEnv x) st_init st_init (CmkEnv x) :=
    SeamBudget.init hFits
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hseam, hpc_sf, ?_, hregs_sf, hx19_sf, ?_⟩⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← A.atState_eq_of_vmPreserved lim st_init hvm, ← sepConj_assoc] at hm_sf
    rw [cmkLoopHeap_placed_eq]
    exact Satisfies.mono
      (sepConj_mono_left (prologueSplitActive_entails_loopHeap
        (A.atState lim st_init sf) cmkDummyImg x s0
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index
        ((x.counter - x.ck.index).zeroExtend 64) hchains hpad hmax))
      hm_sf

end LibsignalBinary.Proofs.ConsumeMessageKey.PrologueSplitBudget
