/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Segment 5: Pack & Version Dispatch (Block `518`)

Zero-allocation event envelope `ClonePackEnv`, `VmPreserved` pack steps (`pack_eq_placed_wp_vm`,
`pack_ne_placed_wp_vm`), and budget-threaded Segment 5 proofs (`clonePack_vregs_placed_ok`,
`+0x1bac → +0x1cd4 / +0x1e04`, `genP3J4PlacedBudget → genP3PostPlacedBudget`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped
  CryptoVerification.RustHeap
  CryptoVerification.LibsignalSessionRepr
  CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
  CryptoVerification.LibsignalTripleRatchet.RawByteMove
  CryptoVerification.LibsignalTripleRatchet.Record
  CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
  CryptoVerification.LibsignalPublicApi
  CryptoVerification.E2E.Pqxdh.ResponderClosure
  CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
  CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoGames.LibsignalSession (SessionState SignalMessage)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost SignalMessageGhost)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (GenP3J4Witness genP3SenderInlineWords)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1 (bind_sepWP_lscro_frame_placed)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4 (
  PackDstVals memRegion_344_entails_packDstSlotsAt packDstSlotsAt packDstSlotsWrittenAt
  packSrcSlotsAt sessionStateAt_entails_pure_sep
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  cloneExitPCPlaced dpClosureEntryM3Placed genP3CallFramePlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux (
  sepWPp_done_any sepWPp_exists_elim_any sepWPp_pure_elim_any sepWPp_weaken_pre_any
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlacedBudget (
  genP3J4PlacedBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBasePlacedBudget (
  genP3PostEqPlacedBudget genP3PostNePlacedBudget genP3PostPlacedBudget packRestFramePlacedBudget
  packed_entails_genP3PostSpatialPlacedBudget_of_vmPreserved
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Zero-Allocation Event List & Envelope for Segment 5 (`+0x1bac → +0x1cd4 / +0x1e04`) -/

/-- Exact allocator event sequence emitted across Stage P3 Segment 5 (`+0x1bac → +0x1cd4 / +0x1e04`):
Segment 5 performs only stack loads/stores and register arithmetic (`[]`). -/
def clonePackEvents : List AllocEvent := []

/-- Exact allocator event envelope for Stage P3 Segment 5 (`clonePack_vregs_placed_ok`). -/
def ClonePackEnv (evs : List AllocEvent) : Prop :=
  evs = clonePackEvents

theorem clonePackEnv_events : ClonePackEnv clonePackEvents := rfl

@[simp]
theorem fitsEnv_clonePack_iff {M : AllocCostModel} {lim : BudgetLimits} {stB : M.σ} :
    FitsEnv M lim stB ClonePackEnv ↔ FitsEvents M lim stB clonePackEvents :=
  FitsEnv.eq_iff

theorem fitsEvents_clonePack (M : AllocCostModel) (lim : BudgetLimits) (stB : M.σ) :
    FitsEvents M lim stB clonePackEvents :=
  trivial

theorem fitsEnv_clonePack (M : AllocCostModel) (lim : BudgetLimits) (stB : M.σ) :
    FitsEnv M lim stB ClonePackEnv :=
  fun _ h => h ▸ trivial

/-! ## 2. `VmPreserved`-Recording Placed Segment 5 Pack Steps -/

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subsPState32_placed (x y : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 x y) = (x == y) := by
  unfold subsPState32
  exact conditionHolds_eq_subs32 x y

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subsPState32_placed (x y : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 x y) = (x != y) := by
  unfold subsPState32
  exact conditionHolds_ne_subs32 x y

private theorem extractLsb'_zero_eq_truncate64 (q : BitVec 128) :
    q.extractLsb' 0 64 = q.truncate 64 := by
  simp

set_option maxHeartbeats 800000 in
/-- Version-match placed step (`+0x1bac → +0x1cd4`, `st.version = msgVer`) recording
`VmPreserved s s1` for budget-pool transport. -/
theorem pack_eq_placed_wp_vm [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (w : GenP3J4Witness) (dv : PackDstVals)
    (hver : st.version = msgVer)
    (hpc : s.pc = (blkPl_518).base + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = w.newPqPtr)
    (hx22 : s.readReg64 .x22 = w.pendCap')
    (hx23 : s.readReg64 .x23 = w.newAlicePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length)
    (hx25 : s.readReg64 .x25 = w.newRcPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 32#64)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1cd4#64) s
      (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsAt s.sp dv)
      (fun s1 P_f =>
        (P_f ⊢
          packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
            packDstSlotsWrittenAt s.sp recG st w ((s.readReg64 .x20).truncate 32)) ∧
        VmPreserved s s1 ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x270#64 ∧
        s1.readReg64 .x1 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x2 = remAddrPtr ∧
        s1.readReg64 .x3 = locAddrPtr ∧
        s1.readReg64 .x4 = whisperMsgPtr ∧
        s1.readReg64 .x5 = 3#64 ∧
        s1.readReg64 .x6 = 0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = fp ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold packSrcSlotsAt genP3SenderInlineWords packDstSlotsAt packDstSlotsWrittenAt
  dsimp only [Reg.x20]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w.newPqPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w.pendCap' := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w.newAlicePtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 recG.alice.bytes.length := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = w.newRcPtr := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 st.pqRatchetState.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 32#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := (blkPl_518).base + 0x1cd4#64)
  intro m_strip
  by_cases hsv0 : st.sessionVersion = 0
  · have hm : msgVer = 2#32 := by
      rw [← hver]; simp only [SessionState.version, hsv0, ↓reduceIte]; rfl
    have hsv0' : st.sessionVersion = 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = true := beq_iff_eq.mpr hsv0'
    have hne1 : (2#32 != msgVer) = false := bne_eq_false_iff_eq.mpr hm.symm
    have hne2 : (msgVer != 2#32) = false := bne_eq_false_iff_eq.mpr hm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
    have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    simp only [State.setMem_setMem] at hvmp ⊢
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hsv0', extractLsb'_zero_eq_truncate64]), hvmp,
      by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  · have hm : st.sessionVersion = msgVer := by
      have hv : st.version = st.sessionVersion := by
        simp only [SessionState.version, hsv0, ↓reduceIte]
      exact hv.symm.trans hver
    have hsv0' : st.sessionVersion ≠ 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hsv0'
    have hne1 : (st.sessionVersion != msgVer) = false := bne_eq_false_iff_eq.mpr hm
    have hne2 : (msgVer != st.sessionVersion) = false := bne_eq_false_iff_eq.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
    have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    simp only [State.setMem_setMem] at hvmp ⊢
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hm, extractLsb'_zero_eq_truncate64]), hvmp,
      by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
/-- Version-mismatch placed step (`+0x1bac → +0x1e04`, `st.version ≠ msgVer`) recording
`VmPreserved s s1` for budget-pool transport. -/
theorem pack_ne_placed_wp_vm [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (w : GenP3J4Witness) (dv : PackDstVals)
    (hver : st.version ≠ msgVer)
    (hpc : s.pc = (blkPl_518).base + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = w.newPqPtr)
    (hx22 : s.readReg64 .x22 = w.pendCap')
    (hx23 : s.readReg64 .x23 = w.newAlicePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length)
    (hx25 : s.readReg64 .x25 = w.newRcPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 32#64)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1e04#64) s
      (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsAt s.sp dv)
      (fun s1 P_f =>
        (P_f ⊢
          packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
            packDstSlotsWrittenAt s.sp recG st w ((s.readReg64 .x20).truncate 32)) ∧
        VmPreserved s s1 ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x9 = msgVer.setWidth 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = fp ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold packSrcSlotsAt genP3SenderInlineWords packDstSlotsAt packDstSlotsWrittenAt
  dsimp only [Reg.x20]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w.newPqPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w.pendCap' := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w.newAlicePtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 recG.alice.bytes.length := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = w.newRcPtr := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 st.pqRatchetState.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 32#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := (blkPl_518).base + 0x1e04#64)
  intro m_strip
  by_cases hsv0 : st.sessionVersion = 0
  · have hm : 2#32 ≠ msgVer := by
      intro h; apply hver
      simp only [SessionState.version, hsv0, ↓reduceIte]; exact h
    have hsv0' : st.sessionVersion = 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = true := beq_iff_eq.mpr hsv0'
    have hne1 : (2#32 != msgVer) = true := bne_iff_ne.mpr hm
    have hne2 : (msgVer != 2#32) = true := bne_iff_ne.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
    have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    simp only [State.setMem_setMem] at hvmp ⊢
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hsv0', extractLsb'_zero_eq_truncate64]), hvmp,
      by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  · have hm : st.sessionVersion ≠ msgVer := by
      intro h; apply hver
      simp only [SessionState.version, hsv0, ↓reduceIte]; exact h
    have hsv0' : st.sessionVersion ≠ 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hsv0'
    have hne1 : (st.sessionVersion != msgVer) = true := bne_iff_ne.mpr hm
    have hne2 : (msgVer != st.sessionVersion) = true := bne_iff_ne.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
    have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    simp only [State.setMem_setMem] at hvmp ⊢
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [extractLsb'_zero_eq_truncate64]), hvmp,
      by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-! ## 3. Budget-Threaded Placed Segment 5 Theorems (`genP3J4PlacedBudget → genP3PostPlacedBudget`) -/

private theorem sepWPp_weaken_post_pack {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hw : ∀ sf P_f, Q sf P_f → Q' sf P_f) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hw sf P_f hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

set_option maxHeartbeats 800000 in
/-- Budget-threaded Placed Segment 5 with `calleeSavedVRegs` (`+0x1bac → +0x1cd4 / +0x1e04`,
`genP3J4PlacedBudget → genP3PostPlacedBudget`): preserves `stB` unchanged (zero allocations). -/
theorem clonePack_vregs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (_hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1bac#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (cloneExitPCPlaced st msgVer) s
      (genP3J4PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3PostPlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  dsimp only [dpClosureEntryM3Placed] at hpc
  dsimp only [genP3J4PlacedBudget]
  refine sepWPp_exists_elim_any fun w => ?_
  refine sepWPp_pure_elim_any
    fun ⟨hsp, hx19, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29,
         hreg_eq, hchains_len, _hsc_rel, hsc_inl⟩ => ?_
  cases hsp
  refine sepWPp_weaken_pre_any
    (sepConj_mono_left (sessionStateAt_entails_pure_sep A.repAlloc (coroPtr + 0xf8#64) recG st)) ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim_any
    fun ⟨h_loc_deser, h_rem_deser, _, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  dsimp only [genP3CallFramePlaced]
  refine sepWPp_weaken_pre_any
    (P' := memRegion (s.sp + 0xa90#64) 344 ∗
            (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
              packRestFramePlacedBudget A lim stB s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
                whisperMsgPtr cur rest recG st w rem loc msgG msg s))
    (Entails.of_eq (by dsimp only [packSrcSlotsAt, packRestFramePlacedBudget]; sep_ac_rfl)) ?_
  refine sepWPp_weaken_pre_any (sepConj_mono_left (memRegion_344_entails_packDstSlotsAt s.sp)) ?_
  rw [sepExists_sepConj_left]
  refine sepWPp_exists_elim_any fun dv => ?_
  refine sepWPp_weaken_pre_any
    (P' := (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
              packDstSlotsAt s.sp dv) ∗
            packRestFramePlacedBudget A lim stB s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
              whisperMsgPtr cur rest recG st w rem loc msgG msg s)
    (Entails.of_eq (by sep_ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, hver, ↓reduceIte]
    have hstep := pack_eq_placed_wp_vm ext s coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr
      msgVer recG st w dv hver hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    refine bind_sepWP_lscro_frame_placed hcro hstep rfl
      fun s1 hpc1 hrun1 hcro1 hregs => ?_
    rcases hregs with ⟨hvmp1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1,
      hx19_1, hx24_1, hx27_1, hx29_1, hvregs1⟩
    refine sepWPp_done_any hpc1 hrun1 ⟨?_, htr1.trans htr, hcro1, hvregs1⟩
    simp only [genP3PostPlacedBudget, hver, ↓reduceIte, genP3PostEqPlacedBudget]
    apply Entails.pure_right
      ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx19_1, hx24_1, hx27_1, hx29_1⟩
    exact packed_entails_genP3PostSpatialPlacedBudget_of_vmPreserved A lim stB s.sp coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st w
      ((s.readReg64 .x20).truncate 32) rem loc msgG msg hvmp1
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl
  · simp only [cloneExitPCPlaced, hver, ↓reduceIte]
    have hstep := pack_ne_placed_wp_vm ext s coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr
      msgVer recG st w dv hver hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    refine bind_sepWP_lscro_frame_placed hcro hstep rfl
      fun s1 hpc1 hrun1 hcro1 hregs => ?_
    rcases hregs with ⟨hvmp1, hsp1, htr1, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1, hvregs1⟩
    refine sepWPp_done_any hpc1 hrun1 ⟨?_, htr1.trans htr, hcro1, hvregs1⟩
    simp only [genP3PostPlacedBudget, hver, ↓reduceIte, genP3PostNePlacedBudget]
    apply Entails.pure_right ⟨hsp1, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩
    exact packed_entails_genP3PostSpatialPlacedBudget_of_vmPreserved A lim stB s.sp coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st w
      ((s.readReg64 .x20).truncate 32) rem loc msgG msg hvmp1
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl

/-- `M.stepEvents clonePackEvents stB` variant of `clonePack_vregs_placed_ok`. -/
theorem clonePack_vregs_placed_ok_stepEvents [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1bac#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (cloneExitPCPlaced st msgVer) s
      (genP3J4PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3PostPlacedBudget A lim (M.stepEvents clonePackEvents stB) sp fp coroPtr ctxPtr
          remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  clonePack_vregs_placed_ok ext s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg hrc_len hsp_align hsp_root hcro hpc hrun htr

/-- Envelope (`ClonePackEnv`) variant of `clonePack_vregs_placed_ok`. -/
theorem clonePack_vregs_placed_ok_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1bac#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (cloneExitPCPlaced st msgVer) s
      (genP3J4PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent, ClonePackEnv evs ∧
          (P_f ⊢ genP3PostPlacedBudget A lim (M.stepEvents evs stB) sp fp coroPtr ctxPtr remAddrPtr
            locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  sepWPp_weaken_post_pack
    (clonePack_vregs_placed_ok_stepEvents ext s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc_len hsp_align hsp_root hcro hpc
      hrun htr)
    fun _ _ ⟨hent1, htr1, hcro1, hv1⟩ => ⟨clonePackEvents, rfl, hent1, htr1, hcro1, hv1⟩

/-- Placed Segment 5 corollary without the `calleeSavedVRegs` conjunct. -/
theorem clonePack_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1bac#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (cloneExitPCPlaced st msgVer) s
      (genP3J4PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3PostPlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl s1.mem)
      Qp :=
  sepWPp_weaken_post_pack
    (clonePack_vregs_placed_ok ext s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg hrc_len hsp_align hsp_root hcro hpc hrun htr)
    fun _ _ ⟨hent1, htr1, hcro1, _⟩ => ⟨hent1, htr1, hcro1⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlacedBudget
