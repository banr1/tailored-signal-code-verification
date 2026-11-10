/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.EpilogueReassembly
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved`-threaded epilogue and reassembly for `SessionStructure::clone`

Relocatable `[LibsignalPlacement]` epilogue proofs (`+924..ret`) for `SessionStructure::clone`
(block `80`), threading `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.EpilogueReassemblyBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.E2E.Record.Placed (blkPl_80 lsProg_80)
open CryptoVerification.E2E.Record.Serialization (SessionCloneGhost)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (chunks96_6QAt)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  DstVals pointsTo128_eq_pointsTo64
)
open CryptoVerification.E2E.Record.Serialization.SessionCloneAux (
  scDstSlotsMidAt scDstSlotsAt scDstSlotsWrittenAt scSpillSlotsAt scSavedRegsAt
  chunks96_6QAt_sp_0x90 sc_chunks96_6QAt_dst_0x98
)
open LibsignalBinary.Heap (VmPreserved)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

macro "sc_close4_b" : tactic =>
  `(tactic| (
    try clear hnext
    first
    | rfl
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, Reg.fp, Reg.lr] at *
       try simp (config := { decide := true }) only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg]
       simp (config := { decide := true }) only [*, reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        State.setPC, State.setPState,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_add, List.length_cons]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, Reg.fp, Reg.lr] at *
       try simp only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg]
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, Reg.fp, Reg.lr] at *
       subst_vars
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32]
       done)))

private theorem sepWPp_of_sepWP_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp :=
  SepWPp.of_sepWP (mid := mid) (SepWP.mono h (fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm))

set_option maxHeartbeats 800000 in
theorem sc_assemble_1_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {x : SessionCloneGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v0c : BitVec 32) (kybPtr' v18 pendPtr' : BitVec 64)
    (v28 v2c : BitVec 32) (alicePtr' : BitVec 64) (w28c : BitVec 32)
    (kybCap' : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (blkPl_80).base + 924#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.dst)
    (hx26 : s.readReg64 .x26 = chainsCap')
    (hx27 : s.readReg64 .x27 = chainsPtr')
    (htr : s.trace = s0.trace)
    (hnext : ∀ s1 : State,
      VmPreserved s s1 →
      s1.pc = (blkPl_80).base + 1028#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x8 = v18 →
      s1.readReg64 .x9 = pendPtr' →
      s1.readReg64 .x19 = x.dst →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_80 H) ret s1
        (scDstSlotsMidAt x.dst dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
          scCap' sq0 sq1 sq2 sq3 sq4 sq5 x.s.state.sessionVersion x.s.state.previousCounter ∗
          chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alicePtr' w28c
            kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗ F)
        Q Qp) :
    SepWPp (lsProg_80 H) ret s
      (scDstSlotsAt x.dst dv ∗
        chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alicePtr' w28c
          kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗ F)
      Q Qp := by
  unfold scDstSlotsMidAt scSpillSlotsAt at hnext
  unfold scDstSlotsAt scSpillSlotsAt
  rw [chunks96_6QAt_sp_0x90 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      sc_chunks96_6QAt_dst_0x98 x.dst dv.q0 dv.q1 dv.q2 dv.q3 dv.q4 dv.q5]
  rw [chunks96_6QAt_sp_0x90 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      sc_chunks96_6QAt_dst_0x98 x.dst sq0 sq1 sq2 sq3 sq4 sq5] at hnext
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply sepWPp_of_sepWP_vm (mid := (blkPl_80).base + 1028#64)
  by_vm_steps
    wp_steps
    refine SepWP.done (by sc_close4_b) (by sc_close4_b) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine SepWPp.weaken_pre ?_
      (hnext _ hvm (by sc_close4_b) (by sc_close4_b) (by sc_close4_b) (by sc_close4_b)
        (by sc_close4_b) (by sc_close4_b) (by sc_close4_b)
        (by sc_close4_b) (by sc_close4_b) (by sc_close4_b)
        (by sc_close4_b) (by sc_close4_b) (by sc_close4_b)
        (by sc_close4_b) (by sc_close4_b) (by sc_close4_b))
    exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem sc_assemble_2_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {x : SessionCloneGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v0c : BitVec 32) (kybCap' kybPtr' pendCap' pendPtr' v18 : BitVec 64)
    (w23 w24 v28 v2c w288 w28c : BitVec 32)
    (r29 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (blkPl_80).base + 1028#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = v18)
    (hx9 : s.readReg64 .x9 = pendPtr')
    (hx19 : s.readReg64 .x19 = x.dst)
    (hx20 : (s.readReg64 .x20).truncate 32 = w288)
    (hx21 : s.readReg64 .x21 = alice'.cap)
    (hx22 : s.readReg64 .x22 = pqCap')
    (hx23 : (s.readReg64 .x23).truncate 32 = w23)
    (hx24 : (s.readReg64 .x24).truncate 32 = w24)
    (hx25 : s.readReg64 .x25 = pqPtr')
    (hx28 : s.readReg64 .x28 = pendCap')
    (htr : s.trace = s0.trace)
    (hnext : ∀ s1 : State,
      VmPreserved s s1 →
      s1.pc = ret →
      s1.status = .Running →
      s1.sp = s.sp + 0x1d0#64 →
      s1.readReg64 .x19 = r19 →
      s1.readReg64 .x20 = r20 →
      s1.readReg64 .x21 = r21 →
      s1.readReg64 .x22 = r22 →
      s1.readReg64 .x23 = r23 →
      s1.readReg64 .x24 = r24 →
      s1.readReg64 .x25 = r25 →
      s1.readReg64 .x26 = r26 →
      s1.readReg64 .x27 = r27 →
      s1.readReg64 .x28 = r28 →
      s1.readReg64 .x29 = r29 →
      s1.readReg64 .lr = ret →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_80 H) ret s1
        (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23 w24 v18 v2c
          kybCap' kybPtr' v28 x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
          scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
            kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
          scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
        Q Qp) :
    SepWPp (lsProg_80 H) ret s
      (scDstSlotsMidAt x.dst dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
        scCap' sq0 sq1 sq2 sq3 sq4 sq5 x.s.state.sessionVersion x.s.state.previousCounter ∗
        scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
          kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
        scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
      Q Qp := by
  unfold scDstSlotsWrittenAt scSpillSlotsAt scSavedRegsAt at hnext
  unfold scDstSlotsMidAt scSpillSlotsAt scSavedRegsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply sepWPp_of_sepWP_vm (mid := ret)
  by_vm_steps
    wp_steps
    refine SepWP.done (by sc_close4_b) (by sc_close4_b) ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine SepWPp.weaken_pre ?_
      (hnext _ hvm (by sc_close4_b) (by sc_close4_b) (by simp_all) (by sc_close4_b)
        (by sc_close4_b) (by sc_close4_b) (by sc_close4_b)
        (by sc_close4_b) (by sc_close4_b) (by sc_close4_b)
        (by sc_close4_b) (by sc_close4_b) (by sc_close4_b)
        (by sc_close4_b) (by sc_close4_b) (by sc_close4_b) (by sc_close4_b))
    exact Entails.of_eq (by sep_ac_rfl)

theorem sc_epilogue_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {x : SessionCloneGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v0c : BitVec 32) (kybCap' kybPtr' pendCap' pendPtr' v18 : BitVec 64)
    (w23 w24 v28 v2c w288 w28c : BitVec 32)
    (r29 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (blkPl_80).base + 924#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.dst)
    (hx20 : (s.readReg64 .x20).truncate 32 = w288)
    (hx21 : s.readReg64 .x21 = alice'.cap)
    (hx22 : s.readReg64 .x22 = pqCap')
    (hx23 : (s.readReg64 .x23).truncate 32 = w23)
    (hx24 : (s.readReg64 .x24).truncate 32 = w24)
    (hx25 : s.readReg64 .x25 = pqPtr')
    (hx26 : s.readReg64 .x26 = chainsCap')
    (hx27 : s.readReg64 .x27 = chainsPtr')
    (hx28 : s.readReg64 .x28 = pendCap')
    (htr : s.trace = s0.trace)
    (hnext : ∀ s1 : State,
      VmPreserved s s1 →
      s1.pc = ret →
      s1.status = .Running →
      s1.sp = s.sp + 0x1d0#64 →
      s1.readReg64 .x19 = r19 →
      s1.readReg64 .x20 = r20 →
      s1.readReg64 .x21 = r21 →
      s1.readReg64 .x22 = r22 →
      s1.readReg64 .x23 = r23 →
      s1.readReg64 .x24 = r24 →
      s1.readReg64 .x25 = r25 →
      s1.readReg64 .x26 = r26 →
      s1.readReg64 .x27 = r27 →
      s1.readReg64 .x28 = r28 →
      s1.readReg64 .x29 = r29 →
      s1.readReg64 .lr = ret →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_80 H) ret s1
        (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23 w24 v18 v2c
          kybCap' kybPtr' v28 x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
          chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
            kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
          scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
        Q Qp) :
    SepWPp (lsProg_80 H) ret s
      (scDstSlotsAt x.dst dv ∗
        chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
          kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
        scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
      Q Qp := by
  refine sc_assemble_1_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' scCap'
    sq0 sq1 sq2 sq3 sq4 sq5 v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c kybCap'
    (scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
    hpc hrun hsp hx19 hx26 hx27 htr
    fun s1 hvm1 hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx28_1 htr1 hvregs1 => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := scDstSlotsMidAt x.dst dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
              scCap' sq0 sq1 sq2 sq3 sq4 sq5 x.s.state.sessionVersion x.s.state.previousCounter ∗
            scSpillSlotsAt s1.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
              kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
              localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
            scSavedRegsAt s1.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗
            (chunks96_6QAt (s1.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine sc_assemble_2_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice' pqCap' pqPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 v0c kybCap' kybPtr' pendCap' pendPtr' v18
    w23 w24 v28 v2c w288 w28c r29 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19
    (chunks96_6QAt (s1.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F)
    hpc1 hrun1 hspA1 hx8_1 hx9_1 hx19_1
    (by rw [hx20_1]; exact hx20) (hx21_1.trans hx21) (hx22_1.trans hx22)
    (by rw [hx23_1]; exact hx23) (by rw [hx24_1]; exact hx24)
    (hx25_1.trans hx25) (hx28_1.trans hx28) htr1
    fun s2 hvm2 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hlr2 htr2 hvregs2 => ?_
  rw [hsp1] at hsp2 ⊢
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext s2 (hvm1.trans hvm2) hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hlr2 htr2
      (hvregs2.trans hvregs1))

end LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.EpilogueReassemblyBudget
