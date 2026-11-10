/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::clone`: Destination Slot Assembly and Epilogue (`+0x39c → ret`)

Assembles the 344-byte destination `SessionStructure`, restores `x19..x30` and `sp`, and
reassembles `stackAt sp0 sessionCloneStackX`.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

macro "sc_close4" : tactic =>
  `(tactic| (
    try clear hnext
    try clear hsub1
    try clear hsub2
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

/-- Intermediate destination layout at `+0x404` after the first 26 epilogue instructions. -/
def scDstSlotsMidAt (dst : BitVec 64) (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (sessVer prevCnt : BitVec 32) : SepProp :=
  (dst ↦₆₄ localIk'.cap) ∗ ((dst + 0x08#64) ↦₆₄ localIk'.ptr) ∗ ((dst + 0x10#64) ↦₆₄ localIk'.cap) ∗
  ((dst + 0x18#64) ↦₆₄ remoteIk'.cap) ∗ ((dst + 0x20#64) ↦₆₄ remoteIk'.ptr) ∗ ((dst + 0x28#64) ↦₆₄ remoteIk'.cap) ∗
  ((dst + 0x30#64) ↦₆₄ 32#64) ∗ ((dst + 0x38#64) ↦₆₄ rootPtr') ∗ ((dst + 0x40#64) ↦₆₄ 32#64) ∗
  ((dst + 0x48#64) ↦₆₄ chainsCap') ∗ ((dst + 0x50#64) ↦₆₄ chainsPtr') ∗ ((dst + 0x58#64) ↦₆₄ chainsCap') ∗
  ((dst + 0x60#64) ↦₆₄ dv.w_d00) ∗ ((dst + 0x68#64) ↦₆₄ dv.w_d08) ∗ ((dst + 0x70#64) ↦₆₄ dv.w_d10) ∗
  ((dst + 0x78#64) ↦₆₄ dv.w_d18) ∗ ((dst + 0x80#64) ↦₆₄ dv.w_d20) ∗ ((dst + 0x88#64) ↦₆₄ dv.w_d28) ∗
  ((dst + 0x90#64) ↦₆₄ scCap') ∗
  chunks96_6QAt (dst + 0x98#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
  ((dst + 0xf8#64) ↦₆₄ dv.w_d98) ∗ ((dst + 0x100#64) ↦₆₄ dv.w_da0) ∗ ((dst + 0x108#64) ↦₆₄ dv.w_da8) ∗
  ((dst + 0x110#64) ↦₃₂ dv.w_db0) ∗ ((dst + 0x114#64) ↦₃₂ dv.w_db4) ∗ ((dst + 0x118#64) ↦₆₄ dv.w_db8) ∗
  ((dst + 0x120#64) ↦₃₂ dv.w_dc0) ∗ memRegion (dst + 0x124#64) 4 ∗
  ((dst + 0x128#64) ↦₆₄ dv.w_dc8) ∗ ((dst + 0x130#64) ↦₆₄ dv.w_dd0) ∗ ((dst + 0x138#64) ↦₆₄ dv.w_dd8) ∗
  ((dst + 0x140#64) ↦₃₂ dv.w_de0) ∗ memRegion (dst + 0x144#64) 4 ∗
  ((dst + 0x148#64) ↦₃₂ sessVer) ∗ ((dst + 0x14c#64) ↦₃₂ prevCnt) ∗
  ((dst + 0x150#64) ↦₃₂ dv.w_df0) ∗ ((dst + 0x154#64) ↦₃₂ dv.w_df4)

set_option maxHeartbeats 800000 in
theorem sc_assemble_1 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v0c : BitVec 32) (kybPtr' v18 pendPtr' : BitVec 64)
    (v28 v2c : BitVec 32) (alicePtr' : BitVec 64) (w28c : BitVec 32)
    (kybCap' : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x39c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.dst)
    (hx26 : s.readReg64 .x26 = chainsCap')
    (hx27 : s.readReg64 .x27 = chainsPtr')
    (htr : s.trace = s0.trace)
    (hnext : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x404#64 →
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (scDstSlotsMidAt x.dst dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
          scCap' sq0 sq1 sq2 sq3 sq4 sq5 x.s.state.sessionVersion x.s.state.previousCounter ∗
          chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alicePtr' w28c
            kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (scDstSlotsAt x.dst dv ∗
        chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alicePtr' w28c
          kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x39c 104
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  unfold scDstSlotsMidAt scSpillSlotsAt at hnext
  unfold scDstSlotsAt scSpillSlotsAt
  rw [chunks96_6QAt_sp_0x90 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      sc_chunks96_6QAt_dst_0x98 x.dst dv.q0 dv.q1 dv.q2 dv.q3 dv.q4 dv.q5]
  rw [chunks96_6QAt_sp_0x90 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      sc_chunks96_6QAt_dst_0x98 x.dst sq0 sq1 sq2 sq3 sq4 sq5] at hnext
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply SepWPpX.of_sepWP (mid := entry + bv% (1028))
  wp_steps
  refine SepWP.done (by sc_close4) (by sc_close4) ?_
  refine SepWPpX.weaken_pre ?_
    (hnext _ (by sc_close4) (by sc_close4) (by sc_close4) (by sc_close4)
      (by sc_close4) (by sc_close4) (by sc_close4)
      (by sc_close4) (by sc_close4) (by sc_close4)
      (by sc_close4) (by sc_close4) (by sc_close4)
      (by sc_close4) (by sc_close4) (by sc_close4))
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem sc_assemble_2 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v0c : BitVec 32) (kybCap' kybPtr' pendCap' pendPtr' v18 : BitVec 64)
    (w23 w24 v28 v2c w288 w28c : BitVec 32)
    (r29 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x404#64)
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23 w24 v18 v2c
          kybCap' kybPtr' v28 x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
          scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
            kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
          scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (scDstSlotsMidAt x.dst dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
        scCap' sq0 sq1 sq2 sq3 sq4 sq5 x.s.state.sessionVersion x.s.state.previousCounter ∗
        scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
          kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
        scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x404 112
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  unfold scDstSlotsWrittenAt scSpillSlotsAt scSavedRegsAt at hnext
  unfold scDstSlotsMidAt scSpillSlotsAt scSavedRegsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply SepWPpX.of_sepWP (mid := ret)
  wp_steps
  refine SepWP.done (by sc_close4) (by sc_close4) ?_
  refine SepWPpX.weaken_pre ?_
    (hnext _ (by sc_close4) (by sc_close4) (by simp_all) (by sc_close4)
      (by sc_close4) (by sc_close4) (by sc_close4)
      (by sc_close4) (by sc_close4) (by sc_close4)
      (by sc_close4) (by sc_close4) (by sc_close4)
      (by sc_close4) (by sc_close4) (by sc_close4) (by sc_close4))
  exact Entails.of_eq (by ac_rfl)

/-- Epilogue and destination `SessionStructure` assembly (`+0x39c → ret`). -/
theorem sc_epilogue {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v0c : BitVec 32) (kybCap' kybPtr' pendCap' pendPtr' v18 : BitVec 64)
    (w23 w24 v28 v2c w288 w28c : BitVec 32)
    (r29 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x39c#64)
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23 w24 v18 v2c
          kybCap' kybPtr' v28 x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
          chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
            kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
          scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (scDstSlotsAt x.dst dv ∗
        chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
          kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
        scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
      Q (scPanicPost A x R s0) := by
  refine sc_assemble_1 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' scCap'
    sq0 sq1 sq2 sq3 sq4 sq5 v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c kybCap'
    (scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
    hpc hrun hsp hx19 hx26 hx27 htr
    fun s1 hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx28_1 htr1 hvregs1 => ?_
  rw [← hsp1]
  refine SepWPpX.weaken_pre
    (P' := scDstSlotsMidAt x.dst dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
              scCap' sq0 sq1 sq2 sq3 sq4 sq5 x.s.state.sessionVersion x.s.state.previousCounter ∗
            scSpillSlotsAt s1.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
              kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
              localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
            scSavedRegsAt s1.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗
            (chunks96_6QAt (s1.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sc_assemble_2 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice' pqCap' pqPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 v0c kybCap' kybPtr' pendCap' pendPtr' v18
    w23 w24 v28 v2c w288 w28c r29 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19
    (chunks96_6QAt (s1.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F)
    hpc1 hrun1 hspA1 hx8_1 hx9_1 hx19_1
    (by rw [hx20_1]; exact hx20) (hx21_1.trans hx21) (hx22_1.trans hx22)
    (by rw [hx23_1]; exact hx23) (by rw [hx24_1]; exact hx24)
    (hx25_1.trans hx25) (hx28_1.trans hx28) htr1
    fun s2 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hlr2 htr2 hvregs2 => ?_
  rw [hsp1] at hsp2 ⊢
  refine SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s2 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hlr2 htr2
      (hvregs2.trans hvregs1))

/-- Reassemble `stackAt sp0 sessionCloneStackX` from the stack frame pieces at `sp = sp0 - 0x1d0#64`. -/
theorem sc_stack_reassemble (sp0 : BitVec 64)
    (v0c : BitVec 32) (v10 v18 v20 : BitVec 64)
    (v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64)
    (v84 : BitVec 32) (v88 : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (r29 r30 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    let sp := sp0 - 0x1d0#64
    (memRegion (sp0 - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
      stackAt sp chainCloneStackX ∗
      scSpillSlotsAt sp v0c v10 v18 v20 v28 v2c v30 v3c
        v40 v48 v54 v58 v60 v68 v70 v78 v84 v88 ∗
      chunks96_6QAt (sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
      memRegion (sp + 0xf0#64) 8 ∗
      memRegion (sp + 0xf8#64) 104 ∗
      memRegion (sp + 0x160#64) 16 ∗
      scSavedRegsAt sp r29 r30 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19) ⊢
      stackAt sp0 sessionCloneStackX := by
  dsimp only
  rw [stackAt_sessionClone_eq sp0]
  dsimp only
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine sepConj_mono (scSpillSlotsAt_entails_memRegion_0x90 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  refine sepConj_mono (chunks96_6QAt_entails_memRegion _ _ _ _ _ _ _) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  exact scSavedRegsAt_entails_memRegion_0x170_0x60 _ _ _ _ _ _ _ _ _ _ _ _ _

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
