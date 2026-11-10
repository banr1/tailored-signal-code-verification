/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.EpilogueReassemblyBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.EpilogueReassemblyX

/-!
# Budget-Threaded `SessionStructure::clone` Epilogue (Block `80`)

Verifies the relocatable `VmPreserved` epilogue (`+924 → ret`) of Block `80`
(`SessionStructure::clone`) in `SepWPpLsCl`, transporting `A.pool lim st` to the return state.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.EpilogueReassemblyXBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.E2E.Record.Placed (blkPl_80 lsProg_80)
open CryptoVerification.E2E.Record.Serialization (SessionCloneGhost)
open CryptoVerification.E2E.Record.Serialization.SessionCloneAux (
  scDstSlotsAt scDstSlotsWrittenAt scSavedRegsAt scSpillSlotsAt
)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (chunks96_6QAt)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (DstVals)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.EpilogueReassemblyBudget (
  sc_epilogue_placed
)

/-- Relocatable `VmPreserved` epilogue (`+924 → ret`) on `lsProg_80 H` under `SepWPpLsCl`. -/
theorem sc_epilogue_placed_x [LibsignalPlacement]
    {H : LibsignalHooks}
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
      s1.calleeSavedVRegs = s.calleeSavedVRegs →
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
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (scDstSlotsAt x.dst dv ∗
        chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        scSpillSlotsAt s.sp v0c kybPtr' v18 pendPtr' v28 v2c alice'.ptr w28c
          kybCap' scCap' x.s.state.previousCounter rootPtr' 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr x.s.state.sessionVersion localIk'.cap ∗
        scSavedRegsAt s.sp r29 ret r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ∗ F)
      Q Qp :=
  fun _ =>
    sc_epilogue_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice' pqCap' pqPtr'
      scCap' sq0 sq1 sq2 sq3 sq4 sq5 v0c kybCap' kybPtr' pendCap' pendPtr' v18
      w23 w24 v28 v2c w288 w28c r29 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 F
      hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr hnext

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.EpilogueReassemblyXBudget
