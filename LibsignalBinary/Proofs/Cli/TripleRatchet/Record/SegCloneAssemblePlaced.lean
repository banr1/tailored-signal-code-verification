/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneAssemble
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlaced
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Destination Slot Assembly for CLI `SegClone`

Proves the `[LibsignalPlacement]` destination `SessionStructure` slot assembly and version-check
branch (`+0x594 → +0x69c / +0x7e4`) on CLI Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record hiding LibsignalCodeRoLoaded ls_externAt?_226 ls_hook_ok_226 recEntryPlaced recVPCPlaced recMPCPlaced recFPCPlaced recJPCPlaced recExitPlaced recMetaPlaced recFramePlaced tryDecryptPlacedSpec recordDecryptPlacedSpec VStatePlaced MStatePlaced FStatePlaced JStatePlaced SegClonePlacedSpec SegDecryptPlacedSpec SegMismatchPlacedSpec SegTailPlacedSpec SegExitPlacedSpec rootStack_le_of_recordPlacedPre recordDecrypt_placed_region_ok_of_seams
open CryptoVerification.Cli.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps hiding clonePanicPostPlaced segClone_assemble_1_placed segClone_assemble_2_placed segClone_fields_10_to_11_placed
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.Cli.CoinsTape

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Destination Slot Assembly -/

abbrev clonePanicPostPlaced [lsmpl : LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (recordDecryptPlacedSpec C A ctl parse S).onPanic x s0 sf ∗ R)

/-- First half of destination slot assembly (`+0x594 → +0x620`, 35 instructions) under
`[LibsignalPlacement]`. -/
theorem segClone_assemble_1_placed [lsmpl : LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (v00 v08 : BitVec 64) (w14 : BitVec 32) (pendPtr' : BitVec 64)
    (w24 w28 w2c sessionVersion previousCounter : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_463).base + 1428#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64) (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_463).base + 1568#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x8 = w2c.setWidth 64 → s1.readReg64 .x9 = w28.setWidth 64 →
      s1.readReg64 .x10 = previousCounter.setWidth 64 → s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 → s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
          scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
            scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗ F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
          scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  unfold segClone_dstSlotsMidAt spillSlotsAt at hnext
  unfold dstSlotsAt spillSlotsAt
  rw [chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      segClone_chunks96_6QAt_sp_0xd38 s.sp dv.q0 dv.q1 dv.q2 dv.q3 dv.q4 dv.q5]
  rw [chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      segClone_chunks96_6QAt_sp_0xd38 s.sp sq0 sq1 sq2 sq3 sq4 sq5] at hnext
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_463).base + 1568#64)
  wp_steps
  refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close))
  exact Entails.of_eq (by ac_rfl)

/-- Second half of destination slot assembly and version check (`+0x620 → +0x69c / +0x7e4`,
31 instructions) under `[LibsignalPlacement]`. -/
theorem segClone_assemble_2_placed [lsmpl : LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' : BitVec 64)
    (alice' : VecGhost) (pqCap' pqPtr' scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c w288 w28c : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_463).base + 1568#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = w2c.setWidth 64) (hx9 : s.readReg64 .x9 = w28.setWidth 64)
    (hx10 : s.readReg64 .x10 = x.st.previousCounter.setWidth 64)
    (hx19 : s.readReg64 .x19 = kybCap') (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64) (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64) (_hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap) (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s
      (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
        scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hver_eq_iff :
      x.st.version.toNat = x.msg.messageVersion.toNat ↔
        (if x.st.sessionVersion = 0 then 2 else x.st.sessionVersion) =
          x.msg.messageVersion.setWidth 32 := by
    unfold SessionState.version
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.msg.messageVersion.isLt; omega)]
    · intro h
      have ht := congrArg BitVec.toNat h
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.msg.messageVersion.isLt; omega)] at ht
  have hpc_ver :
      (if (if x.st.sessionVersion = 0 then 2#64 else BitVec.truncate 64 x.st.sessionVersion) =
          BitVec.zeroExtend 64 x.msg.messageVersion then (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64) =
      (if x.st.version.toNat = x.msg.messageVersion.toNat then (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64) := by
    simp only [segClone_version_cond_iff, ← hver_eq_iff]
  unfold segClone_dstSlotsWrittenAt spillSlotsAt at hnext
  unfold segClone_dstSlotsMidAt spillSlotsAt
  simp only [sepConj_assoc] at hnext ⊢
  apply SepWPp.of_sepWP
    (mid := if x.st.version.toNat = x.msg.messageVersion.toNat then (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64)
  wp_steps
  refine SepWP.done (by simpa using hpc_ver) (by exact hrun) ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simpa using hpc_ver) (by exact hrun) rfl hsp rfl rfl (by segCloneAssemble_close))
  exact Entails.of_eq (by ac_rfl)

theorem segClone_fields_10_to_11_placed [lsmpl : LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' : BitVec 64)
    (alice' : VecGhost) (pqCap' pqPtr' scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c w288 w28c : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_463).base + 1428#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = kybCap') (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64) (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64) (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap) (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr) (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (blkPl_463).base + 1692#64 else (blkPl_463).base + 2020#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPp ((blkPC_463).rebase (blkPl_463).base H) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  refine segClone_assemble_1_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybPtr' v08 w14 pendPtr' w24 w28 w2c
    x.st.sessionVersion x.st.previousCounter
    (((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
    hpc hrun hsp hx24 hx28 htr
    fun s1 hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx24_1 ⊢
  refine SepWPp.weaken_pre
    (P' := segClone_dstSlotsMidAt s1.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
            scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          spillSlotsAt s1.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_assemble_2_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08 w14 pendCap' pendPtr'
    w24 w28 w2c w288 w28c
    (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F)
    hpc1 hrun1 hspA1 hx8_1 hx9_1 hx10_1
    (by reg_chain) (by reg_chain) (by reg_chain)
    (by reg_chain) (by reg_chain) hx24_1
    (by reg_chain) (by reg_chain) (by reg_chain) htr1
    fun s2 hpc2 hrun2 hsp2 hspA2 hx9_2 hx29_2 htr2 => ?_
  rw [hsp1]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s2 hpc2 hrun2 (by reg_chain) hspA2 hx9_2 (by reg_chain) htr2)

end CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps
