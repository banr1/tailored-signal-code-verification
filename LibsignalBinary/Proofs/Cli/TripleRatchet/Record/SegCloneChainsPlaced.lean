/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneChains
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.RegChain

/-!
# Relocatable CLI `SegClone` Sub-Segments 5–7

Proves the `[LibsignalPlacement]` `receiver_chains` clone loop, `pending_pre_key` cloning, and
`pending_kyber_pre_key` cloning on CLI Block `463`.
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

/-- Copy the 104-byte cloned receiver chain from `sp + 0x5f0` to `dst = x23` (`+0x354 → +0x390 / +0x338`). -/
theorem segClone_receiverChains_copy_placed [lsinst : LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (rem : Nat) (src dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64) (F : SepProp)
    (hpc : s.pc = (blkPl_463).base + 0x354#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = off)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 rem)
    (hx22 : s.readReg64 .x22 = src + 0x68#64)
    (hx23 : s.readReg64 .x23 = dst)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : rem < 2 ^ 63)
    (hnext : ∀ s1 : State,
      s1.pc = (if rem = 0 then
                 (blkPl_463).base + 0x390#64
               else
                 (blkPl_463).base + 0x338#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = off + 0x68#64 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = BitVec.ofNat 64 rem →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (chunks104_6QWAt (s.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (chunks104_6QWAt (s.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hpc_rem :
      (if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_463).base + bv% (824) else (blkPl_463).base + bv% (912)) =
      (if rem = 0 then (blkPl_463).base + bv% (912) else (blkPl_463).base + bv% (824)) := by
    rcases Nat.eq_zero_or_pos rem with rfl | hpos
    · simp
    · have hne : rem ≠ 0 := Nat.ne_of_gt hpos
      have hne0 : BitVec.ofNat 64 rem ≠ 0#64 := ofNat_ne_zero_of_pos hpos (by omega)
      have hbeq : (BitVec.ofNat 64 rem == 0#64) = false := beq_false_of_ne hne0
      simp [hne, hbeq]
  clear hrem_lt
  rw [chunks104_6QWAt_sp_0x5f0 s.sp sq0 sq1 sq2 sq3 sq4 sq5 sw6] at hnext ⊢
  unfold chunks104_6QWAt at hnext ⊢
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply SepWPpCl.of_sepWP
    (mid := if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_463).base + bv% (824) else (blkPl_463).base + bv% (912))
  wp_steps
  refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
  refine SepWPpCl.weaken_pre ?_
    (hnext _
      (by rw [← hpc_rem]; segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
      (by segCloneChains_close)
      (by segCloneChains_close)
      (by segCloneChains_close)
      (by segCloneChains_close)
      (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
      (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
  exact Entails.of_eq (by ac_rfl)

/-- Single iteration of the `receiver_chains` clone loop (`+0x338 → +0x390 / +0x338`). -/
theorem segClone_receiverChains_iter_placed [lsinst : LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468) (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    (x : RecordDecryptGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (blkPl_463).base + 0x338#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = src)
    (hx19 : s.readReg64 .x19 = off)
    (hx20 : s.readReg64 .x20 = off + BitVec.ofNat 64 (rem + 1) * 104#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (rem + 1))
    (hx28 : s.readReg64 .x28 = dst_base)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hmul_lt : (rem + 1) * 104 < 2 ^ 63)
    (hnext : ∀ (s1 : State) (g' : ChainGhost),
      s1.pc = (if rem = 0 then
                 (blkPl_463).base + 0x390#64
               else
                 (blkPl_463).base + 0x338#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = off + 0x68#64 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = BitVec.ofNat 64 rem →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = dst_base →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool ∗
          chainAt A (g, rc) src ∗
          chainAt A (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool ∗
        chainAt A (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hcall := hchainClone
  clear hchainClone
  have hsub : ∀ (sf : State) (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
      (sw6 dw6 : BitVec 64) (F_copy : SepProp), _ :=
    fun sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy =>
      segClone_receiverChains_copy_placed (C := C) (A := A) (ctl := ctl)
        (S := S) (H := H) (x := x) (R := R) (s0 := s0) (s := sf) (ret := ret) (Q := Q)
        rem src (dst_base + off) off sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy
  have hsub_eq : (off + BitVec.ofNat 64 (rem + 1) * 104#64) - off =
      BitVec.ofNat 64 (rem + 1) * 104#64 := by bv_arith
  have hmul_beq : (BitVec.ofNat 64 (rem + 1) * 104#64 == 0#64) = false :=
    segClone_bv_ofNat_mul_104_beq_zero (Nat.succ_pos rem) hmul_lt
  have hrem_lt : rem < 2 ^ 63 := by omega
  clear hmul_lt
  apply SepWPpCl.of_sepWP (mid := (lsmpl.base 468))
  wp_steps
  refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
  refine SepWPpCl.weaken_pre
    (P' := (memRegion (s.sp + 0x5f0#64) 104 ∗ chainAt A (g, rc) src ∗ A.pool ∗
              stackAt s.sp chainCloneStack) ∗
            (memRegion (dst_base + off) 104 ∗ F))
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWPpCl.call_frame_cl (x := ⟨s.sp + 0x5f0#64, src, (g, rc)⟩)
      hcall (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
      (ret_pc := (blkPl_463).base + bv% (852)) (by segCloneChains_close)
      rfl ⟨by segCloneChains_close, by segCloneChains_close⟩ rfl
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf _ hm => onPanic_of_callee_panic_placed (by segCloneChains_close) hm)
      fun sf hpcf hrunf hspf hcsm => ?_
  clear hcall
  obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29⟩ := hcsm
  dsimp only [chainCloneSpec]
  simp only [sepConj_assoc]
  refine SepWPpCl.pure_elim fun htr_sf => ?_
  rw [sepExists_sepConj_left]
  refine SepWPpCl.exists_elim fun g' => ?_
  simp only [sepConj_assoc]
  refine SepWPpCl.pure_elim fun ⟨hsrk', hpriv', hkeys'⟩ => ?_
  have hsf_sp : sf.sp = s.sp := hspf
  have hsf19 : sf.readReg64 .x19 = off := by simpa [Reg.x19, hx19] using hcs19
  have hsf20 : sf.readReg64 .x20 = s.readReg64 .x20 := hcs20
  have hsf21 : sf.readReg64 .x21 = BitVec.ofNat 64 rem := by
    rw [segClone_bv_ofNat_succ_sub_one] at hcs21; exact hcs21
  have hsf22 : sf.readReg64 .x22 = src + 0x68#64 := hcs22
  have hsf23 : sf.readReg64 .x23 = dst_base + off := hcs23
  have hsf24 : sf.readReg64 .x24 = s.readReg64 .x24 := hcs24
  have hsf25 : sf.readReg64 .x25 = s.readReg64 .x25 := hcs25
  have hsf26 : sf.readReg64 .x26 = s.readReg64 .x26 := hcs26
  have hsf28 : sf.readReg64 .x28 = dst_base := by simpa [Reg.x28, hx28] using hcs28
  have hsf29 : sf.readReg64 .x29 = s.readReg64 .x29 := hcs29.1
  have hsf_tr : sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    ⟨htr_sf.trans htr.1, hcs29.2.trans htr.2⟩
  have hsf_spA : sf.spAligned = true := by
    unfold State.spAligned at hsp ⊢; rw [hsf_sp]; exact hsp
  dsimp only [State.setPC, State.setPState, State.writeReg64]
  simp only [← hsf_sp]
  refine SepWPpCl.weaken_pre
    (sepConj_mono_left (chainAt_entails_chunks104_6QW A (g', rc) (sf.sp + 0x5f0#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPpCl.exists_elim fun sq0 => SepWPpCl.exists_elim fun sq1 =>
    SepWPpCl.exists_elim fun sq2 => SepWPpCl.exists_elim fun sq3 =>
    SepWPpCl.exists_elim fun sq4 => SepWPpCl.exists_elim fun sq5 =>
    SepWPpCl.exists_elim fun sw6 => ?_
  simp only [sepConj_assoc]
  refine SepWPpCl.pure_elim fun hch_inl => ?_
  refine SepWPpCl.weaken_pre
    (P' := memRegion (dst_base + off) 104 ∗
            chunks104_6QWAt (sf.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
            stackAt sf.sp chainCloneStack ∗ F)
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWPpCl.weaken_pre
    (sepConj_mono_left (memRegion_104_entails_chunks104_6QWAt (dst_base + off))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPpCl.exists_elim fun dq0 => SepWPpCl.exists_elim fun dq1 =>
    SepWPpCl.exists_elim fun dq2 => SepWPpCl.exists_elim fun dq3 =>
    SepWPpCl.exists_elim fun dq4 => SepWPpCl.exists_elim fun dq5 =>
    SepWPpCl.exists_elim fun dw6 => ?_
  refine SepWPpCl.weaken_pre
    (P' := chunks104_6QWAt (sf.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chunks104_6QWAt (dst_base + off) dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗
            (chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
              stackAt sf.sp chainCloneStack ∗ F))
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine hsub sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 _
    hpcf hrunf hsf_spA hsf19 hsf21 hsf22 hsf23 hsf_tr hrem_lt
    fun s1 hpc1 hrun1 hsp1 hspA1 hx1_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
  clear hsub
  rw [hsf_sp]
  refine SepWPpCl.weaken_pre ?_
    (hnext s1 g'
      hpc1 hrun1 (hsp1.trans hsf_sp) hspA1
      hx1_1 hx19_1 (hx20_1.trans hsf20) hx21_1 (hx24_1.trans hsf24)
      (hx25_1.trans hsf25) (hx26_1.trans hsf26) (hx28_1.trans hsf28)
      (hx29_1.trans hsf29) htr1)
  have h104 := chunks104_6QWAt_entails_memRegion (s.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6
  have hdst_chain := chainAt_of_chunks104_6QW A (g', rc) (dst_base + off) hch_inl
  refine Entails.trans (sepConj_mono_left h104) ?_
  refine Entails.trans
    (Q := memRegion (s.sp + 0x5f0#64) 104 ∗
          (chunks104_6QWAt (dst_base + off) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ chainHeap A (g', rc)) ∗
          chainAt A (g, rc) src ∗ A.pool ∗ stackAt s.sp chainCloneStack ∗ F)
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hdst_chain)) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Induction over `rcs_tl` for the `receiver_chains` clone loop (`+0x338 → +0x390`). -/
theorem segClone_receiverChains_loop_placed [lsinst : LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468) (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (dst_base : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length →
      (rcs_tl.length + 1) * 104 < 2 ^ 63 →
      (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      s.pc = (blkPl_463).base + 0x338#64 →
      s.status = .Running →
      s.spAligned = true →
      s.readReg64 .x1 = src →
      s.readReg64 .x19 = off →
      s.readReg64 .x20 = off + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 →
      s.readReg64 .x21 = BitVec.ofNat 64 (rcs_tl.length + 1) →
      s.readReg64 .x28 = dst_base →
      (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) →
      (∀ (s1 : State) (gs' : List ChainGhost),
        gs'.length = (rc :: rcs_tl).length →
        s1.pc = (blkPl_463).base + 0x390#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        s1.spAligned = true →
        s1.readReg64 .x24 = s.readReg64 .x24 →
        s1.readReg64 .x25 = s.readReg64 .x25 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x28 = dst_base →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
        SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
          (A.pool ∗
            arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0x5f0#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            F)
          Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
        (A.pool ∗
          arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  induction rcs_tl with
  | nil =>
    intro s rc g gs_tl src off F hgs hmul_lt _ hpc hrun hsp hx1 hx19 hx20 hx21 hx28 htr hnext
    cases gs_tl with
    | cons _ _ => simp at hgs
    | nil =>
      simp only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil,
        sepConj_emp, List.length_nil, Nat.zero_add, Nat.one_mul] at *
      refine segClone_receiverChains_iter_placed hchainClone x R s0 s ret Q g rc 0 src dst_base off F
        hpc hrun hsp hx1 hx19 hx20 hx21 hx28 htr hmul_lt
        fun s1 g' hpc1 hrun1 hsp1 hspA1 _ _ _ _ hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      simp only [↓reduceIte] at hpc1
      have h1 := hnext s1 [g'] rfl hpc1 hrun1 hsp1 hspA1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1
      simpa only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil, sepConj_emp]
        using h1
  | cons rc2 rcs2 ih =>
    intro s rc g gs_tl src off F hgs hmul_lt hsz_le hpc hrun hsp hx1 hx19 hx20 hx21 hx28 htr hnext
    cases gs_tl with
    | nil => simp at hgs
    | cons g2 gs2 =>
      have hgs2 : gs2.length = rcs2.length := by simpa using hgs
      have hmul2_lt : (rcs2.length + 1) * 104 < 2 ^ 63 := by simp [Nat.add_mul] at hmul_lt; omega
      have hsz2_le : (rcs2.length + 1) * 104 ≤ 2 ^ 64 := by simp [Nat.add_mul] at hsz_le; omega
      have hsplit_mr :
          memRegion (dst_base + off) (((rc2 :: rcs2).length + 1) * 104) =
            memRegion (dst_base + off) 104 ∗
              memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) := by
        refine memRegion_split' (n := 104) (k := (rcs2.length + 1) * 104) ?_
          (by bv_arith) hsz_le
        simp [List.length_cons, Nat.add_mul]; omega
      rw [List.zip_cons_cons, arrayAt_cons, hsplit_mr]
      refine SepWPpCl.weaken_pre
        (P' := A.pool ∗
                chainAt A (g, rc) src ∗
                memRegion (dst_base + off) 104 ∗
                memRegion (s.sp + 0x5f0#64) 104 ∗
                stackAt s.sp chainCloneStack ∗
                (arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                  memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗ F))
        (by exact Entails.of_eq (by ac_rfl)) ?_
      refine segClone_receiverChains_iter_placed hchainClone x R s0 s ret Q g rc (rcs2.length + 1)
        src dst_base off _
        hpc hrun hsp hx1 hx19 hx20 hx21 hx28 htr hmul_lt
        fun s1 g' hpc1 hrun1 hsp1 hspA1 hx1_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      have hne0 : rcs2.length + 1 ≠ 0 := Nat.succ_ne_zero _
      simp only [hne0, ↓reduceIte] at hpc1
      have hx20_next : s1.readReg64 .x20 =
          (off + 0x68#64) + BitVec.ofNat 64 (rcs2.length + 1) * 104#64 := by
        rw [hx20_1, hx20, List.length_cons]
        exact segClone_off_add_succ_mul_104 off (rcs2.length + 1)
      rw [← hsp1]
      refine SepWPpCl.weaken_pre
        (P' := A.pool ∗
                arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗
                memRegion (s1.sp + 0x5f0#64) 104 ∗
                stackAt s1.sp chainCloneStack ∗
                (chainAt A (g, rc) src ∗ chainAt A (g', rc) (dst_base + off) ∗ F))
        (by exact Entails.of_eq (by ac_rfl)) ?_
      refine ih s1 rc2 g2 gs2 (src + 0x68#64) (off + 0x68#64) _
        hgs2 hmul2_lt hsz2_le hpc1 hrun1 hspA1 hx1_1 hx19_1 hx20_next hx21_1 hx28_1 htr1
        fun s2 gs2' hgs2' hpc2 hrun2 hsp2 hspA2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
      rw [hsp1]
      refine SepWPpCl.weaken_pre ?_
        (hnext s2 (g' :: gs2') (by simp [hgs2']) hpc2 hrun2 (by reg_chain) hspA2
          (by reg_chain) (by reg_chain) (by reg_chain)
          hx28_2 (by reg_chain) htr2)
      simp only [List.zip_cons_cons, arrayAt_cons]
      have hd_add : dst_base + off + BitVec.ofNat 64 104 = dst_base + (off + 0x68#64) := by
        bv_arith
      rw [hd_add]
      exact Entails.of_eq (by ac_rfl)

/-- Sub-segment 5 (`+0x544 / +0x300 → +0x548 / +0x390`): clones `receiver_chains`
into a new buffer at `x28 = chainsPtr'` with capacity `chainsCap'`. -/
theorem segClone_receiverChains_placed [lsinst : LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468) (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    (x : RecordDecryptGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (F : SepProp)
    (hpc : s.pc = (if x.st.receiverChains = [] then
                     (blkPl_463).base + 0x544#64
                   else
                     (blkPl_463).base + 0x300#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.st.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.st.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.pc = (if x.st.receiverChains = [] then
                 (blkPl_463).base + 0x548#64
               else
                 (blkPl_463).base + 0x390#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x28 = chainsPtr' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool ∗
          ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool ∗
        ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hshim := hA.shim_ok
  have halloc := hA.alloc_ok
  have hpanic := segClone_panic_0x261c_placed (C := C) (A := A) (ctl := ctl) (S := S) (H := H) hA (ret := ret) (Q := Q) x s0
  cases hrc_eq : x.st.receiverChains with
  | nil =>
    clear hshim halloc hpanic hchainClone
    simp only [hrc_eq, ↓reduceIte, List.length_nil] at hpc hx26 hchains_len ⊢
    apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1352))
    wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    refine SepWPpCl.weaken_pre ?_
      (hnext _ 0#64 8#64 [] (by simp [hrc_eq]) (by simp [hrc_eq])
        (by simp only [hrc_eq, ↓reduceIte]; segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by simp only [hrc_eq, List.length_nil]; segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close))
    simp only [hrc_eq, List.zip_nil_right, segClone_vecBuf_chain_nil_eq]
    exact Entails.of_eq (by ac_rfl)
  | cons rc rcs_tl =>
    have hsub := segClone_receiverChains_loop_placed (C := C) (A := A) (ctl := ctl)
      (S := S) (H := H) hchainClone x R s0 ret Q
    clear hchainClone
    have hne : x.st.receiverChains ≠ [] := by simp [hrc_eq]
    simp only [hne, ↓reduceIte] at hpc hnext
    rw [hrc_eq] at hx26
    cases hgs_eq : x.G.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hgs_tl : gs_tl.length = rcs_tl.length := by
        rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hexpose :=
        segClone_vecBuf_expose_arrayAt A (stride := 104) 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
          ((g :: gs_tl).zip (rc :: rcs_tl))
      refine SepWPpCl.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (hexpose _))) ?_
      refine sepWPpCl_pure_3rd fun hmul_lt => ?_
      have hzip_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs_tl]
      rw [hzip_len] at hmul_lt
      have hpos : 0 < (rc :: rcs_tl).length := by simp
      have hpos_mul : 0 < (rc :: rcs_tl).length * 104 := by simp [List.length_cons]
      have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by simp [List.length_cons] at hmul_lt; omega
      have hsz_le63 : (rc :: rcs_tl).length * 104 + 8 ≤ 2 ^ 63 := by
        simp [List.length_cons] at hmul_lt ⊢; omega
      have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat =
          (rc :: rcs_tl).length * 104 :=
        segClone_bv_ofNat_mul_104_toNat hmul_lt
      have hpow2 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      have hlay : LayoutOk ((rc :: rcs_tl).length * 104) 8 :=
        ⟨hpos_mul, hpow2, hsz_le63⟩
      rw [stackAt_chainClone_eq_alloc s.sp]
      apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (796))
      wp_steps
      wp_call hshim ()
      clear hshim
      wp_steps
      wp_call halloc ((rc :: rcs_tl).length * 104, 8)
      clear halloc
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
      · clear hsub hnext
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPpCl_pure_3rd fun htrace => ?_
        apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (9756))
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        exact hpanic _ _ R (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
      · clear hpanic
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        refine sepWPpCl_pure_3rd fun ⟨hmod, htrace⟩ => ?_
        apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (824))
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        have hsf_sp : sf.sp = s.sp := by segCloneChains_close
        have hsf1_sp : sf_1.sp = s.sp := by segCloneChains_close
        set ptr' := sf_1.readReg64 (Reg.gpr 0#5)
        have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
        have hsz_eq : (rc :: rcs_tl).length * 104 = (rcs_tl.length + 1) * 104 := rfl
        refine SepWPpCl.weaken_pre
          (P' := A.pool ∗
                  arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                  memRegion (sf_1.sp + 0x5f0#64) 104 ∗
                  stackAt sf_1.sp chainCloneStack ∗
                  (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                    ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
                    segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr
                      ((g :: gs_tl).zip (rc :: rcs_tl)) ∗ F))
          (by rw [hsf1_sp, hsf_sp, hptr_zero, ← hsz_eq, stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl)) ?_
        refine hsub ptr' rcs_tl _
          rc g gs_tl x.G.chainsPtr 0#64 _
          hgs_tl (by simpa [List.length_cons] using hmul_lt) hsz_le
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close)
          (by segCloneChains_close) (by dsimp only [ptr']; segCloneChains_close) (by segCloneChains_close)
          fun s2 gs' hgs' hpc2 hrun2 hsp2 hspA2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
        clear hsub
        dsimp only [Reg.x24, Reg.x25, Reg.x26, Reg.x29] at hx24_2 hx25_2 hx26_2 hx29_2
        simp (config := { decide := true }) only [State.sp_setPC, State.sp_writeReg64_gpr,
          State.readReg64_setPC, State.readReg64_writeReg64, reduceStateReadReg64] at hsp2 hx24_2 hx25_2 hx26_2 hx29_2
        rw [hptr_zero]
        refine SepWPpCl.weaken_pre ?_
          (hnext s2 (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' gs'
            (by rw [hrc_eq]; exact hgs') (by rw [hrc_eq])
            hpc2 hrun2 (by segCloneChains_close) hspA2
            (by segCloneChains_close) (by segCloneChains_close) (by simp only [hrc_eq]; segCloneChains_close)
            hx28_2 (by segCloneChains_close) htr2)
        dsimp only [State.setPC, State.setPState, State.writeReg64]
        simp only [hgs_eq, hrc_eq, hsf1_sp]
        have hreasm :=
          segClone_vecBuf_reassemble_arrayAt A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
            ((g :: gs_tl).zip (rc :: rcs_tl))
        have hnew_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
          simp [hgs']
        have hnew_pos : 0 < (gs'.zip (rc :: rcs_tl)).length := by rw [hnew_len]; exact hpos
        have hnew_lt : (gs'.zip (rc :: rcs_tl)).length * 104 < 2 ^ 63 := by rw [hnew_len]; exact hmul_lt
        have hnew_buf := segClone_vecBuf_chain_of_arrayAt A ptr' (gs'.zip (rc :: rcs_tl)) hnew_pos hnew_lt hoom64
        rw [hnew_len] at hnew_buf
        refine Entails.trans
          (Q := (arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
                (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                  arrayAt (chainAt A) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
                A.pool ∗ ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
                memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
          (Entails.of_eq (by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hreasm (sepConj_mono_left hnew_buf)) ?_
        exact Entails.of_eq (by ac_rfl)

theorem segClone_pendingPreKey_39c_pos_placed [lsinst : LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 : BitVec 64}
    {v08 v18 : BitVec 64} {v24 v28 v2c : BitVec 32} {F : SepProp}
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((s.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((s.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s.sp + 0x24c#64) ↦₃₂ tw1) ∗
        ((s.sp + 0x250#64) ↦₆₄ td2) ∗ ((s.sp + 0x258#64) ↦₃₂ tw3) ∗
        ((s.sp + 0x25c#64) ↦₃₂ tw4)))
    (hpos : 0 < gp.vec.bytes.length)
    (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63)
    (hptr : gp.vec.ptr ≠ 0)
    (hpc : s.pc = (blkPl_463).base + 0x39c#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32),
      (s1.pc = (blkPl_463).base + 0x558#64 ∨
       s1.pc = (blkPl_463).base + 0x1904#64 ∨
       s1.pc = (blkPl_463).base + 0x3e8#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool ∗
          (⌜gp.tail.length = 48 - 24⌝ ∗
            vecGhostAt A gp.vec (s.sp + 0x230#64) ∗
            ((s.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length⌝ ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool ∗
        ((s.sp + 0x230#64) ↦₆₄ gp.vec.cap) ∗
        ((s.sp + 0x238#64) ↦₆₄ gp.vec.ptr) ∗
        ((s.sp + 0x240#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
        (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
          (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((s.sp + 0x248#64) ↦₃₂ tw0) ∗
        ((s.sp + 0x24c#64) ↦₃₂ tw1) ∗
        ((s.sp + 0x250#64) ↦₆₄ td2) ∗
        ((s.sp + 0x258#64) ↦₃₂ tw3) ∗
        ((s.sp + 0x25c#64) ↦₃₂ tw4) ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hshim := hA.shim_ok
  have halloc := hA.alloc_ok
  have hmemcpy := hA.memcpy_ok
  have hpanic := segClone_panic_0x2604_placed (C := C) (A := A) (ctl := ctl) (S := S) (H := H) hA (ret := ret) (Q := Q) x s0
  have h238 : s.sp + 0x230#64 + 8#64 = s.sp + 0x238#64 := by bv_arith
  have h240 : s.sp + 0x230#64 + 16#64 = s.sp + 0x240#64 := by bv_arith
  have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gp.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos (by omega)
  have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpos (by omega)
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk gp.vec.bytes.length 1 := ⟨hpos, hpow2, hlen_le63⟩
  have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (972))
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (gp.vec.bytes.length, 1)
  clear halloc
  refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPpCl_pure_3rd fun htrace => ?_
    apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (9732))
    wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    exact hpanic _ _ R (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPpCl_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1000))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gp.vec.ptr, gp.vec.bytes)
    clear hmemcpy
    wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    have hsp_eq : sf.sp = s.sp := by segCloneChains_close
    refine SepWPpCl.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gp.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) td2 tw3 tw0 tw1
        (Or.inr (Or.inr (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
    have h_rfl : (⌜BitVec.ofNat 64 gp.vec.bytes.length = BitVec.ofNat 64 gp.vec.bytes.length⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
      segClone_pure_eq_emp htail
    have h_pure2 : (⌜gp.vec.bytes.length ≤ gp.vec.cap.toNat ∧ gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_pos A gp.vec (s.sp + 0x230#64) hpos, h238, h240,
        htail_eq,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) gp.vec.bytes hpos hlen_lt hoom64,
        h_rfl, h_pure1, h_pure2]
    simp only [sepConj_assoc, hsp_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Sub-segment 6 (`+0x548 / +0x390 → +0x558 / +0x1904 / +0x3e8`): clones `pending_pre_key`
into `x22 = pendCap'` and `[sp + 0x18] = pendPtr'`, plus spill slots `[sp + 0x08, 0x24, 0x28, 0x2c]`. -/
theorem segClone_pendingPreKey_placed [lsinst : LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v08 v18 : BitVec 64} {v24 v28 v2c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.st.receiverChains = [] then
                     (blkPl_463).base + 0x548#64
                   else
                     (blkPl_463).base + 0x390#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32),
      (s1.pc = (blkPl_463).base + 0x558#64 ∨
       s1.pc = (blkPl_463).base + 0x1904#64 ∨
       s1.pc = (blkPl_463).base + 0x3e8#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool ∗
          optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
          OptPendClone A x.G.pending pendCap' pendPtr' ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool ∗
        optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗
        F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  cases hpend : x.G.pending with
  | none =>
    rw [hpend] at hnext
    dsimp only [optTailVecAt, OptPendClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    by_cases hrc : x.st.receiverChains = []
    · simp only [hrc, ↓reduceIte] at hpc
      apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1368))
      wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      refine SepWPpCl.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v18 v08 v24 v28 v2c
          (Or.inl (by segCloneChains_close)) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · simp only [hrc, ↓reduceIte] at hpc
      apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1368))
      wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      refine SepWPpCl.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v18 v08 v24 v28 v2c
          (Or.inl (by segCloneChains_close)) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  | some gp =>
    rw [hpend] at hnext
    dsimp only [optTailVecAt, OptPendClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, _, htail_pts⟩ := exists_tail24_decomp htail
    have h238 : s.sp + 0x230#64 + 8#64 = s.sp + 0x238#64 := by bv_arith
    have h240 : s.sp + 0x230#64 + 16#64 = s.sp + 0x240#64 := by bv_arith
    have h248 : s.sp + 0x230#64 + BitVec.ofNat 64 24 = s.sp + 0x248#64 := by bv_arith
    have h24c : s.sp + 0x248#64 + 4#64 = s.sp + 0x24c#64 := by bv_arith
    have h250 : s.sp + 0x248#64 + 8#64 = s.sp + 0x250#64 := by bv_arith
    have h258 : s.sp + 0x248#64 + 16#64 = s.sp + 0x258#64 := by bv_arith
    have h25c : s.sp + 0x248#64 + 20#64 = s.sp + 0x25c#64 := by bv_arith
    rw [h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c]
    rcases eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · rw [vecGhostAt_eq_of_nil A gp.vec (s.sp + 0x230#64) hnil, h238, h240]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      by_cases hrc : x.st.receiverChains = []
      · simp only [hrc, ↓reduceIte] at hpc
        apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (6404))
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        refine SepWPpCl.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw3 tw0 tw1
            (Or.inr (Or.inl (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
        rw [vecGhostAt_eq_of_nil A gp.vec (s.sp + 0x230#64) hnil, h238, h240,
            h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
      · simp only [hrc, ↓reduceIte] at hpc
        apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (6404))
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        refine SepWPpCl.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw3 tw0 tw1
            (Or.inr (Or.inl (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
        rw [vecGhostAt_eq_of_nil A gp.vec (s.sp + 0x230#64) hnil, h238, h240,
            h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gp.vec (s.sp + 0x230#64) hpos, h238, h240]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hsub := fun (s_39c : State) (htail_eq_39c : ((s_39c.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
          (((s_39c.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s_39c.sp + 0x24c#64) ↦₃₂ tw1) ∗
            ((s_39c.sp + 0x250#64) ↦₆₄ td2) ∗ ((s_39c.sp + 0x258#64) ↦₃₂ tw3) ∗
            ((s_39c.sp + 0x25c#64) ↦₃₂ tw4))) =>
        segClone_pendingPreKey_39c_pos_placed (C := C) (A := A) (ctl := ctl)
          (S := S) (H := H) hA (x := x) (R := R) (s0 := s0) (s := s_39c) (ret := ret) (Q := Q)
          (gp := gp) (tw0 := tw0) (tw1 := tw1) (tw3 := tw3) (tw4 := tw4) (td2 := td2)
          (v08 := v08) (v18 := v18) (v24 := v24) (v28 := v28) (v2c := v2c) (F := F)
          htail htail_eq_39c hpos hlen_le hcap_lt hptr
      suffices h_at_39c : ∀ s_39c : State,
          s_39c.pc = (blkPl_463).base + bv% (924) →
          s_39c.status = .Running →
          s_39c.sp = s.sp →
          s_39c.spAligned = true →
          s_39c.readReg64 .x24 = s.readReg64 .x24 →
          s_39c.readReg64 .x25 = s.readReg64 .x25 →
          s_39c.readReg64 .x26 = s.readReg64 .x26 →
          s_39c.readReg64 .x28 = s.readReg64 .x28 →
          s_39c.readReg64 .x29 = s.readReg64 .x29 →
          (s_39c.trace = s0.trace ∧ calleeSavedVRegs s_39c = calleeSavedVRegs s0) →
          SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s_39c
            (A.pool ∗
              (s_39c.sp + 0x230#64) ↦₆₄ gp.vec.cap ∗
              (s_39c.sp + 0x238#64) ↦₆₄ gp.vec.ptr ∗
              (s_39c.sp + 0x240#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length ∗
              (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
              A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
              memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
                (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
              (s_39c.sp + 0x248#64) ↦₃₂ tw0 ∗
              (s_39c.sp + 0x24c#64) ↦₃₂ tw1 ∗
              (s_39c.sp + 0x250#64) ↦₆₄ td2 ∗
              (s_39c.sp + 0x258#64) ↦₃₂ tw3 ∗
              (s_39c.sp + 0x25c#64) ↦₃₂ tw4 ∗
              (s_39c.sp + 0x08#64) ↦₆₄ v08 ∗
              (s_39c.sp + 0x18#64) ↦₆₄ v18 ∗
              (s_39c.sp + 0x24#64) ↦₃₂ v24 ∗
              (s_39c.sp + 0x28#64) ↦₃₂ v28 ∗
              (s_39c.sp + 0x2c#64) ↦₃₂ v2c ∗
              stackAt s_39c.sp allocHookStack ∗ F)
            Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) by
        clear hsub
        by_cases hrc : x.st.receiverChains = []
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (924))
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
          exact h_at_39c _ (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (924))
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
          exact h_at_39c _ (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
      intro s_39c hpc39c hrun39c hsp39c hspA39c hx24_39c hx25_39c hx26_39c hx28_39c hx29_39c htr39c
      have htail_eq_39c : ((s_39c.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
          (((s_39c.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s_39c.sp + 0x24c#64) ↦₃₂ tw1) ∗
            ((s_39c.sp + 0x250#64) ↦₆₄ td2) ∗ ((s_39c.sp + 0x258#64) ↦₃₂ tw3) ∗
            ((s_39c.sp + 0x25c#64) ↦₃₂ tw4)) := by
        rw [hsp39c, h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c]
      refine hsub s_39c htail_eq_39c hpc39c hrun39c hspA39c htr39c
        fun s1 pendCap' pendPtr' v08' v24' v28' v2c' hpc1 hrun1 hsp1 hspA1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      clear hsub
      rw [hsp39c]
      exact hnext s1 pendCap' pendPtr' v08' v24' v28' v2c'
        hpc1 hrun1 (by reg_chain) hspA1
        hx22_1 (by reg_chain) (by reg_chain)
        (by reg_chain) (by reg_chain) (by reg_chain) htr1

theorem segClone_pendingKyber_3f8_pos_placed [lsinst : LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gk : TailVecGhost} {kw0 kw1 : BitVec 32}
    {v00 : BitVec 64} {v14 : BitVec 32} {F : SepProp}
    (htail : gk.tail.length = 32 - 24)
    (htail_pts : ∀ a : BitVec 64,
      (a ↦ₛ gk.tail) = ((a ↦₃₂ kw0) ∗ ((a + 4#64) ↦₃₂ kw1)))
    (hpos : 0 < gk.vec.bytes.length)
    (hlen_le : gk.vec.bytes.length ≤ gk.vec.cap.toNat)
    (hcap_lt : gk.vec.cap.toNat < 2 ^ 63)
    (hptr : gk.vec.ptr ≠ 0)
    (hpc : s.pc = (blkPl_463).base + 0x3f8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32),
      (s1.pc = (blkPl_463).base + 0x56c#64 ∨
       s1.pc = (blkPl_463).base + 0x1920#64 ∨
       s1.pc = (blkPl_463).base + 0x430#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool ∗
          (⌜gk.tail.length = 32 - 24⌝ ∗
            vecGhostAt A gk.vec (s.sp + 0x260#64) ∗
            ((s.sp + 0x260#64 + BitVec.ofNat 64 24) ↦ₛ gk.tail)) ∗
          (⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length⌝ ∗
            vecU8Buf A kybCap' kybPtr' gk.vec.bytes) ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool ∗
        ((s.sp + 0x260#64) ↦₆₄ gk.vec.cap) ∗
        ((s.sp + 0x268#64) ↦₆₄ gk.vec.ptr) ∗
        ((s.sp + 0x270#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length) ∗
        (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
        A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
        memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length)
          (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
        ((s.sp + 0x278#64) ↦₃₂ kw0) ∗
        ((s.sp + 0x27c#64) ↦₃₂ kw1) ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hshim := hA.shim_ok
  have halloc := hA.alloc_ok
  have hmemcpy := hA.memcpy_ok
  have hpanic := segClone_panic_0x2634_placed (C := C) (A := A) (ctl := ctl) (S := S) (H := H) hA (ret := ret) (Q := Q) x s0
  have h268 : s.sp + 0x260#64 + 8#64 = s.sp + 0x268#64 := by bv_arith
  have h270 : s.sp + 0x260#64 + 16#64 = s.sp + 0x270#64 := by bv_arith
  have h278 : s.sp + 0x260#64 + BitVec.ofNat 64 24 = s.sp + 0x278#64 := by bv_arith
  have h27c : s.sp + 0x278#64 + 4#64 = s.sp + 0x27c#64 := by bv_arith
  have hlen_lt : gk.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gk.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gk.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hlen_ne : BitVec.ofNat 64 gk.vec.bytes.length ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos (by omega)
  have hlen_beq : (BitVec.ofNat 64 gk.vec.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpos (by omega)
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk gk.vec.bytes.length 1 := ⟨hpos, hpow2, hlen_le63⟩
  have htoNat : (BitVec.ofNat 64 gk.vec.bytes.length).toNat = gk.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1052))
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (gk.vec.bytes.length, 1)
  clear halloc
  refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPpCl_pure_3rd fun htrace => ?_
    apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (9780))
    wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    exact hpanic _ _ R (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPpCl_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1072))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gk.vec.ptr, gk.vec.bytes)
    clear hmemcpy
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    have hsp_eq : sf.sp = s.sp := by segCloneChains_close
    refine SepWPpCl.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gk.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) kw0
        (Or.inr (Or.inr (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close))
    have h_rfl : (⌜BitVec.ofNat 64 gk.vec.bytes.length = BitVec.ofNat 64 gk.vec.bytes.length⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp :=
      segClone_pure_eq_emp htail
    have h_pure2 : (⌜gk.vec.bytes.length ≤ gk.vec.cap.toNat ∧ gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_pos A gk.vec (s.sp + 0x260#64) hpos, h268, h270,
        h278, htail_pts (s.sp + 0x278#64), h27c,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) gk.vec.bytes hpos hlen_lt hoom64,
        h_rfl, h_pure1, h_pure2]
    dsimp only [Reg.x25]
    simp only [sepConj_assoc, hsp_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Sub-segment 7 (`+0x558 / +0x1904 / +0x3e8 → +0x56c / +0x1920 / +0x430`):
stores `[sp + 0x3c] = w25` (`session_version`) and clones `pending_kyber_pre_key`
into `x19 = kybCap'`, `[sp + 0x00] = kybPtr'`, and `[sp + 0x14] = v14'`. -/
theorem segClone_pendingKyber_placed [lsinst : LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v00 : BitVec 64} {v14 v3c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (blkPl_463).base + 0x558#64 ∨
           s.pc = (blkPl_463).base + 0x1904#64 ∨
           s.pc = (blkPl_463).base + 0x3e8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32),
      (s1.pc = (blkPl_463).base + 0x56c#64 ∨
       s1.pc = (blkPl_463).base + 0x1920#64 ∨
       s1.pc = (blkPl_463).base + 0x430#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool ∗
          optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
          OptKybClone A x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool ∗
        optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        stackAt s.sp allocHookStack ∗
        F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  cases hkyb : x.G.kyber with
  | none =>
    rw [hkyb] at hnext
    dsimp only [optTailVecAt, OptKybClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    rcases hpc with hpc | hpc | hpc
    · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1388))
      wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      refine SepWPpCl.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v00 v14
          (Or.inl (by segCloneChains_close)) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close))
      rw [h_rfl]; dsimp only [Reg.x25]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1388))
      wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      refine SepWPpCl.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v00 v14
          (Or.inl (by segCloneChains_close)) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close))
      rw [h_rfl]; dsimp only [Reg.x25]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1388))
      wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      refine SepWPpCl.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v00 v14
          (Or.inl (by segCloneChains_close)) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close))
      rw [h_rfl]; dsimp only [Reg.x25]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  | some gk =>
    rw [hkyb] at hnext
    dsimp only [optTailVecAt, OptKybClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPpCl_pure_2nd fun htail => ?_
    obtain ⟨kw0, kw1, _, htail_pts⟩ := exists_unpack32_pair_of_length_8 htail
    have h268 : s.sp + 0x260#64 + 8#64 = s.sp + 0x268#64 := by bv_arith
    have h270 : s.sp + 0x260#64 + 16#64 = s.sp + 0x270#64 := by bv_arith
    have h278 : s.sp + 0x260#64 + BitVec.ofNat 64 24 = s.sp + 0x278#64 := by bv_arith
    have h27c : s.sp + 0x278#64 + 4#64 = s.sp + 0x27c#64 := by bv_arith
    rw [h278, htail_pts (s.sp + 0x278#64), h27c]
    rcases eq_nil_or_length_pos gk.vec.bytes with hnil | hpos
    · rw [vecGhostAt_eq_of_nil A gk.vec (s.sp + 0x260#64) hnil, h268, h270]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      rcases hpc with hpc | hpc | hpc
      · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (6432))
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        refine SepWPpCl.weaken_pre ?_
          (hnext _ 0#64 1#64 kw0
            (Or.inr (Or.inl (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close))
        rw [vecGhostAt_eq_of_nil A gk.vec (s.sp + 0x260#64) hnil, h268, h270,
            h278, htail_pts (s.sp + 0x278#64), h27c, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        dsimp only [Reg.x25]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
      · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (6432))
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        refine SepWPpCl.weaken_pre ?_
          (hnext _ 0#64 1#64 kw0
            (Or.inr (Or.inl (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close))
        rw [vecGhostAt_eq_of_nil A gk.vec (s.sp + 0x260#64) hnil, h268, h270,
            h278, htail_pts (s.sp + 0x278#64), h27c, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        dsimp only [Reg.x25]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
      · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (6432))
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        refine SepWPpCl.weaken_pre ?_
          (hnext _ 0#64 1#64 kw0
            (Or.inr (Or.inl (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close))
        rw [vecGhostAt_eq_of_nil A gk.vec (s.sp + 0x260#64) hnil, h268, h270,
            h278, htail_pts (s.sp + 0x278#64), h27c, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        dsimp only [Reg.x25]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gk.vec (s.sp + 0x260#64) hpos, h268, h270]
      simp only [sepConj_assoc]
      refine sepWPpCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hsub : ∀ (s_3f8 : State), _ := fun s_3f8 =>
        segClone_pendingKyber_3f8_pos_placed (C := C) (A := A) (ctl := ctl)
          (S := S) (H := H) hA (x := x) (R := R) (s0 := s0) (s := s_3f8) (ret := ret) (Q := Q)
          (gk := gk) (kw0 := kw0) (kw1 := kw1) (v00 := v00) (v14 := v14) (F := F)
          htail htail_pts hpos hlen_le hcap_lt hptr
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      suffices h_at_3f8 : ∀ s_3f8 : State,
          s_3f8.pc = (blkPl_463).base + bv% (1016) →
          s_3f8.status = .Running →
          s_3f8.sp = s.sp →
          s_3f8.spAligned = true →
          s_3f8.readReg64 .x22 = s.readReg64 .x22 →
          s_3f8.readReg64 .x24 = s.readReg64 .x24 →
          s_3f8.readReg64 .x25 = s.readReg64 .x25 →
          s_3f8.readReg64 .x26 = s.readReg64 .x26 →
          s_3f8.readReg64 .x28 = s.readReg64 .x28 →
          s_3f8.readReg64 .x29 = s.readReg64 .x29 →
          (s_3f8.trace = s0.trace ∧ calleeSavedVRegs s_3f8 = calleeSavedVRegs s0) →
          SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s_3f8
            (A.pool ∗
              (s_3f8.sp + 0x260#64) ↦₆₄ gk.vec.cap ∗
              (s_3f8.sp + 0x268#64) ↦₆₄ gk.vec.ptr ∗
              (s_3f8.sp + 0x270#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length ∗
              (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
              A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
              memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length)
                (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
              (s_3f8.sp + 0x278#64) ↦₃₂ kw0 ∗
              (s_3f8.sp + 0x27c#64) ↦₃₂ kw1 ∗
              (s_3f8.sp ↦₆₄ v00) ∗
              (s_3f8.sp + 0x14#64) ↦₃₂ v14 ∗
              (s_3f8.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32 ∗
              stackAt s_3f8.sp allocHookStack ∗ F)
            Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) by
        clear hsub
        rcases hpc with hpc | hpc | hpc
        · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1016))
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
          dsimp only [Reg.x25] at h_at_3f8
          exact h_at_3f8 _ (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1016))
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
          dsimp only [Reg.x25] at h_at_3f8
          exact h_at_3f8 _ (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        · apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (1016))
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
          dsimp only [Reg.x25] at h_at_3f8
          exact h_at_3f8 _ (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
      intro s_3f8 hpc3f8 hrun3f8 hsp3f8 hspA3f8 hx22_3f8 hx24_3f8 hx25_3f8 hx26_3f8 hx28_3f8 hx29_3f8 htr3f8
      rw [← hx25_3f8]
      refine hsub s_3f8 hpc3f8 hrun3f8 hspA3f8 htr3f8
        fun s1 kybCap' kybPtr' v14' hpc1 hrun1 hsp1 hspA1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      clear hsub
      rw [hsp3f8, hx25_3f8]
      exact hnext s1 kybCap' kybPtr' v14'
        hpc1 hrun1 (by reg_chain) hspA1
        hx19_1 (by reg_chain) (by reg_chain) (by reg_chain)
        (by reg_chain) (by reg_chain) (by reg_chain) htr1

end CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps
