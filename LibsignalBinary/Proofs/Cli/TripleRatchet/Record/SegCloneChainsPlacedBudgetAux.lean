/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlaced
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneChains -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegClone` Sub-Segment 5 (`receiver_chains` Loop)

Proves `receiver_chains` cloning (`+0x544 / +0x300 → +0x548 / +0x390`) on CLI Block `463`,
threading `RustCliAllocBudget M` (`A.pool`) and `FitsEvents`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (
  LibsignalPlacement lsmpl withLsCodeLoaded lsRustNoAllocShimSym lsRustAllocSym
)
open CryptoVerification.RustHeap (allocHookStack arrayAt arrayAt_cons arrayAt_nil vecBuf)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet (RecordDecryptGhost sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  chunks104_6QWAt chainHeap chainAt_entails_chunks104_6QW chainAt_of_chunks104_6QW
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  ofNat_ne_zero_of_pos chunks104_6QWAt_sp_0x5f0 chunks104_6QWAt_entails_memRegion
  memRegion_104_entails_chunks104_6QWAt pointsTo128_eq_pointsTo64 stackAt_chainClone_eq_alloc
  segClone_bv_ofNat_mul_104_beq_zero segClone_bv_ofNat_succ_sub_one
  segClone_off_add_succ_mul_104 segClone_bv_ofNat_mul_104_toNat
  segClone_vecBuf_chain_nil_eq segClone_vecBuf_expose_arrayAt segClone_vecBufRest
  segClone_vecBuf_reassemble_arrayAt segClone_vecBuf_chain_of_arrayAt
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps (SepWPpCl sepWPpCl_pure_3rd)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved AllocCallPreserved
  RustLayoutOk FitsEvents FitsEnv fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv chainCloneEvents chainCloneSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  SegCloneHooks SepWPpCl_of_sepWP_vm
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget (sepWP_cut_here)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Deterministic `AllocEvent` sequence for `receiver_chains` cloning, matching `segCloneEvents`. -/
def receiverChainsCloneEvents (chains : List ChainGhost) (rcs : List ReceiverChain) :
    List AllocEvent :=
  if rcs = [] then []
  else rustAllocEvents (104 * rcs.length) 8 ++ (chains.zip rcs).flatMap chainCloneEvents

/-- Copy the 104-byte cloned receiver chain from `sp + 0x5f0` to `dst = x23`
    (`+0x354 → +0x390 / +0x338`), threading `VmPreserved s s1` and polymorphic in `{Q Qp}`. -/
theorem segClone_receiverChains_copy_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
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
      VmPreserved s s1 →
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
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (chunks104_6QWAt (s.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q Qp := by
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
  apply SepWPpCl_of_sepWP_vm
    (mid := if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_463).base + bv% (824) else (blkPl_463).base + bv% (912))
  by_vm_steps
    wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine SepWPpCl.weaken_pre ?_
      (hnext _ hvm
        (by rw [← hpc_rem]; segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close))
    exact Entails.of_eq (by sep_ac_rfl)

/-- Single iteration of the `receiver_chains` clone loop (`+0x338 → +0x390 / +0x338`),
    threading `A.pool` across `chainCloneEvents (g, rc)`. -/
theorem segClone_receiverChains_iter_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)}
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (s0 s : State) (ret : BitVec 64) {Q Qp : State → SepProp → Prop}
    (hQp_false : ∀ sf P_p, sf.status = .Panicked → Qp sf ((⌜False⌝ : SepProp) ∗ P_p))
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64) (F : SepProp)
    (hfits : FitsEvents M lim st (chainCloneEvents (g, rc)))
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
        (A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) s1 ∗
          chainAt A.repAlloc (g, rc) src ∗
          chainAt A.repAlloc (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        chainAt A.repAlloc (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q Qp := by
  have hcall := hchainClone
  clear hchainClone
  have hfit_env : FitsEnv M lim st (ChainCloneEnv (g, rc)) :=
    fun _ he => he ▸ hfits
  have hsub : ∀ (sf : State) (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
      (sw6 dw6 : BitVec 64) (F_copy : SepProp), _ :=
    fun sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy =>
      segClone_receiverChains_copy_placed (H := H) (s0 := s0) (s := sf) (ret := ret)
        (Q := Q) (Qp := Qp)
        rem src (dst_base + off) off sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy
  have hsub_eq : (off + BitVec.ofNat 64 (rem + 1) * 104#64) - off =
      BitVec.ofNat 64 (rem + 1) * 104#64 := by bv_arith
  have hmul_beq : (BitVec.ofNat 64 (rem + 1) * 104#64 == 0#64) = false :=
    segClone_bv_ofNat_mul_104_beq_zero (Nat.succ_pos rem) hmul_lt
  have hrem_lt : rem < 2 ^ 63 := by omega
  clear hmul_lt
  apply SepWPpCl_of_sepWP_vm (mid := lsmpl.base 468)
  by_vm_steps
    wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm_call => ?_⟩
    let s_call := (fun {a b : State} (_ : VmPreserved a b) => b) hvm_call
    have hpool_call := A.pool_transport lim st s s_call hvm_call
    have h_sp_call : s_call.sp = s.sp := rfl
    refine SepWPpCl.weaken_pre
      (P' := (memRegion (s.sp + 0x5f0#64) 104 ∗ chainAt A.repAlloc (g, rc) src ∗
                A.pool lim st s_call ∗ stackAt s_call.sp chainCloneStack) ∗
              (memRegion (dst_base + off) 104 ∗ F))
      (by rw [hpool_call, h_sp_call]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPpCl.call_frame_cl (x := (⟨s.sp + 0x5f0#64, src, (g, rc)⟩, st))
        hcall (by segCloneChains_close)
        (by segCloneChains_close)
        (by segCloneChains_close)
        (ret_pc := (blkPl_463).base + bv% (852)) (by segCloneChains_close)
        rfl ⟨by segCloneChains_close, by segCloneChains_close, hfit_env⟩ rfl
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf hp => hQp_false sf _ hp)
        fun sf hpcf hrunf hspf hcsm => ?_
    clear hcall
    obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29⟩ := hcsm
    dsimp only [chainCloneSpec]
    simp only [sepConj_assoc, sepExists_sepConj_left]
    refine SepWPpCl.exists_elim fun evs_ch => ?_
    refine SepWPpCl.pure_elim fun ⟨htr_sf, hevs_ch⟩ => ?_
    dsimp only [ChainCloneEnv] at hevs_ch
    subst hevs_ch
    refine SepWPpCl.exists_elim fun g' => ?_
    refine SepWPpCl.pure_elim fun ⟨hsrk', hpriv', hkeys'⟩ => ?_
    rw [h_sp_call] at hspf ⊢
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
    simp only [← hsf_sp]
    refine SepWPpCl.weaken_pre
      (sepConj_mono_left (chainAt_entails_chunks104_6QW A.repAlloc (g', rc) (sf.sp + 0x5f0#64))) ?_
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
              chainHeap A.repAlloc (g', rc) ∗ chainAt A.repAlloc (g, rc) src ∗
              A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) sf ∗
              stackAt sf.sp chainCloneStack ∗ F)
      (by exact Entails.of_eq (by sep_ac_rfl)) ?_
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
              (chainHeap A.repAlloc (g', rc) ∗ chainAt A.repAlloc (g, rc) src ∗
                A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) sf ∗
                stackAt sf.sp chainCloneStack ∗ F))
      (by exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine hsub sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 _
      hpcf hrunf hsf_spA hsf19 hsf21 hsf22 hsf23 hsf_tr hrem_lt
      fun s1 hvm_copy hpc1 hrun1 hsp1 hspA1 hx1_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
    clear hsub
    have hpool_copy := A.pool_transport lim
      (M.stepEvents (chainCloneEvents (g, rc)) st) sf s1 hvm_copy
    rw [hsf_sp]
    refine SepWPpCl.weaken_pre ?_
      (hnext s1 g'
        hpc1 hrun1 (hsp1.trans hsf_sp) hspA1
        hx1_1 hx19_1 (hx20_1.trans hsf20) hx21_1 (hx24_1.trans hsf24)
        (hx25_1.trans hsf25) (hx26_1.trans hsf26) (hx28_1.trans hsf28)
        (hx29_1.trans hsf29) htr1)
    rw [hpool_copy]
    have h104 := chunks104_6QWAt_entails_memRegion (s.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6
    have hdst_chain := chainAt_of_chunks104_6QW A.repAlloc (g', rc) (dst_base + off) hch_inl
    refine Entails.trans (sepConj_mono_left h104) ?_
    refine Entails.trans
      (Q := memRegion (s.sp + 0x5f0#64) 104 ∗
            (chunks104_6QWAt (dst_base + off) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
              chainHeap A.repAlloc (g', rc)) ∗
            chainAt A.repAlloc (g, rc) src ∗
            A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) sf ∗
            stackAt s.sp chainCloneStack ∗ F)
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hdst_chain)) ?_
    exact Entails.of_eq (by sep_ac_rfl)

/-- Induction over `rcs_tl` for the `receiver_chains` clone loop (`+0x338 → +0x390`),
    threading `A.pool` across `((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents`. -/
theorem segClone_receiverChains_loop_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (s0 : State) (ret : BitVec 64) {Q Qp : State → SepProp → Prop}
    (hQp_false : ∀ sf P_p, sf.status = .Panicked → Qp sf ((⌜False⌝ : SepProp) ∗ P_p))
    (dst_base : BitVec 64) (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (st : M.σ) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      FitsEvents M lim st (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) →
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
          (A.pool lim (M.stepEvents (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) st) s1 ∗
            arrayAt (chainAt A.repAlloc) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A.repAlloc) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0x5f0#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            F)
          Q Qp) →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
        (A.pool lim st s ∗
          arrayAt (chainAt A.repAlloc) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q Qp := by
  induction rcs_tl with
  | nil =>
    intro s st rc g gs_tl src off F hfits hgs hmul_lt _ hpc hrun hsp hx1 hx19 hx20 hx21 hx28 htr hnext
    cases gs_tl with
    | cons _ _ => simp at hgs
    | nil =>
      simp only [List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, arrayAt_cons, arrayAt_nil, sepConj_emp,
        List.length_nil, Nat.zero_add, Nat.one_mul] at *
      refine segClone_receiverChains_iter_placed hchainClone s0 s ret hQp_false
        g rc 0 src dst_base off F hfits
        hpc hrun hsp hx1 hx19 hx20 hx21 hx28 htr hmul_lt
        fun s1 g' hpc1 hrun1 hsp1 hspA1 _ _ _ _ hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      simp only [↓reduceIte] at hpc1
      have h1 := hnext s1 [g'] rfl hpc1 hrun1 hsp1 hspA1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1
      simpa only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil, sepConj_emp]
        using h1
  | cons rc2 rcs2 ih =>
    intro s st rc g gs_tl src off F hfits hgs hmul_lt hsz_le hpc hrun hsp hx1 hx19 hx20 hx21 hx28 htr hnext
    cases gs_tl with
    | nil => simp at hgs
    | cons g2 gs2 =>
      have hfits' :
          FitsEvents M lim st
            (chainCloneEvents (g, rc) ++
              ((g2 :: gs2).zip (rc2 :: rcs2)).flatMap chainCloneEvents) := by
        simpa only [List.zip_cons_cons, List.flatMap_cons] using hfits
      obtain ⟨hfit_hd, hfit_tl⟩ := (fitsEvents_append M lim _ _ st).mp hfits'
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
        (P' := A.pool lim st s ∗
                chainAt A.repAlloc (g, rc) src ∗
                memRegion (dst_base + off) 104 ∗
                memRegion (s.sp + 0x5f0#64) 104 ∗
                stackAt s.sp chainCloneStack ∗
                (arrayAt (chainAt A.repAlloc) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                  memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗ F))
        (by exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine segClone_receiverChains_iter_placed hchainClone s0 s ret hQp_false
        g rc (rcs2.length + 1) src dst_base off _ hfit_hd
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
        (P' := A.pool lim (M.stepEvents (chainCloneEvents (g, rc)) st) s1 ∗
                arrayAt (chainAt A.repAlloc) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗
                memRegion (s1.sp + 0x5f0#64) 104 ∗
                stackAt s1.sp chainCloneStack ∗
                (chainAt A.repAlloc (g, rc) src ∗ chainAt A.repAlloc (g', rc) (dst_base + off) ∗ F))
        (by exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine ih s1 (M.stepEvents (chainCloneEvents (g, rc)) st)
        rc2 g2 gs2 (src + 0x68#64) (off + 0x68#64) _ hfit_tl
        hgs2 hmul2_lt hsz2_le hpc1 hrun1 hspA1 hx1_1 hx19_1 hx20_next hx21_1 hx28_1 htr1
        fun s2 gs2' hgs2' hpc2 hrun2 hsp2 hspA2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
      rw [hsp1]
      refine SepWPpCl.weaken_pre ?_
        (hnext s2 (g' :: gs2') (by simp [hgs2']) hpc2 hrun2 (by reg_chain) hspA2
          (by reg_chain) (by reg_chain) (by reg_chain)
          hx28_2 (by reg_chain) htr2)
      simp only [List.zip_cons_cons, List.flatMap_cons, M.stepEvents_append, arrayAt_cons]
      have hd_add : dst_base + off + BitVec.ofNat 64 104 = dst_base + (off + 0x68#64) := by
        bv_arith
      rw [hd_add]
      exact Entails.of_eq (by sep_ac_rfl)

/-- Sub-segment 5 (`+0x544 / +0x300 → +0x548 / +0x390`): clones `receiver_chains`
    into a new buffer at `x28 = chainsPtr'` with capacity `chainsCap'`, threading `A.pool`
    across `receiverChainsCloneEvents x.G.chains x.st.receiverChains`. -/
theorem segClone_receiverChains_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)} (hA : SegCloneHooks A lim H)
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (x : RecordDecryptGhost) (s0 s : State)
    (ret : BitVec 64) {Q Qp : State → SepProp → Prop}
    (hQp_false : ∀ sf P_p, sf.status = .Panicked → Qp sf ((⌜False⌝ : SepProp) ∗ P_p))
    (F : SepProp)
    (hfits : FitsEvents M lim st (receiverChainsCloneEvents x.G.chains x.st.receiverChains))
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
        (A.pool lim (M.stepEvents (receiverChainsCloneEvents x.G.chains x.st.receiverChains) st) s1 ∗
          ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q Qp := by
  have hshim := hA.shim_ok
  have halloc := hA.allocNoOom_ok
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  cases hrc_eq : x.st.receiverChains with
  | nil =>
    clear hshim halloc hchainClone
    simp only [hrc_eq, ↓reduceIte, List.length_nil] at hpc hx26 hchains_len ⊢
    apply SepWPpCl_of_sepWP_vm (mid := (blkPl_463).base + bv% (1352))
    by_vm_steps
      wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm
      have hpool := A.pool_transport lim st s s_end hvm
      refine SepWPpCl.weaken_pre ?_
        (hnext s_end 0#64 8#64 [] (by simp [hrc_eq]) (by simp [hrc_eq])
          (by dsimp only [s_end]; simp only [hrc_eq, ↓reduceIte]; segCloneChains_close)
          (by dsimp only [s_end]; segCloneChains_close)
          (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
          (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
          (by dsimp only [s_end]; simp only [hrc_eq, List.length_nil]; segCloneChains_close)
          (by dsimp only [s_end]; segCloneChains_close) (by dsimp only [s_end]; segCloneChains_close)
          (by dsimp only [s_end]; segCloneChains_close))
      simp only [hrc_eq, receiverChainsCloneEvents, ↓reduceIte, M.stepEvents_nil, hpool,
        List.zip_nil_right, segClone_vecBuf_chain_nil_eq]
      exact Entails.of_eq (by sep_ac_rfl)
  | cons rc rcs_tl =>
    have hsub := segClone_receiverChains_loop_placed (A := A) (lim := lim) (H := H)
      hchainClone s0 ret (Q := Q) (Qp := Qp) hQp_false
    clear hchainClone
    have hne : x.st.receiverChains ≠ [] := by simp [hrc_eq]
    simp only [hne, ↓reduceIte] at hpc hnext
    rw [hrc_eq] at hx26
    cases hgs_eq : x.G.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hfits' :
          FitsEvents M lim st
            (rustAllocEvents (104 * (rc :: rcs_tl).length) 8 ++
              ((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) := by
        simpa [receiverChainsCloneEvents, hrc_eq, hgs_eq] using hfits
      obtain ⟨hfit_buf, hfit_loop⟩ := (fitsEvents_append M lim _ _ st).mp hfits'
      obtain ⟨⟨hwmax, henf, hram, hva⟩, _⟩ := hfit_buf
      have hgs_tl : gs_tl.length = rcs_tl.length := by
        rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hexpose :=
        segClone_vecBuf_expose_arrayAt A.repAlloc (stride := 104) 8 (chainAt A.repAlloc)
          x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))
      refine SepWPpCl.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (hexpose _))) ?_
      refine sepWPpCl_pure_3rd fun hmul_lt => ?_
      have hzip_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs_tl]
      rw [hzip_len] at hmul_lt
      have hpos : 0 < (rc :: rcs_tl).length := by simp
      have hpos_mul : 0 < 104 * (rc :: rcs_tl).length := by simp [List.length_cons]
      have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by simp [List.length_cons] at hmul_lt; omega
      have hsz_le63 : 104 * (rc :: rcs_tl).length + 8 ≤ 2 ^ 63 := by
        simp [List.length_cons] at hmul_lt ⊢; omega
      have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat =
          104 * (rc :: rcs_tl).length := by
        rw [segClone_bv_ofNat_mul_104_toNat hmul_lt, Nat.mul_comm]
      have hpow2 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      have hlay : RustLayoutOk (104 * (rc :: rcs_tl).length) 8 :=
        ⟨⟨hpos_mul, hpow2, hsz_le63⟩, by decide⟩
      rw [stackAt_chainClone_eq_alloc s.sp]
      apply SepWPpCl.of_sepWP (mid := (blkPl_463).base + bv% (824))
      apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
      by_vm_open (
        wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm1
        refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
        wp_call hshim ()
        clear hshim
        refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
        have htr_sf : sf.trace = s0.trace :=
          (‹sf.trace = _›).trans (by simp only [wp_norm, arm64_norm, htr.1])
        have hsp_sf : sf.sp = s.sp := (‹sf.sp = _›).trans (by segCloneChains_close)
        rw [show stackAt s.sp allocHookStack = stackAt sf.sp allocHookStack from
          congrArg (stackAt · allocHookStack) hsp_sf.symm]
        apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
        by_vm_open (
          wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
            ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm2
          refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
          wp_call halloc (104 * (rc :: rcs_tl).length, 8, st)
          clear halloc
          have hacp : AllocCallPreserved sf sf_1 := by assumption
          have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 .x0 ≠ 0#64›
          have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
            beq_eq_false_iff_ne.mpr hoom64
          have htr_sf1 : sf_1.trace = s0.trace :=
            hacp.2.1.trans (by simp only [wp_norm, arm64_norm, htr_sf])
          have hsf1_sp : sf_1.sp = s.sp := (‹sf_1.sp = _›).trans (by segCloneChains_close)
          try dsimp only [Bool.false_eq_true, ↓reduceIte]
          by_vm_open (
            wp_steps
            refine SepWP.done (by segCloneChains_close) (by segCloneChains_close)
              ⟨by simp only [wp_norm, arm64_norm], ?_⟩
            intro hvm3
            let s_loop := (fun {a b : State} (_ : VmPreserved a b) => b) hvm3
            have hpool3 := A.pool_transport lim
              (M.stepEvents (rustAllocEvents (104 * (rc :: rcs_tl).length) 8) st) sf_1 s_loop hvm3
            have hs_loop_sp : s_loop.sp = s.sp := by
              dsimp only [s_loop]; simpa only [wp_norm, arm64_norm] using hsf1_sp
            set ptr' := sf_1.readReg64 (Reg.gpr 0#5)
            have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
            have hsz_eq : 104 * (rc :: rcs_tl).length = (rcs_tl.length + 1) * 104 :=
              Nat.mul_comm 104 _
            refine SepWPpCl.weaken_pre
              (P' := A.pool lim (M.stepEvents (rustAllocEvents (104 * (rc :: rcs_tl).length) 8) st) s_loop ∗
                      arrayAt (chainAt A.repAlloc) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                      memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                      memRegion (s_loop.sp + 0x5f0#64) 104 ∗
                      stackAt s_loop.sp chainCloneStack ∗
                      (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                        ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
                        segClone_vecBufRest A.repAlloc 104 8 x.G.chainsCap x.G.chainsPtr
                          ((g :: gs_tl).zip (rc :: rcs_tl)) ∗ F))
              (by rw [hpool3, hs_loop_sp, hsp_sf, hptr_zero, Nat.mul_comm 104 (rc :: rcs_tl).length,
                      stackAt_chainClone_eq_alloc s.sp]
                  exact Entails.of_eq (by sep_ac_rfl)) ?_
            refine hsub ptr' rcs_tl s_loop
              (M.stepEvents (rustAllocEvents (104 * (rc :: rcs_tl).length) 8) st)
              rc g gs_tl x.G.chainsPtr 0#64 _ hfit_loop
              hgs_tl (by simpa [List.length_cons] using hmul_lt) hsz_le
              (by dsimp only [s_loop]; segCloneChains_close) (by dsimp only [s_loop]; segCloneChains_close)
              (by dsimp only [s_loop]; segCloneChains_close) (by dsimp only [s_loop]; segCloneChains_close)
              (by dsimp only [s_loop]; segCloneChains_close) (by dsimp only [s_loop]; segCloneChains_close)
              (by dsimp only [s_loop]; segCloneChains_close) (by dsimp only [ptr', s_loop]; segCloneChains_close)
              ⟨by simp only [s_loop, wp_norm, arm64_norm, htr_sf1], by dsimp only [s_loop]; segCloneChains_close⟩
              fun s2 gs' hgs' hpc2 hrun2 hsp2 hspA2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
            clear hsub
            dsimp only [s_loop, Reg.x24, Reg.x25, Reg.x26, Reg.x29] at hsp2 hx24_2 hx25_2 hx26_2 hx29_2
            simp (config := { decide := true }) only [State.sp_setPC, State.sp_writeReg64_gpr,
              State.readReg64_setPC, State.readReg64_writeReg64, reduceStateReadReg64] at hsp2 hx24_2 hx25_2 hx26_2 hx29_2
            rw [hptr_zero, hs_loop_sp]
            refine SepWPpCl.weaken_pre ?_
              (hnext s2 (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' gs'
                (by rw [hrc_eq]; exact hgs') (by rw [hrc_eq])
                hpc2 hrun2 (hsp2.trans hsf1_sp) hspA2
                (by segCloneChains_close) (by segCloneChains_close)
                (by simp only [hrc_eq]; segCloneChains_close)
                hx28_2 (by segCloneChains_close) htr2)
            simp only [hgs_eq, hrc_eq, receiverChainsCloneEvents, reduceCtorEq, ↓reduceIte,
              M.stepEvents_append]
            have hreasm :=
              segClone_vecBuf_reassemble_arrayAt A.repAlloc 104 8 (chainAt A.repAlloc)
                x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))
            have hnew_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
              simp [hgs']
            have hnew_pos : 0 < (gs'.zip (rc :: rcs_tl)).length := by rw [hnew_len]; exact hpos
            have hnew_lt : (gs'.zip (rc :: rcs_tl)).length * 104 < 2 ^ 63 := by rw [hnew_len]; exact hmul_lt
            have hnew_buf := segClone_vecBuf_chain_of_arrayAt A.repAlloc ptr'
              (gs'.zip (rc :: rcs_tl)) hnew_pos hnew_lt hoom64
            rw [hnew_len, RustCliAllocBudget.repAlloc_live] at hnew_buf
            refine Entails.trans
              (Q := (arrayAt (chainAt A.repAlloc) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                      segClone_vecBufRest A.repAlloc 104 8 x.G.chainsCap x.G.chainsPtr
                        ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
                    (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                      arrayAt (chainAt A.repAlloc) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
                    A.pool lim
                      (M.stepEvents (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents)
                        (M.stepEvents (rustAllocEvents (104 * (rc :: rcs_tl).length) 8) st)) s2 ∗
                    ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
                    memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
              (Entails.of_eq (by sep_ac_rfl)) ?_
            refine Entails.trans (sepConj_mono hreasm (sepConj_mono_left hnew_buf)) ?_
            exact Entails.of_eq (by sep_ac_rfl)
          )
        )
      )

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudgetAux
