/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# `HookSat`-backed `black_box` Sibling of `ConsumeMessageKey/FindIndexProofs/LoopBudget`

Weakens `h_bb : H lsBlackBoxU8Sym = some blackBoxHook` to
`h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` for budget-threaded Block `26`
(`RatchetState::find_receiver_chain_index`), obtaining `VmPreserved` directly from
`blackBoxSpecSat` (`0` `bbTrapHooks`) and splitting `16` B out of the `704` B stack region
(`[sp - 1024, sp - 320)`) so `find_receiver_chain_index_placed_ok_sat` keeps a token-identical
conclusion on `findPlacedSpec A`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey ReceiverChain)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_26 blkPC_26 blkPC_201 blkPC_212 blkPl_26
   blkPl_201 blkPl_212 lsBlackBoxU8Sym lsLogFilterAddr ls_subroutine_ok_cl_of_block
   ls_subroutine_ok_cl_of_plain lsmpl sepWP_seq_lscl withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
  (SepWP_chainAt_info SepWP_entails_pre SepWP_sepExists add_120_eq_add_104_add_16
   and32_1_ite_1_0 and32_ite_1_0 and64_1_ite_1_0 and64_ite_1_0 and64_mask255_ite_1_0
   and64_mask32_ite_1_0 arrayAt_cons_sep_pre byte_bne_zext32 cells_208_unfold cells_96_unfold
   chainAt_eq_of_ok csinc_eq_zero32_ite_1_0 findIdx?_map_cons_neg findIdx?_map_cons_pos
   idx_len_step_of_cons_cons idx_lt_two_pow_64_of_cons ite_bne_byte_0_1
   len_mul_104_step_of_cons_cons length_lt_cons list_cons_cons_mul_104_ne_104
   list_cons_mul_104_sub_104 list_length_induction ofNat_idx_add_one pk_208_eq_sep pk_247_eq_sep
   publicKey_bytes_toList_length reg_mul_104_eq_ofNat setWidth32_ite_1_0 setWidth64_ite_1_0_32
   setWidth64_ite_1_0_8 setWidth8_ite_1_0 sp_sub_248_orr_1 toNat_ofNat_of_lt
   zero_add_len_lt_of_mul_104)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open LibsignalBinary.Heap (AllocCostModel FdsHiFrame PoolPreserved RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat publicKeyEqMemBudgetSpec16 publicKeyEqMemSpec16
   publicKey_eq_mem_placed_vm_ok_16_sat)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
  (deserializeMemPlacedSpec deserializeMem_placed_ok findPlacedAllocSpec findPlacedSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopSat
  (after_heq_placed_entails_16 entails_stackAt_1024_16 eqStack16 findIdxStack_split_16 loopStack16
   loopStack16_entails_stackAt memRegion_80_eq_loopEq16 publicKeyEqMemLoopSpec16)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

attribute [local irreducible] Program.fetch Program.externAt?

/-- `VmPreserved`-strengthened `+16 B` `PublicKey::eq` loop adapter. -/
@[expose] def publicKeyEqMemLoopBudgetSpec16 :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  withVmPreserved publicKeyEqMemLoopSpec16

theorem publicKeyEqMemLoop_placed_vm_ok_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemLoopBudgetSpec16) := by
  refine subroutine_ok_map (publicKey_eq_mem_placed_vm_ok_16_sat h_bb) ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj
      (by simpa only [withLsCodeLoaded, publicKeyEqMemBudgetSpec16, withVmPreserved,
        publicKeyEqMemSpec16] using hp))
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj
      (by simpa only [withLsCodeLoaded, publicKeyEqMemBudgetSpec16, withVmPreserved,
        publicKeyEqMemSpec16] using he))
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj
      (by simpa only [withLsCodeLoaded, publicKeyEqMemBudgetSpec16, withVmPreserved,
        publicKeyEqMemSpec16] using ho)))
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [withLsCodeLoaded, publicKeyEqMemLoopBudgetSpec16, publicKeyEqMemBudgetSpec16,
      withVmPreserved, publicKeyEqMemLoopSpec16, publicKeyEqMemSpec16,
      memRegion_80_eq_loopEq16 sp, sepConj_assoc] using hpre
  · intro sf hpost
    simpa only [withLsCodeLoaded, publicKeyEqMemLoopBudgetSpec16, publicKeyEqMemBudgetSpec16,
      withVmPreserved, publicKeyEqMemLoopSpec16, publicKeyEqMemSpec16,
      memRegion_80_eq_loopEq16 sp, sepConj_assoc] using hpost

private theorem vmPreserved_setPC_left {s : State} {pc : BitVec 64} :
    VmPreserved s (s.setPC pc) := by
  simp [VmPreserved, PoolPreserved, FdsHiFrame, State.setPC]

private theorem vmPreserved_setPC_setMem {s : State} {pc1 pc2 : BitVec 64} {m : Memory} :
    VmPreserved ((s.setPC pc1).setMem m) ((s.setPC pc2).setMem m) := by
  simp [VmPreserved, PoolPreserved, FdsHiFrame, State.setPC, State.setMem]

section VmProofs

attribute [local irreducible] VmPreserved
attribute [local simp]
  byte_bne_zext32 ite_bne_byte_0_1 setWidth32_ite_1_0 setWidth8_ite_1_0
  setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 and64_ite_1_0 and64_1_ite_1_0
  and64_mask32_ite_1_0 and32_ite_1_0 and32_1_ite_1_0
  publicKey_bytes_toList_length and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0
attribute [local simp, local wp_norm, local arm64_norm] Bool.and_assoc

set_option maxHeartbeats 1600000 in
theorem find_loop_placed_ok_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64) (idx : Nat) (P_pre : SepProp)
    (u0 u1 u2 u3 : BitVec 64) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_26).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 idx)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0 ∧ VmPreserved s0 s)
    (hidx_len : idx + (gc :: rest).length < 2 ^ 63)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP ((blkPC_26).rebase (blkPl_26).base H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack16 s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜VmPreserved s0 sf ∧
              (sf.trace = s0.trace ∧
                match Option.map (· + idx)
                  ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) with
                | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
                | none => sf.readReg64 .x0 = 0#64)⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
            (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hdeser0 : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (lsmpl.base 201)
      deserializeMemPlacedSpec :=
    deserializeMem_placed_ok H
  have hdeser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_26).rebase (blkPl_26).base H) hdeser0
  simp only [withLsCl, deserializeMemPlacedSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeMemPlacedSpec,
    sepConj_assoc] at hdeser
  have heq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl publicKeyEqMemLoopBudgetSpec16) :=
    publicKeyEqMemLoop_placed_vm_ok_sat h_bb
  have heq := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_26).rebase (blkPl_26).base H) heq0
  simp only [withLsCl, publicKeyEqMemLoopBudgetSpec16, withVmPreserved,
    publicKeyEqMemLoopSpec16, sepConj_assoc] at heq
  induction rest using list_length_induction generalizing gc cur_p idx P_pre u0 u1 u2 u3 s with
  | h rest ih =>
    conv => arg 4; dsimp only [arrayAt]; simp only [sepConj_assoc]
    apply SepWP_chainAt_info
    intro h1 h2 hcap hlen
    conv => arg 4; rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap]; simp only [sepConj_assoc]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 201)
    apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
      blkLib_eq_26 (mid := lsmpl.base 201); intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm_s1 : VmPreserved s _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm_s1 ⊢
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl1 => ?_
    wp_apply
    have hvm_after_deser : VmPreserved s0 _ :=
      htrace.2.2.trans (hvm_s1.trans (by assumption : VmPreserved _ _))
    simp only [hsp, hx19, hx20, hx21, hx22, hx23, hx24, htrace.1, htrace.2.1] at *
    obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
      exists_unpack64_of_length_32 (bs := gc.2.senderRatchetKey.bytes.toList) (by simp)
    rw [← pk_247_eq_sep _ hpk_cells]
    apply sepWP_seq_lscl (by assumption) (mid := lsmpl.base 212)
    apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
      blkLib_eq_26 (mid := lsmpl.base 212); intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm_s2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm_s2 ⊢
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl2 => ?_
    rw [pk_247_eq_sep _ hpk_cells, pk_208_eq_sep _ hpk_cells]
    wp_apply
    have hvm_after_eq : VmPreserved s0 _ :=
      hvm_after_deser.trans (hvm_s2.trans (by assumption : VmPreserved _ _))
    simp only [hsp_sf, h, h_1, h_2, h_3, h_4, h_5, hvregs, hpost] at *
    refine SepWP_entails_pre
      (after_heq_placed_entails_16 A s0 theirA their gc rest cur_p P_pre w0 w1 w2 w3 h1 h2 hcap hpk_cells) ?_
    wp_steps
    wp_if hmatch
    · dsimp only [loopStack16]
      apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
        blkLib_eq_26 (mid := s0.readReg64 .lr); intro _m_strip3
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
      have hvm_s3 : VmPreserved _ _ := _hnsp3.toVmPreserved (by wp_norm_lhs)
      simp only [State.setMem_setMem] at hvm_s3 ⊢
      have hvm_fin : VmPreserved s0 _ := hvm_after_eq.trans (vmPreserved_setPC_left.trans hvm_s3)
      rw [findIdx?_map_cons_pos idx (beq_iff_eq.mpr hmatch)]
      have hidx_toNat : (BitVec.ofNat 64 idx).toNat = idx :=
        toNat_ofNat_of_lt (idx_lt_two_pow_64_of_cons hidx_len)
      refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (loopStack16_entails_stackAt s0 w0 w1 w2 w3))))) ?_
      simp only [hvm_fin, true_and]
      wp_done
    · have hmatch_b : ¬(gc.2.senderRatchetKey == their) = true := by
        rw [beq_iff_eq]; exact hmatch
      rw [findIdx?_map_cons_neg idx hmatch_b]
      rcases rest with _ | ⟨gc', rest'⟩
      · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] at *
        dsimp only [loopStack16]
        apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
          blkLib_eq_26 (mid := s0.readReg64 .lr); intro _m_strip3
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
        have hvm_s3 : VmPreserved _ _ := _hnsp3.toVmPreserved (by wp_norm_lhs)
        simp only [State.setMem_setMem] at hvm_s3 ⊢
        have hvm_fin : VmPreserved s0 _ := hvm_after_eq.trans (vmPreserved_setPC_left.trans hvm_s3)
        simp only [List.map_nil, List.findIdx?_nil, Option.map_none]
        refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (loopStack16_entails_stackAt s0 w0 w1 w2 w3))))) ?_
        try simp only [hvm_fin, true_and]
        wp_done
      · apply sepWP_seq_lscl (by assumption) (mid := (blkPl_26).base + 136#64)
        apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
          blkLib_eq_26 (mid := (blkPl_26).base + 136#64); intro _m_strip3
        wp_steps
        rw [list_cons_cons_mul_104_ne_104 gc gc' rest' hlen_lt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
        have hvm_s3 : VmPreserved _ _ := _hnsp3.toVmPreserved (by wp_norm_lhs)
        simp only [State.setMem_setMem] at hvm_s3 ⊢
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_next => ?_
        have hvm_next : VmPreserved s0 _ := hvm_after_eq.trans (vmPreserved_setPC_left.trans hvm_s3)
        rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        conv => arg 5; ext sf P_f; rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        refine ih rest' (length_lt_cons gc' rest') gc' (cur_p + 104#64) (idx + 1)
          (chainAt A gc cur_p ∗ P_pre) w0 w1 w2 w3 _ hcl_next ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · wp_norm_lhs
        · wp_norm_lhs
        · simp only [wp_norm, arm64_norm, *]
        · exact ofNat_idx_add_one idx
        · simp only [wp_norm, arm64_norm, *]
        · simp only [wp_norm, arm64_norm, *]
        · exact list_cons_mul_104_sub_104 gc (gc' :: rest')
        · simp only [wp_norm, arm64_norm, *]
        · exact add_120_eq_add_104_add_16 cur_p
        · exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], hvm_next⟩
        · exact idx_len_step_of_cons_cons hidx_len
        · exact len_mul_104_step_of_cons_cons hlen_lt

set_option maxHeartbeats 800000 in
theorem find_loop_placed_ok_zero_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64)
    {u0 u1 u2 u3 : BitVec 64} {s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_26).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0 ∧ VmPreserved s0 s)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP ((blkPC_26).rebase (blkPl_26).base H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack16 s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜VmPreserved s0 sf ∧
              (sf.trace = s0.trace ∧
                match (List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their) with
                | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
                | none => sf.readReg64 .x0 = 0#64)⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
            (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have h := find_loop_placed_ok_sat A h_bb s0 theirA their R hsp0 rest gc cur_p 0 emp u0 u1 u2 u3 s
    hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 htrace
    (zero_add_len_lt_of_mul_104 hlen_lt) hlen_lt
  simpa only [emp_sepConj, Nat.add_zero, Option.map_id'] using h

/-- `HookSat` `black_box` sibling of `find_receiver_chain_index_alloc_placed_ok`
(`LoopBudget.lean:732`). -/
theorem find_receiver_chain_index_alloc_placed_ok_sat [LibsignalPlacement]
    {H : String → Option (State → State)} (A : RustAlloc)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedAllocSpec A)) := by
  have hzero := find_loop_placed_ok_zero_sat A h_bb
  clear h_bb
  simp only [withLsCodeLoaded, findPlacedAllocSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.findPlacedSpec, sepConj_assoc]
  wp_init g s0
  obtain ⟨p, cs, theirA, their⟩ := g
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst h_2 h_4
  conv =>
    arg 4
    rw [findIdxStack_split_16 s0.sp, cells_208_unfold s0.sp, cells_96_unfold s0.sp]
    simp only [eqStack16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  iterate 16 (apply SepWP_sepExists; intro _)
  apply sepWP_seq_lscl hcl0 (mid := (blkPl_26).base + 32#64)
  apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
    blkLib_eq_26 (mid := (blkPl_26).base + 32#64); intro _m_strip0
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  have hvm0 : VmPreserved s0 _ := _hnsp0.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm0 ⊢
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_pro => ?_
  wp_steps
  wp_if hcbz
  · apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
      blkLib_eq_26 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip_nil
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_nil _hnsp_nil => ?_
    have hvm_nil : VmPreserved s0 _ :=
      hvm0.trans (vmPreserved_setPC_setMem.trans (_hnsp_nil.toVmPreserved (by wp_norm_lhs)))
    simp only [State.setMem_setMem] at hvm_nil ⊢
    have hcs_nil : cs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← h_3, hcbz]
      rfl
    subst hcs_nil
    simp only [List.map_nil, List.findIdx?_nil]
    refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_stackAt_1024_16 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))) ?_
    try simp only [sepConj_assoc, hvm_nil]
    wp_done
  · apply sepWP_seq_lscl (by simpa [State.setPC] using hcl_pro) (mid := (blkPl_26).base + 136#64)
    apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
      blkLib_eq_26 (mid := (blkPl_26).base + 136#64); intro _m_strip_go
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_go _hnsp_go => ?_
    have hvm_go : VmPreserved s0 _ :=
      hvm0.trans (vmPreserved_setPC_setMem.trans (_hnsp_go.toVmPreserved (by wp_norm_lhs)))
    simp only [State.setMem_setMem] at hvm_go ⊢
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_go => ?_
    rcases cs with _ | ⟨gc, rest⟩
    · exfalso
      apply hcbz
      apply BitVec.eq_of_toNat_eq
      simpa using h_3
    · simp only [sepConj_assoc]
      refine SepWP.mono (hzero s0 (s0.readReg64 (Reg.gpr 2#5)) their R h_1
        rest gc (s0.readReg64 (Reg.gpr 0#5)) hcl_go (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by simpa only [wp_norm, arm64_norm] using reg_mul_104_eq_ofNat h_3)
        (by simpa only [wp_norm, arm64_norm] using sp_sub_248_orr_1 h_1)
        (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, hvm_go⟩ h_5)
        fun sf P_f _ _ ⟨hmf, hsp_f, hcs_f⟩ => ⟨fun hm => ?_, hsp_f, hcs_f⟩
      have hm' := hmf hm
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
      exact ⟨hm'.1.1, hm'.1.2, hm'.2⟩

/-- `HookSat` `black_box` sibling of `find_receiver_chain_index_placed_ok`
(`LoopBudget.lean:804`), with a token-identical conclusion. -/
theorem find_receiver_chain_index_placed_ok_sat [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} (A : RustCliAllocBudget M)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) :=
  find_receiver_chain_index_alloc_placed_ok_sat A.repAlloc h_bb

end VmProofs

end LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudgetSat
