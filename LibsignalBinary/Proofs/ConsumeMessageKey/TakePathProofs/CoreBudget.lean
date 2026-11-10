/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CommonBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Core
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturnBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.LoopBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import ProofLib.RegChain

/-!
# Budget-Threaded Top-Level `TakePath` Proof (Block 24)

Proves `TakePathPlacedSpec` under `RustCliAllocBudget M` and `SeamBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CoreBudget

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (PublicKey ReceiverChain maxMessageKeys)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkLib_eq_24 blkPC_24 blkPl_24 lsLogFilterAddr lsmpl withLsCodeLoaded
)
open CryptoVerification.RustHeap (arrayAt vecBuf)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost chainAt chainKeyBytes messageKeyAt ratchetAt
)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkPreLoopHeap_placed cmkSavedRegs
)
open CryptoVerification.LibsignalSession.TakePath (
  RatchetChainProps add_mul_104_eq_chAddr
  cmk_model_past_miss_chain cmk_model_past_no_chain
  findIdx?_some_lt_length findIdx_map_snd_zip_eq
  ratchetAt_expose_chain ratchetAt_expose_findIndex
  ratchetAt_reassemble_findIndex ratchetAt_reassemble_self
  ratchetChainRest ratchetFindRest
  sepWP_to_reaches_pc stackAt_7712_split_1024
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_refl_iff vmPreserved_setPC vmPreserved_writeReg64
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  FindIndexPlacedOk findIndexPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CommonBudget (TakePathPlacedSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturnBudget (
  cmk_dup_0xb4_placed_outcome
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.LoopBudget (
  cmk_pos_loop_0x94_placed_outcome
)

private theorem ratchetAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetAt (A.atState lim st s) = ratchetAt A.repAlloc :=
  rfl

theorem call_find_index_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} {A : RustCliAllocBudget M}
    {target_pc : BitVec 64}
    (hfind : FindIndexPlacedOk H A)
    (p : BitVec 64) (cs : List (ChainGhost × ReceiverChain))
    (theirA : BitVec 64) (their : PublicKey)
    (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = cs.length)
    (hx2 : s.readReg64 .x2 = theirA)
    (hcap : cs.length * 104 < 2 ^ 63)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 26)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_val)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_val → CalleeSavedPreserved s sf → VmPreserved s sf → sf.trace = s.trace →
      (match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
       | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
       | none => sf.readReg64 .x0 = 0#64) →
      SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc sf
        ((arrayAt (chainAt A.repAlloc) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp_val 1024) ∗ Frame) post) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc s
      ((arrayAt (chainAt A.repAlloc) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp_val 1024) ∗ Frame) post := by
  unfold FindIndexPlacedOk at hfind
  refine SepWP.call_subroutine_frame hfind (x := (p, cs, theirA, their)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [findIndexPlacedSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.findIndexPlacedSpec, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hcap⟩, ?_⟩
    have heq :
        (arrayAt (chainAt A.repAlloc) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp_val 1024 ∗
          ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ Frame ∗ R) =
        (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
          ((arrayAt (chainAt A.repAlloc) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp_val 1024) ∗ Frame) ∗ R) := by
      sep_ac_rfl
    rw [heq, satisfies_pure_sepConj]
    exact ⟨hcl, hm⟩
  · intro R' sf _ hp
    simp only [findIndexPlacedSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.findIndexPlacedSpec] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    simp only [findIndexPlacedSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.findIndexPlacedSpec] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [findIndexPlacedSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.findIndexPlacedSpec, hsp, sepConj_assoc]
    refine SepWP.pure_elim fun hvm => SepWP.pure_elim fun ⟨htr, hres⟩ => ?_
    simpa only [sepConj_assoc] using hnext sf h1 h2 (h3.trans hsp) h4 hvm htr hres

theorem cmk_call_find_index_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} {A : RustCliAllocBudget M}
    (hFind : FindIndexPlacedOk H A)
    (p : BitVec 64) (cs : List (ChainGhost × ReceiverChain))
    (theirA : BitVec 64) (their : PublicKey)
    (v20 v21 v22 v24 v28 v29 : BitVec 64)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 92#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = cs.length)
    (hx2 : s.readReg64 .x2 = theirA)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29)
    (hcap : cs.length * 104 < 2 ^ 63) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 96#64) s
      (arrayAt (chainAt A.repAlloc) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt (s0.sp - 480#64) 1024)
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x21 = v21 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
         | some i => s1.readReg64 .x0 = 1#64 ∧ (s1.readReg64 .x1).toNat = i
         | none => s1.readReg64 .x0 = 0#64) ∧
        (P1 ⊢ arrayAt (chainAt A.repAlloc) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt (s0.sp - 480#64) 1024)) := by
  wp_step
  rw [← sepConj_emp (arrayAt (chainAt A.repAlloc) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt (s0.sp - 480#64) 1024)]
  refine call_find_index_placed_wp hFind p cs theirA their (s0.sp - 480#64) ((blkPl_24).base + 96#64)
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    hcap hcl
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs hvm_sf htr_sf hres
  have hvm : VmPreserved s sf :=
    VmPreserved.trans (by simp [wp_norm, arm64_norm]) hvm_sf
  have hsp_align' : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf]
    simpa [State.spAligned, hsp] using hsp_align
  rcases hcs with ⟨_, hcs20, hcs21, hcs22, _, hcs24, _, _, _, hcs28, hcs29, hcsv⟩
  rw [sepConj_emp]
  refine SepWP.done hpc_sf hrun_sf ?_
  refine ⟨hvm, hsp_sf, hsp_align', ?_, ?_, ?_, ?_, ?_, ?_, ⟨htr_sf, by simp_all [arm64_norm]⟩, hres, Entails.refl _⟩
  · simp_all [arm64_norm]
  · simp_all [arm64_norm]
  · simp_all [arm64_norm]
  · simp_all [arm64_norm]
  · simp_all [arm64_norm]
  · simp_all [arm64_norm]

theorem cmk_after_find_none_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (v20 v22 v28 : BitVec 64) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx20 : s.readReg64 .x20 = v20)
    (hx22 : s.readReg64 .x22 = v22)
    (hx28 : s.readReg64 .x28 = v28) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 180#64) s emp
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x28 = v28 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ emp)) := by
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 (mid := (blkPl_24).base + 180#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun _m_real _hnsp => ?_
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨_hnsp.toVmPreserved (by simp_all [arm64_norm]),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩

theorem cmk_after_find_empty_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (chainsPtr v20 v22 v28 : BitVec 64) (ci chLen : Nat)
    (hci : ci < chLen) (hch_lt : chLen * 104 < 2 ^ 63)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 chLen)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = chainsPtr)
    (hx28 : s.readReg64 .x28 = v28) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 180#64) s
      (((chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ 0#64))
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x28 = v28 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ ((chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ 0#64))) := by
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 (mid := (blkPl_24).base + 180#64)
  intro _m_strip
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.ite_false (by rfl) (by
    have h1 : (BitVec.ofNat 64 ci).toNat = ci := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h2 : (BitVec.ofNat 64 chLen).toNat = chLen := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp_all [arm64_norm, BitVec.ule]
    omega)
  wp_step; wp_step
  rw [← add_mul_104_eq_chAddr chainsPtr ci]
  wp_steps
  rw [add_mul_104_eq_chAddr chainsPtr ci]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun _m_real _hnsp => ?_
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨_hnsp.toVmPreserved (by simp_all [arm64_norm]),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩

theorem cmk_after_find_nonempty_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (chainsPtr mkPtr v20 v22 v28 v29 : BitVec 64) (ci chLen mkLen : Nat)
    (hci : ci < chLen) (hch_lt : chLen * 104 < 2 ^ 63)
    (hmk_pos : 0 < mkLen) (hmk_max : mkLen ≤ maxMessageKeys)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 chLen)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = chainsPtr)
    (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 148#64) s
      (((chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ mkPtr) ∗
       ((chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ BitVec.ofNat 64 mkLen))
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - 0) * 104) ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (0 * 104) + 56#64 ∧
        s1.readReg64 .x19 = chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
        s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 mkLen ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 0 ∧
        s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ ((chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ mkPtr) ∗
              ((chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ BitVec.ofNat 64 mkLen))) := by
  have hmax_val : maxMessageKeys = 2000 := rfl
  have hcbz_ne : BitVec.ofNat 64 mkLen ≠ 0#64 := by
    intro h
    have hto := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show mkLen < 2 ^ 64 by omega)] at hto
    change mkLen = 0 at hto
    omega
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 (mid := (blkPl_24).base + 148#64)
  intro _m_strip
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.ite_false (by rfl) (by
    have h1 : (BitVec.ofNat 64 ci).toNat = ci := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h2 : (BitVec.ofNat 64 chLen).toNat = chLen := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp_all [arm64_norm, BitVec.ule]
    omega)
  wp_step; wp_step
  rw [← add_mul_104_eq_chAddr chainsPtr ci]
  wp_step; wp_step
  apply SepWP.ite_false (by rfl) (by simp [arm64_norm, hcbz_ne])
  wp_steps
  rw [add_mul_104_eq_chAddr chainsPtr ci]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun _m_real _hnsp => ?_
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨_hnsp.toVmPreserved (by simp_all [arm64_norm]),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    ?_, ?_, ?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩
  · simp only [arm64_norm]
    have hmk : mkLen = (mkLen - 1 - 0) + 1 := by omega
    conv => lhs; lhs; rw [show (104#64 : BitVec 64) = BitVec.ofNat 64 104 from rfl, ← BitVec.ofNat_mul, hmk, Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]
    bv_omega
  · simp_all [arm64_norm]
  · simp_all [arm64_norm]

theorem takePath_placed_ok_thm [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    TakePathPlacedSpec F A lim H := by
  intro hA hmemmove_eq hFind x st_init st R s0 s hc_lt hstate
  rcases hstate with ⟨hsb, hpc, hmeta, hregs, hm⟩
  rcases hmeta with ⟨hrun, hsp, _, hsp_align, hx29, htrace, hcl, hvregs⟩
  rcases hregs with ⟨hx0, hx1, hx2, hx20, hx21, hx22, _, hx24, _, _, hx28⟩
  have hpc_sp : s.pc = (blkPl_24).base + 92#64 := hpc
  set cs := x.G.chains.zip x.st.receiverChains
  have hm_exp : s.mem ⊨
      ⌜x.G.chains.length = x.st.receiverChains.length ∧ cs.length * 104 < 2 ^ 63⌝ ∗
      (arrayAt (chainAt A.repAlloc) 104 x.G.chainsPtr cs ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 1024) ∗
      (ratchetFindRest A.repAlloc x.self x.G x.st ∗
       (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗
       stackAt (s0.sp - 480#64 - 1024#64) 6688 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool lim st s ∗ R) := by
    unfold cmkPreLoopHeap_placed at hm
    rw [ratchetAt_atState, RustCliAllocBudget.atState_pool,
      stackAt_7712_split_1024 (s0.sp - 480#64)] at hm
    have hm1 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left (ratchetAt_expose_findIndex A.repAlloc x.self x.G x.st))) hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
  rw [satisfies_pure_sepConj] at hm_exp
  rcases hm_exp with ⟨⟨hchains_len, hcs_lt⟩, hm_find⟩
  have hcs_len : cs.length = x.st.receiverChains.length := by
    simp [cs, hchains_len]
  have hx1_len : (s.readReg64 .x1).toNat = cs.length := by
    rw [hx1, hcs_len, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show x.st.receiverChains.length < 2 ^ 64 by omega)]
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hvm1, hsp1, hsp1_align,
    hx20_1, hx21_1, hx22_1, hx24_1, hx28_1, hx29_1, htr1, hres, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_call_find_index_placed_wp hFind x.G.chainsPtr cs x.theirA x.their
        (x.counter.zeroExtend 64) (BitVec.ofNat 64 x.st.receiverChains.length)
        x.ret x.G.chainsPtr (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
        s0 s hpc_sp hrun hsp hsp_align hcl
        hx0 hx1_len hx2 hx20 hx21 hx22 hx24 hx28 hx29 hcs_lt)
      hm_find hL
  have hm1_pre : s1.mem ⊨ cmkPreLoopHeap_placed (A.atState lim st s1) x s0 ∗ R := by
    unfold cmkPreLoopHeap_placed
    rw [ratchetAt_atState, RustCliAllocBudget.atState_pool,
      stackAt_7712_split_1024 (s0.sp - 480#64)]
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    rw [← A.pool_transport lim st s s1 hvm1] at hm1'
    have hreassemble := ratchetAt_reassemble_findIndex A.repAlloc x.self x.G x.st
    have hm1'' : s1.mem ⊨
        (arrayAt (chainAt A.repAlloc) 104 x.G.chainsPtr cs ∗
          ratchetFindRest A.repAlloc x.self x.G x.st) ∗
        ((x.theirA ↦ₛ x.their.bytes.toList) ∗
          (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
          memRegion x.ret 88 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 480#64) 1024 ∗
          stackAt (s0.sp - 480#64 - 1024#64) 6688 ∗
          memRegion (s0.sp - 480#64) 384 ∗
          cmkSavedRegs s0.sp s0 ∗
          A.pool lim st s1 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1'
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
      (Satisfies.mono (sepConj_mono_left hreassemble) hm1'')
  have hL1 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s1.mem :=
    hsteps1.codeLoaded hL
  rw [findIdx_map_snd_zip_eq x.G x.st x.their hchains_len] at hres
  cases hci : x.st.findReceiverChainIndex x.their with
  | none =>
    rw [hci] at hres
    have hm1_emp : s1.mem ⊨ emp ∗ (cmkPreLoopHeap_placed (A.atState lim st s1) x s0 ∗ R) := by
      rwa [emp_sepConj]
    obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hvm2, hsp2, hsp2_align,
      hx20_2, hx22_2, hx28_2, htr2, hP2⟩ :=
      sepWP_to_reaches_pc
        (cmk_after_find_none_placed_wp (x.counter.zeroExtend 64) x.ret (x.ck.index.zeroExtend 64)
          s0 s1 hpc1 hrun1 hsp1 hsp1_align hres hx20_1 hx22_1 hx28_1)
        hm1_emp hL1
    have hm2_pre : s2.mem ⊨ cmkPreLoopHeap_placed (A.atState lim st s2) x s0 ∗ R := by
      have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
      rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st hvm2] at hm2'
      exact hm2'
    have hmodel := cmk_model_past_no_chain F x hci hc_lt
    exact reaches_outcome_steps (hsteps1.trans hsteps2)
      (cmk_dup_0xb4_placed_outcome x hsb R s0 s2 hpc2 hrun2 hsp2 hsp2_align
        (by reg_chain) hx20_2 hx22_2 hx28_2 hmodel hm2_pre)
  | some ci =>
    rw [hci] at hres
    rcases hres with ⟨hx0_1, hx1_nat⟩
    have hi : ci < x.st.receiverChains.length :=
      findIdx?_some_lt_length hci
    have hgi : ci < x.G.chains.length := by omega
    have hch_lt : x.st.receiverChains.length * 104 < 2 ^ 63 := by
      rwa [← hcs_len]
    have hx1_1 : s1.readReg64 .x1 = BitVec.ofNat 64 ci := by
      apply BitVec.eq_of_toNat_eq
      rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ci < 2 ^ 64 by omega)]
    have hm1_chain : s1.mem ⊨
        ⌜RatchetChainProps x.G x.st ci hgi hi⌝ ∗
        (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
         ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
           BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
         vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
           (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
         ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗
         A.pool lim st s1 ∗ R) := by
      unfold cmkPreLoopHeap_placed at hm1_pre
      rw [ratchetAt_atState, RustCliAllocBudget.atState_pool] at hm1_pre
      have hm1_c := Satisfies.mono
        (sepConj_mono_left (sepConj_mono_left (ratchetAt_expose_chain A.repAlloc x.self x.G x.st hi hgi)))
        hm1_pre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1_c
    rw [satisfies_pure_sepConj] at hm1_chain
    rcases hm1_chain with ⟨hprops, hm1_c⟩
    have hkl : x.G.chains[ci].keys.length = x.st.receiverChains[ci].messageKeys.length :=
      hprops.keys_len
    have hmax_c : x.st.receiverChains[ci].messageKeys.length ≤ maxMessageKeys := hprops.mk_max
    have hzip_len :
        (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length =
          x.st.receiverChains[ci].messageKeys.length := by
      simp [hkl]
    by_cases hgks : (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length = 0
    · have hm1_empty : s1.mem ⊨
          ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ 0#64) ∗
          (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
           vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
             (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
           ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool lim st s1 ∗ R) := by
        rw [hgks] at hm1_c
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1_c
      obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hvm2, hsp2, hsp2_align,
        hx20_2, hx22_2, hx28_2, htr2, hP2⟩ :=
        sepWP_to_reaches_pc
          (cmk_after_find_empty_placed_wp x.G.chainsPtr (x.counter.zeroExtend 64) x.ret
            (x.ck.index.zeroExtend 64) ci x.st.receiverChains.length hi hch_lt
            s0 s1 hpc1 hrun1 hsp1 hsp1_align hx0_1 hx1_1 hx20_1 hx21_1 hx22_1 hx24_1 hx28_1)
          hm1_empty hL1
      have hm2_pre : s2.mem ⊨ cmkPreLoopHeap_placed (A.atState lim st s2) x s0 ∗ R := by
        unfold cmkPreLoopHeap_placed
        rw [ratchetAt_atState, RustCliAllocBudget.atState_pool]
        have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
        rw [← A.pool_transport lim st s1 s2 hvm2] at hm2'
        have hreassemble := ratchetAt_reassemble_self A.repAlloc x.self x.G x.st hi hgi hprops
        rw [hgks] at hreassemble
        have hm2'' : s2.mem ⊨
            (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
              ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ 0#64) ∗
              vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
                (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
              ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi) ∗
            ((x.theirA ↦ₛ x.their.bytes.toList) ∗
              (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
              memRegion x.ret 88 ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗
              stackAt (s0.sp - 480#64) 7712 ∗
              memRegion (s0.sp - 480#64) 384 ∗
              cmkSavedRegs s0.sp s0 ∗
              A.pool lim st s2 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2'
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
          (Satisfies.mono (sepConj_mono_left hreassemble) hm2'')
      have hmk_nil : x.st.receiverChains[ci].messageKeys = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      have hfind_none :
          x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) = none := by
        simp [hmk_nil]
      have hmodel := cmk_model_past_miss_chain F x hci hi hfind_none hc_lt
      exact reaches_outcome_steps (hsteps1.trans hsteps2)
        (cmk_dup_0xb4_placed_outcome x hsb R s0 s2 hpc2 hrun2 hsp2 hsp2_align
          (by reg_chain) hx20_2 hx22_2 hx28_2 hmodel hm2_pre)
    · have hmk_pos : 0 < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length :=
        Nat.pos_of_ne_zero hgks
      have hmk_max :
          (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length ≤ maxMessageKeys := by
        rw [hzip_len]; exact hmax_c
      have hm1_nonempty : s1.mem ⊨
          (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
           ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
             BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)) ∗
          (vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
             (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
           ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool lim st s1 ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1_c
      obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hvm2, hsp2, hsp2_align,
        hx2_2, hx8_2, hx19_2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hP2⟩ :=
        sepWP_to_reaches_pc
          (cmk_after_find_nonempty_placed_wp x.G.chainsPtr x.G.chains[ci].mkPtr
            (x.counter.zeroExtend 64) x.ret (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            ci x.st.receiverChains.length
            (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length
            hi hch_lt hmk_pos hmk_max s0 s1 hpc1 hrun1 hsp1 hsp1_align
            hx0_1 hx1_1 hx20_1 hx21_1 hx22_1 hx24_1 hx28_1 hx29_1)
          hm1_nonempty hL1
      have hm2' : s2.mem ⊨
          (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
           ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
             BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
           vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
             (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
           ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool lim st s2) ∗ R := by
        have hm2_0 := Satisfies.mono (sepConj_mono_left hP2) hm2
        rw [← A.pool_transport lim st s1 s2 hvm2] at hm2_0
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2_0
      exact reaches_outcome_steps (hsteps1.trans hsteps2)
        (cmk_pos_loop_0x94_placed_outcome hA hmemmove_eq x hsb R s0 hci hi hgi hprops hc_lt
          (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length 0 s2
          (by omega) hmk_pos rfl hpc2 hrun2 hsp2 hsp2_align
          (by reg_chain)
          hx2_2 hx8_2 hx19_2 hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2 hm2')

end LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CoreBudget
