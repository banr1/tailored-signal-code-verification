/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXB
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `encode::<Chain, Vec<u8>>` Segment 2: `sender_ratchet_key_private` (`+176` → `+284`)

Verifies relocatable Segment 2 (`sender_ratchet_key_private`, Block `12` offsets `+176..+284`,
cold `+1780..+1848`) under `RustCliAllocBudget M` and `EncRawSegEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXBBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsρ lsMemcpySym
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncodeVarintGhost vecU8Buf encodeVarint_length_bounds
  vecU8Buf_eq_open_one vecU8Buf_snoc_eq
  cap_beq_len_false cap_eq_ofNat_len bv_len_add_one
)
open CryptoVerification.E2E.Record (bytesField)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12)
open CryptoVerification.E2E.Record.Serialization (
  encChainSubStackX bv_add_neg96
  bytesField_nonempty_eq bv_ofNat_beq_zero_false
  vecU8At_eq_cells_buf vecU8At_add24_eq_cells_buf
  vecU8Buf_eq_open_bytes vecReadRest bv_len_add_slice
  spare_ult_iff ule_of_ult_false
)
open Proofs.libsignal.Hooks2 (
  SepWPpLsCl sepWPpLsCl_extract_vecU8Buf_bounds
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX DoReservePlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm encRawSegEnv_doReserve encRawSegEnv_of_encodeVarintEnv
  step_encChain_encodeVarint_placed_x step_encChain_reserve1_placed_x
  step_encChain_reserveSlice_placed_x step_encChain_memcpy_placed_x
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg96

/-- Segment 2 tag + length varint (`+176 → +236`, cold `1780..1808`): `sender_ratchet_key_private`. -/
theorem step_encChain_seg2_tag_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a curCap curPtr privPtr sp0 : BitVec 64) (curBs privBs : List (BitVec 8))
    (st : M.σ)
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv curBs.length (1 + (encodeVarint (BitVec.ofNat 64 privBs.length)).length)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 236#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length →
      sm.readReg64 .x22 = privPtr →
      EncRawSegEnv curBs.length (1 + (encodeVarint (BitVec.ofNat 64 privBs.length)).length) evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have ⟨_, hvar_le⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 privBs.length)
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hle _ _ => ?_
  have hpriv_nz := bv_ofNat_beq_zero_false hpriv_pos hpriv_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x12#8
    have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
      (x := EncodeVarintGhost.mk (BitVec.ofNat 64 privBs.length) v curCap curPtr (curBs ++ [0x12#8]))
      (by dsimp; omega)
      (by dsimp; rw [List.length_append, List.length_singleton]; omega)
      (by omega) hfit
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs 0x12#8 hlt,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    refine step_encChain_encodeVarint_placed_x A lim H hEV
      (BitVec.ofNat 64 privBs.length) v curCap curPtr sp0 ((blkPl_12).base + bv% (236))
      (curBs ++ [0x12#8]) st
      (by simp only [List.length_append, List.length_singleton]; omega)
      hfit_ev (s0 := s0)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
    intro sm cap2 ptr2 evs hpcm hrunm hspm htrm hcsm hevs _ _
    refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
      (hnext sm cap2 ptr2 evs hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_of_encodeVarintEnv (by dsimp; omega)
          (by dsimp; rw [List.length_append, List.length_singleton]; omega) (by omega) hevs))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hfit_dr : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs 1)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
        (fitsEnv_encRawSeg_left hfit)
    have hevs1 : EncRawSegEnv curBs.length 1 (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) :=
      encRawSegEnv_doReserve (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
    have hfit2 := fitsEnv_encRawSeg_right hfit hevs1
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_reserve1_placed_x A lim H hDR v curCap curPtr sp0
      ((blkPl_12).base + bv% (1800)) curBs st hcap_eq (by omega) hfit_dr (s0 := s0)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt _
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = privPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x12#8
    have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
      (x := EncodeVarintGhost.mk (BitVec.ofNat 64 privBs.length) v newCap p' (curBs ++ [0x12#8]))
      (Nat.le_refl _)
      (by dsimp only; rw [List.length_append, List.length_singleton])
      (by dsimp only; omega) hfit2
    rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs 0x12#8 hnew_gt,
      ← A.pool_of_vmPreserved (lim := lim)
        (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) hvm2]
    refine step_encChain_encodeVarint_placed_x A lim H hEV
      (BitVec.ofNat 64 privBs.length) v newCap p' sp0 ((blkPl_12).base + bv% (236))
      (curBs ++ [0x12#8])
      (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st)
      (by simp only [List.length_append, List.length_singleton]; omega)
      hfit_ev (s0 := s0)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
    intro sm cap2 ptr2 evs2 hpcm hrunm hspm htrm hcsm hevs2 _ _
    have hevs2' : EncRawSegEnv (curBs.length + 1)
        (encodeVarint (BitVec.ofNat 64 privBs.length)).length evs2 :=
      encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
        (by dsimp; rw [List.length_append, List.length_singleton]) (by omega) hevs2
    rw [← M.stepEvents_append]
    refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
      (hnext sm cap2 ptr2
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) ++ evs2)
        hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_append hevs1 hevs2'))

/-- Segment 2 payload copy (`+236 → +284`, cold `1808..1848`): reserve & `memcpy` `privBs`. -/
theorem step_encChain_seg2_copy_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a cap2 ptr2 privCap privPtr sp0 : BitVec 64) (bsMid privBs : List (BitVec 8))
    (st : M.σ)
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv bsMid.length privBs.length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 236#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 privBs.length)
    (hx22 : s.readReg64 .x22 = privPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc cap2 ptr2 bsMid ∗
      vecU8Buf A.repAlloc privCap privPtr privBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 284#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      EncRawSegEnv bsMid.length privBs.length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3 (bsMid ++ privBs) ∗
          vecU8Buf A.repAlloc privCap privPtr privBs ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc privCap privPtr privBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hle2 _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := privCap) (ptr := privPtr) (bs := privBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc cap2 ptr2 bsMid ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hpriv_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid privBs
  by_cases hspare : bsMid.length + privBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hpriv_lt).2.mpr hspare
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [vecU8Buf_eq_open_bytes A.repAlloc privCap privPtr privBs hpriv_pos hpriv_le,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_memcpy_placed_x A lim H hC cap2 ptr2 privPtr sp0
      ((blkPl_12).base + bv% (276)) bsMid privBs st hpriv_pos hspare (by omega) (s0 := s0)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A.repAlloc privCap privPtr privBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sm _ hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (284))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm2]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ cap2 ptr2 [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (encRawSegEnv_nil bsMid.length privBs.length))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A.repAlloc privCap privPtr privBs hpriv_pos hpriv_le]
    sep_ac_rfl
  · have hrem : cap2.toNat - bsMid.length < privBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hpriv_lt).1.mpr hrem
    have hfit_dr : FitsEnv M lim st
        (DoReserveEnv (DoReserveCall.mk v cap2 ptr2 bsMid privBs.length)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp; omega) (by dsimp; omega) (by omega) hfit
    have hevs_dr : EncRawSegEnv bsMid.length privBs.length
        (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid privBs.length)) :=
      encRawSegEnv_doReserve (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_reserveSlice_placed_x A lim H hDR v cap2 ptr2 sp0
      ((blkPl_12).base + bv% (1832)) bsMid privBs.length st hle2 hrem (by omega) (by omega) hfit_dr
      (s0 := s0)
      (F := vecU8Buf A.repAlloc privCap privPtr privBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false _
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = privPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [vecU8Buf_eq_open_bytes A.repAlloc privCap privPtr privBs hpriv_pos hpriv_le,
      ← A.pool_of_vmPreserved (lim := lim)
        (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid privBs.length)) st)
        hvm2]
    refine step_encChain_memcpy_placed_x A lim H hC newCap p' privPtr sp0
      ((blkPl_12).base + bv% (276)) bsMid privBs
      (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid privBs.length)) st)
      hpriv_pos hnew_ge (by omega) (s0 := s0)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A.repAlloc privCap privPtr privBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sm _ hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (284))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm3 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim)
      (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid privBs.length)) st)
      hvm3]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ newCap p' (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid privBs.length))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hevs_dr)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A.repAlloc privCap privPtr privBs hpriv_pos hpriv_le]
    sep_ac_rfl

/-- Combined Segment 2 (`+176 → +284`): `sender_ratchet_key_private: Vec<u8>`. -/
theorem step_encChain_seg2_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a curCap curPtr sp0 : BitVec 64) (priv : VecGhost) (curBs : List (BitVec 8))
    (st : M.σ)
    (hbound : curBs.length + (bytesField 2 priv.bytes).length < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv curBs.length (bytesField 2 priv.bytes).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ vecGhostAt A.repAlloc priv (a + 24#64) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 284#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      EncRawSegEnv curBs.length (bytesField 2 priv.bytes).length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap' ptr' (curBs ++ bytesField 2 priv.bytes) ∗
          vecGhostAt A.repAlloc priv (a + 24#64) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  by_cases hnil : priv.bytes = []
  · unfold vecGhostAt
    rw [vecU8At_add24_eq_cells_buf A.repAlloc a priv.cap priv.ptr priv.bytes]
    have hlen0 : BitVec.ofNat 64 priv.bytes.length = 0#64 := by simp [hnil]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (284))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hbf0 : curBs ++ bytesField 2 priv.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_add24_eq_cells_buf A.repAlloc a priv.cap priv.ptr priv.bytes, ← hbf0,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    exact hnext _ curCap curPtr [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (encRawSegEnv_nil curBs.length (bytesField 2 priv.bytes).length)
  · have hpriv_pos : 0 < priv.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x12#8] ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length) ++ priv.bytes =
        bytesField 2 priv.bytes :=
      bytesField_nonempty_eq 2 0x12#8 priv.bytes hnil (by decide +kernel)
    have hbf_len :
        (bytesField 2 priv.bytes).length =
        (1 + (encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length) + priv.bytes.length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 priv.bytes.length)
    have hfit12 : FitsEnv M lim st
        (EncRawSegEnv curBs.length
          ((1 + (encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length) + priv.bytes.length)) := by
      rw [← hbf_len]; exact hfit
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A.repAlloc v curCap curPtr curBs,
        vecU8At_add24_eq_cells_buf A.repAlloc a priv.cap priv.ptr priv.bytes]
    refine step_encChain_seg2_tag_placed_x A lim H hEV hDR
      v a curCap curPtr priv.ptr sp0 curBs priv.bytes st
      hpriv_pos (by omega) (by omega)
      (fitsEnv_encRawSeg_left hfit12)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ vecU8Buf A.repAlloc priv.cap priv.ptr priv.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by sep_ac_rfl) ?_
    intro s1 cap2 ptr2 evs1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hevs1
    have hfit2 := fitsEnv_encRawSeg_right hfit12 hevs1
    have hbsMid_len :
        ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length =
        curBs.length + (1 + (encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length) := by
      rw [List.length_append, List.length_append, List.length_singleton, Nat.add_assoc]
    rw [vecU8At_eq_cells_buf A.repAlloc v cap2 ptr2
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length))]
    refine step_encChain_seg2_copy_placed_x A lim H hC hDR
      v a cap2 ptr2 priv.cap priv.ptr sp0
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) priv.bytes
      (M.stepEvents evs1 st)
      hpriv_pos (by omega) (by rw [hbsMid_len]; omega)
      (hbsMid_len ▸ hfit2)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ ((a + 32#64) ↦₆₄ priv.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 priv.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by sep_ac_rfl) ?_
    intro s2 cap3 ptr3 evs2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hevs2
    have hevs2' : EncRawSegEnv
        (curBs.length + (1 + (encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length))
        priv.bytes.length evs2 := by
      rw [hbsMid_len] at hevs2; exact hevs2
    have hevs12 : EncRawSegEnv curBs.length (bytesField 2 priv.bytes).length (evs1 ++ evs2) := by
      rw [hbf_len]
      exact encRawSegEnv_append hevs1 hevs2'
    have hlist : ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) ++ priv.bytes =
        curBs ++ bytesField 2 priv.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    rw [← M.stepEvents_append]
    refine SepWPpLsCl.congr_pre ?_
      (hnext s2 cap3 ptr3 (evs1 ++ evs2) hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hevs12)
    unfold vecGhostAt
    rw [hlist, vecU8At_add24_eq_cells_buf A.repAlloc a priv.cap priv.ptr priv.bytes]
    sep_ac_rfl

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXBBudget
