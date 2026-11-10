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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.ChainKeyFieldX
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `encode::<Chain, Vec<u8>>` Segment 3: `chain_key` (`+284` → `+600`)

Verifies relocatable Segment 3 (`chain_key: Option<ChainKey>`, Block `12` offsets `+284..+600`,
cold `+1884..+2012`) under `RustCliAllocBudget M` and `EncRawSegEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.ChainKeyFieldXBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ChainKey)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsρ lsMemcpySym
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecPin optChainKeyAt optChainKeyNone)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncodeVarintGhost vecU8Buf
  vecU8Buf_eq_open_one vecU8Buf_snoc_eq
  cap_beq_len_false cap_eq_ofNat_len bv_len_add_one
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length hwVarintLen_w32_natShift_eq_encodeVarint_length
  cap_add_one_beq_zero_false encodeVarint_length_bounds
)
open CryptoVerification.E2E.Record (uint32Field msgField encChainKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12)
open CryptoVerification.E2E.Record.Serialization (
  encChainSubStackX vecU8At_eq_cells_buf
  vecU8Buf_eq_open_bytes vecReadRest bv_len_add_slice
  spare_ult_iff ule_of_ult_false
  encChainKey_length_zero encChainKey_length_nonzero
  uint32Field1_zero_eq uint32Field1_nonzero_eq
  optChainKeyAt_none_eq optChainKeyAt_some_eq_encChain
  msgField3_some_eq bytesField2_keyToBytes32_length_encChain
  keyToBytes32_length bytesField2_keyToBytes32_eq
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
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  ofNat_countLeadingZeros_64
  ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length
  hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length
  hwVarintLen_w32_natShift_eq_encodeVarint_length

/-- Checks `Some`, writes tag `0x1a#8`, and loads `w22`, `x21` (`+284 → +340`, cold `1884..1908`). -/
theorem step_encChain_seg3_write_tag_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a curCap curPtr ckCap sp0 : BitVec 64) (ckIdx : BitVec 32) (curBs : List (BitVec 8))
    (st : M.σ)
    (hck_lt : ckCap.toNat < 2 ^ 63)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv curBs.length 1))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 340#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx →
      EncRawSegEnv curBs.length 1 evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap1 ptr1 (curBs ++ [0x1a#8]) ∗
          ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hle _ _ => ?_
  have hck_niche := cap_add_one_beq_zero_false hck_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x1a#8
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (340))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs 0x1a#8 hlt,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ curCap curPtr [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (encRawSegEnv_nil curBs.length 1))
    rw [vecU8At_eq_cells_buf]; sep_ac_rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hfit_dr : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs 1)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp; omega) (by dsimp; omega) (by omega) hfit
    have hevs_dr : EncRawSegEnv curBs.length 1
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) :=
      encRawSegEnv_doReserve (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_reserve1_placed_x A lim H hDR v curCap curPtr sp0
      ((blkPl_12).base + bv% (1904)) curBs st hcap_eq (by omega) hfit_dr (s0 := s0)
      (F := ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt _
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x1a#8
    rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (340))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs 0x1a#8 hnew_gt,
      ← A.pool_of_vmPreserved (lim := lim)
        (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) hvm2]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ newCap p' (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hevs_dr)
    rw [vecU8At_eq_cells_buf]; sep_ac_rfl

/-- Computes `(encChainKey ck).length` and calls `encode_varint` (`+340 → +416`). -/
theorem step_encChain_seg3_len_varint_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (v a cap1 ptr1 sp0 : BitVec 64) (ck : ChainKey) (bs1 : List (BitVec 8))
    (st : M.σ)
    (hcur_lt : bs1.length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv bs1.length (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ck.index)
    (hP : P = (vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 416#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ck.index →
      EncRawSegEnv bs1.length (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have ⟨_, hvar_le⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 (encChainKey ck).length)
  have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
    (x := EncodeVarintGhost.mk (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 bs1)
    (Nat.le_refl _) (Nat.le_refl _) (by dsimp only; omega) hfit
  by_cases hidx : ck.index = 0#32
  · have hidx_beq : (ck.index == 0#32) = true := by simp [hidx]
    have hlen_eq := encChainKey_length_zero hidx
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    refine step_encChain_encodeVarint_placed_x A lim H hEV
      (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (416)) bs1 st
      hcur_lt hfit_ev (s0 := s0) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by sep_ac_rfl) ?_
    intro sm cap2 ptr2 evs hpcm hrunm hspm htrm hcsm hevs _ _
    exact hnext sm cap2 ptr2 evs hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
      (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _) (Nat.le_refl _) (by omega) hevs)
  · have hidx_beq : (ck.index == 0#32) = false := beq_eq_false_iff_ne.mpr hidx
    have hlen_eq := encChainKey_length_nonzero hidx
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    refine step_encChain_encodeVarint_placed_x A lim H hEV
      (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (416)) bs1 st
      hcur_lt hfit_ev (s0 := s0) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by sep_ac_rfl) ?_
    intro sm cap2 ptr2 evs hpcm hrunm hspm htrm hcsm hevs _ _
    exact hnext sm cap2 ptr2 evs hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
      (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _) (Nat.le_refl _) (by omega) hevs)

/-- Encodes `uint32Field 1 ck.index` (`+416 → +496`, cold `1912..1936`). -/
theorem step_encChain_seg3_index_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a cap2 ptr2 sp0 : BitVec 64) (ckIdx : BitVec 32) (bs2 : List (BitVec 8))
    (st : M.σ)
    (hcur_lt : bs2.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs2.length (uint32Field 1 ckIdx).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx)
    (hP : P = (vecU8At A.repAlloc v cap2 ptr2 bs2 ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 496#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      EncRawSegEnv bs2.length (uint32Field 1 ckIdx).length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3 (bs2 ++ uint32Field 1 ckIdx) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  by_cases hidx : ckIdx = 0#32
  · have hidx_bne : (ckIdx != 0#32) = false := by simp [hidx]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (496))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hu0 : bs2 ++ uint32Field 1 ckIdx = bs2 := by simp [hidx, uint32Field1_zero_eq]
    rw [← hu0, ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    exact hnext _ cap2 ptr2 [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (encRawSegEnv_nil bs2.length (uint32Field 1 ckIdx).length)
  · have hidx_bne : (ckIdx != 0#32) = true := bne_iff_ne.mpr hidx
    have hu_eq : (bs2 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 ckIdx) =
        bs2 ++ uint32Field 1 ckIdx := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hidx]
    have hu_len : (uint32Field 1 ckIdx).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length := by
      rw [← uint32Field1_nonzero_eq hidx, List.length_append, List.length_singleton]
    have ⟨hvar_pos, hvar_le⟩ := encodeVarint_length_bounds (BitVec.zeroExtend 64 ckIdx)
    have hcur_snoc_lt : (bs2 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A.repAlloc v cap2 ptr2 bs2]
    refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by sep_ac_rfl) fun hle _ _ => ?_
    by_cases hlt : bs2.length < cap2.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs2 0x08#8
      have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
        (x := EncodeVarintGhost.mk (BitVec.zeroExtend 64 ckIdx) v cap2 ptr2 (bs2 ++ [0x08#8]))
        (by dsimp only; omega)
        (by dsimp only; rw [List.length_append, List.length_singleton]; omega)
        (by omega) hfit
      rw [vecU8Buf_eq_open_one A.repAlloc cap2 ptr2 bs2 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpLsCl.exists_elim fun y => ?_
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
      by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      rw [vecU8Buf_snoc_eq A.repAlloc cap2 ptr2 bs2 0x08#8 hlt,
        ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
      refine step_encChain_encodeVarint_placed_x A lim H hEV
        (BitVec.zeroExtend 64 ckIdx) v cap2 ptr2 sp0 ((blkPl_12).base + bv% (496)) (bs2 ++ [0x08#8]) st
        hcur_snoc_lt hfit_ev (s0 := s0) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]) ?_
      intro sm cap3 ptr3 evs hpcm hrunm hspm htrm hcsm hevs _ _
      rw [hu_eq]
      exact hnext sm cap3 ptr3 evs hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_of_encodeVarintEnv (by dsimp only; omega)
          (by dsimp only; rw [List.length_append, List.length_singleton]; omega) (by omega) hevs)
    · have hcap_eq : cap2.toNat = bs2.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      have hfit12 : FitsEnv M lim st
          (EncRawSegEnv bs2.length (1 + (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length)) := by
        rw [← hu_len]; exact hfit
      have hfit_dr : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap2 ptr2 bs2 1)) :=
        fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega)
          (fitsEnv_encRawSeg_left hfit12)
      have hevs1 : EncRawSegEnv bs2.length 1 (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)) :=
        encRawSegEnv_doReserve (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega)
      have hfit2 := fitsEnv_encRawSeg_right hfit12 hevs1
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
      by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
      refine step_encChain_reserve1_placed_x A lim H hDR v cap2 ptr2 sp0
        ((blkPl_12).base + bv% (1932)) bs2 st hcap_eq (by omega) hfit_dr (s0 := s0)
        (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt _
      have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
      have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
      have hx21r : sr.readReg64 .x21 = 32#64 := hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hx22r : sr.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx :=
        hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one bs2 0x08#8
      have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
        (x := EncodeVarintGhost.mk (BitVec.zeroExtend 64 ckIdx) v newCap p' (bs2 ++ [0x08#8]))
        (Nat.le_refl _)
        (by dsimp only; rw [List.length_append, List.length_singleton])
        (by dsimp only; omega) hfit2
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' bs2 hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpLsCl.exists_elim fun y => ?_
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
      by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      rw [vecU8Buf_snoc_eq A.repAlloc newCap p' bs2 0x08#8 hnew_gt,
        ← A.pool_of_vmPreserved (lim := lim)
          (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)) st) hvm2]
      refine step_encChain_encodeVarint_placed_x A lim H hEV
        (BitVec.zeroExtend 64 ckIdx) v newCap p' sp0 ((blkPl_12).base + bv% (496)) (bs2 ++ [0x08#8])
        (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)) st)
        hcur_snoc_lt hfit_ev (s0 := s0) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
      intro sm cap3 ptr3 evs2 hpcm hrunm hspm htrm hcsm hevs2 _ _
      have hevs2' : EncRawSegEnv (bs2.length + 1)
          (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length evs2 :=
        encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
          (by dsimp only; rw [List.length_append, List.length_singleton]) (by omega) hevs2
      have hevs12 : EncRawSegEnv bs2.length (uint32Field 1 ckIdx).length
          (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1) ++ evs2) := by
        rw [hu_len]
        exact encRawSegEnv_append hevs1 hevs2'
      rw [hu_eq, ← M.stepEvents_append]
      exact hnext sm cap3 ptr3
        (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1) ++ evs2)
        hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        hevs12

/-- Writes key tag `0x12#8` and calls `encode_varint 32#64` (`+496 → +552`, cold `1940..1968`). -/
theorem step_encChain_seg3_key_tag_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a cap3 ptr3 ckPtr sp0 : BitVec 64) (bs3 : List (BitVec 8))
    (st : M.σ)
    (hcur_lt : bs3.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs3.length (1 + (encodeVarint 32#64).length)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hP : P = ((v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A.repAlloc cap3 ptr3 bs3 ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 552#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = ckPtr →
      EncRawSegEnv bs3.length (1 + (encodeVarint 32#64).length) evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap4 ptr4 ((bs3 ++ [0x12#8]) ++ encodeVarint 32#64) ∗
          ((a + 80#64) ↦₆₄ ckPtr) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have ⟨hvar_pos, hvar_le⟩ := encodeVarint_length_bounds 32#64
  have hcur_snoc_lt : (bs3 ++ [0x12#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hle _ _ => ?_
  by_cases hlt : bs3.length < cap3.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs3 0x12#8
    have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
      (x := EncodeVarintGhost.mk 32#64 v cap3 ptr3 (bs3 ++ [0x12#8]))
      (by dsimp; omega)
      (by dsimp; rw [List.length_append, List.length_singleton]; omega)
      (by omega) hfit
    rw [vecU8Buf_eq_open_one A.repAlloc cap3 ptr3 bs3 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    rw [vecU8Buf_snoc_eq A.repAlloc cap3 ptr3 bs3 0x12#8 hlt,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    refine step_encChain_encodeVarint_placed_x A lim H hEV
      32#64 v cap3 ptr3 sp0 ((blkPl_12).base + bv% (552)) (bs3 ++ [0x12#8]) st
      hcur_snoc_lt hfit_ev (s0 := s0) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
    intro sm cap4 ptr4 evs hpcm hrunm hspm htrm hcsm hevs _ _
    refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
      (hnext sm cap4 ptr4 evs hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_of_encodeVarintEnv (by dsimp; omega)
          (by dsimp; rw [List.length_append, List.length_singleton]; omega) (by omega) hevs))
  · have hcap_eq : cap3.toNat = bs3.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hfit_dr : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap3 ptr3 bs3 1)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
        (fitsEnv_encRawSeg_left hfit)
    have hevs1 : EncRawSegEnv bs3.length 1 (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) :=
      encRawSegEnv_doReserve (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
    have hfit2 := fitsEnv_encRawSeg_right hfit hevs1
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_reserve1_placed_x A lim H hDR v cap3 ptr3 sp0
      ((blkPl_12).base + bv% (1960)) bs3 st hcap_eq (by omega) hfit_dr (s0 := s0)
      (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt _
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = 32#64 := hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = ckPtr := hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one bs3 0x12#8
    have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
      (x := EncodeVarintGhost.mk 32#64 v newCap p' (bs3 ++ [0x12#8]))
      (Nat.le_refl _)
      (by dsimp only; rw [List.length_append, List.length_singleton])
      (by dsimp only; omega) hfit2
    rw [vecU8Buf_eq_open_one A.repAlloc newCap p' bs3 hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [vecU8Buf_snoc_eq A.repAlloc newCap p' bs3 0x12#8 hnew_gt,
      ← A.pool_of_vmPreserved (lim := lim)
        (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) st) hvm2]
    refine step_encChain_encodeVarint_placed_x A lim H hEV
      32#64 v newCap p' sp0 ((blkPl_12).base + bv% (552)) (bs3 ++ [0x12#8])
      (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1)) st)
      hcur_snoc_lt hfit_ev (s0 := s0) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
    intro sm cap4 ptr4 evs2 hpcm hrunm hspm htrm hcsm hevs2 _ _
    have hevs2' : EncRawSegEnv (bs3.length + 1) (encodeVarint 32#64).length evs2 :=
      encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
        (by dsimp; rw [List.length_append, List.length_singleton]) (by omega) hevs2
    rw [← M.stepEvents_append]
    refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
      (hnext sm cap4 ptr4
        (doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 1) ++ evs2)
        hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_append hevs1 hevs2'))

/-- Reserves space and copies the 32 key bytes via `memcpy` (`+552 → +600`, cold `1968..2012`). -/
theorem step_encChain_seg3_key_copy_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a cap4 ptr4 ckCap ckPtr sp0 : BitVec 64) (bsMid keyBs : List (BitVec 8))
    (st : M.σ)
    (hkey_pos : 0 < keyBs.length)
    (hkey_lt : keyBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv bsMid.length keyBs.length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 552#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 keyBs.length)
    (hx22 : s.readReg64 .x22 = ckPtr)
    (hP : P = ((v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc cap4 ptr4 bsMid ∗
      vecU8Buf A.repAlloc ckCap ckPtr keyBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      EncRawSegEnv bsMid.length keyBs.length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap5 ptr5 (bsMid ++ keyBs) ∗
          vecU8Buf A.repAlloc ckCap ckPtr keyBs ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := cap4) (ptr := ptr4) (bs := bsMid)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc ckCap ckPtr keyBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hle4 _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := ckCap) (ptr := ckPtr) (bs := keyBs)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc cap4 ptr4 bsMid ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hkey_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid keyBs
  by_cases hspare : bsMid.length + keyBs.length ≤ cap4.toNat
  · have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = false :=
      (spare_ult_iff hle4 hmid_lt hkey_lt).2.mpr hspare
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [vecU8Buf_eq_open_bytes A.repAlloc ckCap ckPtr keyBs hkey_pos hkey_le,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_memcpy_placed_x A lim H hC cap4 ptr4 ckPtr sp0
      ((blkPl_12).base + bv% (592)) bsMid keyBs st hkey_pos hspare hkey_lt (s0 := s0)
      (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A.repAlloc ckCap ckPtr keyBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sm _ hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (600))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm2]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ cap4 ptr4 [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (encRawSegEnv_nil bsMid.length keyBs.length))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A.repAlloc ckCap ckPtr keyBs hkey_pos hkey_le]
    sep_ac_rfl
  · have hrem : cap4.toNat - bsMid.length < keyBs.length := by omega
    have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = true :=
      (spare_ult_iff hle4 hmid_lt hkey_lt).1.mpr hrem
    have hfit_dr : FitsEnv M lim st
        (DoReserveEnv (DoReserveCall.mk v cap4 ptr4 bsMid keyBs.length)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp; omega) (by dsimp; omega) (by omega) hfit
    have hevs_dr : EncRawSegEnv bsMid.length keyBs.length
        (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bsMid keyBs.length)) :=
      encRawSegEnv_doReserve (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_reserveSlice_placed_x A lim H hDR v cap4 ptr4 sp0
      ((blkPl_12).base + bv% (1992)) bsMid keyBs.length st hle4 hrem hmid_lt hkey_lt hfit_dr
      (s0 := s0)
      (F := vecU8Buf A.repAlloc ckCap ckPtr keyBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false _
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = ckPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [vecU8Buf_eq_open_bytes A.repAlloc ckCap ckPtr keyBs hkey_pos hkey_le,
      ← A.pool_of_vmPreserved (lim := lim)
        (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bsMid keyBs.length)) st)
        hvm2]
    refine step_encChain_memcpy_placed_x A lim H hC newCap p' ckPtr sp0
      ((blkPl_12).base + bv% (592)) bsMid keyBs
      (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bsMid keyBs.length)) st)
      hkey_pos hnew_ge hkey_lt (s0 := s0)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A.repAlloc ckCap ckPtr keyBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sm _ hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (600))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm3 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim)
      (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bsMid keyBs.length)) st)
      hvm3]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ newCap p' (doReserveEvents (DoReserveCall.mk v cap4 ptr4 bsMid keyBs.length))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hevs_dr)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A.repAlloc ckCap ckPtr keyBs hkey_pos hkey_le]
    sep_ac_rfl

/-- Combined Segment 3 (`+284 → +600`): `chain_key: Option<ChainKey>`. -/
theorem step_encChain_seg3_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a curCap curPtr sp0 : BitVec 64) (pin : VecPin) (o : Option ChainKey)
    (curBs : List (BitVec 8))
    (st : M.σ)
    (hbound : curBs.length + (msgField 3 (o.map encChainKey)).length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv curBs.length (msgField 3 (o.map encChainKey)).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ optChainKeyAt A.repAlloc pin o (a + 72#64) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      EncRawSegEnv curBs.length (msgField 3 (o.map encChainKey)).length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap' ptr' (curBs ++ msgField 3 (o.map encChainKey)) ∗
          optChainKeyAt A.repAlloc pin o (a + 72#64) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  cases o with
  | none =>
    rw [optChainKeyAt_none_eq]
    have hnone_beq : (optChainKeyNone + 1#64 == 0#64) = true := rfl
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (600))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hmf0 : curBs ++ msgField 3 (Option.map encChainKey none) = curBs := by simp [msgField]
    rw [← optChainKeyAt_none_eq, ← hmf0, ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    exact hnext _ curCap curPtr [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (encRawSegEnv_nil curBs.length (msgField 3 (Option.map encChainKey none)).length)
  | some ck =>
    have hmf_eq := msgField3_some_eq ck
    have hmf_len : 1 + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length +
        (uint32Field 1 ck.index).length + 34 =
        (msgField 3 (some (encChainKey ck))).length := by
      have h := congrArg List.length hmf_eq
      simp only [List.length_append, List.length_singleton, bytesField2_keyToBytes32_length_encChain] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 (encChainKey ck).length)
    have hev32_len : (encodeVarint 32#64).length = 1 := by decide +kernel
    have hkey_len := keyToBytes32_length ck.key
    have hdecomp :
        (msgField 3 (Option.map encChainKey (some ck))).length =
        1 + ((encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length +
          ((uint32Field 1 ck.index).length +
            ((1 + (encodeVarint 32#64).length) + (keyToBytes32 ck.key).length))) := by
      simp only [Option.map_some, hev32_len, hkey_len]
      omega
    have hfit0 : FitsEnv M lim st
        (EncRawSegEnv curBs.length
          (1 + ((encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length +
            ((uint32Field 1 ck.index).length +
              ((1 + (encodeVarint 32#64).length) + (keyToBytes32 ck.key).length))))) := by
      rw [← hdecomp]; exact hfit
    rw [optChainKeyAt_some_eq_encChain A.repAlloc pin ck a, vecU8At_eq_cells_buf A.repAlloc v curCap curPtr curBs]
    refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := pin.cap) (ptr := pin.ptr)
      (bs := keyToBytes32 ck.key)
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
        vecU8Buf A.repAlloc curCap curPtr curBs ∗
        ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗ memRegion (a + 100#64) 4 ∗
        A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by sep_ac_rfl) fun _ hck_lt _ => ?_
    refine step_encChain_seg3_write_tag_placed_x A lim H hDR
      v a curCap curPtr pin.cap sp0 ck.index curBs st hck_lt
      (by simp only [Option.map_some] at hbound; omega)
      (fitsEnv_encRawSeg_left hfit0)
      (F := ((a + 80#64) ↦₆₄ pin.ptr) ∗ vecU8Buf A.repAlloc pin.cap pin.ptr (keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by sep_ac_rfl) ?_
    intro s1 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hevs1
    have hfit1 := fitsEnv_encRawSeg_right hfit0 hevs1
    have hbs1_len : (curBs ++ [0x1a#8]).length = curBs.length + 1 := by
      rw [List.length_append, List.length_singleton]
    refine step_encChain_seg3_len_varint_placed_x A lim H hEV
      v a cap1 ptr1 sp0 ck (curBs ++ [0x1a#8]) (M.stepEvents evs1 st)
      (by rw [hbs1_len]; simp only [Option.map_some] at hbound; omega)
      (hbs1_len ▸ fitsEnv_encRawSeg_left hfit1)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A.repAlloc pin.cap pin.ptr (keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by sep_ac_rfl) ?_
    intro s2 cap2 ptr2 evs2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hevs2
    have hevs2' : EncRawSegEnv (curBs.length + 1)
        (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length evs2 := by
      rw [hbs1_len] at hevs2; exact hevs2
    have hfit2 := fitsEnv_encRawSeg_right hfit1 hevs2'
    have hbs2_len :
        ((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length =
        (curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length := by
      rw [List.length_append, hbs1_len]
    refine step_encChain_seg3_index_placed_x A lim H hEV hDR
      v a cap2 ptr2 sp0 ck.index
      ((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length))
      (M.stepEvents evs2 (M.stepEvents evs1 st))
      (by rw [hbs2_len]; simp only [Option.map_some] at hbound; omega)
      (hbs2_len ▸ fitsEnv_encRawSeg_left hfit2)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A.repAlloc pin.cap pin.ptr (keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 (by sep_ac_rfl) ?_
    intro s3 cap3 ptr3 evs3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hevs3
    have hevs3' : EncRawSegEnv
        ((curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length)
        (uint32Field 1 ck.index).length evs3 := by
      rw [hbs2_len] at hevs3; exact hevs3
    have hfit3 := fitsEnv_encRawSeg_right hfit2 hevs3'
    have hbs3_len :
        (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
          uint32Field 1 ck.index).length =
        ((curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length) +
          (uint32Field 1 ck.index).length := by
      rw [List.length_append, hbs2_len]
    rw [vecU8At_eq_cells_buf A.repAlloc v cap3 ptr3
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)]
    refine step_encChain_seg3_key_tag_placed_x A lim H hEV hDR
      v a cap3 ptr3 pin.ptr sp0
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)
      (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))
      (by rw [hbs3_len]; simp only [Option.map_some] at hbound; omega)
      (hbs3_len ▸ fitsEnv_encRawSeg_left hfit3)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A.repAlloc pin.cap pin.ptr (keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 (by sep_ac_rfl) ?_
    intro s4 cap4 ptr4 evs4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hevs4
    have hevs4' : EncRawSegEnv
        (((curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length) +
          (uint32Field 1 ck.index).length)
        (1 + (encodeVarint 32#64).length) evs4 := by
      rw [hbs3_len] at hevs4; exact hevs4
    have hfit4 := fitsEnv_encRawSeg_right hfit3 hevs4'
    have hbs4_len :
        (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
          uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64).length =
        (((curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length) +
          (uint32Field 1 ck.index).length) + (1 + (encodeVarint 32#64).length) := by
      rw [List.length_append, List.length_append, List.length_singleton, hbs3_len, Nat.add_assoc]
    rw [vecU8At_eq_cells_buf A.repAlloc v cap4 ptr4
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)]
    have hx21_4' : s4.readReg64 .x21 = BitVec.ofNat 64 (keyToBytes32 ck.key).length := by
      rw [hkey_len]; exact hx21_4
    refine step_encChain_seg3_key_copy_placed_x A lim H hC hDR
      v a cap4 ptr4 pin.cap pin.ptr sp0
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)
      (keyToBytes32 ck.key)
      (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))))
      (by omega) (by omega)
      (by rw [hbs4_len, hev32_len]; simp only [Option.map_some] at hbound; omega)
      (hbs4_len ▸ hfit4)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4' hx22_4 (by sep_ac_rfl) ?_
    intro s5 cap5 ptr5 evs5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hevs5
    have hevs5' : EncRawSegEnv
        ((((curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length) +
          (uint32Field 1 ck.index).length) + (1 + (encodeVarint 32#64).length))
        (keyToBytes32 ck.key).length evs5 := by
      rw [hbs4_len] at hevs5; exact hevs5
    have hevs_all : EncRawSegEnv curBs.length
        (msgField 3 (Option.map encChainKey (some ck))).length
        (evs1 ++ (evs2 ++ (evs3 ++ (evs4 ++ evs5)))) := by
      rw [hdecomp]
      exact encRawSegEnv_append hevs1
        (encRawSegEnv_append hevs2'
          (encRawSegEnv_append hevs3'
            (encRawSegEnv_append hevs4' hevs5')))
    have hst_eq :
        M.stepEvents evs5 (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))) =
        M.stepEvents (evs1 ++ (evs2 ++ (evs3 ++ (evs4 ++ evs5)))) st := by
      simp only [M.stepEvents_append]
    have hlist :
        ((((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
          uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64) ++
          keyToBytes32 ck.key) =
        curBs ++ msgField 3 (Option.map encChainKey (some ck)) := by
      have hbf2 := bytesField2_keyToBytes32_eq ck.key
      simp only [Option.map_some, ← hmf_eq, ← hbf2, List.append_assoc]
    rw [hst_eq]
    refine SepWPpLsCl.congr_pre ?_
      (hnext s5 cap5 ptr5 (evs1 ++ (evs2 ++ (evs3 ++ (evs4 ++ evs5))))
        hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hevs_all)
    rw [hlist, optChainKeyAt_some_eq_encChain A.repAlloc pin ck a]
    sep_ac_rfl

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.ChainKeyFieldXBudget
