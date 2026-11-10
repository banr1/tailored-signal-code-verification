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
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

/-!
# Budget-threaded `chain_key` header, length, and `index` steps (`+0x11c..+0x1f0`)

Budget-threaded `[LibsignalPlacement]` stepping lemmas for the `Some` tag, submessage length varint,
and `index` field of `chain_key: Option<ChainKey>` in `encode::<Chain, Vec<u8>>` (block `12`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyFieldBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ChainKey)
open CryptoVerification (
  LibsignalPlacement lsmpl LibsignalCodeLoaded withLsCodeLoaded
  blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncodeVarintGhost vecU8Buf sepWPp_extract_vecU8Buf_le
  cap_beq_len_false bv_len_add_one vecU8Buf_eq_open_one vecU8Buf_snoc_eq cap_eq_ofNat_len
  encodeVarint_length_bounds cap_add_one_beq_zero_false
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length hwVarintLen_w32_natShift_eq_encodeVarint_length
)
open CryptoVerification.E2E.Record (uint32Field encChainKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12)
open CryptoVerification.E2E.Record.Serialization (
  encChainSubStack vecU8At_eq_cells_buf
  sepWPp_congr_pre uint32Field1_zero_eq uint32Field1_nonzero_eq
  encChainKey_length_zero encChainKey_length_nonzero
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  doReserveEvents doReserveSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget (
  sepWPp_of_sepWP_lscl_vm step_encChain_encodeVarint_placed step_encChain_reserve1_placed
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
  doReserveEnv_sub_boundedRustEvs encodeVarintEnv_sub_boundedRustEvs
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  ofNat_countLeadingZeros_64
  ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length
  hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length
  hwVarintLen_w32_natShift_eq_encodeVarint_length

/-! ## Allocation envelope membership helpers -/

theorem encRawSegEnv_doReserve (x : DoReserveCall) {bsLen addedLen : Nat}
    (ha_pos : 1 ≤ addedLen)
    (hcap : x.cap.toNat ≤ bsLen + addedLen)
    (hlen : x.bs.length + x.additional ≤ bsLen + addedLen)
    (hout : bsLen + addedLen < 2 ^ 61) :
    EncRawSegEnv bsLen addedLen (doReserveEvents x) :=
  (doReserveEnv_sub_boundedRustEvs hcap hlen hout rfl).mono (by omega) (Nat.le_refl _)

theorem encRawSegEnv_of_encodeVarintEnv {x : EncodeVarintGhost} {bsLen addedLen : Nat}
    (ha : (encodeVarint x.val).length ≤ addedLen)
    (hlen : x.bs.length + (encodeVarint x.val).length ≤ bsLen + addedLen)
    (hout : bsLen + addedLen < 2 ^ 61)
    {evs : List AllocEvent} (hevs : EncodeVarintEnv x evs) :
    EncRawSegEnv bsLen addedLen evs :=
  (encodeVarintEnv_sub_boundedRustEvs hlen hout hevs).mono (by omega) (Nat.le_refl _)

/-! ## `chain_key` tag, length varint, and `index` steps (`+284..+496`) -/

theorem step_encChain_seg3_write_tag_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (v a curCap curPtr ckCap sp0 : BitVec 64) (ckIdx : BitVec 32) (curBs : List (BitVec 8))
    (st : M.σ)
    (hck_lt : ckCap.toNat < 2 ^ 63)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv curBs.length 1))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 284#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 340#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx →
      EncRawSegEnv curBs.length 1 evs →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap1 ptr1 (curBs ++ [0x1a#8]) ∗
          ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hck_niche := cap_add_one_beq_zero_false hck_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x1a#8
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_12).base + bv% (340))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      refine sepWPp_congr_pre ?_
        (hnext _ curCap curPtr [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (encRawSegEnv_nil curBs.length 1))
      rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs 0x1a#8 hlt]
      simp only [M.stepEvents_nil]; ac_rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hfitDR : FitsEnv M lim st ( _ ) :=
      fitsEnv_doReserve_of_encRawSeg (x := DoReserveCall.mk v curCap curPtr curBs 1)
        (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega) hfit
    have hevsDR : EncRawSegEnv curBs.length 1
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) :=
      encRawSegEnv_doReserve _ (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega)
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      refine step_encChain_reserve1_placed A lim H hDR v curCap curPtr sp0
        ((blkPl_12).base + bv% (1904)) curBs st hcap_eq (by omega) hfitDR
        (s0 := s0)
        (F := ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_gt _hnew_eq
      have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
      have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one curBs 0x1a#8
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      let st1 := M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st
      apply sepWPp_of_sepWP_lscl_vm hclr (mid := (blkPl_12).base + bv% (340))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl2 hvm2 =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st1) hvm2 (by sep_focus) ?_⟩
        refine sepWPp_congr_pre ?_
          (hnext _ newCap p' (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1))
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hevsDR)
        rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc newCap p' curBs 0x1a#8 hnew_gt]
        dsimp only [st1]; ac_rfl

theorem step_encChain_seg3_len_varint_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (v a cap1 ptr1 sp0 : BitVec 64) (ck : ChainKey) (bs1 : List (BitVec 8))
    (st : M.σ)
    (hcur_lt : bs1.length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv bs1.length (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 340#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ck.index)
    (hP : P = (vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 416#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ck.index →
      EncRawSegEnv bs1.length
        (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length evs →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2
            (bs1 ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have ⟨_, hvar_le⟩ :=
    encodeVarint_length_bounds (BitVec.ofNat 64 (encChainKey ck).length)
  have hfitEV : FitsEnv M lim st
      (EncodeVarintEnv
        (EncodeVarintGhost.mk (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 bs1)) :=
    fitsEnv_encodeVarint_of_encRawSeg (Nat.le_refl _) (Nat.le_refl _) (by dsimp only; omega) hfit
  by_cases hidx : ck.index = 0#32
  · have hidx_beq : (ck.index == 0#32) = true := by simp [hidx]
    have hlen_eq := encChainKey_length_zero hidx
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      refine step_encChain_encodeVarint_placed A lim H hEV
        (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (416)) bs1
        st hcur_lt hfitEV (s0 := s0) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by ac_rfl) ?_
      intro sm cap2 ptr2 evs hpcm hrunm hclm hspm htrm hcsm hevs _hcap_le _hspare
      exact hnext sm cap2 ptr2 evs hpcm hrunm hclm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _) (Nat.le_refl _) (by dsimp only; omega) hevs)
  · have hidx_beq : (ck.index == 0#32) = false := beq_eq_false_iff_ne.mpr hidx
    have hlen_eq := encChainKey_length_nonzero hidx
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      refine step_encChain_encodeVarint_placed A lim H hEV
        (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (416)) bs1
        st hcur_lt hfitEV (s0 := s0) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by ac_rfl) ?_
      intro sm cap2 ptr2 evs hpcm hrunm hclm hspm htrm hcsm hevs _hcap_le _hspare
      exact hnext sm cap2 ptr2 evs hpcm hrunm hclm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _) (Nat.le_refl _) (by dsimp only; omega) hevs)

theorem step_encChain_seg3_index_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (v a cap2 ptr2 sp0 : BitVec 64) (ckIdx : BitVec 32) (bs2 : List (BitVec 8))
    (st : M.σ)
    (hcur_lt : bs2.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs2.length (uint32Field 1 ckIdx).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 416#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx)
    (hP : P = (vecU8At A.repAlloc v cap2 ptr2 bs2 ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 496#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      EncRawSegEnv bs2.length (uint32Field 1 ckIdx).length evs →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3 (bs2 ++ uint32Field 1 ckIdx) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  by_cases hidx : ckIdx = 0#32
  · have hidx_bne : (ckIdx != 0#32) = false := by simp [hidx]
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_12).base + bv% (496))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      have hu0 : bs2 ++ uint32Field 1 ckIdx = bs2 := by simp [hidx, uint32Field1_zero_eq]
      refine sepWPp_congr_pre ?_
        (hnext _ cap2 ptr2 []
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (encRawSegEnv_nil bs2.length (uint32Field 1 ckIdx).length))
      rw [hu0]; simp only [M.stepEvents_nil]; ac_rfl
  · have hidx_bne : (ckIdx != 0#32) = true := bne_iff_ne.mpr hidx
    have hu_eq : (bs2 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 ckIdx) =
        bs2 ++ uint32Field 1 ckIdx := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hidx]
    have hu_len : (uint32Field 1 ckIdx).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length := by
      rw [← uint32Field1_nonzero_eq hidx, List.length_append, List.length_singleton]
    have ⟨_, hvar_le⟩ := encodeVarint_length_bounds (BitVec.zeroExtend 64 ckIdx)
    have hfit12 : FitsEnv M lim st
        (EncRawSegEnv bs2.length (1 + (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length)) := by
      rwa [hu_len] at hfit
    have hfit1 : FitsEnv M lim st (EncRawSegEnv bs2.length 1) :=
      fitsEnv_encRawSeg_left hfit12
    have hcur_snoc_lt : (bs2 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A.repAlloc v cap2 ptr2 bs2]
    refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by ac_rfl) fun hle => ?_
    by_cases hlt : bs2.length < cap2.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs2 0x08#8
      have hfit2 : FitsEnv M lim st
          (EncRawSegEnv (bs2.length + 1) (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length) :=
        fitsEnv_encRawSeg_right hfit12 (encRawSegEnv_nil bs2.length 1)
      have hfitEV : FitsEnv M lim st
          (EncodeVarintEnv
            (EncodeVarintGhost.mk (BitVec.zeroExtend 64 ckIdx) v cap2 ptr2 (bs2 ++ [0x08#8]))) :=
        fitsEnv_encodeVarint_of_encRawSeg (Nat.le_refl _)
          (by dsimp only; rw [List.length_append, List.length_singleton])
          (by dsimp only; omega) hfit2
      rw [vecU8Buf_eq_open_one A.repAlloc cap2 ptr2 bs2 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 10)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
        refine step_encChain_encodeVarint_placed A lim H hEV
          (BitVec.zeroExtend 64 ckIdx) v cap2 ptr2 sp0 ((blkPl_12).base + bv% (496))
          (bs2 ++ [0x08#8]) st hcur_snoc_lt hfitEV (s0 := s0) (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc cap2 ptr2 bs2 0x08#8 hlt]; ac_rfl) ?_
        intro sm cap3 ptr3 evs hpcm hrunm hclm hspm htrm hcsm hevs _hcap_le _hspare
        have hevs_seg : EncRawSegEnv bs2.length (uint32Field 1 ckIdx).length evs := by
          rw [hu_len]
          simpa using encRawSegEnv_append (encRawSegEnv_nil bs2.length 1)
            (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
              (by dsimp only; rw [List.length_append, List.length_singleton])
              (by dsimp only; omega) hevs)
        rw [hu_eq]
        exact hnext sm cap3 ptr3 evs hpcm hrunm hclm hspm htrm
          (hcsm.1.trans (by simp only [arm64_norm, *]))
          (hcsm.2.1.trans (by simp only [arm64_norm, *]))
          (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
          hevs_seg
    · have hcap_eq : cap2.toNat = bs2.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      let evs1 := doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)
      let st1 := M.stepEvents evs1 st
      have hfitDR : FitsEnv M lim st _ :=
        fitsEnv_doReserve_of_encRawSeg (x := DoReserveCall.mk v cap2 ptr2 bs2 1)
          (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega) hfit1
      have hevs1 : EncRawSegEnv bs2.length 1 evs1 :=
        encRawSegEnv_doReserve _ (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega)
      have hfit2 : FitsEnv M lim st1
          (EncRawSegEnv (bs2.length + 1) (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length) :=
        fitsEnv_encRawSeg_right hfit12 hevs1
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 13)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
        refine step_encChain_reserve1_placed A lim H hDR v cap2 ptr2 sp0
          ((blkPl_12).base + bv% (1932)) bs2 st hcap_eq (by omega) hfitDR (s0 := s0) (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by ac_rfl) ?_
        intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_gt _hnew_eq
        have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
        have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
        have hx21r : sr.readReg64 .x21 = 32#64 := hcsr.2.2.1.trans (by simp only [arm64_norm, *])
        have hx22r : sr.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx :=
          hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
        have hlen1 := bv_len_add_one bs2 0x08#8
        have hfitEV : FitsEnv M lim st1
            (EncodeVarintEnv
              (EncodeVarintGhost.mk (BitVec.zeroExtend 64 ckIdx) v newCap p' (bs2 ++ [0x08#8]))) :=
          fitsEnv_encodeVarint_of_encRawSeg (Nat.le_refl _)
            (by dsimp only; rw [List.length_append, List.length_singleton])
            (by dsimp only; omega) hfit2
        rw [vecU8Buf_eq_open_one A.repAlloc newCap p' bs2 hnew_gt]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun y => ?_
        apply sepWPp_of_sepWP_lscl_vm hclr (mid := lsmpl.base 10)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hcl2 hvm2 =>
              SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st1) hvm2 (by sep_focus) ?_⟩
          refine step_encChain_encodeVarint_placed A lim H hEV
            (BitVec.zeroExtend 64 ckIdx) v newCap p' sp0 ((blkPl_12).base + bv% (496))
            (bs2 ++ [0x08#8]) st1 hcur_snoc_lt hfitEV (s0 := s0) (F := F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
            (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc newCap p' bs2 0x08#8 hnew_gt]; dsimp only [st1, evs1]; ac_rfl) ?_
          intro sm cap3 ptr3 evs2 hpcm hrunm hclm hspm htrm hcsm hevs2 _hcap_le _hspare
          have hevs_seg : EncRawSegEnv bs2.length (uint32Field 1 ckIdx).length (evs1 ++ evs2) := by
            rw [hu_len]
            exact encRawSegEnv_append hevs1
              (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
                (by dsimp only; rw [List.length_append, List.length_singleton])
                (by dsimp only; omega) hevs2)
          have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st :=
            (M.stepEvents_append evs1 evs2 st).symm
          rw [hu_eq, hst_eq]
          exact hnext sm cap3 ptr3 (evs1 ++ evs2) hpcm hrunm hclm hspm htrm
            (hcsm.1.trans (by simp only [arm64_norm, *]))
            (hcsm.2.1.trans (by simp only [arm64_norm, *]))
            (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
            hevs_seg

end LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyFieldBudgetAux
