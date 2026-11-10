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
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyFieldBudgetAux
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBody
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudgetAux
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
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
# Budget-threaded per-element `MessageKey` loop body (`+0x2a8..+0x29c`)

Budget-threaded `[LibsignalPlacement]` proofs for the per-element `MessageKey` loop body of
`encode::<Chain, Vec<u8>>` (block `12`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator)
open CryptoVerification (
  LibsignalPlacement lsmpl LibsignalCodeLoaded withLsCodeLoaded
  lsMemcpySym lsρ blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSessionRepr (MessageKeyGhost messageKeyAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncodeVarintGhost vecU8Buf sepWPp_extract_vecU8Buf_le
  cap_beq_len_false bv_len_add_one vecU8Buf_eq_open_one vecU8Buf_snoc_eq cap_eq_ofNat_len
  encodeVarint_length_bounds
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length hwVarintLen_w32_natShift_eq_encodeVarint_length
)
open CryptoVerification.E2E.Record (uint32Field lenField encMessageKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_118 lsProg_118)
open CryptoVerification.E2E.Record.Serialization (
  encChainSubStack vecU8At_eq_cells_buf
  bv_len_add_slice spare_ult_iff ule_of_ult_false ule_false_of_ult_true bv_len_beq_zero_false
  vecReadRest vecU8Buf_eq_open_bytes sepWPp_congr_pre
  MkLoopRegs lenField4_encMessageKey_eq lenField4_encMessageKey_len_parts
  mkUnusedAt messageKeyAt_eq_cells sepWPp_extract_messageKey_seed_ne_nil
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  doReserveEvents doReserveSpec framelessMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (msgKeyLenSpec)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget (
  sepWPp_of_sepWP_lscl_vm step_encChain_encodeVarint_placed step_encChain_reserve1_placed
  step_encChain_reserveSlice_placed step_encChain_memcpy_placed
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyFieldBudgetAux (
  encRawSegEnv_doReserve encRawSegEnv_of_encodeVarintEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
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

export MessageKeyLoopBodyBudgetAux (
  step_encChain_msgKeyLen_placed
  step_encChain_mk_tag_len_placed
  step_encChain_mk_counter_placed
)

theorem step_encChain_mk_seed_tag_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (v cur endPtr cap2 ptr2 seedPtr sp0 : BitVec 64) (bs2 seedBs : List (BitVec 8))
    (st : M.σ)
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hbs2_lt : bs2.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv bs2.length (1 + (encodeVarint (BitVec.ofNat 64 seedBs.length)).length)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 776#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A.repAlloc v cap2 ptr2 bs2 ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 1148#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length →
      sm.readReg64 .x22 = seedPtr →
      EncRawSegEnv bs2.length (1 + (encodeVarint (BitVec.ofNat 64 seedBs.length)).length) evs →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3
          ((bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 seedBs.length)) ∗
          ((cur + 16#64) ↦₆₄ 0#64) ∗
          ((cur + 40#64) ↦₆₄ 0#64) ∗
          ((cur + 64#64) ↦₆₄ 0#64) ∗
          ((cur + 80#64) ↦₆₄ seedPtr) ∗
          ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hseed_nz := bv_len_beq_zero_false hseed_pos hseed_lt
  have hbs2_snoc_lt : (bs2 ++ [0x2a#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hbs2_lt
  have ⟨_, hvar_le⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 seedBs.length)
  have hfit1 : FitsEnv M lim st (EncRawSegEnv bs2.length 1) :=
    fitsEnv_encRawSeg_left hfit
  rw [vecU8At_eq_cells_buf A.repAlloc v cap2 ptr2 bs2]
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : bs2.length < cap2.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs2 0x2a#8
    have hfit2 : FitsEnv M lim st
        (EncRawSegEnv (bs2.length + 1) (encodeVarint (BitVec.ofNat 64 seedBs.length)).length) :=
      fitsEnv_encRawSeg_right hfit (encRawSegEnv_nil bs2.length 1)
    have hfitEV : FitsEnv M lim st
        (EncodeVarintEnv
          (EncodeVarintGhost.mk (BitVec.ofNat 64 seedBs.length) v cap2 ptr2 (bs2 ++ [0x2a#8]))) :=
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
        (BitVec.ofNat 64 seedBs.length) v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1148))
        (bs2 ++ [0x2a#8]) st hbs2_snoc_lt hfitEV (s0 := s0)
        (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
          ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
          ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc cap2 ptr2 bs2 0x2a#8 hlt]; ac_rfl) ?_
      intro sm cap3 ptr3 evs hpcm hrunm hclm hspm htrm hcsm hevs _hcap_le _hspare
      have hevs_seg :
          EncRawSegEnv bs2.length (1 + (encodeVarint (BitVec.ofNat 64 seedBs.length)).length) evs := by
        simpa using encRawSegEnv_append (encRawSegEnv_nil bs2.length 1)
          (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
            (by dsimp only; rw [List.length_append, List.length_singleton])
            (by dsimp only; omega) hevs)
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
        hcsm.2.2.1.trans (by simp only [arm64_norm, *])
      have hx22m : sm.readReg64 .x22 = seedPtr :=
        hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
      refine sepWPp_congr_pre (by ac_rfl)
        (hnext sm cap3 ptr3 evs hpcm hrunm hclm hspm htrm hregsm hx21m hx22m hevs_seg)
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
        (EncRawSegEnv (bs2.length + 1) (encodeVarint (BitVec.ofNat 64 seedBs.length)).length) :=
      fitsEnv_encRawSeg_right hfit hevs1
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      refine step_encChain_reserve1_placed A lim H hDR v cap2 ptr2 sp0
        ((blkPl_12).base + bv% (1640)) bs2 st hcap_eq (by omega) hfitDR (s0 := s0)
        (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
          ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
          ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_gt _hnew_eq
      have hregsr : MkLoopRegs sr v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
      have hx19r : sr.readReg64 .x19 = v := hregsr.1
      have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
      have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
      have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
      have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
      have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
        hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hx22r : sr.readReg64 .x22 = seedPtr :=
        hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one bs2 0x2a#8
      have hfitEV : FitsEnv M lim st1
          (EncodeVarintEnv
            (EncodeVarintGhost.mk (BitVec.ofNat 64 seedBs.length) v newCap p' (bs2 ++ [0x2a#8]))) :=
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
          (BitVec.ofNat 64 seedBs.length) v newCap p' sp0 ((blkPl_12).base + bv% (1148))
          (bs2 ++ [0x2a#8]) st1 hbs2_snoc_lt hfitEV (s0 := s0)
          (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
            ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
            ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc newCap p' bs2 0x2a#8 hnew_gt]; dsimp only [st1, evs1]; ac_rfl) ?_
        intro sm cap3 ptr3 evs2 hpcm hrunm hclm hspm htrm hcsm hevs2 _hcap_le _hspare
        have hevs_seg :
            EncRawSegEnv bs2.length
              (1 + (encodeVarint (BitVec.ofNat 64 seedBs.length)).length) (evs1 ++ evs2) :=
          encRawSegEnv_append hevs1
            (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
              (by dsimp only; rw [List.length_append, List.length_singleton])
              (by dsimp only; omega) hevs2)
        have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st :=
          (M.stepEvents_append evs1 evs2 st).symm
        have hregsm : MkLoopRegs sm v cur endPtr :=
          MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
        have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
          hcsm.2.2.1.trans (by simp only [arm64_norm, *])
        have hx22m : sm.readReg64 .x22 = seedPtr :=
          hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
        refine sepWPp_congr_pre (by rw [hst_eq]; ac_rfl)
          (hnext sm cap3 ptr3 (evs1 ++ evs2) hpcm hrunm hclm hspm htrm hregsm hx21m hx22m hevs_seg)

theorem step_encChain_mk_seed_copy_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (v cur endPtr cap3 ptr3 seedCap seedPtr sp0 : BitVec 64)
    (bs3 seedBs : List (BitVec 8))
    (st : M.σ)
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hsum_lt : bs3.length + seedBs.length < 2 ^ 32)
    (hfit_env : FitsEnv M lim st (EncRawSegEnv bs3.length seedBs.length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 1148#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 seedBs.length)
    (hx22 : s.readReg64 .x22 = seedPtr)
    (hP : P = (vecU8At A.repAlloc v cap3 ptr3 bs3 ∗
      vecU8Buf A.repAlloc seedCap seedPtr seedBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 668#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      EncRawSegEnv bs3.length seedBs.length evs →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ seedBs) ∗
          vecU8Buf A.repAlloc seedCap seedPtr seedBs ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hbs3_lt : bs3.length < 2 ^ 32 := by omega
  have hlen_add := bv_len_add_slice bs3 seedBs
  rw [vecU8At_eq_cells_buf A.repAlloc v cap3 ptr3 bs3]
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A.repAlloc seedCap seedPtr seedBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := seedCap) (ptr := seedPtr) (bs := seedBs)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A.repAlloc cap3 ptr3 bs3 ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hseed_le => ?_
  by_cases hfit : bs3.length + seedBs.length ≤ cap3.toNat
  · have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = false :=
      (spare_ult_iff hle hbs3_lt hseed_lt).2.mpr hfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = true :=
      ule_of_ult_false hult
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsρ lsMemcpySym)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      rw [vecU8Buf_eq_open_bytes A.repAlloc seedCap seedPtr seedBs hseed_pos hseed_le]
      refine step_encChain_memcpy_placed A lim H hmc cap3 ptr3 seedPtr sp0
        ((blkPl_12).base + bv% (660)) bs3 seedBs st hseed_pos hfit hseed_lt (s0 := s0)
        (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
          vecReadRest A.repAlloc seedCap seedPtr seedBs ∗
          stackAt (sp0 - 96#64) encChainSubStack ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sc _hvm_mc hpcc hrunc hclc hspc htrc hcsc
      have hregsc : MkLoopRegs sc v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsc
      have hx19c : sc.readReg64 .x19 = v := hregsc.1
      have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
        hcsc.2.2.1.trans (by simp only [arm64_norm, *])
      have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
        hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
      apply sepWPp_of_sepWP_lscl_vm hclc (mid := (blkPl_12).base + bv% (668))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl2 hvm2 =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm2 (by sep_focus) ?_⟩
        refine sepWPp_congr_pre ?_
          (hnext _ cap3 ptr3 [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
             by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
             by simp only [arm64_norm, hregsc.2.2.2.2]⟩
            (encRawSegEnv_nil bs3.length seedBs.length))
        rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A.repAlloc seedCap seedPtr seedBs hseed_pos hseed_le]
        simp only [M.stepEvents_nil]; ac_rfl
  · have hnfit : cap3.toNat - bs3.length < seedBs.length := by omega
    have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = true :=
      (spare_ult_iff hle hbs3_lt hseed_lt).1.mpr hnfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = false :=
      ule_false_of_ult_true hult
    let evs1 := doReserveEvents (DoReserveCall.mk v cap3 ptr3 bs3 seedBs.length)
    let st1 := M.stepEvents evs1 st
    have hfitDR : FitsEnv M lim st _ :=
      fitsEnv_doReserve_of_encRawSeg (x := DoReserveCall.mk v cap3 ptr3 bs3 seedBs.length)
        hseed_pos (by dsimp only; omega) (by dsimp only; omega) (by omega) hfit_env
    have hevs1 : EncRawSegEnv bs3.length seedBs.length evs1 :=
      encRawSegEnv_doReserve _ hseed_pos (by dsimp only; omega) (by dsimp only; omega) (by omega)
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      refine step_encChain_reserveSlice_placed A lim H hDR v cap3 ptr3 sp0
        ((blkPl_12).base + bv% (1192)) bs3 seedBs.length st hle hnfit hbs3_lt hseed_lt hfitDR (s0 := s0)
        (F := vecU8Buf A.repAlloc seedCap seedPtr seedBs ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      rintro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_fit hult_false -
      have hule_true := ule_of_ult_false hult_false
      have hregsr : MkLoopRegs sr v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
      have hx19r : sr.readReg64 .x19 = v := hregsr.1
      have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
        hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hx22r : sr.readReg64 .x22 = seedPtr :=
        hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
      apply sepWPp_of_sepWP_lscl_vm hclr (mid := lsρ lsMemcpySym)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl2 hvm2 =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st1) hvm2 (by sep_focus) ?_⟩
        rw [vecU8Buf_eq_open_bytes A.repAlloc seedCap seedPtr seedBs hseed_pos hseed_le]
        refine step_encChain_memcpy_placed A lim H hmc newCap p' seedPtr sp0
          ((blkPl_12).base + bv% (660)) bs3 seedBs st1 hseed_pos hnew_fit hseed_lt (s0 := s0)
          (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
            vecReadRest A.repAlloc seedCap seedPtr seedBs ∗
            stackAt (sp0 - 96#64) encChainSubStack ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by dsimp only [st1, evs1]; ac_rfl) ?_
        intro sc _hvm_mc hpcc hrunc hclc hspc htrc hcsc
        have hregsc : MkLoopRegs sc v cur endPtr :=
          MkLoopRegs.of_calleeSaved
            ⟨by simp only [arm64_norm, hregsr.1], by simp only [arm64_norm, hregsr.2.1],
             by simp only [arm64_norm, hregsr.2.2.1], by simp only [arm64_norm, hregsr.2.2.2.1],
             by simp only [arm64_norm, hregsr.2.2.2.2]⟩ hcsc
        have hx19c : sc.readReg64 .x19 = v := hregsc.1
        have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
          hcsc.2.2.1.trans (by simp only [arm64_norm, *])
        have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
          hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
        apply sepWPp_of_sepWP_lscl_vm hclc (mid := (blkPl_12).base + bv% (668))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hcl3 hvm3 =>
              SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st1) hvm3 (by sep_focus) ?_⟩
          refine sepWPp_congr_pre ?_
            (hnext _ newCap p' evs1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl3
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
               by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
               by simp only [arm64_norm, hregsc.2.2.2.2]⟩
              hevs1)
          rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A.repAlloc seedCap seedPtr seedBs hseed_pos hseed_le]
          dsimp only [st1, evs1]; ac_rfl

theorem step_encChain_mk_elem_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hMK : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A.repAlloc)))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (curBs : List (BitVec 8))
    (st : M.σ)
    (hbound : curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv curBs.length (lenField 4 (encMessageKey gk.2)).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗
      messageKeyAt A.repAlloc gk cur ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 668#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      EncRawSegEnv curBs.length (lenField 4 (encMessageKey gk.2)).length evs →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v capOut ptrOut (curBs ++ lenField 4 (encMessageKey gk.2)) ∗
          messageKeyAt A.repAlloc gk cur ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPp_extract_messageKey_seed_ne_nil (A := A.repAlloc) (gk := gk) (cur := cur)
    (F := vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim st s ∗
      stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hseed => ?_
  have hseed_pos : 0 < gk.2.seed.length := List.length_pos_of_ne_nil hseed
  have hparts := lenField4_encMessageKey_len_parts gk.2 hseed
  let a1 := 1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length
  let a2 := (uint32Field 1 gk.2.counter).length
  let a3 := 1 + (encodeVarint (BitVec.ofNat 64 gk.2.seed.length)).length
  let a4 := gk.2.seed.length
  have hsum_parts : a1 + (a2 + (a3 + a4)) = (lenField 4 (encMessageKey gk.2)).length := by
    dsimp only [a1, a2, a3, a4]; omega
  have hfit0 : FitsEnv M lim st (EncRawSegEnv curBs.length (a1 + (a2 + (a3 + a4)))) := by
    rwa [hsum_parts]
  have hfit_s1 : FitsEnv M lim st (EncRawSegEnv curBs.length a1) :=
    fitsEnv_encRawSeg_left hfit0
  have hcur_lt : curBs.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_tag_len_placed A lim H hMK hEV hDR
    v cur endPtr curCap curPtr sp0 gk curBs st hcur_lt hfit_s1
    (F := F) hpc hrun hcl hsp halign htr hregs
    (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
  intro s1 cap1 ptr1 evs1 hpc1 hrun1 hcl1 hsp1 htr1 hregs1 hevs1
  set bs1 := (curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)
  let st1 := M.stepEvents evs1 st
  have hbs1_len : bs1.length = curBs.length + a1 := by
    simp only [bs1, a1, List.length_append, List.length_singleton]; omega
  have hfit1 : FitsEnv M lim st1 (EncRawSegEnv (curBs.length + a1) (a2 + (a3 + a4))) :=
    fitsEnv_encRawSeg_right hfit0 hevs1
  have hfit_s2 : FitsEnv M lim st1 (EncRawSegEnv bs1.length a2) := by
    rw [hbs1_len]; exact fitsEnv_encRawSeg_left hfit1
  have hbs1_lt : bs1.length + 1 < 2 ^ 32 := by
    rw [hbs1_len]; dsimp only [a1, a2, a3, a4] at hsum_parts ⊢; omega
  refine step_encChain_mk_counter_placed A lim H hEV hDR
    v cur endPtr cap1 ptr1 sp0 gk.2.counter bs1 st1 hbs1_lt hfit_s2
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      vecU8Buf A.repAlloc gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A.repAlloc gk cur ∗ F)
    hpc1 hrun1 hcl1 hsp1 halign htr1 hregs1
    (by rw [messageKeyAt_eq_cells A.repAlloc gk cur]; dsimp only [st1]; ac_rfl) ?_
  intro s2 cap2 ptr2 evs2 hpc2 hrun2 hcl2 hsp2 htr2 hregs2 hevs2
  set bs2 := bs1 ++ uint32Field 1 gk.2.counter
  let st2 := M.stepEvents evs2 st1
  have hevs2' : EncRawSegEnv (curBs.length + a1) a2 evs2 := by rwa [← hbs1_len]
  have hfit2 : FitsEnv M lim st2 (EncRawSegEnv ((curBs.length + a1) + a2) (a3 + a4)) :=
    fitsEnv_encRawSeg_right hfit1 hevs2'
  have hbs2_len : bs2.length = (curBs.length + a1) + a2 := by
    simp [bs2, hbs1_len, a2]
  have hfit_s3 : FitsEnv M lim st2 (EncRawSegEnv bs2.length a3) := by
    rw [hbs2_len]; exact fitsEnv_encRawSeg_left hfit2
  have hbs2_lt : bs2.length + 1 < 2 ^ 32 := by
    rw [hbs2_len]; dsimp only [a1, a2, a3, a4] at hsum_parts ⊢; omega
  have hseed_lt : gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_tag_placed A lim H hEV hDR
    v cur endPtr cap2 ptr2 gk.1.seed.ptr sp0 bs2 gk.2.seed st2 hseed_pos hseed_lt hbs2_lt hfit_s3
    (F := ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      vecU8Buf A.repAlloc gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A.repAlloc gk cur ∗ F)
    hpc2 hrun2 hcl2 hsp2 halign htr2 hregs2 (by dsimp only [st2]; ac_rfl) ?_
  intro s3 cap3 ptr3 evs3 hpc3 hrun3 hcl3 hsp3 htr3 hregs3 hx21_3 hx22_3 hevs3
  set bs3 := (bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 gk.2.seed.length)
  let st3 := M.stepEvents evs3 st2
  have hevs3' : EncRawSegEnv ((curBs.length + a1) + a2) a3 evs3 := by rwa [← hbs2_len]
  have hfit3 : FitsEnv M lim st3 (EncRawSegEnv (((curBs.length + a1) + a2) + a3) a4) :=
    fitsEnv_encRawSeg_right hfit2 hevs3'
  have hbs3_len : bs3.length = ((curBs.length + a1) + a2) + a3 := by
    simp only [bs3, hbs2_len, a3, List.length_append, List.length_singleton]; omega
  have hfit_s4 : FitsEnv M lim st3 (EncRawSegEnv bs3.length a4) := by
    rwa [hbs3_len]
  have hsum_lt : bs3.length + gk.2.seed.length < 2 ^ 32 := by
    rw [hbs3_len]; dsimp only [a1, a2, a3, a4] at hsum_parts ⊢; omega
  refine step_encChain_mk_seed_copy_placed A lim H hDR hmc
    v cur endPtr cap3 ptr3 gk.1.seed.cap gk.1.seed.ptr sp0 bs3 gk.2.seed st3
    hseed_pos hseed_lt hsum_lt hfit_s4
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      mkUnusedAt A.repAlloc gk cur ∗ F)
    hpc3 hrun3 hcl3 hsp3 halign htr3 hregs3 hx21_3 hx22_3 (by dsimp only [st3]; ac_rfl) ?_
  intro s4 cap4 ptr4 evs4 hpc4 hrun4 hcl4 hsp4 htr4 hregs4 hevs4
  have hevs4' : EncRawSegEnv (((curBs.length + a1) + a2) + a3) a4 evs4 := by
    rwa [← hbs3_len]
  let evs_tot := evs1 ++ (evs2 ++ (evs3 ++ evs4))
  have hevs_tot :
      EncRawSegEnv curBs.length (lenField 4 (encMessageKey gk.2)).length evs_tot := by
    rw [← hsum_parts]
    have h34 : EncRawSegEnv ((curBs.length + a1) + a2) (a3 + a4) (evs3 ++ evs4) :=
      encRawSegEnv_append hevs3' hevs4'
    have h234 : EncRawSegEnv (curBs.length + a1) (a2 + (a3 + a4)) (evs2 ++ (evs3 ++ evs4)) :=
      encRawSegEnv_append hevs2' h34
    exact encRawSegEnv_append hevs1 h234
  have hst_tot : M.stepEvents evs4 st3 = M.stepEvents evs_tot st := by
    simp only [st3, st2, st1, evs_tot, M.stepEvents_append]
  have hbs4_eq : bs3 ++ gk.2.seed = curBs ++ lenField 4 (encMessageKey gk.2) := by
    rw [← lenField4_encMessageKey_eq gk.2 hseed]
    simp [bs3, bs2, bs1, List.append_assoc]
  refine sepWPp_congr_pre ?_
    (hnext s4 cap4 ptr4 evs_tot hpc4 hrun4 hcl4 hsp4 htr4 hregs4 hevs_tot)
  rw [hbs4_eq, hst_tot, messageKeyAt_eq_cells A.repAlloc gk cur]
  ac_rfl

end LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudget
