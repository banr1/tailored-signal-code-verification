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
# Budget-threaded `MessageKey` tag, length, and `index` steps

Budget-threaded `[LibsignalPlacement]` stepping lemmas for the `MessageKey::encoded_len` call,
outer tag/length varint, and `index` field inside the `message_keys` loop of
`encode::<Chain, Vec<u8>>` (block `12`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator)
open CryptoVerification (
  LibsignalPlacement lsmpl LibsignalCodeLoaded withLsCodeLoaded ls_subroutine_ok_of_block
  blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
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
open CryptoVerification.E2E.Record (uint32Field encMessageKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_118 lsProg_118)
open CryptoVerification.E2E.Record.Serialization (
  MsgKeyLenGhost msgKeyLenStack encChainSubStack sp_sub_96_aligned stackAt_sub_to_msgKeyLen
  trVRegs_of_call vecU8At_eq_cells_buf
  sepWPp_congr_pre uint32Field1_zero_eq uint32Field1_nonzero_eq MkLoopRegs
)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  doReserveEvents doReserveSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (msgKeyLenSpec)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget (
  sepWPp_of_sepWP_lscl_vm sepWPp_call_lscl_noPanic
  step_encChain_encodeVarint_placed step_encChain_reserve1_placed
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

theorem step_encChain_msgKeyLen_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hMK : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (cur sp0 ret_pc : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 118)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = cur)
    (hP : P = (messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encMessageKey gk.2).length →
      SepWPp (lsProg_12 H) ret sm
        ((messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  have hMK' : subroutine_ok (lsProg_12 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hMK
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPp_call_lscl_noPanic (x := MsgKeyLenGhost.mk cur gk)
    (F := memRegion (sp0 - 96#64 - 8544#64) 8528 ∗ F)
    hMK' hpc hrun hsp_aligned hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_msgKeyLen (sp0 - 96#64)] at hm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    convert hm using 1; ac_rfl
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm, hvmm⟩ => ?_
    refine sepWPp_congr_pre ?_
      (hnext sm hvmm hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m)
    rw [stackAt_sub_to_msgKeyLen (sp0 - 96#64)]
    ac_rfl

theorem step_encChain_mk_tag_len_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hMK : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A.repAlloc)))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (v cur endPtr curCap curPtr sp0 : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    (curBs : List (BitVec 8))
    (st : M.σ)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv curBs.length
        (1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      messageKeyAt A.repAlloc gk cur ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 728#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      EncRawSegEnv curBs.length
        (1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length) evs →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap1 ptr1
          ((curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)) ∗
          messageKeyAt A.repAlloc gk cur ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hcur_snoc_lt : (curBs ++ [0x22#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  have ⟨_, hvar_le⟩ :=
    encodeVarint_length_bounds (BitVec.ofNat 64 (encMessageKey gk.2).length)
  have hfit1 : FitsEnv M lim st (EncRawSegEnv curBs.length 1) :=
    fitsEnv_encRawSeg_left hfit
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      messageKeyAt A.repAlloc gk cur ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x22#8
    have hfit2 : FitsEnv M lim st
        (EncRawSegEnv (curBs.length + 1)
          (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length) :=
      fitsEnv_encRawSeg_right hfit (encRawSegEnv_nil curBs.length 1)
    have hfitEV : FitsEnv M lim st
        (EncodeVarintEnv
          (EncodeVarintGhost.mk (BitVec.ofNat 64 (encMessageKey gk.2).length)
            v curCap curPtr (curBs ++ [0x22#8]))) :=
      fitsEnv_encodeVarint_of_encRawSeg (Nat.le_refl _)
        (by dsimp only; rw [List.length_append, List.length_singleton])
        (by dsimp only; omega) hfit2
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 118)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl0 hvm0 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine step_encChain_msgKeyLen_placed A.repAlloc H hMK cur sp0 ((blkPl_12).base + bv% (720)) gk
        (s0 := s0)
        (F := vecU8At A.repAlloc v curCap curPtr (curBs ++ [0x22#8]) ∗ A.pool lim st _ ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs 0x22#8 hlt]; ac_rfl) ?_
      intro s1 hvm_mk hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hx0_1
      refine SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm_mk (by sep_focus) ?_
      have hregs1 : MkLoopRegs s1 v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
      have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
      apply sepWPp_of_sepWP_lscl_vm hcl1 (mid := lsmpl.base 10)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl2 hvm2 =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm2 (by sep_focus) ?_⟩
        refine step_encChain_encodeVarint_placed A lim H hEV
          (BitVec.ofNat 64 (encMessageKey gk.2).length) v curCap curPtr sp0
          ((blkPl_12).base + bv% (728)) (curBs ++ [0x22#8]) st hcur_snoc_lt hfitEV
          (s0 := s0) (F := messageKeyAt A.repAlloc gk cur ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by ac_rfl) ?_
        intro sm cap1 ptr1 evs hpcm hrunm hclm hspm htrm hcsm hevs _hcap_le _hspare
        have hevs_seg :
            EncRawSegEnv curBs.length
              (1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length) evs := by
          simpa using encRawSegEnv_append (encRawSegEnv_nil curBs.length 1)
            (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
              (by dsimp only; rw [List.length_append, List.length_singleton])
              (by dsimp only; omega) hevs)
        have hregs2 : MkLoopRegs sm v cur endPtr :=
          MkLoopRegs.of_calleeSaved
            ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
             by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
             by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
        refine sepWPp_congr_pre (by ac_rfl)
          (hnext sm cap1 ptr1 evs hpcm hrunm hclm hspm htrm hregs2 hevs_seg)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    let evs1 := doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)
    let st1 := M.stepEvents evs1 st
    have hfitDR : FitsEnv M lim st _ :=
      fitsEnv_doReserve_of_encRawSeg (x := DoReserveCall.mk v curCap curPtr curBs 1)
        (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega) hfit1
    have hevs1 : EncRawSegEnv curBs.length 1 evs1 :=
      encRawSegEnv_doReserve _ (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega)
    have hfit2 : FitsEnv M lim st1
        (EncRawSegEnv (curBs.length + 1)
          (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length) :=
      fitsEnv_encRawSeg_right hfit hevs1
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl0 hvm0 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine step_encChain_reserve1_placed A lim H hDR v curCap curPtr sp0
        ((blkPl_12).base + bv% (1264)) curBs st hcap_eq (by omega) hfitDR
        (s0 := s0) (F := messageKeyAt A.repAlloc gk cur ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0
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
      have hlen1 := bv_len_add_one curBs 0x22#8
      have hfitEV : FitsEnv M lim st1
          (EncodeVarintEnv
            (EncodeVarintGhost.mk (BitVec.ofNat 64 (encMessageKey gk.2).length)
              v newCap p' (curBs ++ [0x22#8]))) :=
        fitsEnv_encodeVarint_of_encRawSeg (Nat.le_refl _)
          (by dsimp only; rw [List.length_append, List.length_singleton])
          (by dsimp only; omega) hfit2
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply sepWPp_of_sepWP_lscl_vm hclr (mid := lsmpl.base 118)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl0' hvm0' =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st1) hvm0' (by sep_focus) ?_⟩
        refine step_encChain_msgKeyLen_placed A.repAlloc H hMK cur sp0 ((blkPl_12).base + bv% (720)) gk
          (s0 := s0)
          (F := vecU8At A.repAlloc v newCap p' (curBs ++ [0x22#8]) ∗ A.pool lim st1 _ ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0'
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc newCap p' curBs 0x22#8 hnew_gt]; dsimp only [st1, evs1]; ac_rfl) ?_
        intro s1 hvm_mk hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hx0_1
        refine SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st1) hvm_mk (by sep_focus) ?_
        have hregs1 : MkLoopRegs s1 v cur endPtr :=
          MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
        have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
        apply sepWPp_of_sepWP_lscl_vm hcl1 (mid := lsmpl.base 10)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hcl2 hvm2 =>
              SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st1) hvm2 (by sep_focus) ?_⟩
          refine step_encChain_encodeVarint_placed A lim H hEV
            (BitVec.ofNat 64 (encMessageKey gk.2).length) v newCap p' sp0
            ((blkPl_12).base + bv% (728)) (curBs ++ [0x22#8]) st1 hcur_snoc_lt hfitEV
            (s0 := s0) (F := messageKeyAt A.repAlloc gk cur ∗ F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
            (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by ac_rfl) ?_
          intro sm cap1 ptr1 evs2 hpcm hrunm hclm hspm htrm hcsm hevs2 _hcap_le _hspare
          have hevs_seg :
              EncRawSegEnv curBs.length
                (1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length)
                (evs1 ++ evs2) :=
            encRawSegEnv_append hevs1
              (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
                (by dsimp only; rw [List.length_append, List.length_singleton])
                (by dsimp only; omega) hevs2)
          have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st :=
            (M.stepEvents_append evs1 evs2 st).symm
          have hregs2 : MkLoopRegs sm v cur endPtr :=
            MkLoopRegs.of_calleeSaved
              ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
               by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
               by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
          refine sepWPp_congr_pre (by rw [hst_eq]; ac_rfl)
            (hnext sm cap1 ptr1 (evs1 ++ evs2) hpcm hrunm hclm hspm htrm hregs2 hevs_seg)

theorem step_encChain_mk_counter_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (v cur endPtr cap1 ptr1 sp0 : BitVec 64) (cnt : BitVec 32) (bs1 : List (BitVec 8))
    (st : M.σ)
    (hcur_lt : bs1.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs1.length (uint32Field 1 cnt).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 728#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      ((cur + 96#64) ↦₃₂ cnt) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 776#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      EncRawSegEnv bs1.length (uint32Field 1 cnt).length evs →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ uint32Field 1 cnt) ∗
          ((cur + 96#64) ↦₃₂ cnt) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  by_cases hcnt : cnt = 0#32
  · have hcnt_beq : (cnt == 0#32) = true := by simp [hcnt]
    apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_12).base + bv% (776))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
          SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
      have hu0 : bs1 ++ uint32Field 1 cnt = bs1 := by simp [hcnt, uint32Field1_zero_eq]
      refine sepWPp_congr_pre ?_
        (hnext _ cap1 ptr1 []
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *], by simp only [arm64_norm, *],
           by simp only [arm64_norm, *]⟩
          (encRawSegEnv_nil bs1.length (uint32Field 1 cnt).length))
      rw [hu0]; simp only [M.stepEvents_nil]; ac_rfl
  · have hcnt_beq : (cnt == 0#32) = false := beq_eq_false_iff_ne.mpr hcnt
    have hu_eq : (bs1 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 cnt) =
        bs1 ++ uint32Field 1 cnt := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hcnt]
    have hu_len : (uint32Field 1 cnt).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 cnt)).length := by
      rw [← uint32Field1_nonzero_eq hcnt, List.length_append, List.length_singleton]
    have ⟨_, hvar_le⟩ := encodeVarint_length_bounds (BitVec.zeroExtend 64 cnt)
    have hfit12 : FitsEnv M lim st
        (EncRawSegEnv bs1.length (1 + (encodeVarint (BitVec.zeroExtend 64 cnt)).length)) := by
      rwa [hu_len] at hfit
    have hfit1 : FitsEnv M lim st (EncRawSegEnv bs1.length 1) :=
      fitsEnv_encRawSeg_left hfit12
    have hcur_snoc_lt : (bs1 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A.repAlloc v cap1 ptr1 bs1]
    refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := (v ↦₆₄ cap1) ∗ ((v + 8#64) ↦₆₄ ptr1) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        ((cur + 96#64) ↦₃₂ cnt) ∗
        A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by ac_rfl) fun hle => ?_
    by_cases hlt : bs1.length < cap1.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs1 0x08#8
      have hfit2 : FitsEnv M lim st
          (EncRawSegEnv (bs1.length + 1) (encodeVarint (BitVec.zeroExtend 64 cnt)).length) :=
        fitsEnv_encRawSeg_right hfit12 (encRawSegEnv_nil bs1.length 1)
      have hfitEV : FitsEnv M lim st
          (EncodeVarintEnv
            (EncodeVarintGhost.mk (BitVec.zeroExtend 64 cnt) v cap1 ptr1 (bs1 ++ [0x08#8]))) :=
        fitsEnv_encodeVarint_of_encRawSeg (Nat.le_refl _)
          (by dsimp only; rw [List.length_append, List.length_singleton])
          (by dsimp only; omega) hfit2
      rw [vecU8Buf_eq_open_one A.repAlloc cap1 ptr1 bs1 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 10)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
        refine step_encChain_encodeVarint_placed A lim H hEV
          (BitVec.zeroExtend 64 cnt) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (776))
          (bs1 ++ [0x08#8]) st hcur_snoc_lt hfitEV
          (s0 := s0) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc cap1 ptr1 bs1 0x08#8 hlt]; ac_rfl) ?_
        intro sm cap2 ptr2 evs hpcm hrunm hclm hspm htrm hcsm hevs _hcap_le _hspare
        have hevs_seg : EncRawSegEnv bs1.length (uint32Field 1 cnt).length evs := by
          rw [hu_len]
          simpa using encRawSegEnv_append (encRawSegEnv_nil bs1.length 1)
            (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
              (by dsimp only; rw [List.length_append, List.length_singleton])
              (by dsimp only; omega) hevs)
        have hregsm : MkLoopRegs sm v cur endPtr :=
          MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
        rw [hu_eq]
        refine sepWPp_congr_pre (by ac_rfl)
          (hnext sm cap2 ptr2 evs hpcm hrunm hclm hspm htrm hregsm hevs_seg)
    · have hcap_eq : cap1.toNat = bs1.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      let evs1 := doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)
      let st1 := M.stepEvents evs1 st
      have hfitDR : FitsEnv M lim st _ :=
        fitsEnv_doReserve_of_encRawSeg (x := DoReserveCall.mk v cap1 ptr1 bs1 1)
          (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega) hfit1
      have hevs1 : EncRawSegEnv bs1.length 1 evs1 :=
        encRawSegEnv_doReserve _ (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega)
      have hfit2 : FitsEnv M lim st1
          (EncRawSegEnv (bs1.length + 1) (encodeVarint (BitVec.zeroExtend 64 cnt)).length) :=
        fitsEnv_encRawSeg_right hfit12 hevs1
      apply sepWPp_of_sepWP_lscl_vm hcl (mid := lsmpl.base 13)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 =>
            SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvm1 (by sep_focus) ?_⟩
        refine step_encChain_reserve1_placed A lim H hDR v cap1 ptr1 sp0
          ((blkPl_12).base + bv% (1296)) bs1 st hcap_eq (by omega) hfitDR
          (s0 := s0) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
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
        have hx21r : sr.readReg64 .x21 = BitVec.zeroExtend 64 cnt :=
          hcsr.2.2.1.trans (by simp only [arm64_norm, *])
        have hlen1 := bv_len_add_one bs1 0x08#8
        have hfitEV : FitsEnv M lim st1
            (EncodeVarintEnv
              (EncodeVarintGhost.mk (BitVec.zeroExtend 64 cnt) v newCap p' (bs1 ++ [0x08#8]))) :=
          fitsEnv_encodeVarint_of_encRawSeg (Nat.le_refl _)
            (by dsimp only; rw [List.length_append, List.length_singleton])
            (by dsimp only; omega) hfit2
        rw [vecU8Buf_eq_open_one A.repAlloc newCap p' bs1 hnew_gt]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun y => ?_
        apply sepWPp_of_sepWP_lscl_vm hclr (mid := lsmpl.base 10)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hcl2 hvm2 =>
              SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st1) hvm2 (by sep_focus) ?_⟩
          refine step_encChain_encodeVarint_placed A lim H hEV
            (BitVec.zeroExtend 64 cnt) v newCap p' sp0 ((blkPl_12).base + bv% (776))
            (bs1 ++ [0x08#8]) st1 hcur_snoc_lt hfitEV
            (s0 := s0) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
            (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [vecU8At_eq_cells_buf, ← vecU8Buf_snoc_eq A.repAlloc newCap p' bs1 0x08#8 hnew_gt]; dsimp only [st1, evs1]; ac_rfl) ?_
          intro sm cap2 ptr2 evs2 hpcm hrunm hclm hspm htrm hcsm hevs2 _hcap_le _hspare
          have hevs_seg : EncRawSegEnv bs1.length (uint32Field 1 cnt).length (evs1 ++ evs2) := by
            rw [hu_len]
            exact encRawSegEnv_append hevs1
              (encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
                (by dsimp only; rw [List.length_append, List.length_singleton])
                (by dsimp only; omega) hevs2)
          have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st :=
            (M.stepEvents_append evs1 evs2 st).symm
          have hregsm : MkLoopRegs sm v cur endPtr :=
            MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
              by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
          rw [hu_eq]
          refine sepWPp_congr_pre (by rw [hst_eq]; ac_rfl)
            (hnext sm cap2 ptr2 (evs1 ++ evs2) hpcm hrunm hclm hspm htrm hregsm hevs_seg)

end LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudgetAux
