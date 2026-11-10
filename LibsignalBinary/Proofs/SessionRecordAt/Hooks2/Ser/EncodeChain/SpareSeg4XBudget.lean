/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopBodyXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareVarintXBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoop
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBody
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

/-!
# Spare-Capacity `encode::<Chain, Vec<u8>>` Segment 4 and Epilogue (`+600` → `ret`)

Proves zero-allocation (`VmPreserved`-preserving) relocatable step lemmas over an arbitrary
`A : RustAlloc` for the `message_keys` loop (`+600 → +1648`) and epilogue (`+1648 → ret`) of
Block `12` (`encode::<Chain, Vec<u8>>`) when the output `Vec<u8>` already has sufficient capacity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareSeg4XBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator ReceiverChain maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded withLsCl
  lsρ lsMemcpySym
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open CryptoVerification.RustHeap (RustAlloc vecBuf vecU8At arrayAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost messageKeyAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf encodeVarint_length_bounds
  vecU8Buf_eq_open_one vecU8Buf_snoc_eq
  cap_beq_len_false bv_len_add_one
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length hwVarintLen_w32_natShift_eq_encodeVarint_length
)
open CryptoVerification.E2E.Record (uint32Field lenField encMessageKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_118 lsProg_118)
open CryptoVerification.E2E.Record.Serialization (
  EncodeChainGhost encChainMem protoChainAt
  stackAt_encodeChainStackX_split sp_sub_96_aligned
  encChainSubStackX encChainSavedRegs
  vecU8At_eq_cells_buf vecU8Buf_eq_open_bytes vecReadRest
  bv_len_add_slice spare_ult_iff ule_of_ult_false bv_len_beq_zero_false
  uint32Field1_zero_eq uint32Field1_nonzero_eq
  MkLoopRegs lenField4_encMessageKey_eq lenField4_encMessageKey_len_parts
  mkUnusedAt messageKeyAt_eq_cells
  mk_endPtr_step mk_endPtr_ne_of_pos bv_nat_beq_zero_false bv_madd_104
  zip_length_eq_right zip_map_snd_eq_encChain
  chainMkUnusedAt chainAt_eq_mk_cells vecMkRest vecBuf_mk_eq_open
  sepWPpLsCl_extract_chain_mk_bounds_x sepWPpLsCl_extract_vecBuf_mk_le_x
)
open Proofs.libsignal.Hooks2 (
  SepWPpLsCl sepWPpLsCl_extract_vecU8Buf_bounds
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (msgKeyLenSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (encodeChainStackX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.MessageKeyLoopBodyXBudget (
  sepWPpLsCl_extract_messageKey_seed_ne_nil_x
  step_encChain_msgKeyLen_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareVarintXBudget (
  step_encChain_encodeVarint_prealloc_x
  step_encChain_memcpy_prealloc_x
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

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

/-! ## Pure bounds helpers -/

private theorem mk_len_tl_lt {α : Type} (x : α) (xs : List α)
    (h : (x :: xs).length * 104 < 2 ^ 32) :
    xs.length * 104 < 2 ^ 32 := by
  simp only [List.length_cons] at h
  omega

private theorem mk_bound_head (curBs : List (BitVec 8))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32) :
    curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hbound
  omega

private theorem mk_bound_tail (curBs : List (BitVec 8))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32) :
    (curBs ++ lenField 4 (encMessageKey gk.2)).length +
      ((tl.map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hbound ⊢
  omega

private theorem mk_spare_head (curBs : List (BitVec 8)) (capNat : Nat)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hspare : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length ≤ capNat) :
    curBs.length + (lenField 4 (encMessageKey gk.2)).length ≤ capNat := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hspare
  omega

private theorem mk_spare_tail (curBs : List (BitVec 8)) (capNat : Nat)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hspare : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length ≤ capNat) :
    (curBs ++ lenField 4 (encMessageKey gk.2)).length +
      ((tl.map (fun p => lenField 4 (encMessageKey p.2))).flatten).length ≤ capNat := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hspare ⊢
  omega

/-! ## Per-element `MessageKey` body (`+680 → +668`) -/

theorem step_encChain_mk_tag_len_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (v cur endPtr curCap curPtr sp0 : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    (curBs : List (BitVec 8))
    (hspare : curBs.length +
      (1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length) ≤ curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 728#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr
          ((curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)) ∗
          messageKeyAt A gk cur ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 (encMessageKey gk.2).length)
  have hlt : curBs.length < curCap.toNat := by omega
  have hspare_ev : (curBs ++ [0x22#8]).length +
      (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length ≤ curCap.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs 0x22#8
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun y => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 118)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x22#8 hlt]
  refine step_encChain_msgKeyLen_placed_x A H hmk cur sp0
    ((blkPl_12).base + bv% (720)) gk
    (s0 := s0)
    (F := vecU8At A v curCap curPtr (curBs ++ [0x22#8]) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
  intro s1 hvm_mk hpc1 hrun1 hsp1 htr1 hcs1 hx0_1
  have hregs1 : MkLoopRegs s1 v cur endPtr :=
    MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
  have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
  refine step_encChain_encodeVarint_prealloc_x A H
    (BitVec.ofNat 64 (encMessageKey gk.2).length) v curCap curPtr sp0 ((blkPl_12).base + bv% (728))
    (curBs ++ [0x22#8]) hspare_ev
    (s0 := s0) (F := messageKeyAt A gk cur ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by sep_ac_rfl) ?_
  intro sm hvm3 hpcm hrunm hspm htrm hcsm
  have hregs2 : MkLoopRegs sm v cur endPtr :=
    MkLoopRegs.of_calleeSaved
      ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
       by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
       by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
  refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
    (hnext sm (hvm1.trans (hvm_mk.trans (hvm2.trans hvm3))) hpcm hrunm hspm htrm hregs2)

theorem step_encChain_mk_counter_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (v cur endPtr cap1 ptr1 sp0 : BitVec 64) (cnt : BitVec 32) (bs1 : List (BitVec 8))
    (hspare : bs1.length + (uint32Field 1 cnt).length ≤ cap1.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      ((cur + 96#64) ↦₃₂ cnt) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 776#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap1 ptr1 (bs1 ++ uint32Field 1 cnt) ∗
          ((cur + 96#64) ↦₃₂ cnt) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  by_cases hcnt : cnt = 0#32
  · have hcnt_beq : (cnt == 0#32) = true := by simp only [hcnt, beq_self_eq_true]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (776))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hu0 : bs1 ++ uint32Field 1 cnt = bs1 := by
      simp only [hcnt, uint32Field1_zero_eq, List.append_nil]
    rw [← hu0]
    exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *]⟩
  · have hcnt_beq : (cnt == 0#32) = false := beq_eq_false_iff_ne.mpr hcnt
    have hu_eq : (bs1 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 cnt) =
        bs1 ++ uint32Field 1 cnt := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hcnt]
    have hu_len : (uint32Field 1 cnt).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 cnt)).length := by
      rw [← uint32Field1_nonzero_eq hcnt, List.length_append, List.length_singleton]
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.zeroExtend 64 cnt)
    have hlt : bs1.length < cap1.toNat := by omega
    have hspare_ev : (bs1 ++ [0x08#8]).length +
        (encodeVarint (BitVec.zeroExtend 64 cnt)).length ≤ cap1.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs1 0x08#8
    rw [vecU8At_eq_cells_buf A v cap1 ptr1 bs1, vecU8Buf_eq_open_one A cap1 ptr1 bs1 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [vecU8Buf_snoc_eq A cap1 ptr1 bs1 0x08#8 hlt]
    refine step_encChain_encodeVarint_prealloc_x A H
      (BitVec.zeroExtend 64 cnt) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (776))
      (bs1 ++ [0x08#8]) hspare_ev
      (s0 := s0) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
    intro sm hvm2 hpcm hrunm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    rw [hu_eq]
    refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
      (hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm hregsm)

theorem step_encChain_mk_seed_tag_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (v cur endPtr cap2 ptr2 seedPtr sp0 : BitVec 64) (bs2 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hspare : bs2.length + (1 + (encodeVarint (BitVec.ofNat 64 seedBs.length)).length) ≤ cap2.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 776#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 1148#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length →
      sm.readReg64 .x22 = seedPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2
          ((bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 seedBs.length)) ∗
          ((cur + 16#64) ↦₆₄ 0#64) ∗
          ((cur + 40#64) ↦₆₄ 0#64) ∗
          ((cur + 64#64) ↦₆₄ 0#64) ∗
          ((cur + 80#64) ↦₆₄ seedPtr) ∗
          ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hseed_nz := bv_len_beq_zero_false hseed_pos hseed_lt
  have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 seedBs.length)
  have hlt : bs2.length < cap2.toNat := by omega
  have hspare_ev : (bs2 ++ [0x2a#8]).length +
      (encodeVarint (BitVec.ofNat 64 seedBs.length)).length ≤ cap2.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one bs2 0x2a#8
  rw [vecU8At_eq_cells_buf A v cap2 ptr2 bs2, vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun y => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x2a#8 hlt]
  refine step_encChain_encodeVarint_prealloc_x A H
    (BitVec.ofNat 64 seedBs.length) v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1148))
    (bs2 ++ [0x2a#8]) hspare_ev
    (s0 := s0)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
  intro sm hvm2 hpcm hrunm hspm htrm hcsm
  have hregsm : MkLoopRegs sm v cur endPtr :=
    MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
  have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
    hcsm.2.2.1.trans (by simp only [arm64_norm, *])
  have hx22m : sm.readReg64 .x22 = seedPtr :=
    hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
  refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
    (hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm hregsm hx21m hx22m)

theorem step_encChain_mk_seed_copy_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (v cur endPtr cap3 ptr3 seedCap seedPtr sp0 : BitVec 64)
    (bs3 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hsum_lt : bs3.length + seedBs.length < 2 ^ 32)
    (hspare : bs3.length + seedBs.length ≤ cap3.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 1148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 seedBs.length)
    (hx22 : s.readReg64 .x22 = seedPtr)
    (hP : P = (vecU8At A v cap3 ptr3 bs3 ∗
      vecU8Buf A seedCap seedPtr seedBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 668#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap3 ptr3 (bs3 ++ seedBs) ∗
          vecU8Buf A seedCap seedPtr seedBs ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hbs3_lt : bs3.length < 2 ^ 32 := by omega
  have hlen_add := bv_len_add_slice bs3 seedBs
  rw [vecU8At_eq_cells_buf A v cap3 ptr3 bs3]
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A seedCap seedPtr seedBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hle _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := seedCap) (ptr := seedPtr)
    (bs := seedBs)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A cap3 ptr3 bs3 ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hseed_le _ _ => ?_
  have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = false :=
    (spare_ult_iff hle hbs3_lt hseed_lt).2.mpr hspare
  have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = true :=
    ule_of_ult_false hult
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
  refine step_encChain_memcpy_prealloc_x A H hmc cap3 ptr3 seedPtr sp0
    ((blkPl_12).base + bv% (660)) bs3 seedBs hseed_pos hspare hseed_lt
    (s0 := s0)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecReadRest A seedCap seedPtr seedBs ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
  intro sc hvm2 hpcc hrunc hspc htrc hcsc
  have hregsc : MkLoopRegs sc v cur endPtr :=
    MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsc
  have hx19c : sc.readReg64 .x19 = v := hregsc.1
  have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
    hcsc.2.2.1.trans (by simp only [arm64_norm, *])
  have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
    hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (668))
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm3 => ?_⟩
  refine SepWPpLsCl.congr_pre ?_
    (hnext _ (hvm1.trans (hvm2.trans hvm3))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
       by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
       by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
  rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
  sep_ac_rfl

theorem step_encChain_mk_elem_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (curBs : List (BitVec 8))
    (hbound : curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32)
    (hspare : curBs.length + (lenField 4 (encMessageKey gk.2)).length ≤ curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 668#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ lenField 4 (encMessageKey gk.2)) ∗
          messageKeyAt A gk cur ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_messageKey_seed_ne_nil_x (A := A) (gk := gk) (cur := cur)
    (F := vecU8At A v curCap curPtr curBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hseed => ?_
  have hseed_pos : 0 < gk.2.seed.length := List.length_pos_of_ne_nil hseed
  have hparts := lenField4_encMessageKey_len_parts gk.2 hseed
  let a1 := 1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length
  let a2 := (uint32Field 1 gk.2.counter).length
  let a3 := 1 + (encodeVarint (BitVec.ofNat 64 gk.2.seed.length)).length
  let a4 := gk.2.seed.length
  have hsum_parts : a1 + (a2 + (a3 + a4)) = (lenField 4 (encMessageKey gk.2)).length := by
    dsimp only [a1, a2, a3, a4]; omega
  refine step_encChain_mk_tag_len_prealloc_x A H hmk
    v cur endPtr curCap curPtr sp0 gk curBs
    (by dsimp only [a1] at hsum_parts; omega)
    (s0 := s0) (F := F) hpc hrun hsp halign htr hregs
    (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
  intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hregs1
  set bs1 := (curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)
  have hbs1_len : bs1.length = curBs.length + a1 := by
    simp only [bs1, a1, List.length_append, List.length_singleton]; omega
  refine step_encChain_mk_counter_prealloc_x A H
    v cur endPtr curCap curPtr sp0 gk.2.counter bs1
    (by rw [hbs1_len]; dsimp only [a2] at hsum_parts; omega)
    (s0 := s0)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc1 hrun1 hsp1 halign htr1 hregs1
    (by rw [messageKeyAt_eq_cells A gk cur]; sep_ac_rfl) ?_
  intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hregs2
  set bs2 := bs1 ++ uint32Field 1 gk.2.counter
  have hbs2_len : bs2.length = (curBs.length + a1) + a2 := by
    simp only [bs2, hbs1_len, a2, List.length_append]
  have hseed_lt : gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_tag_prealloc_x A H
    v cur endPtr curCap curPtr gk.1.seed.ptr sp0 bs2 gk.2.seed hseed_pos hseed_lt
    (by rw [hbs2_len]; dsimp only [a3] at hsum_parts; omega)
    (s0 := s0)
    (F := ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc2 hrun2 hsp2 halign htr2 hregs2 (by sep_ac_rfl) ?_
  intro s3 hvm3 hpc3 hrun3 hsp3 htr3 hregs3 hx21_3 hx22_3
  set bs3 := (bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 gk.2.seed.length)
  have hbs3_len : bs3.length = ((curBs.length + a1) + a2) + a3 := by
    simp only [bs3, hbs2_len, a3, List.length_append, List.length_singleton]; omega
  refine step_encChain_mk_seed_copy_prealloc_x A H hmc
    v cur endPtr curCap curPtr gk.1.seed.cap gk.1.seed.ptr sp0 bs3 gk.2.seed
    hseed_pos hseed_lt
    (by rw [hbs3_len]; dsimp only [a4] at hsum_parts; omega)
    (by rw [hbs3_len]; dsimp only [a4] at hsum_parts; omega)
    (s0 := s0)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      mkUnusedAt A gk cur ∗ F)
    hpc3 hrun3 hsp3 halign htr3 hregs3 hx21_3 hx22_3 (by sep_ac_rfl) ?_
  intro s4 hvm4 hpc4 hrun4 hsp4 htr4 hregs4
  have hbs4_eq : bs3 ++ gk.2.seed = curBs ++ lenField 4 (encMessageKey gk.2) := by
    rw [← lenField4_encMessageKey_eq gk.2 hseed]
    simp only [bs3, bs2, bs1, List.append_assoc]
  refine SepWPpLsCl.congr_pre ?_
    (hnext s4 (hvm1.trans (hvm2.trans (hvm3.trans hvm4))) hpc4 hrun4 hsp4 htr4 hregs4)
  rw [hbs4_eq, messageKeyAt_eq_cells A gk cur]
  sep_ac_rfl

/-! ## `message_keys` loop and Segment 4 (`+600 → +1648`) -/

theorem step_encChain_mk_next_eq_prealloc_x [LibsignalPlacement]
    (H : LibsignalHooks)
    (v cur endPtr sp0 : BitVec 64)
    (heq : ((cur + 104#64) == endPtr) = true)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm P Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (1648))
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
  exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_mk_next_ne_prealloc_x [LibsignalPlacement]
    (H : LibsignalHooks)
    (v cur endPtr sp0 : BitVec 64)
    (hne : ((cur + 104#64) == endPtr) = false)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 680#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v (cur + 104#64) endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm P Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (680))
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
  exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *]⟩

theorem step_encChain_mk_loop_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (curBs : List (BitVec 8))
    (hend : endPtr = cur + BitVec.ofNat 64 ((gk :: tl).length * 104))
    (hlen_mk : (gk :: tl).length * 104 < 2 ^ 32)
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32)
    (hspare : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length ≤ curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      arrayAt (messageKeyAt A) 104 cur (gk :: tl) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr
          (curBs ++ ((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten) ∗
          arrayAt (messageKeyAt A) 104 cur (gk :: tl) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  induction tl generalizing gk cur curBs s P F with
  | nil =>
    have hbound1 := mk_bound_head curBs gk [] hbound
    have hspare1 := mk_spare_head curBs curCap.toNat gk [] hspare
    have heq_end : ((cur + 104#64) == endPtr) = true := by
      rw [hend]; simp
    refine step_encChain_mk_elem_prealloc_x A H hmc hmk
      v cur endPtr curCap curPtr sp0 gk curBs hbound1 hspare1
      (s0 := s0) (F := F) hpc hrun hsp halign htr hregs
      (by rw [hP]; simp only [arrayAt, sepConj_emp]) ?_
    intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hregs1
    refine step_encChain_mk_next_eq_prealloc_x H v cur endPtr sp0 heq_end
      (s0 := s0) hpc1 hrun1 hsp1 htr1 hregs1 ?_
    intro sm hvm2 hpcm hrunm hspm htrm
    refine SepWPpLsCl.congr_pre ?_ (hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm)
    simp only [arrayAt, sepConj_emp, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil]
  | cons gk2 tl2 ih =>
    have hbound1 := mk_bound_head curBs gk (gk2 :: tl2) hbound
    have hspare1 := mk_spare_head curBs curCap.toNat gk (gk2 :: tl2) hspare
    have hlen_tl := mk_len_tl_lt gk (gk2 :: tl2) hlen_mk
    have hbound_tl := mk_bound_tail curBs gk (gk2 :: tl2) hbound
    have hspare_tl := mk_spare_tail curBs curCap.toNat gk (gk2 :: tl2) hspare
    refine step_encChain_mk_elem_prealloc_x A H hmc hmk
      v cur endPtr curCap curPtr sp0 gk curBs hbound1 hspare1
      (s0 := s0)
      (F := arrayAt (messageKeyAt A) 104 (cur + 104#64) (gk2 :: tl2) ∗ F)
      hpc hrun hsp halign htr hregs
      (by rw [hP]; simp only [arrayAt]; sep_ac_rfl) ?_
    intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hregs1
    have hend_step : endPtr = (cur + 104#64) + BitVec.ofNat 64 ((gk2 :: tl2).length * 104) := by
      rw [hend]
      exact mk_endPtr_step cur (gk2 :: tl2).length
    have hne_end : ((cur + 104#64) == endPtr) = false := by
      rw [hend_step]
      exact mk_endPtr_ne_of_pos cur (gk2 :: tl2).length (by simp) hlen_tl
    refine step_encChain_mk_next_ne_prealloc_x H v cur endPtr sp0 hne_end
      (s0 := s0) hpc1 hrun1 hsp1 htr1 hregs1 ?_
    intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hregs2
    refine ih gk2 (cur + 104#64) (curBs ++ lenField 4 (encMessageKey gk.2))
      hend_step hlen_tl hbound_tl hspare_tl
      (F := messageKeyAt A gk cur ∗ F)
      hpc2 hrun2 hsp2 htr2 hregs2
      (by sep_ac_rfl) ?_
    intro sm hvm3 hpcm hrunm hspm htrm
    refine SepWPpLsCl.congr_pre ?_
      (hnext sm (hvm1.trans (hvm2.trans hvm3)) hpcm hrunm hspm htrm)
    simp only [arrayAt, List.map_cons, List.flatten_cons, List.append_assoc]
    sep_ac_rfl

theorem step_encChain_seg4_empty_prealloc_x [LibsignalPlacement]
    (H : LibsignalHooks)
    (a sp0 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((a + 64#64) ↦₆₄ 0#64) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm (((a + 64#64) ↦₆₄ 0#64) ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (1648))
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
  exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_seg4_init_prealloc_x [LibsignalPlacement]
    (H : LibsignalHooks)
    (v a mkPtr sp0 : BitVec 64) (n : Nat)
    (hpos : 0 < n) (hlt : n < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (((a + 56#64) ↦₆₄ mkPtr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n)) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 680#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v mkPtr (mkPtr + BitVec.ofNat 64 (n * 104)) →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((((a + 56#64) ↦₆₄ mkPtr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n)) ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have hnz := bv_nat_beq_zero_false hpos hlt
  have hmadd := bv_madd_104 mkPtr n
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (680))
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
  exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *]⟩

theorem step_encChain_seg4_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (v a curCap curPtr sp0 : BitVec 64) (gc : ChainGhost × ReceiverChain)
    (curBs : List (BitVec 8))
    (hbound : curBs.length +
      ((gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length < 2 ^ 32)
    (hspare : curBs.length +
      ((gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length ≤ curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      protoChainAt A gc a ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr
          (curBs ++ (gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten) ∗
          protoChainAt A gc a ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_chain_mk_bounds_x (A := A) (gc := gc) (a := a)
    (F := vecU8At A v curCap curPtr curBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hmk_max hkeys_len => ?_
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length :=
    zip_length_eq_right gc.1.keys gc.2.messageKeys hkeys_len
  have hzip_map :
      (gc.1.keys.zip gc.2.messageKeys).map (fun p => lenField 4 (encMessageKey p.2)) =
      gc.2.messageKeys.map (fun mk => lenField 4 (encMessageKey mk)) :=
    zip_map_snd_eq_encChain gc.1.keys gc.2.messageKeys (fun mk => lenField 4 (encMessageKey mk)) hkeys_len
  rw [chainAt_eq_mk_cells A gc a]
  rcases hmks : gc.1.keys.zip gc.2.messageKeys with _ | ⟨gk, tl⟩
  · have hmks_len : gc.2.messageKeys.length = 0 := by
      rw [← hzip_len, hmks]; rfl
    have hmks_nil : gc.2.messageKeys = [] := List.eq_nil_of_length_eq_zero hmks_len
    refine step_encChain_seg4_empty_prealloc_x H a sp0 (s0 := s0)
      (F := vecU8At A v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr [] ∗
        chainMkUnusedAt A gc a ∗
        stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      hpc hrun hsp htr hx20 (by simp only [List.length_nil]; sep_ac_rfl) ?_
    intro sm hvm hpcm hrunm hspm htrm
    refine SepWPpLsCl.congr_pre ?_
      (hnext sm hvm hpcm hrunm hspm htrm)
    rw [chainAt_eq_mk_cells A gc a, hmks, hmks_nil]
    simp only [List.length_nil, List.map_nil, List.flatten_nil, List.append_nil]
    sep_ac_rfl
  · rw [hmks] at hzip_len hzip_map
    have hlen_le : (gk :: tl).length ≤ 2000 := by
      have : maxMessageKeys = 2000 := rfl
      omega
    have hlen_pos : 0 < (gk :: tl).length := by simp
    have hlen_lt : (gk :: tl).length < 2 ^ 32 := by omega
    have hlen_mk : (gk :: tl).length * 104 < 2 ^ 32 := by omega
    refine sepWPpLsCl_extract_vecBuf_mk_le_x (A := A) (cap := gc.1.mkCap) (ptr := gc.1.mkPtr)
      (mks := gk :: tl)
      (F := vecU8At A v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (gk :: tl).length) ∗
        chainMkUnusedAt A gc a ∗
        stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by sep_ac_rfl) fun hle_cap => ?_
    rw [vecBuf_mk_eq_open A gc.1.mkCap gc.1.mkPtr (gk :: tl) hlen_pos hle_cap]
    refine step_encChain_seg4_init_prealloc_x H v a gc.1.mkPtr sp0 (gk :: tl).length
      hlen_pos hlen_lt (s0 := s0)
      (F := vecU8At A v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gk :: tl) ∗
        vecMkRest A gc.1.mkCap gc.1.mkPtr (gk :: tl) ∗
        chainMkUnusedAt A gc a ∗
        stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      hpc hrun hsp htr hx19 hx20 (by sep_ac_rfl) ?_
    intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hregs1
    have hbound_mks :
        curBs.length +
          (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32 := by
      rw [hzip_map]; exact hbound
    have hspare_mks :
        curBs.length +
          (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length ≤
          curCap.toNat := by
      rw [hzip_map]; exact hspare
    refine step_encChain_mk_loop_prealloc_x A H hmc hmk
      gk tl v gc.1.mkPtr (gc.1.mkPtr + BitVec.ofNat 64 ((gk :: tl).length * 104))
      curCap curPtr sp0 curBs rfl hlen_mk hbound_mks hspare_mks
      (s0 := s0)
      (F := ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (gk :: tl).length) ∗
        vecMkRest A gc.1.mkCap gc.1.mkPtr (gk :: tl) ∗
        chainMkUnusedAt A gc a ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hregs1 (by sep_ac_rfl) ?_
    intro sm hvm2 hpcm hrunm hspm htrm
    refine SepWPpLsCl.congr_pre ?_ (hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm)
    rw [chainAt_eq_mk_cells A gc a, hmks,
        vecBuf_mk_eq_open A gc.1.mkCap gc.1.mkPtr (gk :: tl) hlen_pos hle_cap,
        hzip_map]
    sep_ac_rfl

/-! ## Epilogue (`+1648 → ret`) -/

theorem step_encChain_epilogue_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    {x : EncodeChainGhost} {R : SepProp}
    {s0 s : State} {P : SepProp} {Qp : State → SepProp → Prop}
    (hvm_so_far : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_12).base + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (vecU8At A x.v x.cap x.ptr (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      protoChainAt A x.gc x.a ∗
      stackAt (s0.sp - 96#64) encChainSubStackX ∗
      encChainSavedRegs s0.sp s0)) :
    SepWPpLsCl lsmpl (lsProg_12 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
            protoChainAt A x.gc x.a ∗
            vecU8At A x.v x.cap x.ptr (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
            stackAt s0.sp encodeChainStackX) ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  unfold encChainSavedRegs
  have hsp_align96 := sp_sub_96_aligned halign
  apply sepWPpLsCl_of_sepWP_vm (mid := s0.readReg64 .lr)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm_ep => ?_⟩
    apply SepWPpLsCl.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, htr.2]⟩⟩
    intro hm
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by (try simp only [wp_norm, arm64_norm]); exact htr.1, hvm_so_far.trans hvm_ep⟩, ?_⟩
    rw [stackAt_encodeChainStackX_split s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 28#5), s0.readReg64 (Reg.gpr 27#5),
      s0.readReg64 (Reg.gpr 26#5), s0.readReg64 (Reg.gpr 25#5),
      s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
      s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareSeg4XBudget
