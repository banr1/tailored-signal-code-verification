/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareVarintXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXABudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXBBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.ChainKeyFieldXBudget
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
# Spare-Capacity `encode::<Chain, Vec<u8>>` Segments 0–3 (`+0` → `+600`)

Proves zero-allocation (`VmPreserved`-preserving) relocatable step lemmas over an arbitrary
`A : RustAlloc` for Segments 0–3 (`+0..+600`, prologue through `chain_key`) of Block `12`
(`encode::<Chain, Vec<u8>>`) when the output `Vec<u8>` already has sufficient capacity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareSeg0123XBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ChainKey)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded withLsCl
  lsρ lsMemcpySym
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt VecPin optChainKeyAt optChainKeyNone)
open CryptoVerification.LibsignalProtoCodec (encodeKey encodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf encodeVarint_length_bounds
  vecU8Buf_eq_open_one vecU8Buf_snoc_eq
  cap_beq_len_false bv_len_add_one
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length hwVarintLen_w32_natShift_eq_encodeVarint_length
  cap_add_one_beq_zero_false
)
open CryptoVerification.E2E.Record (lenField bytesField uint32Field msgField encChainKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_88 lsProg_88)
open CryptoVerification.E2E.Record.Serialization (
  EncodeChainGhost encChainMem protoChainAt
  stackAt_encodeChainStackX_split
  encChainSubStackX encChainSavedRegs trVRegs_trans
  bv_add_neg96 encChain_encodeKey_eq encChain_encodeKey_len
  encChainMem_len_lt bytesField_nonempty_eq bv_ofNat_beq_zero_false
  vecU8At_eq_cells_buf vecU8At_add24_eq_cells_buf
  vecU8Buf_eq_open_bytes vecReadRest bv_len_add_slice
  spare_ult_iff
  encChainKey_length_zero encChainKey_length_nonzero
  uint32Field1_zero_eq uint32Field1_nonzero_eq
  optChainKeyAt_none_eq optChainKeyAt_some_eq_encChain
  msgField3_some_eq bytesField2_keyToBytes32_length_encChain
  keyToBytes32_length bytesField2_keyToBytes32_eq
)
open Proofs.libsignal.Hooks2 (
  SepWPpLsCl sepWPpLsCl_extract_vecU8Buf_bounds
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (chainLenSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (encodeChainStackX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXABudget (
  step_encChain_prologue_placed_x
  step_encChain_to_chainLen_placed_x
  step_encChain_to_lenVarint_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareVarintXBudget (
  step_encChain_encodeVarint_prealloc_x
  step_encChain_chainLen_prealloc_x
  step_encChain_memcpy_prealloc_x
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg96
  ofNat_countLeadingZeros_64
  ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length
  hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length
  hwVarintLen_w32_natShift_eq_encodeVarint_length

/-! ## Segment 0 (`+0 → +68`) -/

theorem step_encChain_seg0_raw_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (x : EncodeChainGhost)
    (htag : x.tag = 6 ∨ x.tag = 7)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32)
    (hspare : x.bs.length +
      (encodeKey x.tag .lengthDelimited ++
        encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length ≤ x.cap.toNat)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_12).base)
    (hrun : s0.status = .Running)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = BitVec.ofNat 64 x.tag)
    (hx1 : s0.readReg64 .x1 = x.a)
    (hx2 : s0.readReg64 .x2 = x.v)
    (hP : P = (protoChainAt A x.gc x.a ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt s0.sp encodeChainStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (blkPl_12).base + 68#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = x.v →
      sm.readReg64 .x20 = x.a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A x.v x.cap x.ptr
          (x.bs ++ encodeKey x.tag .lengthDelimited ++
            encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
          protoChainAt A x.gc x.a ∗
          stackAt (s0.sp - 96#64) encChainSubStackX ∗
          encChainSavedRegs s0.sp s0) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s0 P Q Qp := by
  subst hP
  have hkey_eq := encChain_encodeKey_eq htag
  have hkey_len := encChain_encodeKey_len htag
  have hev_tag_len : (encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))).length = 1 := by
    rw [hkey_eq]; exact hkey_len
  have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 (encChainMem x.gc).length)
  have hhdr_len :
      (encodeKey x.tag .lengthDelimited ++
        encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length =
      1 + (encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length := by
    rw [List.length_append, hkey_len]
  have hspare1 : x.bs.length + (encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))).length ≤
      x.cap.toNat := by omega
  have hspare2 : (x.bs ++ encodeKey x.tag .lengthDelimited).length +
      (encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length ≤ x.cap.toNat := by
    rw [List.length_append, hkey_len]; omega
  rw [stackAt_encodeChainStackX_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun w96 => SepWPpLsCl.exists_elim fun w88 =>
    SepWPpLsCl.exists_elim fun w80 => SepWPpLsCl.exists_elim fun w72 =>
    SepWPpLsCl.exists_elim fun w64 => SepWPpLsCl.exists_elim fun w56 =>
    SepWPpLsCl.exists_elim fun w48 => SepWPpLsCl.exists_elim fun w40 =>
    SepWPpLsCl.exists_elim fun w32 => SepWPpLsCl.exists_elim fun w24 =>
    SepWPpLsCl.exists_elim fun w16 => SepWPpLsCl.exists_elim fun w8 => ?_
  refine step_encChain_prologue_placed_x H x.tag x.a x.v s0.sp
    w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 htag
    (F := protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt (s0.sp - 96#64) encChainSubStackX ∗ F)
    hpc hrun rfl halign hx0 hx1 hx2 (by sep_ac_rfl) ?_
  intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx19_1 hx20_1
  refine step_encChain_encodeVarint_prealloc_x A H
    (BitVec.ofNat 64 (x.tag * 8 + 2)) x.v x.cap x.ptr s0.sp
    ((blkPl_12).base + 52#64) x.bs hspare1 (s0 := s0)
    (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0 ∗ F)
    hpc1 hrun1 hsp1 halign htr1 hlr1 hx0_1 hx1_1 (by sep_ac_rfl) ?_
  intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hcs2
  have hx19_2 : s2.readReg64 .x19 = x.v := hcs2.1.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = x.a := hcs2.2.1.trans hx20_1
  refine step_encChain_to_chainLen_placed_x H x.a x.v
    hpc2 hrun2 hx19_2 hx20_2 ?_
  intro s3 hvm3 hpc3 hrun3 hsp3 htr3 hlr3 hx0_3 hx19_3 hx20_3
  refine step_encChain_chainLen_prealloc_x A H hchain s0.sp
    ((blkPl_12).base + 60#64) (x := x) (s0 := s0)
    (F := vecU8At A x.v x.cap x.ptr (x.bs ++ encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))) ∗
      encChainSavedRegs s0.sp s0 ∗ F)
    hpc3 hrun3 (hsp3.trans hsp2) halign (trVRegs_trans htr3 htr2) hlr3 hx0_3 (encChainMem_len_lt hlen)
    (by sep_ac_rfl) ?_
  intro s4 hvm4 hpc4 hrun4 hsp4 htr4 hcs4 hx0_4
  have hx19_4 : s4.readReg64 .x19 = x.v := hcs4.1.trans hx19_3
  have hx20_4 : s4.readReg64 .x20 = x.a := hcs4.2.1.trans hx20_3
  rw [hkey_eq]
  refine step_encChain_to_lenVarint_placed_x H x.a x.v
    (BitVec.ofNat 64 (encChainMem x.gc).length)
    hpc4 hrun4 hx0_4 hx19_4 hx20_4 ?_
  intro s5 hvm5 hpc5 hrun5 hsp5 htr5 hlr5 hx0_5 hx1_5 hx19_5 hx20_5
  refine step_encChain_encodeVarint_prealloc_x A H
    (BitVec.ofNat 64 (encChainMem x.gc).length) x.v x.cap x.ptr s0.sp
    ((blkPl_12).base + 68#64)
    (x.bs ++ encodeKey x.tag .lengthDelimited) hspare2 (s0 := s0)
    (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0 ∗ F)
    hpc5 hrun5 (hsp5.trans hsp4) halign (trVRegs_trans htr5 htr4) hlr5 hx0_5 hx1_5
    (by sep_ac_rfl) ?_
  intro s6 hvm6 hpc6 hrun6 hsp6 htr6 hcs6
  have hx19_6 : s6.readReg64 .x19 = x.v := hcs6.1.trans hx19_5
  have hx20_6 : s6.readReg64 .x20 = x.a := hcs6.2.1.trans hx20_5
  have hvm_all : VmPreserved s0 s6 :=
    hvm1.trans (hvm2.trans (hvm3.trans (hvm4.trans (hvm5.trans hvm6))))
  refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
    (hnext s6 hvm_all hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6)

/-! ## Segment 1 (`+68 → +176`): `sender_ratchet_key` -/

theorem step_encChain_seg1_tag_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (v a curCap curPtr srkPtr sp0 : BitVec 64) (curBs srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hspare : curBs.length + (1 + (encodeVarint (BitVec.ofNat 64 srkBs.length)).length) ≤
      curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 128#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length →
      sm.readReg64 .x22 = srkPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srkBs.length)
  have hlt : curBs.length < curCap.toNat := by omega
  have hspare_ev : (curBs ++ [0x0a#8]).length +
      (encodeVarint (BitVec.ofNat 64 srkBs.length)).length ≤ curCap.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hsrk_nz := bv_ofNat_beq_zero_false hsrk_pos hsrk_lt
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs 0x0a#8
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun y => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x0a#8 hlt]
  refine step_encChain_encodeVarint_prealloc_x A H
    (BitVec.ofNat 64 srkBs.length) v curCap curPtr sp0 ((blkPl_12).base + bv% (128))
    (curBs ++ [0x0a#8]) hspare_ev (s0 := s0)
    (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
  intro sm hvm2 hpcm hrunm hspm htrm hcsm
  refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
    (hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))

theorem step_encChain_seg1_copy_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (v a cap2 ptr2 srkCap srkPtr sp0 : BitVec 64) (bsMid srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    (hspare : bsMid.length + srkBs.length ≤ cap2.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 srkBs.length)
    (hx22 : s.readReg64 .x22 = srkPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      vecU8Buf A srkCap srkPtr srkBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2 (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A srkCap srkPtr srkBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hle2 _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := srkCap) (ptr := srkPtr) (bs := srkBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hsrk_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid srkBs
  have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = false :=
    (spare_ult_iff hle2 hmid_lt hsrk_lt).2.mpr hspare
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
  refine step_encChain_memcpy_prealloc_x A H hmc cap2 ptr2 srkPtr sp0
    ((blkPl_12).base + bv% (168)) bsMid srkBs hsrk_pos hspare hsrk_lt (s0 := s0)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecReadRest A srkCap srkPtr srkBs ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
  intro sm hvm2 hpcm hrunm hspm htrm hcsm
  have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
  have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
  have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
    hcsm.2.2.1.trans (by simp only [arm64_norm, *])
  have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
    hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (176))
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm3 => ?_⟩
  refine SepWPpLsCl.congr_pre ?_
    (hnext _ (hvm1.trans (hvm2.trans hvm3))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
  rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
  sep_ac_rfl

theorem step_encChain_seg1_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (v a curCap curPtr sp0 : BitVec 64) (srk : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 1 srk.bytes).length < 2 ^ 32)
    (hspare : curBs.length + (bytesField 1 srk.bytes).length ≤ curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A srk a ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ bytesField 1 srk.bytes) ∗
          vecGhostAt A srk a ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  by_cases hnil : srk.bytes = []
  · unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    have hlen0 : BitVec.ofNat 64 srk.bytes.length = 0#64 := by simp [hnil]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (176))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hbf0 : curBs ++ bytesField 1 srk.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes, ← hbf0]
    exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hsrk_pos : 0 < srk.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length) ++ srk.bytes =
        bytesField 1 srk.bytes :=
      bytesField_nonempty_eq 1 0x0a#8 srk.bytes hnil (by decide +kernel)
    have hbf_len :
        (bytesField 1 srk.bytes).length =
        (1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length) + srk.bytes.length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srk.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    refine step_encChain_seg1_tag_prealloc_x A H
      v a curCap curPtr srk.ptr sp0 curBs srk.bytes
      hsrk_pos (by omega) (by omega) (s0 := s0)
      (F := (a ↦₆₄ srk.cap) ∗ vecU8Buf A srk.cap srk.ptr srk.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by sep_ac_rfl) ?_
    intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    have hbsMid_len :
        ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length =
        curBs.length + (1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length) := by
      rw [List.length_append, List.length_append, List.length_singleton, Nat.add_assoc]
    rw [vecU8At_eq_cells_buf A v curCap curPtr
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length))]
    refine step_encChain_seg1_copy_prealloc_x A H hmc
      v a curCap curPtr srk.cap srk.ptr sp0
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) srk.bytes
      hsrk_pos (by omega) (by rw [hbsMid_len]; omega) (by rw [hbsMid_len]; omega) (s0 := s0)
      (F := (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by sep_ac_rfl) ?_
    intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes =
        curBs ++ bytesField 1 srk.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    refine SepWPpLsCl.congr_pre ?_
      (hnext s2 (hvm1.trans hvm2) hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2)
    unfold vecGhostAt
    rw [hlist, vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    sep_ac_rfl

/-! ## Segment 2 (`+176 → +284`): `sender_ratchet_key_private` -/

theorem step_encChain_seg2_tag_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (v a curCap curPtr privPtr sp0 : BitVec 64) (curBs privBs : List (BitVec 8))
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hspare : curBs.length + (1 + (encodeVarint (BitVec.ofNat 64 privBs.length)).length) ≤
      curCap.toNat)
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
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 236#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length →
      sm.readReg64 .x22 = privPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 privBs.length)
  have hlt : curBs.length < curCap.toNat := by omega
  have hspare_ev : (curBs ++ [0x12#8]).length +
      (encodeVarint (BitVec.ofNat 64 privBs.length)).length ≤ curCap.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hpriv_nz := bv_ofNat_beq_zero_false hpriv_pos hpriv_lt
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs 0x12#8
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun y => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x12#8 hlt]
  refine step_encChain_encodeVarint_prealloc_x A H
    (BitVec.ofNat 64 privBs.length) v curCap curPtr sp0 ((blkPl_12).base + bv% (236))
    (curBs ++ [0x12#8]) hspare_ev (s0 := s0)
    (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
  intro sm hvm2 hpcm hrunm hspm htrm hcsm
  refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
    (hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))

theorem step_encChain_seg2_copy_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (v a cap2 ptr2 privCap privPtr sp0 : BitVec 64) (bsMid privBs : List (BitVec 8))
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    (hspare : bsMid.length + privBs.length ≤ cap2.toNat)
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
      vecU8Buf A cap2 ptr2 bsMid ∗
      vecU8Buf A privCap privPtr privBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 284#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2 (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A privCap privPtr privBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hle2 _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := privCap) (ptr := privPtr) (bs := privBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hpriv_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid privBs
  have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = false :=
    (spare_ult_iff hle2 hmid_lt hpriv_lt).2.mpr hspare
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
  refine step_encChain_memcpy_prealloc_x A H hmc cap2 ptr2 privPtr sp0
    ((blkPl_12).base + bv% (276)) bsMid privBs hpriv_pos hspare hpriv_lt (s0 := s0)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecReadRest A privCap privPtr privBs ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
  intro sm hvm2 hpcm hrunm hspm htrm hcsm
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
  refine SepWPpLsCl.congr_pre ?_
    (hnext _ (hvm1.trans (hvm2.trans hvm3))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
  rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
  sep_ac_rfl

theorem step_encChain_seg2_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (v a curCap curPtr sp0 : BitVec 64) (priv : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 2 priv.bytes).length < 2 ^ 32)
    (hspare : curBs.length + (bytesField 2 priv.bytes).length ≤ curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A priv (a + 24#64) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 284#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ bytesField 2 priv.bytes) ∗
          vecGhostAt A priv (a + 24#64) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  by_cases hnil : priv.bytes = []
  · unfold vecGhostAt
    rw [vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    have hlen0 : BitVec.ofNat 64 priv.bytes.length = 0#64 := by simp [hnil]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (284))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hbf0 : curBs ++ bytesField 2 priv.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes, ← hbf0]
    exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
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
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    refine step_encChain_seg2_tag_prealloc_x A H
      v a curCap curPtr priv.ptr sp0 curBs priv.bytes
      hpriv_pos (by omega) (by omega) (s0 := s0)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ vecU8Buf A priv.cap priv.ptr priv.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by sep_ac_rfl) ?_
    intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    have hbsMid_len :
        ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length =
        curBs.length + (1 + (encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length) := by
      rw [List.length_append, List.length_append, List.length_singleton, Nat.add_assoc]
    rw [vecU8At_eq_cells_buf A v curCap curPtr
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length))]
    refine step_encChain_seg2_copy_prealloc_x A H hmc
      v a curCap curPtr priv.cap priv.ptr sp0
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) priv.bytes
      hpriv_pos (by omega) (by rw [hbsMid_len]; omega) (by rw [hbsMid_len]; omega) (s0 := s0)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ ((a + 32#64) ↦₆₄ priv.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 priv.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by sep_ac_rfl) ?_
    intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) ++ priv.bytes =
        curBs ++ bytesField 2 priv.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    refine SepWPpLsCl.congr_pre ?_
      (hnext s2 (hvm1.trans hvm2) hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2)
    unfold vecGhostAt
    rw [hlist, vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    sep_ac_rfl

/-! ## Segment 3 (`+284 → +600`): `chain_key` -/

theorem step_encChain_seg3_write_tag_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (v a curCap curPtr ckCap sp0 : BitVec 64) (ckIdx : BitVec 32) (curBs : List (BitVec 8))
    (hck_lt : ckCap.toNat < 2 ^ 63)
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (_halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 340#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ [0x1a#8]) ∗
          ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have hck_niche := cap_add_one_beq_zero_false hck_lt
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs 0x1a#8
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun y => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (340))
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
  rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x1a#8 hlt]
  refine SepWPpLsCl.congr_pre ?_
    (hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
  rw [vecU8At_eq_cells_buf]; sep_ac_rfl

theorem step_encChain_seg3_len_varint_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (v a cap1 ptr1 sp0 : BitVec 64) (ck : ChainKey) (bs1 : List (BitVec 8))
    (hspare : bs1.length + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length ≤
      cap1.toNat)
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
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 416#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ck.index →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap1 ptr1 (bs1 ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  by_cases hidx : ck.index = 0#32
  · have hidx_beq : (ck.index == 0#32) = true := by simp [hidx]
    have hlen_eq := encChainKey_length_zero hidx
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    refine step_encChain_encodeVarint_prealloc_x A H
      (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (416)) bs1
      hspare (s0 := s0) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by sep_ac_rfl) ?_
    intro sm hvm2 hpcm hrunm hspm htrm hcsm
    exact hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hidx_beq : (ck.index == 0#32) = false := beq_eq_false_iff_ne.mpr hidx
    have hlen_eq := encChainKey_length_nonzero hidx
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    refine step_encChain_encodeVarint_prealloc_x A H
      (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (416)) bs1
      hspare (s0 := s0) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by sep_ac_rfl) ?_
    intro sm hvm2 hpcm hrunm hspm htrm hcsm
    exact hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg3_index_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (v a cap2 ptr2 sp0 : BitVec 64) (ckIdx : BitVec 32) (bs2 : List (BitVec 8))
    (hspare : bs2.length + (uint32Field 1 ckIdx).length ≤ cap2.toNat)
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
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 496#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2 (bs2 ++ uint32Field 1 ckIdx) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
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
    rw [← hu0]
    exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
  · have hidx_bne : (ckIdx != 0#32) = true := bne_iff_ne.mpr hidx
    have hu_eq : (bs2 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 ckIdx) =
        bs2 ++ uint32Field 1 ckIdx := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hidx]
    have hu_len : (uint32Field 1 ckIdx).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length := by
      rw [← uint32Field1_nonzero_eq hidx, List.length_append, List.length_singleton]
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.zeroExtend 64 ckIdx)
    have hlt : bs2.length < cap2.toNat := by omega
    have hspare_ev : (bs2 ++ [0x08#8]).length +
        (encodeVarint (BitVec.zeroExtend 64 ckIdx)).length ≤ cap2.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs2 0x08#8
    rw [vecU8At_eq_cells_buf A v cap2 ptr2 bs2, vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x08#8 hlt]
    refine step_encChain_encodeVarint_prealloc_x A H
      (BitVec.zeroExtend 64 ckIdx) v cap2 ptr2 sp0 ((blkPl_12).base + bv% (496)) (bs2 ++ [0x08#8])
      hspare_ev (s0 := s0) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]) ?_
    intro sm hvm2 hpcm hrunm hspm htrm hcsm
    rw [hu_eq]
    exact hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg3_key_tag_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (v a cap3 ptr3 ckPtr sp0 : BitVec 64) (bs3 : List (BitVec 8))
    (hspare : bs3.length + (1 + (encodeVarint 32#64).length) ≤ cap3.toNat)
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
      vecU8Buf A cap3 ptr3 bs3 ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 552#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = ckPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap3 ptr3 ((bs3 ++ [0x12#8]) ++ encodeVarint 32#64) ∗
          ((a + 80#64) ↦₆₄ ckPtr) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds 32#64
  have hlt : bs3.length < cap3.toNat := by omega
  have hspare_ev : (bs3 ++ [0x12#8]).length + (encodeVarint 32#64).length ≤ cap3.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one bs3 0x12#8
  rw [vecU8Buf_eq_open_one A cap3 ptr3 bs3 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun y => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_snoc_eq A cap3 ptr3 bs3 0x12#8 hlt]
  refine step_encChain_encodeVarint_prealloc_x A H
    32#64 v cap3 ptr3 sp0 ((blkPl_12).base + bv% (552)) (bs3 ++ [0x12#8]) hspare_ev (s0 := s0)
    (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
  intro sm hvm2 hpcm hrunm hspm htrm hcsm
  refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
    (hnext sm (hvm1.trans hvm2) hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))

theorem step_encChain_seg3_key_copy_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (v a cap4 ptr4 ckCap ckPtr sp0 : BitVec 64) (bsMid keyBs : List (BitVec 8))
    (hkey_pos : 0 < keyBs.length)
    (hkey_lt : keyBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    (hspare : bsMid.length + keyBs.length ≤ cap4.toNat)
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
      vecU8Buf A cap4 ptr4 bsMid ∗
      vecU8Buf A ckCap ckPtr keyBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap4 ptr4 (bsMid ++ keyBs) ∗
          vecU8Buf A ckCap ckPtr keyBs ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap4) (ptr := ptr4) (bs := bsMid)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A ckCap ckPtr keyBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hle4 _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := ckCap) (ptr := ckPtr) (bs := keyBs)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap4 ptr4 bsMid ∗
      stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by sep_ac_rfl) fun hkey_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid keyBs
  have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = false :=
    (spare_ult_iff hle4 hmid_lt hkey_lt).2.mpr hspare
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
  rw [vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
  refine step_encChain_memcpy_prealloc_x A H hmc cap4 ptr4 ckPtr sp0
    ((blkPl_12).base + bv% (592)) bsMid keyBs hkey_pos hspare hkey_lt (s0 := s0)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecReadRest A ckCap ckPtr keyBs ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
  intro sm hvm2 hpcm hrunm hspm htrm hcsm
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
  refine SepWPpLsCl.congr_pre ?_
    (hnext _ (hvm1.trans (hvm2.trans hvm3))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
  rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
  sep_ac_rfl

theorem step_encChain_seg3_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (v a curCap curPtr sp0 : BitVec 64) (pin : VecPin) (o : Option ChainKey)
    (curBs : List (BitVec 8))
    (hbound : curBs.length + (msgField 3 (o.map encChainKey)).length < 2 ^ 32)
    (hspare : curBs.length + (msgField 3 (o.map encChainKey)).length ≤ curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ optChainKeyAt A pin o (a + 72#64) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_12).base + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ msgField 3 (o.map encChainKey)) ∗
          optChainKeyAt A pin o (a + 72#64) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
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
    rw [← optChainKeyAt_none_eq, ← hmf0]
    exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
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
    rw [optChainKeyAt_some_eq_encChain A pin ck a, vecU8At_eq_cells_buf A v curCap curPtr curBs]
    refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := pin.cap) (ptr := pin.ptr)
      (bs := keyToBytes32 ck.key)
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
        vecU8Buf A curCap curPtr curBs ∗
        ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗ memRegion (a + 100#64) 4 ∗
        stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by sep_ac_rfl) fun _ hck_lt _ => ?_
    refine step_encChain_seg3_write_tag_prealloc_x A H
      v a curCap curPtr pin.cap sp0 ck.index curBs hck_lt
      (by simp only [Option.map_some] at hspare; omega) (s0 := s0)
      (F := ((a + 80#64) ↦₆₄ pin.ptr) ∗ vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by sep_ac_rfl) ?_
    intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    have hbs1_len : (curBs ++ [0x1a#8]).length = curBs.length + 1 := by
      rw [List.length_append, List.length_singleton]
    refine step_encChain_seg3_len_varint_prealloc_x A H
      v a curCap curPtr sp0 ck (curBs ++ [0x1a#8])
      (by rw [hbs1_len]; simp only [Option.map_some] at hspare; omega) (s0 := s0)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by sep_ac_rfl) ?_
    intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2
    have hbs2_len :
        ((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length =
        (curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length := by
      rw [List.length_append, hbs1_len]
    refine step_encChain_seg3_index_prealloc_x A H
      v a curCap curPtr sp0 ck.index
      ((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length))
      (by rw [hbs2_len]; simp only [Option.map_some] at hspare; omega) (s0 := s0)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 (by sep_ac_rfl) ?_
    intro s3 hvm3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3
    have hbs3_len :
        (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
          uint32Field 1 ck.index).length =
        ((curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length) +
          (uint32Field 1 ck.index).length := by
      rw [List.length_append, hbs2_len]
    rw [vecU8At_eq_cells_buf A v curCap curPtr
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)]
    refine step_encChain_seg3_key_tag_prealloc_x A H
      v a curCap curPtr pin.ptr sp0
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)
      (by rw [hbs3_len, hev32_len]; simp only [Option.map_some] at hspare; omega) (s0 := s0)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 (by sep_ac_rfl) ?_
    intro s4 hvm4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4
    have hbs4_len :
        (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
          uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64).length =
        (((curBs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length) +
          (uint32Field 1 ck.index).length) + (1 + (encodeVarint 32#64).length) := by
      rw [List.length_append, List.length_append, List.length_singleton, hbs3_len, Nat.add_assoc]
    rw [vecU8At_eq_cells_buf A v curCap curPtr
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)]
    have hx21_4' : s4.readReg64 .x21 = BitVec.ofNat 64 (keyToBytes32 ck.key).length := by
      rw [hkey_len]; exact hx21_4
    refine step_encChain_seg3_key_copy_prealloc_x A H hmc
      v a curCap curPtr pin.cap pin.ptr sp0
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)
      (keyToBytes32 ck.key)
      (by omega) (by omega)
      (by rw [hbs4_len, hev32_len]; simp only [Option.map_some] at hbound; omega)
      (by rw [hbs4_len, hev32_len, hkey_len]; simp only [Option.map_some] at hspare; omega)
      (s0 := s0)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4' hx22_4 (by sep_ac_rfl) ?_
    intro s5 hvm5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5
    have hlist :
        ((((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
          uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64) ++
          keyToBytes32 ck.key) =
        curBs ++ msgField 3 (Option.map encChainKey (some ck)) := by
      have hbf2 := bytesField2_keyToBytes32_eq ck.key
      simp only [Option.map_some, ← hmf_eq, ← hbf2, List.append_assoc]
    have hvm_all : VmPreserved s s5 :=
      hvm1.trans (hvm2.trans (hvm3.trans (hvm4.trans hvm5)))
    refine SepWPpLsCl.congr_pre ?_
      (hnext s5 hvm_all hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5)
    rw [hlist, optChainKeyAt_some_eq_encChain A pin ck a]
    sep_ac_rfl

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareSeg0123XBudget
