/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent2StagesPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent1
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Proof of `encode<Ct1Sent> [local#1, 2]` (Blocks 156 & 319)

Completes Stage 6 (`ct1: Vec<u8>`) and the epilogue for `encode<unchunked::Ct1Sent, Vec<u8>> [local#2]`
(Block 319), discharges `encode<Authenticator>` on both `[local#1]` (Block 156) and `[local#2]`
(Block 319), and provides the `EncodeToVec` (`Block 426`) exact callee bridges at `lsmpl.base 319`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
  (ct1SentPBEncodedLen ct1SentPBPinnedAt ct1SentPBAt unchunked5PinnedAt Unchunked5PBGhost
   optAuthenticatorPBPinnedAt AuthenticatorPBGhost
   ct1SentEncodedLenPinnedSpec unchunked93_entry_pinned_ok)
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm] private theorem bv_pc_add_sub_cancel_ct1 (a b : BitVec 64) : a + (b - a) = b := by bv_omega

local macro "an" : term => `(by simp only [arm64_norm, *])
local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(UnchunkedEncodeCalleeSavedPlaced.step $hcs (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) $hinv)

/-! ## 1. Stage 6: Field 5 — `ct1: Vec<u8>` & Epilogue (`Block 319`) -/

private theorem step_ct1f_from_452_2_placed
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr ct1Cap ct1Ptr sp : BitVec 64) (bs_mid ct1 : List (BitVec 8))
    (hct1_ne : ct1.isEmpty = false) (hle : bs_mid.length + ct1.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ct1Ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs_mid.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = fnBase + 480#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr (bs_mid ++ ct1)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ct1_enc2_fetches_range_placed hfn 452 480
  examples_hide_fetches; subst hP
  have hct1_ne_nil : ct1 ≠ [] := List.isEmpty_eq_false_iff.mp hct1_ne
  have hct1_pos : 0 < ct1.length := List.length_pos_of_ne_nil hct1_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x30#64) (cap := ct1Cap) (ptr := ct1Ptr) (bs := ct1)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by ac_rfl) fun hct1_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid ct1.length hle hcap_lt hptr_ne hct1_pos,
    vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 hct1_ne_nil hct1_le]
  apply SepWPp.of_sepWP_cs_placed (mid := memcpy_pc); wp_steps; apply SepWP.done an an; intro hinv1
  refine step_unchunked_memcpy_call_placed hmemcpy (curPtr + BitVec.ofNat 64 bs_mid.length) ct1Ptr sp
    (fnBase + 472#64) ct1
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 ct1.length)
        (curCap.toNat - bs_mid.length - ct1.length) ∗
      (vecHeader (msgA + 0x30#64) ct1Cap ct1Ptr (BitVec.ofNat 64 ct1.length) ∗
        ⌜ct1Ptr ≠ 0 ∧ ct1.length ≤ ct1Cap.toNat ∧ ct1Cap.toNat < 2 ^ 63⌝ ∗
        memRegion (ct1Ptr + BitVec.ofNat 64 ct1.length) (ct1Cap.toNat - ct1.length) ∗
        A.live ct1Ptr ct1Cap.toNat 1) ∗ F)
    an an an halign an an an an
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (cs_step hcs hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
  have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs_mid.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 480#64); wp_steps; apply SepWP.done an an; intro hinv2
  refine SepWPp.weaken_pre ?_ (hnext _ an an an an (cs_step hcs1 hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs_mid ct1 hle hcap_lt hptr_ne hct1_ne_nil,
    vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 hct1_ne_nil hct1_le]
  exact Entails.of_eq (by ac_rfl)

private theorem step_ct1f_from_400_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr ct1Cap ct1Ptr sp : BitVec 64) (bs4 ct1 : List (BitVec 8))
    (hct1_ne : ct1.isEmpty = false) (hlt : bs4.length < curCap.toNat)
    (hfit : bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ curCap.toNat ∨ bs4.length + (bytesFieldTagged 5#32 ct1).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 400#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs4.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ct1Ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr bs4 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64),
      sm.pc = fnBase + 480#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap5.toNat →
      (bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ curCap.toNat → cap5 = curCap ∧ ptr5 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v cap5 ptr5 (bs4 ++ bytesFieldTagged 5#32 ct1) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep452 := step_ct1f_from_452_2_placed A hfn hmemcpy
  ct1_enc2_fetches_range_placed hfn 400 452
  ct1_enc2_fetches_range_placed hfn 800 844
  examples_hide_fetches; subst hP
  have hct1_len := bytesField5_len_of_ne_empty hct1_ne
  rw [vecU8At_open_one A v curCap curPtr bs4 hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv1
  have hvarint_fit : (bs4 ++ [0x2a#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat ∨
      (bs4 ++ [0x2a#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_unchunked_encode_varint_call_placed hres A henc (BitVec.ofNat 64 ct1.length) v curCap curPtr sp
    (fnBase + 432#64) (bs4 ++ [0x2a#8]) hvarint_fit (F := vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F)
    an an an halign an an an an (cs_step hcs hinv1)
    (by rw [← vecU8At_close_one A v curCap curPtr bs4 0x2a#8 hlt]; ac_rfl) ?_
  intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
  let bs_mid := (bs4 ++ [0x2a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 ct1.length)
  have hbs_mid_len : bs_mid.length + ct1.length = bs4.length + (bytesFieldTagged 5#32 ct1).length := by
    dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hct1_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = ct1Ptr := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap_mid) (ptr := ptr_mid) (bs := bs_mid)
    (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F)
    (by dsimp [bs_mid]; ac_rfl) fun hle_mid hcap_mid_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap_mid ptr_mid bs_mid, vecHeader]
  have hct1_lt63 : ct1.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap_mid.toNat < bs_mid.length + ct1.length
  · have hfit_ct1 : bs_mid.length + ct1.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 ct1.length) = true :=
      (elem_len_ult_spare_iff hle_mid hcap_mid_lt hct1_lt63).mpr hneed
    obtain ⟨hnot_ult, hle_res, hge_res, hbound_ct1⟩ := elem_len_after_reserve_not_ult hfit_ct1 hneed
    apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv2
    refine step_unchunked_do_reserve7_call_placed hres A hdoReserve v cap_mid ptr_mid sp (fnBase + 824#64)
      bs_mid ct1.length hbound_ct1 (F := vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F)
      an an an halign an an an
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      an an (cs_step hcs2 hinv2) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length ct1.length)
    change (BitVec.ofNat 64 ct1.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = ct1Ptr := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap_res ptr_res bs_mid, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 452#64); wp_steps; apply SepWP.done an an; intro hinv3
    exact hstep452 msgA v cap_res ptr_res ct1Cap ct1Ptr sp bs_mid ct1 hct1_ne hle_res
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an (cs_step hcs3 hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField5_of_ne_empty hct1_ne bs4]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap_res ptr_res hpcm hrunm hspm htrm hcsm (Nat.le_trans hge_mid hge_res) (fun h => absurd h (by omega))))
  · have hle_fast : bs_mid.length + ct1.length ≤ cap_mid.toNat := by omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 ct1.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hct1_lt63).mp h)
    have hpres_all : bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ curCap.toNat → cap_mid = curCap ∧ ptr_mid = curPtr := by
      intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 452#64); wp_steps; apply SepWP.done an an; intro hinv2
    exact hstep452 msgA v cap_mid ptr_mid ct1Cap ct1Ptr sp bs_mid ct1 hct1_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an (cs_step hcs2 hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField5_of_ne_empty hct1_ne bs4]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap_mid ptr_mid hpcm hrunm hspm htrm hcsm hge_mid hpres_all))

theorem step_ct1_ct1f_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v cap4 ptr4 ct1Cap ct1Ptr sp : BitVec 64) (bs4 ct1 : List (BitVec 8))
    (hfit : bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ cap4.toNat ∨ bs4.length + (bytesFieldTagged 5#32 ct1).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v cap4 ptr4 bs4 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64),
      sm.pc = fnBase + 480#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → cap4.toNat ≤ cap5.toNat →
      (bs4.length + (bytesFieldTagged 5#32 ct1).length ≤ cap4.toNat → cap5 = cap4 ∧ ptr5 = ptr4) →
      SepWPp prog ret sm
        ((vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v cap5 ptr5 (bs4 ++ bytesFieldTagged 5#32 ct1) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep400 := step_ct1f_from_400_2_placed hres A hfn henc hdoReserve hmemcpy
  ct1_enc2_fetches_range_placed hfn 372 400
  ct1_enc2_fetches_range_placed hfn 772 800
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x30#64) (cap := ct1Cap) (ptr := ct1Ptr) (bs := ct1)
    (F := vecU8At A v cap4 ptr4 bs4 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by ac_rfl) fun hct1_le hct1_cap_lt _ => ?_
  have ⟨hct1_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := ct1) (by omega)
  cases hct1 : ct1.isEmpty
  · have hct1_len := bytesField5_len_of_ne_empty hct1
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap4) (ptr := ptr4) (bs := bs4)
      (F := vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by ac_rfl) fun hcap4_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap4 ptr4 bs4, vecHeader,
      vecU8At_eq_header_sep_buf A (msgA + 0x30#64) ct1Cap ct1Ptr ct1, vecHeader]
    by_cases hcap4 : cap4 == BitVec.ofNat 64 bs4.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
      have hcap_eq : cap4.toNat = bs4.length :=
        CryptoVerification.SpqrV1.Auth.cap_toNat_eq_of_beq hcap4 (Nat.lt_of_le_of_lt hcap4_le (BitVec.isLt cap4))
      have hfit2 : bs4.length + (bytesFieldTagged 5#32 ct1).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := CryptoVerification.SpqrV1.Auth.reserveCap_one_bounds hcap_eq (by omega)
      refine step_unchunked_do_reserve7_call_placed hres A hdoReserve v cap4 ptr4 sp (fnBase + 792#64) bs4 1 hbound1
        (F := vecU8At A (msgA + 0x30#64) ct1Cap ct1Ptr ct1 ∗ F)
        an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        an an an (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap4.toNat bs4.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs4, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 400#64); wp_steps; apply SepWP.done an an; intro hinv1
      exact hstep400 msgA v newCap1 newPtr1 ct1Cap ct1Ptr sp bs4 ct1 hct1 hlt1 (Or.inr hfit2) (F := F)
        an an an halign an an an
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (cs_step hcs1 hinv1) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap5 ptr5 hpcm hrunm hspm htrm hcsm hge2 _ =>
          hnext sm cap5 ptr5 hpcm hrunm hspm htrm hcsm (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)))
    · have hcap4_f : (cap4 == BitVec.ofNat 64 bs4.length) = false := Bool.eq_false_iff.mpr hcap4
      have hlt4 : bs4.length < cap4.toNat :=
        CryptoVerification.SpqrV1.Auth.lt_cap_toNat_of_beq_false hcap4_f hcap4_le (Nat.lt_of_le_of_lt hcap4_le (BitVec.isLt cap4))
      apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 400#64); wp_steps; apply SepWP.done an an; intro hinv0
      exact hstep400 msgA v cap4 ptr4 ct1Cap ct1Ptr sp bs4 ct1 hct1 hlt4 hfit (F := F)
        an an an halign an an an an an (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) hnext
  · rw [vecU8At_eq_header_sep_buf A (msgA + 0x30#64) ct1Cap ct1Ptr ct1, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 480#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre (by rw [← bs_append_bytesFieldTagged_of_empty 5#32 hct1 bs4,
        vecU8At_eq_header_sep_buf A (msgA + 0x30#64) ct1Cap ct1Ptr ct1, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap4 ptr4 an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

/-- Epilogue (`+480 .. +500`) of `encode<Ct1Sent> [local#2]`. -/
theorem step_ct1_epilogue_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn : IsCt1Enc2EntryProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (sp sv3 : BitVec 64) {s0 s : State} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 480#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State), sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp →
      sf.trace = s0.trace → CalleeSavedPreserved s0 sf → StepInv s0 sf →
      Q sf (stackAt sp (unchunkedMsgEncodeStackOf resStack) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ct1_enc2_fetches_range_placed hfn 480 500; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_64_aligned halign
  apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr); wp_steps; apply SepWP.done an an; intro hinv
  have hcs' := cs_step hcs hinv
  refine SepWPp.weaken_pre ?_ (SepWPp.done an an (hnext _ an an an an ⟨an, an, an, an, an, hcs'.1, hcs'.2.1, hcs'.2.2.1, hcs'.2.2.2.1, hcs'.2.2.2.2.1, an, hcs'.2.2.2.2.2.1⟩ hcs'.2.2.2.2.2.2.1))
  rw [stackAt_unchunkedMsgEncode hres sp]; refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right (s0.readReg64 .fp) (Entails.sepExists_right (s0.readReg64 .lr)
    (Entails.sepExists_right (s0.readReg64 .x23) (Entails.sepExists_right sv3
      (Entails.sepExists_right (s0.readReg64 .x22) (Entails.sepExists_right (s0.readReg64 .x21)
        (Entails.sepExists_right (s0.readReg64 .x20) (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))

/-! ## 2. General & Placed `subroutine_ok` for `encode<Ct1Sent> [local#1, 2]` -/

theorem ct1SentEncode2_gen_ok_prog {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn : IsCt1Enc2EntryProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    {A : RustAlloc} {x : Ct1SentEncodePinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok prog encLen_pc (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A)))
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hauth : subroutine_ok prog auth_pc (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (hpc : s0.pc = fnBase) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (ct1SentEncodePinnedSpecOf resStack A).pre x s0 ∗ R) (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp prog (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (ct1SentEncodePinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧ s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (ct1SentEncodePinnedSpec A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre; dsimp only [ct1SentEncodePinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure; obtain ⟨⟨hx0, hx1, hfit⟩, hpre_mem⟩ := hpre_pure
  obtain ⟨hcap_le, hcap_lt, _⟩ := vecU8At_bounds_of_satisfies (A := A) (v := x.v) (cap := x.cap) (ptr := x.ptr) (bs := x.bs)
    (F := ct1SentPBPinnedAt A x.g x.msgA x.m ∗ A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R) (by convert hpre_mem using 1; ac_rfl)
  have hpre_rewritten : s0.mem ⊨ ((ct1SentPBPinnedAt A x.g x.msgA x.m ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)) ∗ emp) ∗ R := by
    rw [sepConj_emp]; convert hpre_mem using 1
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodeCt1SentMsg_len_split x.m
  have hhdr_bds := msgHeaderBytes_len_bounds (ct1SentPBEncodedLen x.m)
  have hlen_eq_fields := ct1SentPBEncodedLen_eq_fields_len x.m
  have hlen_fit : ct1SentPBEncodedLen x.m < 2 ^ 64 := by rcases hfit with h | h <;> omega
  have hfit_hdr : x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length ≤ x.cap.toNat ∨
      x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_hdr_2_placed hres A hfn hencLen henc hdoReserve x.g x.msgA x.v x.cap x.ptr s0.sp x.bs x.m
    hcap_le hlen_fit hfit_hdr (F := emp) hpc hrun rfl halign rfl hx0 hx1 (UnchunkedEncodeCalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 sv3 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hge1 hpres1
  let bs1 := x.bs ++ msgHeaderBytes (ct1SentPBEncodedLen x.m)
  let S := ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ sv3) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hbs1_len : bs1.length = x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length := List.length_append
  have hfit_ep : bs1.length + (u64Field1Bytes x.m.epoch).length ≤ cap1.toNat ∨ bs1.length + (u64Field1Bytes x.m.epoch).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_epoch_2_placed hres A hfn henc hdoReserve x.msgA x.v cap1 ptr1 x.m.epoch s0.sp bs1 hfit_ep hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗ vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗
      vecU8At A (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗ optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x48#64) x.m.auth ∗ S ∗ emp)
    (by dsimp [bs1, S, ct1SentPBPinnedAt, unchunked5PinnedAt]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2
  let bs2 := bs1 ++ u64Field1Bytes x.m.epoch
  have hbs2_len : bs2.length = bs1.length + (u64Field1Bytes x.m.epoch).length := List.length_append
  have hfit_auth : bs2.length + (optAuthField2Bytes x.m.auth).length ≤ cap2.toNat ∨ bs2.length + (optAuthField2Bytes x.m.auth).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_auth_2_placed A hfn hauth x.g.auth x.msgA x.v cap2 ptr2 s0.sp bs2 x.m.auth hfit_auth hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗ vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗
      vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗ vecU8At A (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs2]; ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hge3 hpres3
  let bs3 := bs2 ++ optAuthField2Bytes x.m.auth
  have hbs3_len : bs3.length = bs2.length + (optAuthField2Bytes x.m.auth).length := List.length_append
  have hfit_hdrf : bs3.length + (bytesFieldTagged 3#32 x.m.hdr).length ≤ cap3.toNat ∨ bs3.length + (bytesFieldTagged 3#32 x.m.hdr).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_hdrf_2_placed hres A hfn henc hdoReserve hmemcpy x.msgA x.v cap3 ptr3 x.g.f3.cap x.g.f3.ptr s0.sp bs3 x.m.hdr
    hfit_hdrf hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x48#64) x.m.auth ∗ ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗
      vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗ vecU8At A (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs3]; ac_rfl) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 hge4 hpres4
  let bs4 := bs3 ++ bytesFieldTagged 3#32 x.m.hdr
  have hbs4_len : bs4.length = bs3.length + (bytesFieldTagged 3#32 x.m.hdr).length := List.length_append
  have hfit_es : bs4.length + (bytesFieldTagged 4#32 x.m.es).length ≤ cap4.toNat ∨ bs4.length + (bytesFieldTagged 4#32 x.m.es).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_es_2_placed hres A hfn henc hdoReserve hmemcpy x.msgA x.v cap4 ptr4 x.g.f4.cap x.g.f4.ptr s0.sp bs4 x.m.es
    hfit_es hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4
    (F := vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗ optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x48#64) x.m.auth ∗
      ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗ vecU8At A (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs4]; ac_rfl) ?_
  intro s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5 hge5 hpres5
  let bs5 := bs4 ++ bytesFieldTagged 4#32 x.m.es
  have hbs5_len : bs5.length = bs4.length + (bytesFieldTagged 4#32 x.m.es).length := List.length_append
  have hfit_ct1f : bs5.length + (bytesFieldTagged 5#32 x.m.ct1).length ≤ cap5.toNat ∨ bs5.length + (bytesFieldTagged 5#32 x.m.ct1).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ct1_ct1f_2_placed hres A hfn henc hdoReserve hmemcpy x.msgA x.v cap5 ptr5 x.g.f5.cap x.g.f5.ptr s0.sp bs5 x.m.ct1
    hfit_ct1f hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hcs5
    (F := vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗ vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗
      optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x48#64) x.m.auth ∗ ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗ S ∗ emp)
    (by dsimp [bs5]; ac_rfl) ?_
  intro s6 cap6 ptr6 hpc6 hrun6 hsp6 htr6 hcs6 hge6 hpres6
  refine step_ct1_epilogue_2_placed hres hfn s0.sp sv3
    (F := vecU8At A (x.msgA + 0x30#64) x.g.f5.cap x.g.f5.ptr x.m.ct1 ∗ vecU8At A x.v cap6 ptr6 (bs5 ++ bytesFieldTagged 5#32 x.m.ct1) ∗
      A.pool ∗ vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.es ∗ vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.hdr ∗
      optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x48#64) x.m.auth ∗ ((x.msgA + 0x78#64) ↦₆₄ x.m.epoch) ∗ emp)
    hpc6 hrun6 hsp6 halign htr6 hcs6 (by dsimp [S]; ac_rfl) ?_
  intro sf _ _ hspf htrf hcc _; refine ⟨fun hm => ?_, hspf, hcc⟩
  have hge_all : x.cap.toNat ≤ cap6.toNat := Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 (Nat.le_trans hge4 (Nat.le_trans hge5 hge6))))
  have hpres_all : x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat → cap6 = x.cap ∧ ptr6 = x.ptr := by
    intro hfit_cap
    obtain ⟨hc1, hp1⟩ := hpres1 (by omega); obtain ⟨hc2, hp2⟩ := hpres2 (by omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by omega); obtain ⟨hc4, hp4⟩ := hpres4 (by omega)
    obtain ⟨hc5, hp5⟩ := hpres5 (by omega); obtain ⟨hc6, hp6⟩ := hpres6 (by omega)
    exact ⟨hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))), hp6.trans (hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1))))⟩
  dsimp only [ct1SentEncodePinnedSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]; refine ⟨cap6, ptr6, ?_⟩
  have hpure : (x.cap.toNat ≤ cap6.toNat ∧ (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat → cap6 = x.cap ∧ ptr6 = x.ptr)) = True := eq_true ⟨hge_all, hpres_all⟩
  rw [hpure, pure_true, emp_sepConj, ct1SentPBPinnedAt, unchunked5PinnedAt, ← bs0_append_encodeCt1SentMsg x.bs x.m]
  dsimp only [bs5, bs4, bs3, bs2, bs1] at hm; rw [sepConj_emp] at hm; convert hm using 1; ac_rfl

theorem ct1_sent_encode_1_pinned_placed_ok_uncond [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_156 H) (blkPl_156).base (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpec A)) :=
  ct1_sent_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc
    (ls_subroutine_ok_of_block (auth_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc))

theorem ct1_sent_encode_1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_156 H) (blkPl_156).base (withLsCodeLoaded lsmpl (ct1SentEncodeSpec A)) :=
  ct1SentEncode_unpinned_of_pinned_placed
    (ct1_sent_encode_1_pinned_placed_ok_uncond h_panic hshim halloc hrealloc hmc)

theorem ct1_sent_encode_1_pinned_placed_ok_x_uncond [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_156 H) (blkPl_156).base (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecX A)) :=
  ct1_sent_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc
    (ls_subroutine_ok_of_block (auth_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc))

theorem ct1_sent_encode_1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_156 H) (blkPl_156).base (withLsCodeLoaded lsmpl (ct1SentEncodeSpecX A)) :=
  ct1SentEncode_unpinned_of_pinned_placed
    (ct1_sent_encode_1_pinned_placed_ok_x_uncond h_panic hshim halloc hrealloc hmc)

theorem ct1_sent_encode_2_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_319 H) (blkPl_319).base (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpec A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn2 : IsCt1Enc2EntryProg (lsProg_319 H) (blkPl_319).base (blkPl_408).base (blkPl_292).base (lsmpl.base 314) (blkPl_320).base (lsρ lsMemcpySym) :=
    Or.inr ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hencLen0 : subroutine_ok (lsProg_408 H) (blkPl_408).base (ct1SentEncodedLenPinnedSpec A) :=
    subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
      (unchunked93_entry_pinned_ok (lsProg_408 H) A (blkPl_408).base
        (Or.inr ⟨‹_›, H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)).mono_outcome
        (spec₂ := ct1SentEncodedLenPinnedSpec A) (y := x) (R₂ := R)
        ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩ R s0 hpc hrun hpre hsp (fun _ h => h)
  have hauth0 : subroutine_ok (lsProg_319 H) (lsmpl.base 314) (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf doReserveStack A)) :=
    ls_subroutine_ok_of_block (auth_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc)
  obtain ⟨P, hP, hwp⟩ := ct1SentEncode2_gen_ok_prog (by decide) hfn2
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (subroutine_ok_withLsCodeLoaded_unchunked hencLen0))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (encode_varint4_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed s0 hcl0 hauth0)
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem ct1_sent_encode_2_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_319 H) (blkPl_319).base (withLsCodeLoaded lsmpl (ct1SentEncodeSpec A)) :=
  ct1SentEncode_unpinned_of_pinned_placed
    (ct1_sent_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem ct1_sent_encode_2_pinned_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_319 H) (blkPl_319).base (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecX A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn2 : IsCt1Enc2EntryProg (lsProg_319 H) (blkPl_319).base (blkPl_408).base (blkPl_292).base (lsmpl.base 314) (blkPl_320).base (lsρ lsMemcpySym) :=
    Or.inr ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hencLen0 : subroutine_ok (lsProg_408 H) (blkPl_408).base (ct1SentEncodedLenPinnedSpec A) :=
    subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
      (unchunked93_entry_pinned_ok (lsProg_408 H) A (blkPl_408).base
        (Or.inr ⟨‹_›, H, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)).mono_outcome
        (spec₂ := ct1SentEncodedLenPinnedSpec A) (y := x) (R₂ := R)
        ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩ R s0 hpc hrun hpre hsp (fun _ h => h)
  have hauth0 : subroutine_ok (lsProg_319 H) (lsmpl.base 314) (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf doReserveStackX A)) :=
    ls_subroutine_ok_of_block (auth_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)
  obtain ⟨P, hP, hwp⟩ := ct1SentEncode2_gen_ok_prog (by decide) hfn2
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (subroutine_ok_withLsCodeLoaded_unchunked hencLen0))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed s0 hcl0 hauth0)
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem ct1_sent_encode_2_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_319 H) (blkPl_319).base (withLsCodeLoaded lsmpl (ct1SentEncodeSpecX A)) :=
  ct1SentEncode_unpinned_of_pinned_placed
    (ct1_sent_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

/-! ## 3. `EncodeToVec` (`Block 426`) Callee Bridges (`lsmpl.base 319`) -/

section EncodeToVecBridge

open CryptoVerification.SpqrV1.Prost.EncodeToVec

private theorem unchunkedMsgEncodeStackOf_eq_etv (resStack : Nat) :
    unchunkedMsgEncodeStackOf resStack = encodeToVecCalleeStackOf resStack := by
  dsimp [unchunkedMsgEncodeStackOf, authEncodeStackOf, encodeToVecCalleeStackOf]; omega

theorem etv_ct1SentEncode_of_lscl [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc}
    (hct1_ok : subroutine_ok prog call_pc (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOf resStack A))) :
    subroutine_ok prog call_pc (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOf resStack A)).pre
      ⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withLsCodeLoaded, ct1SentEncodePinnedSpecOf, etvCt1SentEncodeSpecOf,
      encodeCt1SentMsg] at hpre ⊢
    rwa [unchunkedMsgEncodeStackOf_eq_etv]
  refine (hct1_ok.to_outcome ⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩ R s hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, ct1SentEncodePinnedSpecOf, etvCt1SentEncodeSpecOf,
      encodeCt1SentMsg] at hpost ⊢
    rwa [← unchunkedMsgEncodeStackOf_eq_etv]
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact (ProofLib.allowPanic_not_exited hq).elim
  · exact (ProofLib.allowPanic_not_exited hoom).elim

theorem etv_ct1SentEncode_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStack A)) :=
  etv_ct1SentEncode_of_lscl
    (ls_subroutine_ok_of_block (ct1_sent_encode_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc))

theorem etv_ct1SentEncode_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStackX A)) :=
  etv_ct1SentEncode_of_lscl
    (ls_subroutine_ok_of_block (ct1_sent_encode_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc))

end EncodeToVecBridge

end CryptoVerification.SpqrV1.Prost.MessageEncode
