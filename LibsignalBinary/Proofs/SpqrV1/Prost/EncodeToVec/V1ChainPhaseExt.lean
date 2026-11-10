/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainFields
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainPhase
import ProofLib.SepLogic.WPp

/-!
# Bounded-Stack Phase 2c (`AllocContractsX`): `Option<Chain>` Encoding

Lifts `Option<Chain>` encoding (`+1212 .. +1740`, `0x6d4cc .. 0x6d6dc`) in
`PqRatchetState::encode_to_vec` to bounded-stack `AllocContractsX` callee contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec.Ext

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

private theorem step_etv_memcpy_call_x {resStack : Nat}
    (b : BitVec 64) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length) (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_encodeToVec_chain_nextRoot {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeBytesField 4#32 ch.nextRoot).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1552#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1660#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeBytesField 4#32 ch.nextRoot) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1552 1660
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h72 : a + 48#64 + 0x18#64 = a + 72#64 := by bv_omega
  have h80 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have h88 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  dsimp only [chainPBPinnedAt]
  rw [h72, EncodedLen.vecU8At_eq_header_sep_buf A (a + 72#64), vecHeader, h80, h88]
  refine sepWPp_extract_pure
    (ch.nextRoot.length ≤ g.nextRoot.cap.toNat ∧ g.nextRoot.cap.toNat < 2 ^ 63)
    (fun R' hm => by
      have hm' : s.mem ⊨ EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
          (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
           ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
           ((a + 88#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length) ∗
           ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
           ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
           optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
           ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction) ∗
           vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
           stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact EncodedLen.vecU8Buf_bounds hm')
    fun ⟨hnr_le, hnr_cap⟩ => ?_
  have hnr_lt : ch.nextRoot.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hnr_lt
  cases hemp : ch.nextRoot.isEmpty
  · simp only [hemp, Bool.not_false] at hbeqz hbnez
    have hpos_nr : 0 < ch.nextRoot.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
    have hne_nr : ch.nextRoot ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : Proto.encodeBytesField 4#32 ch.nextRoot =
        [0x22#8] ++ Proto.encodeVarint (BitVec.ofNat 64 ch.nextRoot.length) ++ ch.nextRoot := by
      rw [encodeBytesField_4_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all :
        bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 ch.nextRoot.length)).length +
          ch.nextRoot.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt_tag : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        (((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt_tag hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack_tag := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x22#8 hlt_tag hcap hptr
    rw [h112, h104] at hpack_tag
    refine step_etv_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 ch.nextRoot.length) (sp - 120#64) cap ptr sp (entry + 1612#64) (bs ++ [0x22#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        (((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack_tag]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
    rcases hcss1 with ⟨_, hs1_20, hs1_21, hs1_22, hs1_23, _, _, _, hs1_27, hs1_28, hs1_fp, _⟩
    simp only [arm64_norm, hx20] at hs1_20 hs1_21 hs1_22 hs1_23 hs1_27 hs1_28 hs1_fp
    let bs1 := (bs ++ [0x22#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 ch.nextRoot.length)
    have hfit_mc : bs1.length + ch.nextRoot.length ≤ cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
    rw [vecU8At_expose_slice A (sp - 120#64) cap ptr bs1 ch.nextRoot.length hfit_mc hcap hptr hpos_nr,
      h112, h104, vecU8Buf_eq_of_nonempty A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot hemp hnr_le]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hlen_nr_toNat : (BitVec.ofNat 64 ch.nextRoot.length).toNat = ch.nextRoot.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_etv_memcpy_call_x b ext hmemcpy
      (ptr + BitVec.ofNat 64 bs1.length) g.nextRoot.ptr sp (entry + 1652#64) ch.nextRoot
      (F := ((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
        ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs1) ∗
        memRegion (ptr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 ch.nextRoot.length)
          (cap.toNat - bs1.length - ch.nextRoot.length) ∗
        A.pool ∗
        chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        (((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        (⌜ch.nextRoot.length ≤ g.nextRoot.cap.toNat ∧ g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
          A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗
          memRegion (g.nextRoot.ptr + BitVec.ofNat 64 ch.nextRoot.length)
            (g.nextRoot.cap.toNat - ch.nextRoot.length)) ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hlen_nr_toNat, *]) (hinv_s1.trans hinv2) (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hcss2 hinv_s2
    rcases hcss2 with ⟨_, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, _, _, hs2_27, hs2_28, hs2_fp, _⟩
    simp only [arm64_norm, hs1_20, hs1_21, hs1_22, hs1_23, hs1_27, hs1_28, hs1_fp]
      at hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_27 hs2_28 hs2_fp
    apply SepWPp.of_sepWP_cs (mid := entry + 1660#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hpack_mc := vecU8At_pack_slice A (sp - 120#64) cap ptr bs1 ch.nextRoot hfit_mc hcap hptr hne_nr
    have hbs_eq : bs1 ++ ch.nextRoot = bs ++ Proto.encodeBytesField 4#32 ch.nextRoot := by
      dsimp only [bs1]; rw [henc_eq]; simp only [List.append_assoc]
    rw [h112, h104, hbs_eq] at hpack_mc
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]
          rw [h72, EncodedLen.vecU8At_eq_header_sep_buf A (a + 72#64), vecHeader, h80, h88,
            vecU8Buf_eq_of_nonempty A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot hemp hnr_le, ← hpack_mc]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_s2.trans hinv3))
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have henc_nil : Proto.encodeBytesField 4#32 ch.nextRoot = [] := by
      rw [encodeBytesField_4_eq, hemp]; simp only [↓reduceIte]
    apply SepWPp.of_sepWP_cs (mid := entry + 1660#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]
          rw [h72, EncodedLen.vecU8At_eq_header_sep_buf A (a + 72#64), vecHeader, h80, h88,
            henc_nil, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))

theorem step_encodeToVec_chain {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hChainLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hep_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709524204#64)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (hed_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442992#64)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (hcp_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (sret a sp ptr : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1212#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = optChainCap g.chain st.chain)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx22 : s.readReg64 .x22 = a + 48#64) (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
        (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
      A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1740#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = a + 128#64 →
      sm.readReg64 .x27 = sret → sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      sm.readReg64 .fp = sp - 96#64 → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g a st ∗
          vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
              Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1212 1220
  examples_hide_fetches; subst hP
  let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
  let bs0 := Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation
  have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_extract_pure
    ((optChainCap g.chain st.chain + 1#64 == 0#64) = !st.chain.isSome ∧
     (optChainCap g.chain st.chain + 1#64 != 0#64) = st.chain.isSome)
    (fun R' hm => by
      rw [pqRatchetStatePBPinnedAt, optChainPBPinnedAt_eq A g.chain (a + 48#64) st.chain] at hm
      apply optChainRest_cap_bounds (A := A) (g := g.chain) (p := a + 48#64)
        (R := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
          ((a + 48#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner ∗
          vecU8At A (sp - 120#64) cap ptr bs0 ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    fun hch_cap => ?_
  cases hch : st.chain with
  | none =>
    rw [hch] at hch_cap hx19; simp only [Option.isSome_none, Bool.not_false] at hch_cap
    apply SepWPp.of_sepWP_cs (mid := entry + 1740#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by rw [hch]; dsimp only [Proto.encodeOptMessage]; rw [List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  | some ch =>
    rw [hch] at hch_cap hx19; simp only [Option.isSome_some, Bool.not_true] at hch_cap
    have ⟨hch_len, _, _⟩ := chainPBEncodedLen_lt_of_state hch hlen
    have hch_fit_all :
        bs0.length + (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 (some ch)).length ≤ cap.toNat := by
      rw [hcap_toNat, ← hch]; exact optChainPB_encode_len_le st
    rw [encodeOptMessage_chain_some ch] at hch_fit_all
    simp only [List.length_append, List.length_singleton] at hch_fit_all
    apply SepWPp.of_sepWP_cs (mid := entry + 1220#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    let F_rest : SepProp :=
      optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner ∗ F
    refine step_encodeToVec_chain_push_tag_len hres b A ext hfn hChainLen hvarint
      a sp cap ptr g.chain ch bs0 hch_len (by omega) halign
      (F := F_rest)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by unfold pqRatchetStatePBPinnedAt; rw [hch]; dsimp only [optChainPBPinnedAt, F_rest]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_20 hs1_21 hs1_22 hs1_27 hs1_28 hs1_fp hinv_s1
    simp only [arm64_norm, hx21, hx27, hx28, hfp] at hs1_21 hs1_27 hs1_28 hs1_fp
    refine step_encodeToVec_chain_dir b A ext hfn hvarint
      a sp cap ptr g.chain ch
      ((bs0 ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch)))
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs1 hruns1 hsps1 htrs1 hs1_20 hinv_s1 (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_20 hs2_21 hs2_22 hs2_27 hs2_28 hs2_fp hinv_s2
    rw [hs1_21] at hs2_21; rw [hs1_27] at hs2_27; rw [hs1_28] at hs2_28; rw [hs1_fp] at hs2_fp
    refine step_encodeToVec_chain_currentEpoch b A ext hfn hvarint
      a sp cap ptr g.chain ch
      (((bs0 ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        Proto.encodeInt32Field 1#32 ch.direction)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs2 hruns2 hsps2 htrs2 hs2_20 hinv_s2 (by ac_rfl) ?_
    intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_20 hs3_21 hs3_22 hs3_27 hs3_28 hs3_fp hinv_s3
    rw [hs2_21] at hs3_21; rw [hs2_27] at hs3_27; rw [hs2_28] at hs3_28; rw [hs2_fp] at hs3_fp
    refine step_encodeToVec_chain_links b A ext hfn hep_call hvarint hed_call
      a sp cap ptr g.chain ch
      ((((bs0 ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        Proto.encodeInt32Field 1#32 ch.direction) ++ Proto.encodeUint64Field 2#32 ch.currentEpoch)
      hch_len (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs3 hruns3 hsps3 htrs3 hs3_20 hinv_s3 (by ac_rfl) ?_
    intro s4 hpcs4 hruns4 hsps4 htrs4 hs4_20 hs4_21 hs4_27 hs4_28 hs4_fp hinv_s4
    rw [hs3_21] at hs4_21; rw [hs3_27] at hs4_27; rw [hs3_28] at hs4_28; rw [hs3_fp] at hs4_fp
    refine Ext.step_encodeToVec_chain_nextRoot b A ext hfn hvarint hmemcpy
      a sp cap ptr g.chain ch
      (((((bs0 ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        Proto.encodeInt32Field 1#32 ch.direction) ++ Proto.encodeUint64Field 2#32 ch.currentEpoch) ++
        Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs4 hruns4 hsps4 htrs4 hs4_20 hinv_s4 (by ac_rfl) ?_
    intro s5 hpcs5 hruns5 hsps5 htrs5 hs5_20 hs5_21 hs5_27 hs5_28 hs5_fp hinv_s5
    rw [hs4_21] at hs5_21; rw [hs4_27] at hs5_27; rw [hs4_28] at hs5_28; rw [hs4_fp] at hs5_fp
    refine step_encodeToVec_chain_sendEpoch b A ext hfn hvarint
      a sp cap ptr g.chain ch
      ((((((bs0 ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        Proto.encodeInt32Field 1#32 ch.direction) ++ Proto.encodeUint64Field 2#32 ch.currentEpoch) ++
        Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links) ++
        Proto.encodeBytesField 4#32 ch.nextRoot)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs5 hruns5 hsps5 htrs5 hs5_20 hinv_s5 (by ac_rfl) ?_
    intro s6 hpcs6 hruns6 hsps6 htrs6 hs6_20 hs6_21 hs6_27 hs6_28 hs6_fp hinv_s6
    rw [hs5_21] at hs6_21; rw [hs5_27] at hs6_27; rw [hs5_28] at hs6_28; rw [hs5_fp] at hs6_fp
    refine step_encodeToVec_chain_params b A ext hfn hcp_call
      a sp cap ptr g.chain ch
      (((((((bs0 ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        Proto.encodeInt32Field 1#32 ch.direction) ++ Proto.encodeUint64Field 2#32 ch.currentEpoch) ++
        Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links) ++
        Proto.encodeBytesField 4#32 ch.nextRoot) ++
        Proto.encodeUint64Field 5#32 ch.sendEpoch)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs6 hruns6 hsps6 htrs6 hs6_20 hinv_s6 (by ac_rfl) ?_
    intro s7 hpcs7 hruns7 hsps7 htrs7 hs7_20 hs7_21 hs7_27 hs7_28 hs7_fp hinv_s7
    rw [hs6_21] at hs7_21; rw [hs6_27] at hs7_27; rw [hs6_28] at hs7_28; rw [hs6_fp] at hs7_fp
    refine SepWPp.weaken_pre ?_
      (hnext s7 hpcs7 hruns7 hsps7 htrs7 hs7_20 hs7_21 hs7_27 hs7_28 hs7_fp hinv_s7)
    unfold pqRatchetStatePBPinnedAt
    rw [hch, encodeOptMessage_chain_some ch]
    dsimp only [optChainPBPinnedAt, cap, bs0, F_rest]
    simp only [List.append_assoc]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Prost.EncodeToVec.Ext
