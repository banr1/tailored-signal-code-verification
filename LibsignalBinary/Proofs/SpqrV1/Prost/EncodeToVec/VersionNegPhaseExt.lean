/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import ProofLib.SepLogic.WPp

/-!
# Bounded-Stack Phase 2b (`AllocContractsX`): `Option<VersionNegotiation>` Encoding

Lifts `Option<VersionNegotiation>` encoding (`+580 .. +1212`, `0x6d254 .. 0x6d4cc`) in
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

theorem step_encodeToVec_vn_encode_authKey {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (a sp cap ptr v1 v2 : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeBytesField 1#32 vn.authKey).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (if vn.authKey.isEmpty then entry + 1088#64 else entry + 972#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length)
    (hx26 : s.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g a vn ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2)) ∗ F)
    (hnext : ∀ (sm : State) (w1 w2 : BitVec 64),
      sm.pc = entry + 1088#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((versionNegotiationRest A g a vn ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeBytesField 1#32 vn.authKey) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  cases hemp : vn.authKey.isEmpty
  · rw [hemp] at hpc; simp only [Bool.false_eq_true, ↓reduceIte] at hpc
    have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
    have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
    have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
    have h132 : (sp - 136#64) + 4#64 = sp - 132#64 := by bv_omega
    have hpos_ak : 0 < vn.authKey.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
    have hne_ak : vn.authKey ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : Proto.encodeBytesField 1#32 vn.authKey =
        [0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length) ++ vn.authKey := by
      rw [encodeBytesField_1_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all :
        bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length)).length +
          vn.authKey.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt_tag : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := versionNegotiationRest A g a vn ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
    refine sepWPp_extract_pure
      (vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63)
      (fun R' hm => by
        dsimp only [versionNegotiationRest] at hm
        have hm' : s.mem ⊨ EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
            (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
             optChainParamsPBAt (a + 24#64) vn.chainParams ∗
             ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
             memRegion (a + 44#64) 4 ∗ vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
             stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
             ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F ∗ R') := by
          convert hm using 1; ac_rfl
        exact EncodedLen.vecU8Buf_bounds hm')
      fun ⟨hak_le, hak_cap⟩ => ?_
    etv_fetches b (Rust.withPanics ext) hfn 972 1088
    examples_hide_fetches
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    refine sepWPp_split_pointsTo64 (sp - 136#64) v1
      (vecU8At A (sp - 120#64) cap ptr bs ∗ versionNegotiationRest A g a vn ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F)
      (by ac_rfl) fun v1_lo v1_hi => ?_
    rw [h132, vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt_tag hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [versionNegotiationRest]
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack_tag := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x0a#8 hlt_tag hcap hptr
    rw [h112, h104] at hpack_tag
    refine step_etv_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 vn.authKey.length) (sp - 120#64) cap ptr sp (entry + 1032#64) (bs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (F := versionNegotiationRest A g a vn ∗ ((sp - 136#64) ↦₃₂ v1_lo) ∗
        ((sp - 132#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗
        ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack_tag]; dsimp only [versionNegotiationRest]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
    rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩
    simp only [arm64_norm, hx20, hx25] at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26 hs1_27 hs1_28 hs1_fp
    let bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length)
    have hfit_mc : bs1.length + vn.authKey.length ≤ cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
    rw [vecU8At_expose_slice A (sp - 120#64) cap ptr bs1 vn.authKey.length hfit_mc hcap hptr hpos_ak, h112, h104]
    dsimp only [versionNegotiationRest]
    rw [vecU8Buf_eq_of_nonempty A g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hlen_ak_toNat : (BitVec.ofNat 64 vn.authKey.length).toNat = vn.authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_etv_memcpy_call_x b ext hmemcpy
      (ptr + BitVec.ofNat 64 bs1.length) g.authKey.ptr sp (entry + 1072#64) vn.authKey
      (F := ((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
        ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs1) ∗
        memRegion (ptr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 vn.authKey.length)
          (cap.toNat - bs1.length - vn.authKey.length) ∗
        A.pool ∗
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (⌜vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63 ∧ g.authKey.ptr ≠ 0⌝ ∗
          A.live g.authKey.ptr g.authKey.cap.toNat 1 ∗
          memRegion (g.authKey.ptr + BitVec.ofNat 64 vn.authKey.length)
            (g.authKey.cap.toNat - vn.authKey.length)) ∗
        optChainParamsPBAt (a + 24#64) vn.chainParams ∗
        ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion (a + 44#64) 4 ∗
        ((sp - 136#64) ↦₃₂ v1_lo) ∗ ((sp - 132#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗
        ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hlen_ak_toNat, *]) (hinv_s1.trans hinv2) (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hcss2 hinv_s2
    rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩
    simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_28, hs1_fp]
      at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp
    apply SepWPp.of_sepWP_cs (mid := entry + 1088#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hpack_mc := vecU8At_pack_slice A (sp - 120#64) cap ptr bs1 vn.authKey hfit_mc hcap hptr hne_ak
    have hbs_eq : bs1 ++ vn.authKey = bs ++ Proto.encodeBytesField 1#32 vn.authKey := by
      dsimp only [bs1]; rw [henc_eq]; simp only [List.append_assoc]
    rw [h112, h104, hbs_eq] at hpack_mc
    refine sepWPp_merge_pointsTo32 (sp - 136#64) v1_lo (optChainParamsTag vn.chainParams)
      (versionNegotiationRest A g a vn ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeBytesField 1#32 vn.authKey) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
      (by rw [h132, ← hpack_mc]; dsimp only [versionNegotiationRest]
          rw [vecU8Buf_eq_of_nonempty A g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]; ac_rfl)
      fun w1 => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _ w1 (s.readReg64 .x27)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2.trans hinv3))
  · rw [hemp] at hpc; simp only [↓reduceIte] at hpc
    have henc_nil : Proto.encodeBytesField 1#32 vn.authKey = [] := by
      rw [encodeBytesField_1_eq, hemp]; simp only [↓reduceIte]
    refine SepWPp.weaken_pre
      (by rw [henc_nil, List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext s v1 v2 hpc hrun hsp htr rfl hx20 rfl rfl rfl rfl hx26 rfl rfl rfl hinv0)

theorem step_encodeToVec_versionNeg {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (hcp_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (sret a sp ptr v0 v1 v2 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (if st.versionNegotiation.isSome then entry + 580#64 else entry + 1212#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx19 : s.readReg64 .x19 = optChainCap g.chain st.chain)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx22 : s.readReg64 .x22 = a + 48#64) (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ (sm : State) (w1 w2 : BitVec 64),
      sm.pc = entry + 1212#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = optChainCap g.chain st.chain → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = a + 128#64 → sm.readReg64 .x22 = a + 48#64 →
      sm.readReg64 .x27 = sret → sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      sm.readReg64 .fp = sp - 96#64 → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g a st ∗
          vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    refine SepWPp.weaken_pre (by rw [hvn]; exact Entails.refl _)
      (hnext s v1 v2 hpc hrun hsp htr hx19 hx20 hx21 hx22 hx27 hx28 hfp hinv0)
  | some vn =>
    rw [hvn] at hpc hx0; simp only [Option.isSome_some, ↓reduceIte] at hpc hx0
    have hx0' := hx0 trivial
    let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
    have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
      dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hvn_len_le :
        (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 (some vn)).length ≤ cap.toNat := by
      rw [hcap_toNat, ← hvn]; exact optVersionNegotiationPB_encode_len_le st
    rw [encodeOptMessage_versionNeg_some vn] at hvn_len_le
    simp only [List.length_append, List.length_singleton] at hvn_len_le
    have hpos : 0 < cap.toNat := by
      have := encodeVarint_length_pos (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)); omega
    have hak_lt : vn.authKey.length < 2 ^ 64 := vn_authKey_len_lt_of_state hvn hlen
    let F_rest : SepProp :=
      (a ↦₆₄ g.vn.authKey.cap) ∗ optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner ∗
        ((sp - 144#64) ↦₆₄ v0) ∗ encodeToVecSavedRegs sp s0 ∗ F
    refine step_encodeToVec_vn_push_tag b A ext hfn a sp cap ptr g.vn vn hpos halign
      (F := A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpc hrun hsp hx0' hx20 hinv0
      (by unfold pqRatchetStatePBPinnedAt
          rw [hvn, optVersionNegotiationPBPinnedAt_eq A g.vn a (some vn)]
          dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_25 hs1_27 hs1_28 hs1_fp hinv1
    refine step_encodeToVec_vn_authKey_len b A ext hfn a g.vn vn hak_lt
      (F := vecU8At A (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs1 hruns1 hs1_20 hs1_25 hinv1 (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_19 hs2_20 hs2_21 hs2_22 hs2_24 hs2_25 hs2_27 hs2_28 hs2_fp hinv2
    refine step_encodeToVec_vn_dir_len b A ext hfn a g.vn vn
      (F := vecU8At A (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs2 hruns2 hs2_20 hs2_24 hinv2 (by ac_rfl) ?_
    intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_8 hs3_9 hs3_19 hs3_20 hs3_21 hs3_22 hs3_23 hs3_24 hs3_25 hs3_27 hs3_28 hs3_fp hinv3
    refine step_encodeToVec_vn_minVer_len b A ext hfn a g.vn vn
      (F := vecU8At A (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs3 hruns3 hs3_20 hs3_23 hinv3 (by ac_rfl) ?_
    intro s4 hpcs4 hruns4 hsps4 htrs4 hs4_8 hs4_9 hs4_10 hs4_19 hs4_20 hs4_21 hs4_22 hs4_23 hs4_24 hs4_25 hs4_27 hs4_28 hs4_fp hinv4
    have hsps4' : s4.sp = sp - 144#64 := by rw [hsps4, hsps3, hsps2, hsps1]
    have hs4_8' : s4.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) := by rw [hs4_8, hs3_8, hs2_8]
    have hs4_9' : s4.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) := by rw [hs4_9, hs3_9]
    refine step_encodeToVec_vn_chainParams_len b A ext hfn a sp g.vn vn
      (F := vecU8At A (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs4 hruns4 hsps4' hs4_8' hs4_9' hs4_10 hs4_20 hinv4 (by ac_rfl) ?_
    intro s5 hpcs5 hruns5 hsps5 htrs5 hs5_0 hs5_1 hs5_lr hs5_19 hs5_20 hs5_21 hs5_22 hs5_23 hs5_24 hs5_25 hs5_26 hs5_27 hs5_28 hs5_fp hinv5
    have htrs5' : s5.trace = s0.trace := by rw [htrs5, htrs4, htrs3, htrs2, htrs1, htr]
    refine step_etv_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)) (sp - 120#64) cap ptr sp
      (if vn.chainParams.isSome then entry + 968#64 else entry + 924#64) [0x0a#8]
      (by simp only [List.length_singleton]; omega)
      (F := versionNegotiationRest A g.vn a vn ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs5 hruns5 hsps5 halign htrs5' hs5_lr hs5_0 hs5_1 hinv5 (by ac_rfl) ?_
    intro s6 hpcs6 hruns6 hsps6 htrs6 hcsm6 hinv6
    have hs6_19 : s6.readReg64 .x19 = optChainCap g.chain st.chain := by
      rw [hcsm6.1, hs5_19, hs4_19, hs3_19, hs2_19, hs1_19, hx19]
    have hs6_20 : s6.readReg64 .x20 = a := by rw [hcsm6.2.1, hs5_20]
    have hs6_21 : s6.readReg64 .x21 = a + 128#64 := by
      rw [hcsm6.2.2.1, hs5_21, hs4_21, hs3_21, hs2_21, hs1_21, hx21]
    have hs6_22 : s6.readReg64 .x22 = a + 48#64 := by
      rw [hcsm6.2.2.2.1, hs5_22, hs4_22, hs3_22, hs2_22, hs1_22, hx22]
    have hs6_23 : s6.readReg64 .x23 = vn.minVersion.signExtend 64 := by rw [hcsm6.2.2.2.2.1, hs5_23, hs4_23]
    have hs6_24 : s6.readReg64 .x24 = vn.direction.signExtend 64 := by rw [hcsm6.2.2.2.2.2.1, hs5_24, hs4_24, hs3_24]
    have hs6_25 : s6.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length := by
      rw [hcsm6.2.2.2.2.2.2.1, hs5_25, hs4_25, hs3_25, hs2_25]
    have hs6_26 : s6.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64 := by
      rw [hcsm6.2.2.2.2.2.2.2.1, hs5_26]
    have hs6_27 : s6.readReg64 .x27 = sret := by
      rw [hcsm6.2.2.2.2.2.2.2.2.1, hs5_27, hs4_27, hs3_27, hs2_27, hs1_27, hx27]
    have hs6_28 : s6.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.1, hs5_28, hs4_28, hs3_28, hs2_28, hs1_28, hx28]
    have hs6_fp : s6.readReg64 .fp = sp - 96#64 := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.2.1, hs5_fp, hs4_fp, hs3_fp, hs2_fp, hs1_fp, hfp]
    refine step_encodeToVec_vn_branch_authKey b ext hfn vn hak_lt hpcs6 hruns6 hs6_25 hinv6 ?_
    intro s7 hpcs7 hruns7 hsps7 htrs7 hs7_19 hs7_20 hs7_21 hs7_22 hs7_23 hs7_24 hs7_25 hs7_26 hs7_27 hs7_28 hs7_fp hinv7
    rw [hsps6] at hsps7; rw [htrs6] at htrs7
    rw [hs6_19] at hs7_19; rw [hs6_20] at hs7_20; rw [hs6_21] at hs7_21; rw [hs6_22] at hs7_22
    rw [hs6_23] at hs7_23; rw [hs6_24] at hs7_24; rw [hs6_25] at hs7_25
    rw [hs6_26] at hs7_26; rw [hs6_27] at hs7_27; rw [hs6_28] at hs7_28; rw [hs6_fp] at hs7_fp
    refine Ext.step_encodeToVec_vn_encode_authKey b A ext hfn hvarint hmemcpy
      a sp cap ptr v1 v2 g.vn vn
      ([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)))
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs7 hruns7 hsps7 htrs7 hs7_20 hs7_25 hs7_26 hinv7 (by ac_rfl) ?_
    intro s8 w1 w2 hpcs8 hruns8 hsps8 htrs8 hs8_19 hs8_20 hs8_21 hs8_22 hs8_23 hs8_24 hs8_26 hs8_27 hs8_28 hs8_fp hinv8
    rw [hs7_19] at hs8_19; rw [hs7_21] at hs8_21; rw [hs7_22] at hs8_22; rw [hs7_23] at hs8_23
    rw [hs7_24] at hs8_24; rw [hs7_27] at hs8_27; rw [hs7_28] at hs8_28; rw [hs7_fp] at hs8_fp
    refine step_encodeToVec_vn_encode_dir b A ext hfn hvarint sp cap ptr vn
      (([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A g.vn a vn ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs8 hruns8 hsps8 htrs8 hs8_24 hinv8 (by ac_rfl) ?_
    intro s9 hpcs9 hruns9 hsps9 htrs9 hs9_19 hs9_20 hs9_21 hs9_22 hs9_23 hs9_26 hs9_27 hs9_28 hs9_fp hinv9
    rw [hs8_19] at hs9_19; rw [hs8_20] at hs9_20; rw [hs8_21] at hs9_21; rw [hs8_22] at hs9_22
    rw [hs8_23] at hs9_23; rw [hs8_26] at hs9_26; rw [hs8_27] at hs9_27
    rw [hs8_28] at hs9_28; rw [hs8_fp] at hs9_fp
    refine step_encodeToVec_vn_encode_minVer b A ext hfn hvarint sp cap ptr vn
      ((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey) ++ Proto.encodeInt32Field 2#32 vn.direction)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A g.vn a vn ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs9 hruns9 hsps9 htrs9 hs9_23 hinv9 (by ac_rfl) ?_
    intro s10 hpcs10 hruns10 hsps10 htrs10 hs10_19 hs10_20 hs10_21 hs10_22 hs10_26 hs10_27 hs10_28 hs10_fp hinv10
    rw [hs9_19] at hs10_19; rw [hs9_20] at hs10_20; rw [hs9_21] at hs10_21; rw [hs9_22] at hs10_22
    rw [hs9_26] at hs10_26; rw [hs9_27] at hs10_27; rw [hs9_28] at hs10_28; rw [hs9_fp] at hs10_fp
    refine step_encodeToVec_vn_encode_chainParams b A ext hfn hcp_call a sp cap ptr g.vn vn
      (((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey) ++
        Proto.encodeInt32Field 2#32 vn.direction) ++ Proto.encodeInt32Field 3#32 vn.minVersion)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs10 hruns10 hsps10 htrs10 hs10_20 hs10_26 hinv10 (by ac_rfl) ?_
    intro s11 hpcs11 hruns11 hsps11 htrs11 hs11_19 hs11_20 hs11_21 hs11_22 hs11_27 hs11_28 hs11_fp hinv11
    rw [hs10_19] at hs11_19; rw [hs10_21] at hs11_21; rw [hs10_22] at hs11_22; rw [hs10_27] at hs11_27
    rw [hs10_28] at hs11_28; rw [hs10_fp] at hs11_fp
    refine SepWPp.weaken_pre ?_
      (hnext s11 w1 w2 hpcs11 hruns11 hsps11 htrs11 hs11_19 hs11_20 hs11_21 hs11_22 hs11_27 hs11_28 hs11_fp hinv11)
    unfold pqRatchetStatePBPinnedAt
    rw [hvn, optVersionNegotiationPBPinnedAt_eq A g.vn a (some vn), encodeOptMessage_versionNeg_some vn]
    dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]
    simp only [List.append_assoc]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Prost.EncodeToVec.Ext
