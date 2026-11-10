/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `VersionNegotiationPB` Framing & Tag Body Helpers for `spqr::decode_state` (`0x5349c`)

Defines `VersionNegotiationPB` stack-frame layout and initialization helpers and proves the
per-field body lemmas (Tags 1..4 and `skip_field`) for the inlined `VersionNegotiationPB::merge`
loop.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. `VersionNegotiationPB` Framing and Initialization Helpers -/

theorem optChainParamsPBAt_none_to_init (a : BitVec 64) :
    (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8 ⊢
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 32, (a + 8#64) ↦₃₂ w1) := by
  have h1 : (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8 ⊢ memRegion a 4 ∗ memRegion (a + 4#64) 8 :=
    sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion a 0#32)
  have h2 : memRegion a 4 ∗ memRegion (a + 4#64) 8 = memRegion a 12 :=
    (ProofLib.memRegion_split a 4 8 (by decide)).symm
  have h3 : memRegion a 12 = memRegion a 8 ∗ memRegion (a + 8#64) 4 :=
    ProofLib.memRegion_split a 8 4 (by decide)
  rw [h2, h3, ProofLib.memRegion_eight a, ProofLib.memRegion_four (a + 8#64)] at h1
  exact h1

theorem optVersionNegotiationPB_none_split40 (a : BitVec 64) :
    memRegion (a + 8#64) 40 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 32, ∃∗ w4 : BitVec 64,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₃₂ w3) ∗
        memRegion (a + 28#64) 8 ∗ ((a + 36#64) ↦₆₄ w4) ∗ memRegion (a + 44#64) 4 := by
  have hs1 := ProofLib.memRegion_split (a + 8#64) 8 32 (by decide)
  have hs2 := ProofLib.memRegion_split ((a + 8#64) + 8#64) 8 24 (by decide)
  have hs3 := ProofLib.memRegion_split (((a + 8#64) + 8#64) + 8#64) 4 20 (by decide)
  have hs4 := ProofLib.memRegion_split ((((a + 8#64) + 8#64) + 8#64) + 4#64) 8 12 (by decide)
  have hs5 := ProofLib.memRegion_split (((((a + 8#64) + 8#64) + 8#64) + 4#64) + 8#64) 8 4 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs1 hs2 hs3 hs4 hs5
  rw [hs1, hs2, hs3, hs4, hs5,
    ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_four (a + 24#64),
    ProofLib.memRegion_eight (a + 36#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem protoPqRatchetStateCapOkAt_some_vn_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (vn : VersionNegotiationPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨some vn, optCh, inner⟩ =
      (vecU8CapOkAt A (sp - 1040#64) remLen vn.authKey ∗
        optChainParamsPBAt (sp - 1016#64) vn.chainParams ∗
        ((sp - 1004#64) ↦₃₂ vn.direction) ∗
        ((sp - 1000#64) ↦₃₂ vn.minVersion) ∗
        memRegion (sp - 996#64) 4) ∗
      optChainPBCapOkAt A (sp - 992#64) remLen optCh ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner := by
  unfold protoPqRatchetStateCapOkAt optVersionNegotiationPBCapOkAt versionNegotiationPBCapOkAt
  dsimp only
  have ha18 : sp - 1040#64 + 0x18#64 = sp - 1016#64 := by bv_omega
  have ha24 : sp - 1040#64 + 0x24#64 = sp - 1004#64 := by bv_omega
  have ha28 : sp - 1040#64 + 0x28#64 = sp - 1000#64 := by bv_omega
  have ha2c : sp - 1040#64 + 0x2c#64 = sp - 996#64 := by bv_omega
  have ha30 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha80 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  rw [ha18, ha24, ha28, ha2c, ha30, ha80]

theorem protoPqRatchetStateAt_some_vn_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (vn : VersionNegotiationPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateAt H_inner A (sp - 1040#64) ⟨some vn, optCh, inner⟩ =
      (rustBytesVecAt A (sp - 1040#64) vn.authKey ∗
        optChainParamsPBAt (sp - 1016#64) vn.chainParams ∗
        ((sp - 1004#64) ↦₃₂ vn.direction) ∗
        ((sp - 1000#64) ↦₃₂ vn.minVersion) ∗
        memRegion (sp - 996#64) 4) ∗
      optChainPBAt A (sp - 992#64) optCh ∗
      optProtoPqRatchetInnerAt H_inner A (sp - 912#64) inner := by
  unfold protoPqRatchetStateAt optVersionNegotiationPBAt versionNegotiationPBAt
  dsimp only
  have ha18 : sp - 1040#64 + 0x18#64 = sp - 1016#64 := by bv_omega
  have ha24 : sp - 1040#64 + 0x24#64 = sp - 1004#64 := by bv_omega
  have ha28 : sp - 1040#64 + 0x28#64 = sp - 1000#64 := by bv_omega
  have ha2c : sp - 1040#64 + 0x2c#64 = sp - 996#64 := by bv_omega
  have ha30 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha80 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  rw [ha18, ha24, ha28, ha2c, ha30, ha80]

theorem optChainParamsPBAt_some_eq (sp : BitVec 64) (cp : ChainParamsPB) :
    optChainParamsPBAt (sp - 1016#64) (some cp) =
      ((sp - 1016#64) ↦₃₂ 1#32) ∗ chainParamsPBAt (sp - 1012#64) cp := by
  unfold optChainParamsPBAt
  dsimp only
  have ha : sp - 1016#64 + 4#64 = sp - 1012#64 := by bv_omega
  rw [ha]

theorem errFrame_parts_fold (A : RustAlloc) (x : DecodeStateGhost) (s0 : State)
    {cur : List (BitVec 8)} (hle : cur.length ≤ x.st.bytes.length)
    (hsuf : IsDropSuffix x.st.bytes cur) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      vecArgRestAt A x.st ∗
      memRegion (s0.sp - 1392#64) 336 ∗
      ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
      memRegion (s0.sp - 328#64) 224 ∗
      memRegion (s0.sp - 104#64) 8 ⊢
    x.st.at A ∗ memRegion (s0.sp - 1392#64) 352 ∗ memRegion (s0.sp - 336#64) 240 := by
  have hs := pointsToBytes_prefix_join (ptr := x.st.ptr) hle hsuf
  have hst := Entails.trans (sepConj_mono_left hs) (vecArg_join_bytes A x.st)
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        vecArgRestAt A x.st ∗
        memRegion (s0.sp - 1392#64) 336 ∗
        ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
        memRegion (s0.sp - 328#64) 224 ∗
        memRegion (s0.sp - 104#64) 8 =
      (((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        vecArgRestAt A x.st) ∗
      (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
      (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
        memRegion (s0.sp - 328#64) 224 ∗
        memRegion (s0.sp - 104#64) 8) := by ac_rfl
  rw [hreord]
  exact sepConj_mono hst (sepConj_mono hlow hup)

theorem wireType_ofNat64_ne_zero_of_ne_varint {iwt : WireType} (h : iwt ≠ .varint) :
    BitVec.ofNat 64 iwt.toNat ≠ 0#64 := by
  cases iwt <;> first | contradiction | decide

/-! ## 2. `VersionNegotiationPB` Tag Body Helpers -/

/-- Tag 1 (`auth_key`, `0x53a20`, `+1412`): calls `bytes::merge` on `vn.authKey` (`sp + 0x160`),
    then either jumps to `0x53d08` on error or returns via `0x53978..0x5397c` to `0x53980` (`+1252`). -/
theorem decodeState_vn_tag1_53a20 {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX4K H_inner img b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : (Proto.mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (bs' rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeBytes (codecWireTypeToProto iwt) rest1).toOption = some (bs', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨some { vn with authKey := bs' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hbm := hc.bytesMerge3_at
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
    protoPqRatchetStateCapOkAt_some_vn_eq]
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon] at hpc hbm ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1412 20
  decodeState_fetches b (Rust.withPanics ext) 1244 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + (0x47d44#64 - 0x4e0a4#64))
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hsp160 : s0.sp - 1392#64 + 352#64 = s0.sp - 1040#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpI.call_bytesMerge3 hbm iwt (s0.sp - 1040#64) vn.authKey
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := entry + 1424#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hsp, hsp160])
    (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 bs' rest2 hmb hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 1252#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_mono (A := A) (a := s0.sp - 992#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop bs' rest2 _ _ hmb hle2 hsuf2
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [protoPqRatchetStateCapOkAt_some_vn_eq]; dsimp only [decodeStateLoopCommon]; ac_rfl)
  · intro s1 hmb hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 2156#64)
    wp_steps 1
    wp_if hcbz
    · exact absurd hcbz hx0_ne
    · wp_steps 1
      refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A (s0.sp - 992#64) rest1.length optCh)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
        (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact SepWPpI.of_sepWPp (decodeState_err_push_53d08 hc.toDecodeStateCalleeContracts4K x
        ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
        (herr_of_none hmb) (by decide)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_vn_eq]; simp only [arm64_norm]; ac_rfl))

/-- Tag 2 (`direction: i32`) in `VersionNegotiation` at `0x539cc..0x539e4`, `0x53a50..0x53a58`,
`0x5397c` (`+1328..+1352`, `+1460..+1468`, `+1248`). -/
theorem decodeState_vn_tag2_539cc {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1328#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨some { vn with direction := v.truncate 32 }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  by_cases hwt : iwt = .varint
  · subst hwt
    have hdv_call := hc.decodeVarint2_at
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_some_vn_eq]
    dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon, WireType.toNat] at hpc hdv_call hx0 ⊢
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 1328 28
    decodeState_fetches b (Rust.withPanics ext) 1460 12
    decodeState_fetches b (Rust.withPanics ext) 1244 8
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + (0x480d4#64 - 0x4e0a4#64))
    wp_steps 3
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine SepWPpI.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
      (ret_pc := entry + 1340#64)
      (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
      (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
      (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hP := by sep_focus) ?_ ?_
    · intro s1 v rest2 hdv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1_a : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      apply SepWPpI.of_sepWP (mid := entry + 1252#64)
      wp_steps 6
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_mono (A := A) (v := s0.sp - 1040#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (bs := vn.authKey) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optChainPBCapOkAt_mono (A := A) (a := s0.sp - 992#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
        (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact hloop v rest2 _ _ rfl hdv hle2 hsuf2
        (by simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
        (by simp only [arm64_norm, htr1])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [protoPqRatchetStateCapOkAt_some_vn_eq]; dsimp only [decodeStateLoopCommon, BitVec.truncate]; ac_rfl)
    · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpI.of_sepWP (mid := entry + 2216#64)
      wp_steps 3
      wp_if hcbz
      · exact absurd hcbz hx1_ne
      · wp_steps 1
        refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
        refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (s0.sp - 1040#64) rest1.length vn.authKey)
          (by sep_focus) ?_
        refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A (s0.sp - 992#64) rest1.length optCh)
          (by sep_focus) ?_
        refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
          (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
        exact SepWPpI.of_sepWPp (decodeState_err_push_53d44 hc x ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none rfl hdv) (by decide)
          (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_vn_eq]; simp only [arm64_norm]; ac_rfl))
  · subst hP
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 1328 4
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 2192#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold
        (loopCommon_cursor_to_errFrame H_inner b A x rest1 rest1.length ⟨some vn, optCh, inner⟩ s0)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      exact SepWPpI.of_sepWPp (decodeState_err_53d2c hc x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost (herr_of_ne hwt)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx21]) (by ac_rfl))
    · exact absurd hcbnz (wireType_ofNat64_ne_zero_of_ne_varint hwt)

/-- Tag 3 (`min_version: i32`) in `VersionNegotiation` at `0x53a34..0x53a4c`, `0x53a5c..0x53a64`,
`0x5397c` (`+1432..+1456`, `+1472..+1480`, `+1248`). -/
theorem decodeState_vn_tag3_53a34 {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨some { vn with minVersion := v.truncate 32 }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  by_cases hwt : iwt = .varint
  · subst hwt
    have hdv_call := hc.decodeVarint2_at
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_some_vn_eq]
    dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon, WireType.toNat] at hpc hdv_call hx0 ⊢
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 1432 28
    decodeState_fetches b (Rust.withPanics ext) 1472 12
    decodeState_fetches b (Rust.withPanics ext) 1244 8
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + (0x480d4#64 - 0x4e0a4#64))
    wp_steps 3
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine SepWPpI.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
      (ret_pc := entry + 1444#64)
      (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
      (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
      (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hP := by sep_focus) ?_ ?_
    · intro s1 v rest2 hdv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1_a : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      apply SepWPpI.of_sepWP (mid := entry + 1252#64)
      wp_steps 6
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_mono (A := A) (v := s0.sp - 1040#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (bs := vn.authKey) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optChainPBCapOkAt_mono (A := A) (a := s0.sp - 992#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
        (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact hloop v rest2 _ _ rfl hdv hle2 hsuf2
        (by simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
        (by simp only [arm64_norm, htr1])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by rw [protoPqRatchetStateCapOkAt_some_vn_eq]; dsimp only [decodeStateLoopCommon, BitVec.truncate]; ac_rfl)
    · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpI.of_sepWP (mid := entry + 2276#64)
      wp_steps 3
      wp_if hcbz
      · exact absurd hcbz hx1_ne
      · wp_steps 1
        refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
        refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (s0.sp - 1040#64) rest1.length vn.authKey)
          (by sep_focus) ?_
        refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A (s0.sp - 992#64) rest1.length optCh)
          (by sep_focus) ?_
        refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
          (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
        exact SepWPpI.of_sepWPp (decodeState_err_push_53d80 hc x ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none rfl hdv) (by decide)
          (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_vn_eq]; simp only [arm64_norm]; ac_rfl))
  · subst hP
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 1432 4
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 2252#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold
        (loopCommon_cursor_to_errFrame H_inner b A x rest1 rest1.length ⟨some vn, optCh, inner⟩ s0)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      exact SepWPpI.of_sepWPp (decodeState_err_53d68 hc x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost (herr_of_ne hwt)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx21]) (by ac_rfl))
    · exact absurd hcbnz (wireType_ofNat64_ne_zero_of_ne_varint hwt)

/-- Call helper at `0x53968..0x5397c` (`+1228..+1248`) for Tag 4 (`chain_params`) of `VersionNegotiation`. -/
theorem decodeState_vn_tag4_call_53968 {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (cp : ChainParamsPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length
        ⟨some { vn with chainParams := some cp }, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (cp' : ChainParamsPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        some (cp', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨some { vn with chainParams := some cp' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hcp_call := hc.chainParamsMerge_at
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
    protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon] at hpc hcp_call ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1228 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + (0x48900#64 - 0x4e0a4#64))
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx22_1c : s0.sp - 1040#64 + 28#64 = s0.sp - 1012#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpI.call_chainParamsMerge hcp_call iwt (s0.sp - 1012#64) cp
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := entry + 1240#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hx22, hx22_1c])
    (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 cp' rest2 hcp hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 1252#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (vecU8CapOkAt_mono (A := A) (v := s0.sp - 1040#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (bs := vn.authKey) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_mono (A := A) (a := s0.sp - 992#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop cp' rest2 _ _ hcp hle2 hsuf2
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]; dsimp only [decodeStateLoopCommon]; ac_rfl)
  · intro s1 n cp' hcp hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn_le
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 2312#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (s0.sp - 1040#64) rest1.length vn.authKey)
        (by sep_focus) ?_
      refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A (s0.sp - 992#64) rest1.length optCh)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A
        (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact SepWPpI.of_sepWPp (decodeState_err_push_53da4 hc x ⟨some { vn with chainParams := some cp' }, optCh, inner⟩
        w0 n s0 _ _ R post hpost (herr_of_none hcp) (by omega)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by unfold decodeStateErrFrame; rw [protoPqRatchetStateAt_some_vn_eq, optChainParamsPBAt_some_eq]; simp only [arm64_norm]; ac_rfl))
    · exact absurd hcbnz hx0_ne

/-- Tag 4 (`chain_params: Option<ChainParams>`) in `VersionNegotiation` at `0x539f8..0x53a08`,
`0x53968..0x5397c` (`+1372..+1388`, `+1228..+1248`). -/
theorem decodeState_vn_tag4_539f8 {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1372#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (cp' : ChainParamsPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = some (cp', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨some { vn with chainParams := some cp' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases vn with ⟨authKey, dir, minVer, _ | cp⟩
  · rw [protoPqRatchetStateCapOkAt_some_vn_eq]
    dsimp only [Option.getD] at herr_of_none hloop ⊢
    have hnone_eq : optChainParamsPBAt (s0.sp - 1016#64) none =
        ((s0.sp - 1016#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 1016#64 + 4#64) 8 := rfl
    rw [hnone_eq]
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 1372 20
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 1228#64)
    wp_steps 2
    refine SepWP.fold (optChainParamsPBAt_none_to_init (s0.sp - 1016#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps 3
    have hinit : ((s0.sp - 1016#64) ↦₆₄ 1#64) ∗ ((s0.sp - 1008#64) ↦₃₂ 0#32) ⊢
        optChainParamsPBAt (s0.sp - 1016#64) (some default) := by
      have h1 := optChainParamsPBAt_some_default_init (s0.sp - 1016#64)
      have ha8 : s0.sp - 1016#64 + 8#64 = s0.sp - 1008#64 := by bv_omega
      rw [ha8] at h1
      exact h1
    refine SepWP.fold hinit (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    rw [← hentry, ← decodeStateEntry_eq] at hloop
    exact decodeState_vn_tag4_call_53968 (v27 := v27) hc x w0 ⟨authKey, dir, minVer, none⟩ default optCh inner rest1 limit iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by rw [protoPqRatchetStateCapOkAt_some_vn_eq]; ac_rfl) hloop
  · rw [protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]
    dsimp only [Option.getD] at herr_of_none hloop ⊢
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 1372 8
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 1228#64)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    rw [← hentry, ← decodeStateEntry_eq] at hloop
    exact decodeState_vn_tag4_call_53968 (v27 := v27) hc x w0 ⟨authKey, dir, minVer, some cp⟩ cp optCh inner rest1 limit iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by rw [protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]) hloop

/-- Unknown tag (`skip_field`) in `VersionNegotiation` at `0x53a0c..0x53a1c`, `0x5397c` (`+1392..+1408`, `+1248`). -/
theorem decodeState_vn_skip_53a0c {H_inner : V1InnerHeapPred} {img : Obj.Image} {b v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit tag : Nat) (iwt : WireType)
    (htag : 1 ≤ tag ∧ tag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : skipField (2 * rest1.length + 2) 99 tag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : BitVec.setWidth 8 (s.readReg64 .x0) = BitVec.ofNat 8 iwt.toNat)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 99 tag iwt rest1 = some rest2 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length ⟨some vn, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hsf_call := hc.skipField3_at
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon] at hpc hsf_call ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1392 20
  decodeState_fetches b (Rust.withPanics ext) 1248 4
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + (0x4677c#64 - 0x4e0a4#64))
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpI.call_skipField3 hsf_call iwt tag 99
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := entry + 1404#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0]) (hx1 := by simp only [arm64_norm, hx1])
    (htag := htag.2) (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hx3 := by simp only [arm64_norm]) (hdepth := by decide) (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 rest2 hsf hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 1252#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
      (st := ⟨some vn, optCh, inner⟩) hle2) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop rest2 _ _ hsf hle2 hsuf2
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateLoopCommon]; ac_rfl)
  · intro s1 hsf hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpI.of_sepWP (mid := entry + 2352#64)
    wp_steps 3
    wp_if hcbnz
    · refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A
        (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact SepWPpI.of_sepWPp (decodeState_err_push_53dcc hc x ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
        (herr_of_none hsf) (by decide)
        (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [decodeStateErrFrame, arm64_norm]; ac_rfl))
    · exact absurd hcbnz hx0_ne

end CryptoVerification.SpqrV1.Top.DecodeState
