/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationPlaced
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Verification of `spqr::decode_state` (Block `325`) — `VersionNegotiationPB` Merge Loop & Tag-1 Entry
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
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
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

theorem after_decodeVarint2_to_errFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) {cur rest1 : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hle1 : rest1.length ≤ cur.length) (curSt : PqRatchetState) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64)
        (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateErrFramePlaced H_inner A x curSt s0 := by
  have hj := sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr) hcur_le hcur_suf hle1
  have hreord :
      sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 =
      ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hj) ?_
  exact loopCommon_cursor_to_errFrame_placed H_inner A x rest1 cur.length curSt s0

/-- Tag dispatch for `VersionNegotiationPB` at `+1304` given `1 ≤ tag < 2 ^ 29`. -/
theorem decodeState_vn_dispatch_539b4_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (match (VersionNegotiationPB.mergeField vn (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 99).toOption with
       | none => none
       | some (vn', rest2) => mergeLoopBin VersionNegotiationPB.mergeField (rest2.length - limit) vn' rest2 limit 99) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1304#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hnext : ∀ (vn' : VersionNegotiationPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (VersionNegotiationPB.mergeField vn (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 99).toOption =
        some (vn', rest2) →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length ⟨some vn', optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  have hwt8 := wt_setWidth8 iwt
  by_cases htag1 : tag = 1
  · subst htag1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1412#64)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    refine decodeState_vn_tag1_53a20_placed (v27 := v27) hc x w0 vn optCh inner rest1 limit iwt
      hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by
        rw [show BitVec.ofNat 32 1 = 1#32 from rfl, versionNegotiationPB_mergeField_tag1, hnone]; rfl))
      s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0, hwt8])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29]) rfl ?_
    intro v rest2 sf P' hmb hle2 hsuf2 hpc'
    exact hnext { vn with authKey := v } rest2 sf P' hle2 hsuf2
      (by rw [show BitVec.ofNat 32 1 = 1#32 from rfl, versionNegotiationPB_mergeField_tag1, hmb]; rfl) hpc'
  · by_cases htag2 : tag = 2
    · subst htag2
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1328#64)
      wp_steps 6
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      refine decodeState_vn_tag2_539cc_placed (v27 := v27) hc.toDecodeStateCalleeContractsPlaced x w0 vn optCh inner rest1 limit iwt
        hrest1_le hrest1_suf hlen_bound
        (fun hne => herr_of_none (by
          rw [show BitVec.ofNat 32 2 = 2#32 from rfl, versionNegotiationPB_mergeField_tag2]
          simp only [hne, ↓reduceIte]))
        (fun hwt_eq hnone => herr_of_none (by
          rw [show BitVec.ofNat 32 2 = 2#32 from rfl, versionNegotiationPB_mergeField_tag2]
          simp only [hwt_eq, ↓reduceIte, hnone]; rfl))
        s0 _ _ R post hpost hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
        (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29]) rfl ?_
      intro v rest2 sf P' hwt_eq hdv2 hle2 hsuf2 hpc'
      exact hnext { vn with direction := v.truncate 32 } rest2 sf P' hle2 hsuf2
        (by rw [show BitVec.ofNat 32 2 = 2#32 from rfl, versionNegotiationPB_mergeField_tag2]
            simp only [hwt_eq, ↓reduceIte, hdv2]; rfl) hpc'
    · by_cases htag3 : tag = 3
      · subst htag3
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1432#64)
        wp_steps 4
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        refine decodeState_vn_tag3_53a34_placed (v27 := v27) hc.toDecodeStateCalleeContractsPlaced x w0 vn optCh inner rest1 limit iwt
          hrest1_le hrest1_suf hlen_bound
          (fun hne => herr_of_none (by
            rw [show BitVec.ofNat 32 3 = 3#32 from rfl, versionNegotiationPB_mergeField_tag3]
            simp only [hne, ↓reduceIte]))
          (fun hwt_eq hnone => herr_of_none (by
            rw [show BitVec.ofNat 32 3 = 3#32 from rfl, versionNegotiationPB_mergeField_tag3]
            simp only [hwt_eq, ↓reduceIte, hnone]; rfl))
          s0 _ _ R post hpost hs0A
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
          (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
          (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
          (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
          (by simp only [arm64_norm, hx29]) rfl ?_
        intro v rest2 sf P' hwt_eq hdv2 hle2 hsuf2 hpc'
        exact hnext { vn with minVersion := v.truncate 32 } rest2 sf P' hle2 hsuf2
          (by rw [show BitVec.ofNat 32 3 = 3#32 from rfl, versionNegotiationPB_mergeField_tag3]
              simp only [hwt_eq, ↓reduceIte, hdv2]; rfl) hpc'
      · by_cases htag4 : tag = 4
        · subst htag4
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1372#64)
          wp_steps 6
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          refine decodeState_vn_tag4_539f8_placed (v27 := v27) hc.toDecodeStateCalleeContractsPlaced x w0 vn optCh inner rest1 limit iwt
            hrest1_le hrest1_suf hlen_bound
            (fun hnone => herr_of_none (by
              rw [show BitVec.ofNat 32 4 = 4#32 from rfl, versionNegotiationPB_mergeField_tag4, hnone]; rfl))
            s0 _ _ R post hpost hs0A
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
            (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0, hwt8])
            (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
            (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
            (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
            (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
            (by simp only [arm64_norm, hx29]) rfl ?_
          intro cp' rest2 sf P' hcp hle2 hsuf2 hpc'
          exact hnext { vn with chainParams := some cp' } rest2 sf P' hle2 hsuf2
            (by rw [show BitVec.ofNat 32 4 = 4#32 from rfl, versionNegotiationPB_mergeField_tag4, hcp]; rfl) hpc'
        · have ⟨hgt2, hsle2, _, _, _, _⟩ := tag_cmp32_of_gt (c := 2) (by omega) htag29
          have ⟨_, _, _, _, hbeq3, hbne3⟩ := tag_cmp32_of_gt (c := 3) (by omega) htag29
          have ⟨_, _, _, _, hbeq4, hbne4⟩ := tag_cmp32_of_gt (c := 4) (by omega) htag29
          have htw32 := tag_setWidth32_ofNat tag
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1392#64)
          wp_steps 6
          apply SepWP.done (by simp only [arm64_norm, hx1, htw32, hgt2, hsle2, hbeq3, hbne3, hbeq4, hbne4])
            (by simp only [arm64_norm, hrun])
          refine decodeState_vn_skip_53a0c_placed (v27 := v27) hc.toDecodeStateCalleeContractsPlaced x w0 vn optCh inner rest1 limit tag iwt
            ⟨by omega, by omega⟩ hrest1_le hrest1_suf hlen_bound
            (fun hnone => herr_of_none (by
              rw [versionNegotiationPB_mergeField_other vn tag htag1 htag2 htag3 htag4 (by omega) iwt rest1 99, hnone]; rfl))
            s0 _ _ R post hpost hs0A
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx1, htw32, hgt2, hsle2, hbeq3, hbne3, hbeq4, hbne4])
            (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0, hwt8])
            (by simp only [arm64_norm, hx1, htw32])
            (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
            (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
            (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
            (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
            (by simp only [arm64_norm, hx29]) rfl ?_
          intro rest2 sf P' hsf hle2 hsuf2 hpc'
          exact hnext vn rest2 sf P' hle2 hsuf2
            (by rw [versionNegotiationPB_mergeField_other vn tag htag1 htag2 htag3 htag4 (by omega) iwt rest1 99, hsf]; rfl)
            hpc'

/-- One field-key decode + tag dispatch step of `VersionNegotiationPB` at `+1264`. -/
theorem decodeState_vn_body_5398c_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (cur : List (BitVec 8)) (limit : Nat) (hgt : ¬ cur.length ≤ limit)
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : mergeLoopBin VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1264#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hnext : ∀ (vn' : VersionNegotiationPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      rest2.length < cur.length → rest2.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest2 →
      mergeLoopBin VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 =
        mergeLoopBin VersionNegotiationPB.mergeField (rest2.length - limit) vn' rest2 limit 99 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length ⟨some vn', optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hdv_call := hc.decodeVarint2
  subst hP
  rw [sliceCursorAfter_eq_split hcur_le hcur_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hdv_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_decodeVarint2 hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur
    (ret_pc := (blkPl_325).base + 1272#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega) (hP := by sep_focus) ?_ ?_
  · intro s1 key rest1 hdv hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
    have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
    have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
    have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · have hk_ne : (key >>> 32 == 0#64) = false := key_lsr32_ne_zero_of_ge hk
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1728#64)
      wp_steps 3
      refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A x hcur_le hcur_suf hle1
        ⟨some vn, optCh, inner⟩ s0)
        (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_ne]) (by simp only [arm64_norm, hrun1])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_53b5c_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
        (herr_of_none (mergeLoopBin_of_key_ge protoPrefixStep_versionNegotiationPB_mergeField hgt hdv hk))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_ne])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [decodeStateErrFramePlaced, decodeStateErrFrame, arm64_norm]; ac_rfl))
    · have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hk
      rcases hwt : WireType.ofNat? (key.toNat % 8) with _ | iwt
      · rcases key_and7_of_wt_none hwt with hand7 | hand7
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1740#64)
          wp_steps 6
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A x hcur_le hcur_suf hle1
            ⟨some vn, optCh, inner⟩ s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7]) (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_53b68_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_wt_none protoPrefixStep_versionNegotiationPB_mergeField hgt hdv hk hwt))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [decodeStateErrFramePlaced, decodeStateErrFrame, arm64_norm]; ac_rfl))
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1740#64)
          wp_steps 6
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A x hcur_le hcur_suf hle1
            ⟨some vn, optCh, inner⟩ s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7]) (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_53b68_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_wt_none protoPrefixStep_versionNegotiationPB_mergeField hgt hdv hk hwt))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [decodeStateErrFramePlaced, decodeStateErrFrame, arm64_norm]; ac_rfl))
      · have hand7 : key &&& 7#64 = BitVec.ofNat 64 iwt.toNat := key_and7_of_wt_some hwt
        have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 iwt
        have hlsr3 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) := key_lsr3_32_eq hk
        have htag29 : key.toNat / 8 < 2 ^ 29 := tag_lt_pow29_of_key_lt hk
        have hze : BitVec.zeroExtend 64 (BitVec.ofNat 32 (key.toNat / 8)) = BitVec.ofNat 64 (key.toNat / 8) :=
          tag_zeroExtend64_ofNat32 htag29
        have htw32 : BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) = BitVec.ofNat 32 (key.toNat / 8) :=
          tag_setWidth32_ofNat (key.toNat / 8)
        by_cases htag0 : key.toNat / 8 < 1
        · have htag_eq0 : key.toNat / 8 = 0 := by omega
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1752#64)
          wp_steps 8
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A x hcur_le hcur_suf hle1
            ⟨some vn, optCh, inner⟩ s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_53b74_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_tag_zero protoPrefixStep_versionNegotiationPB_mergeField hgt hdv hk hwt htag0))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [decodeStateErrFramePlaced, decodeStateErrFrame, arm64_norm]; ac_rfl))
        · have hloop_step := mergeLoopBin_of_key_ok protoPrefixStep_versionNegotiationPB_mergeField
            (m := vn) (depth' := 99) hgt hdv hk hwt htag0
          have hcbz64 := tag_cbz64_false (by omega : 1 ≤ key.toNat / 8) htag29
          have hcbz32 := tag_cbz32_false (by omega : 1 ≤ key.toNat / 8) htag29
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1304#64)
          wp_steps 8
          refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
            hcur_le hcur_suf hle1) (by sep_focus) ?_
          refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
            (a := s0.sp - 1040#64) (rem1 := cur.length) (rem2 := rest1.length)
            (st := ⟨some vn, optCh, inner⟩) hle1) (by sep_focus) ?_
          apply SepWP.done
            (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1])
          refine decodeState_vn_dispatch_539b4_placed (v27 := v27) hc x w0 vn optCh inner rest1 limit (key.toNat / 8) iwt
            (by omega) htag29 hrest1_le hrest1_suf hlen_bound
            (fun hnone => herr_of_none (by
              rw [hloop_step]
              revert hnone
              rcases (vn.mergeField (BitVec.ofNat 32 (key.toNat / 8)) (codecWireTypeToProto iwt) rest1 99).toOption with _ | ⟨_, _⟩ <;>
                intro hnone <;> exact hnone))
            s0 _ _ R post hpost hs0A
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, hand7, *])
            (by simp only [arm64_norm, hlsr3, hze, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by dsimp only [decodeStateLoopCommonPlaced]; ac_rfl) ?_
          intro vn' rest2 sf P' hle2 hsuf2 hmf
          exact hnext vn' rest2 sf P'
            (Nat.lt_of_le_of_lt hle2 hlt1) (Nat.le_trans hle2 hrest1_le)
            (suffix_trans hrest1_le hrest1_suf hle2 hsuf2) (by rw [hloop_step, hmf])
  · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2352#64)
    wp_steps 1
    refine SepWP.fold (errFrame_parts_fold A x s0 hcur_le hcur_suf) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A
      (s0.sp - 1040#64) cur.length ⟨some vn, optCh, inner⟩) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_1]) (by simp only [arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53dcc_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
      (herr_of_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_versionNegotiationPB_mergeField hgt hdv))
      (by decide)
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
      (by simp only [decodeStateErrFramePlaced, decodeStateErrFrame, arm64_norm]; ac_rfl))

/-- Inlined `VersionNegotiationPB` merge loop at `+1252`, proved by induction on `fuel`. -/
theorem decodeState_vn_loop_53980_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (limit : Nat) (hlim_bound : limit < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (vn : VersionNegotiationPB) (cur : List (BitVec 8)) (s : State) (P : SepProp),
      cur.length - limit ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      (mergeLoopBin VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      s.pc = decodeStatePlacedEntry + 1252#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = BitVec.ofNat 64 limit →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = v27 → s.readReg64 .x28 = 1#64 → s.readReg64 .x29 = s0.sp - 96#64 →
      P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length ⟨some vn, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 →
      (∀ (vn' : VersionNegotiationPB) (rest : List (BitVec 8)) (sf : State) (P' : SepProp),
        mergeLoopBin VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 = some vn' →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limit →
        sf.pc = decodeStatePlacedEntry + 1576#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
        sf.readReg64 .x21 = 0x8000000000000006#64 →
        sf.readReg64 .x22 = s0.sp - 1040#64 → sf.readReg64 .x23 = -1#64 →
        sf.readReg64 .x24 = s0.sp - 912#64 → sf.readReg64 .x25 = s0.sp - 688#64 →
        sf.readReg64 .x26 = -2#64 → sf.readReg64 .x27 = v27 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
          sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest.length ⟨some vn', optCh, inner⟩ ∗
          memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
          decodeStateLoopCommonPlaced A x s0 →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlaced H_inner A x s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  intro fuel
  induction fuel with
  | zero =>
    intro vn cur s P hfuel hcur_le hcur_suf herr_of_none
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone
    have hle : cur.length ≤ limit := by omega
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    subst hP
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq heq
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq]) (by simp only [arm64_norm, hrun])
      exact hdone vn cur _ _
        (mergeLoopBin_eq_limit VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 heq)
        hcur_le hcur_suf heq (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by rw [heq]; simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
        (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29]) (by dsimp only [sliceCursorAfter])
    · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
      have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2964#64)
      wp_steps 5
      refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A x cur cur.length ⟨some vn, optCh, inner⟩ s0)
        (by dsimp only [sliceCursorAfter]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne]) (by simp only [arm64_norm, hrun])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_54030_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
        (herr_of_none (mergeLoopBin_lt_limit VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 hlt))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
        (by unfold decodeStateErrFramePlaced; simp only [arm64_norm]; ac_rfl))
  | succ fuel ih =>
    intro vn cur s P hfuel hcur_le hcur_suf herr_of_none
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    by_cases hle : cur.length ≤ limit
    · subst hP
      dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq heq
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
        wp_steps 4
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq]) (by simp only [arm64_norm, hrun])
        exact hdone vn cur _ _
          (mergeLoopBin_eq_limit VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 heq)
          hcur_le hcur_suf heq (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19]) (by rw [heq]; simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
          (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
          (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
          (by simp only [arm64_norm, hx29]) (by dsimp only [sliceCursorAfter])
      · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
        have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2964#64)
        wp_steps 5
        refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A x cur cur.length ⟨some vn, optCh, inner⟩ s0)
          (by dsimp only [sliceCursorAfter]; sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne]) (by simp only [arm64_norm, hrun])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_54030_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
          (herr_of_none (mergeLoopBin_lt_limit VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 hlt))
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
          (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
          (by unfold decodeStateErrFramePlaced; simp only [arm64_norm]; ac_rfl))
    · have ⟨hult, hule⟩ := cmp_len_limit_of_gt hle (by omega)
      subst hP
      dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1264#64)
      wp_steps 3
      apply SepWP.done (by simp only [arm64_norm, hult, hule]) (by simp only [arm64_norm, hrun])
      refine decodeState_vn_body_5398c_placed (v27 := v27) hc x w0 vn optCh inner cur limit
        hle hcur_le hcur_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
        (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
        (by dsimp only [sliceCursorAfter]) ?_
      intro vn' rest2 sf P' hlt2 hle2 hsuf2 hmerge_eq
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
      exact ih vn' rest2 sf P' (by omega) hle2 hsuf2
        (fun hnone => herr_of_none (by rw [hmerge_eq, hnone]))
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
        (fun vn'' rest3 sf' P'' hok => hdone vn'' rest3 sf' P'' (by rw [hmerge_eq, hok]))

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

/-- Delimited `VersionNegotiationPB::merge` entry at `+216`. -/
theorem decodeState_vn_merge_53574_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt) vn rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
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
      decodeStateLoopCommonPlaced A x s0)
    (hdone : ∀ (vn' : VersionNegotiationPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt) vn rest1 100).toOption =
        some (vn', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
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
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length ⟨some vn', optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  by_cases hwt : iwt = .lengthDelimited
  · subst hwt
    dsimp only [codecWireTypeToProto] at herr_of_none hdone
    have hdv_call := hc.decodeVarint2
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced, WireType.toNat] at hpc hdv_call hx0 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
    refine SepWPpIPlaced.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
      (ret_pc := (blkPl_325).base + 232#64)
      (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
      (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
      (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hP := by sep_focus) ?_ ?_
    · intro s1 len64 rest2 hdv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_len
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      have hrest2_le : rest2.length ≤ x.st.bytes.length := Nat.le_trans hle2 hrest1_le
      have hrest2_suf : IsDropSuffix x.st.bytes rest2 := suffix_trans hrest1_le hrest1_suf hle2 hsuf2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_len hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1A : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      by_cases hlt_len : rest2.length < len64.toNat
      · have ⟨hult, hule⟩ := len_ult_of_lt hlt_len
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2148#64)
        refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
          hrest1_le hrest1_suf hle2) (by sep_focus) ?_
        dsimp only [sliceCursorAfter]
        wp_steps 5
        refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A x rest2 rest1.length
          ⟨some vn, optCh, inner⟩ s0)
          (by dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]; sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule]) (by simp only [arm64_norm, hrun1])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_53d00_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
          (herr_of_none (mergeMessage_toOption_of_lt VersionNegotiationPB.mergeField hdv hlt_len))
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by simp only [decodeStateErrFramePlaced, decodeStateErrFrame, arm64_norm]; ac_rfl))
      · have ⟨hult, hule⟩ := len_ult_of_ge hlt_len (by omega)
        have hsub_lim := bv_len_sub_limit hlt_len
        have hmm_eq := mergeMessage_toOption_of_ge protoPrefixStep_versionNegotiationPB_mergeField
          (m := vn) (depth' := 99) hdv hlt_len
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
        refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
          hrest1_le hrest1_suf hle2) (by sep_focus) ?_
        dsimp only [sliceCursorAfter]
        wp_steps 4
        refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
          (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
          (st := ⟨some vn, optCh, inner⟩) hle2) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule]) (by simp only [arm64_norm, hrun1])
        refine decodeState_vn_loop_53980_placed (v27 := v27) hc x w0 optCh inner (rest2.length - len64.toNat)
          (by omega) hlen_bound s0 R post hpost hs0A
          (rest2.length - (rest2.length - len64.toNat)) vn rest2 _ _
          (Nat.le_refl _) hrest2_le hrest2_suf
          (fun hnone => herr_of_none (by rw [hmm_eq, hnone]; rfl))
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
          (by simp only [arm64_norm, htr1])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hsub_lim, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter]; rw [hsp1048]; ac_rfl) ?_
        intro vn' rest3 sf P' hloop_ok hrest3_le hrest3_suf hrest3_eq
        have hdrop : rest3 = rest2.drop len64.toNat :=
          suffix_eq_drop_of_len_eq hrest2_le hrest2_suf hlt_len hrest3_le hrest3_suf hrest3_eq
        have hle3_2 : rest3.length ≤ rest2.length := by omega
        have hle3_1 : rest3.length ≤ rest1.length := Nat.le_trans hle3_2 hle2
        have hsuf3_2 : IsDropSuffix rest2 rest3 := by
          unfold IsDropSuffix
          rw [hrest3_eq, Nat.sub_sub_self (Nat.not_lt.mp hlt_len)]
          exact hdrop
        have hsuf3_1 : IsDropSuffix rest1 rest3 :=
          suffix_trans hle2 hsuf2 hle3_2 hsuf3_2
        have hok_mm :
            (Proto.mergeMessage VersionNegotiationPB.mergeField
              .lengthDelimited vn rest1 100).toOption = some (vn', rest3) := by
          rw [hmm_eq, hloop_ok, ← hdrop]; rfl
        exact hdone vn' rest3 sf P' hok_mm hle3_1 hsuf3_1
    · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2352#64)
      wp_steps 2
      wp_if hcbz
      · exact absurd hcbz hx1_ne
      · wp_steps 1
        refine SepWP.fold (errFrame_parts_fold A x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
        refine SepWP.fold (protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A
          (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53dcc_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none (mergeMessage_toOption_of_decodeVarint_none VersionNegotiationPB.mergeField hdv))
          (by decide)
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by simp only [decodeStateErrFramePlaced, decodeStateErrFrame, arm64_norm]; ac_rfl))
  · have ⟨hbne, hbeq⟩ := wt64_ne_two_of_ne_lengthDelimited hwt
    subst hP
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1852#64)
    wp_steps 2
    refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A x rest1 rest1.length ⟨some vn, optCh, inner⟩ s0)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0, hbne, hbeq]) (by simp only [arm64_norm, hrun])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_53bd8_placed hc.toDecodeStateCalleeContractsPlaced x ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
      (herr_of_none (mergeMessage_toOption_of_ne_lengthDelimited VersionNegotiationPB.mergeField hwt))
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0, hbne, hbeq])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
      (by unfold decodeStateErrFramePlaced; simp only [arm64_norm]; ac_rfl))

/-- Outer loop tag-1 (`PqRatchetState::version_negotiation`, `+184`) reaching `entry + 1576`. -/
theorem decodeState_vn_entry_53554_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt)
        (optVn.getD default) rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
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
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hdone : ∀ (vn' : VersionNegotiationPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt)
        (optVn.getD default) rest1 100).toOption = some (vn', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
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
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length ⟨some vn', optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  cases optVn with
  | none =>
    subst hP
    unfold protoPqRatchetStateCapOkAt optVersionNegotiationPBCapOkAt
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, Option.getD] at hpc herr_of_none hdone ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 216#64)
    refine SepWP.fold (optVersionNegotiationPB_none_split40 (s0.sp - 1040#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps 8
    refine SepWP.fold (versionNegotiationPBCapOkAt_default_init A (s0.sp - 1040#64) rest1.length)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_vn_merge_53574_placed (v27 := v27) hc x w0 default optCh inner rest1 iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
      (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
      (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
      (by unfold protoPqRatchetStateCapOkAt optVersionNegotiationPBCapOkAt; ac_rfl)
      hdone
  | some vn =>
    subst hP
    rw [protoPqRatchetStateCapOkAt_some_vn_eq]
    unfold vecU8CapOkAt
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, Option.getD] at hpc herr_of_none hdone ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 216#64)
    wp_pull_exists
    rename_i cap ptr
    wp_focus_pure; intro hcap
    rw [vecU8At_eq_header_heap]
    refine SepWP.fold (vecU8Heap_cap_lt A cap ptr vn.authKey) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    unfold vecHeader
    have hcmn : (cap + 1#64 != 0#64) = true := by
      rw [bne_iff_ne, ← beq_eq_false_iff_ne, Bool.eq_false_iff]
      exact cap_add_one_beq_zero_false hcap_lt
    wp_steps 3
    refine SepWP.fold (vecU8At_header_fold A (s0.sp - 1040#64) cap ptr vn.authKey rest1.length hcap)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcmn]) (by simp only [arm64_norm, hrun])
    exact decodeState_vn_merge_53574_placed (v27 := v27) hc x w0 vn optCh inner rest1 iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hcmn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
      (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
      (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
      (by rw [protoPqRatchetStateCapOkAt_some_vn_eq]; ac_rfl)
      hdone

end CryptoVerification.SpqrV1.Top.DecodeState
