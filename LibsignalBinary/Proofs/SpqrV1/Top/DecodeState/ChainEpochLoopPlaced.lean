/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Relocatable `ChainEpochPB` Merge Loop

Relocatable `[LibsignalPlacement]` proofs of `ChainEpochPB` tag dispatch (`+1036`), loop body (`+996`),
merge loop (`+984`), and length-delimited entry (`+600`).
-/

@[expose] public section

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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] truncate32_zeroExtend64_lsr3

/-! ## Framing Helper After `decode_varint` Inside `ChainEpochPB` Loop -/

theorem after_decodeVarint2_to_epochErrFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (x : DecodeStateGhost) {cur rest1 : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hle1 : rest1.length ≤ cur.length)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64)
        (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0 := by
  have hj := sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr) hcur_le hcur_suf hle1
  have hreord :
      sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) cur.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 =
      ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) cur.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hj) ?_
  exact epochLoop_cursor_to_epochErrFrame_placed H_inner A x rest1 cur.length cur.length curSt curEpoch s0

theorem after_decodeVarint2_err_to_epochErrFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0 := by
  have hep := chainEpochPBCapOkAt_entails_chainEpochPBAt A (s0.sp - 688#64) cur.length curEpoch
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hep))))) ?_
  exact epochLoop_calleeErr_to_epochErrFrame_placed H_inner A x hcur_le hcur_suf cur.length curSt curEpoch s0

/-! ## Tag Dispatch and Single Loop Iteration of `ChainEpochPB::merge` -/

/-- Tag dispatch for `ChainEpochPB` at `+1036` given `1 ≤ tag < 2 ^ 29`. -/
theorem decodeState_epoch_dispatch_538a8_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (match (ChainEpochPB.mergeField curEpoch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 98).toOption with
       | none => none
       | some (ep', rest2) => mergeLoopBin ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2 limitEpoch 98) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1036#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hnext : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (ChainEpochPB.mergeField curEpoch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 98).toOption =
        some (ep', rest2) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
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
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1108#64)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    refine decodeState_epoch_send_538f0_placed (v20 := v20) hc x curSt curEpoch rest1 limitEpoch iwt
      hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by
        rw [show BitVec.ofNat 32 1 = 1#32 from rfl, chainEpochPB_mergeField_tag1, hnone]; rfl))
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
    intro d' rest2 sf P' hed hle2 hsuf2 hpc'
    exact hnext { curEpoch with send := some d' } rest2 sf P' hle2 hsuf2
      (by rw [show BitVec.ofNat 32 1 = 1#32 from rfl, chainEpochPB_mergeField_tag1, hed]; rfl) hpc'
  · by_cases htag2 : tag = 2
    · subst htag2
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1052#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      refine decodeState_epoch_recv_538b8_placed (v20 := v20) hc x curSt curEpoch rest1 limitEpoch iwt
        hrest1_le hrest1_suf hlen_bound
        (fun hnone => herr_of_none (by
          rw [show BitVec.ofNat 32 2 = 2#32 from rfl, chainEpochPB_mergeField_tag2, hnone]; rfl))
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
      intro d' rest2 sf P' hed hle2 hsuf2 hpc'
      exact hnext { curEpoch with recv := some d' } rest2 sf P' hle2 hsuf2
        (by rw [show BitVec.ofNat 32 2 = 2#32 from rfl, chainEpochPB_mergeField_tag2, hed]; rfl) hpc'
    · -- tag >= 3 -> +964
      have ⟨_, _, _, _, hbeq1, hbne1⟩ := tag_cmp32_of_gt (c := 1) (by omega) htag29
      have ⟨_, _, _, _, hbeq2, hbne2⟩ := tag_cmp32_of_gt (c := 2) (by omega) htag29
      have htw32 := tag_setWidth32_ofNat tag
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 964#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm, hx1, htw32, hbeq1, hbne1, hbeq2, hbne2])
        (by simp only [arm64_norm, hrun])
      refine decodeState_epoch_skip_53860_placed (v20 := v20) hc.toDecodeStateCalleeContractsPlaced x curSt curEpoch rest1 limitEpoch tag iwt
        ⟨by omega, by omega⟩ hrest1_le hrest1_suf hlen_bound
        (fun hnone => herr_of_none (by
          rw [chainEpochPB_mergeField_other curEpoch tag htag1 htag2 (by omega) iwt rest1 98, hnone]; rfl))
        s0 _ _ R post hpost hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx1, htw32, hbeq1, hbne1, hbeq2, hbne2])
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
      exact hnext curEpoch rest2 sf P' hle2 hsuf2
        (by rw [chainEpochPB_mergeField_other curEpoch tag htag1 htag2 (by omega) iwt rest1 98, hsf]; rfl) hpc'

/-- One field-key decode + tag dispatch step of `ChainEpochPB` at `+996`,
when `¬ cur.length ≤ limitEpoch`. -/
theorem decodeState_epoch_body_53880_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (cur : List (BitVec 8)) (limitEpoch : Nat) (hgt : ¬ cur.length ≤ limitEpoch)
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 996#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hnext : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      rest2.length < cur.length → rest2.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest2 →
      mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 =
        mergeLoopBin ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2 limitEpoch 98 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
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
    (ret_pc := (blkPl_325).base + 1004#64)
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
    · -- key >= 2^32 -> +1872
      have hk_ne : (key >>> 32 == 0#64) = false := key_lsr32_ne_zero_of_ge hk
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1872#64)
      wp_steps 3
      refine SepWP.fold (after_decodeVarint2_to_epochErrFrame_placed H_inner A x hcur_le hcur_suf hle1
        curSt curEpoch s0)
        (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_ne]) (by simp only [arm64_norm, hrun1])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_key_overflow_53bec_placed hc.toDecodeStateCalleeContractsPlaced x curSt curEpoch s0 _ _ R post hpost
        (herr_of_none (mergeLoopBin_of_key_ge protoPrefixStep_chainEpochPB_mergeField hgt hdv hk))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_ne])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl))
    ·
      have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hk
      rcases hwt : WireType.ofNat? (key.toNat % 8) with _ | iwt
      · -- invalid wire type -> +1884
        rcases key_and7_of_wt_none hwt with hand7 | hand7
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1884#64)
          wp_steps 6
          refine SepWP.fold (after_decodeVarint2_to_epochErrFrame_placed H_inner A x hcur_le hcur_suf hle1
            curSt curEpoch s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7]) (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_invalid_wt_53bf8_placed hc.toDecodeStateCalleeContractsPlaced x curSt curEpoch s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_wt_none protoPrefixStep_chainEpochPB_mergeField hgt hdv hk hwt))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by ac_rfl))
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1884#64)
          wp_steps 6
          refine SepWP.fold (after_decodeVarint2_to_epochErrFrame_placed H_inner A x hcur_le hcur_suf hle1
            curSt curEpoch s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7]) (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_invalid_wt_53bf8_placed hc.toDecodeStateCalleeContractsPlaced x curSt curEpoch s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_wt_none protoPrefixStep_chainEpochPB_mergeField hgt hdv hk hwt))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by ac_rfl))
      ·
        have hand7 : key &&& 7#64 = BitVec.ofNat 64 iwt.toNat := key_and7_of_wt_some hwt
        have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 iwt
        have hlsr3 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) := key_lsr3_32_eq hk
        have htag29 : key.toNat / 8 < 2 ^ 29 := tag_lt_pow29_of_key_lt hk
        have hze : BitVec.zeroExtend 64 (BitVec.ofNat 32 (key.toNat / 8)) = BitVec.ofNat 64 (key.toNat / 8) :=
          tag_zeroExtend64_ofNat32 htag29
        have htw32 : BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) = BitVec.ofNat 32 (key.toNat / 8) :=
          tag_setWidth32_ofNat (key.toNat / 8)
        by_cases htag0 : key.toNat / 8 < 1
        · -- tag == 0 -> +1896
          have htag_eq0 : key.toNat / 8 = 0 := by omega
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1896#64)
          wp_steps 8
          refine SepWP.fold (after_decodeVarint2_to_epochErrFrame_placed H_inner A x hcur_le hcur_suf hle1
            curSt curEpoch s0)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_zero_tag_53c04_placed hc.toDecodeStateCalleeContractsPlaced x curSt curEpoch s0 _ _ R post hpost
            (herr_of_none (mergeLoopBin_of_tag_zero protoPrefixStep_chainEpochPB_mergeField hgt hdv hk hwt htag0))
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by ac_rfl))
        · -- tag >= 1 -> +1036
          have hloop_step := mergeLoopBin_of_key_ok protoPrefixStep_chainEpochPB_mergeField
            (m := curEpoch) (depth' := 98) hgt hdv hk hwt htag0
          have hcbz64 := tag_cbz64_false (by omega : 1 ≤ key.toNat / 8) htag29
          have hcbz32 := tag_cbz32_false (by omega : 1 ≤ key.toNat / 8) htag29
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1036#64)
          wp_steps 8
          refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
            hcur_le hcur_suf hle1) (by sep_focus) ?_
          refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
            (a := s0.sp - 1040#64) (rem1 := cur.length) (rem2 := rest1.length)
            (st := curSt) hle1) (by sep_focus) ?_
          refine SepWP.fold (chainEpochPBCapOkAt_mono (A := A)
            (a := s0.sp - 688#64) (rem1 := cur.length) (rem2 := rest1.length)
            (ep := curEpoch) hle1) (by sep_focus) ?_
          apply SepWP.done
            (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1])
          refine decodeState_epoch_dispatch_538a8_placed (v20 := v20) hc x curSt curEpoch rest1 limitEpoch (key.toNat / 8) iwt
            (by omega) htag29 hrest1_le hrest1_suf hlen_bound
            (fun hnone => herr_of_none (by
              rw [hloop_step]
              revert hnone
              rcases (curEpoch.mergeField (BitVec.ofNat 32 (key.toNat / 8)) (codecWireTypeToProto iwt) rest1 98).toOption with _ | ⟨_, _⟩ <;>
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
          intro ep' rest2 sf P' hle2 hsuf2 hmf
          exact hnext ep' rest2 sf P'
            (Nat.lt_of_le_of_lt hle2 hlt1) (Nat.le_trans hle2 hrest1_le)
            (suffix_trans hrest1_le hrest1_suf hle2 hsuf2) (by rw [hloop_step, hmf])
  · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1916#64)
    wp_steps 1
    have hfold := after_decodeVarint2_err_to_epochErrFrame_placed H_inner A x hcur_le hcur_suf curSt curEpoch s0
    dsimp only [decodeStateLoopCommonPlaced] at hfold
    refine SepWP.fold hfold (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_1]) (by simp only [arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_drop_epoch_53c18_placed hc.toDecodeStateCalleeContractsPlaced x curSt curEpoch 0 (by decide)
      (s1.readReg64 (Reg.gpr 1#5)) s0 _ _ R post hpost
      (herr_of_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chainEpochPB_mergeField hgt hdv))
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl))

/-! ## Full `ChainEpochPB` Merge Loop (`+984`) -/

/-- Inlined `ChainEpochPB` merge loop at `+984`, proved by induction on `fuel`. -/
theorem decodeState_epoch_loop_53874_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState)
    (limitEpoch : Nat) (hlim_bound : limitEpoch < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R) (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (curEpoch : ChainEpochPB) (cur : List (BitVec 8)) (s : State) (P : SepProp),
      cur.length - limitEpoch ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      (mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      s.pc = decodeStatePlacedEntry + 984#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → s.readReg64 .x28 = 1#64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) cur.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 →
      (∀ (ep' : ChainEpochPB) (rest : List (BitVec 8)) (sf : State) (P' : SepProp),
        mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = some ep' →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limitEpoch →
        sf.pc = decodeStatePlacedEntry + 624#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
        sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
        sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
        sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest.length curSt ∗
          chainEpochPBCapOkAt A (s0.sp - 688#64) rest.length ep' ∗
          memRegion (s0.sp - 576#64) 240 ∗
          decodeStateLoopCommonPlaced A x s0 →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlaced H_inner A x s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  intro fuel
  induction fuel with
  | zero =>
    intro curEpoch cur s P hfuel hcur_le hcur_suf herr_of_none
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone
    have hle : cur.length ≤ limitEpoch := by omega
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    subst hP
    dsimp only [decodeStatePlacedEntry, decodeStatePlacedProg, sliceCursorAfter] at hpc ⊢
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq heq
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 624#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq]) (by simp only [arm64_norm, hrun])
      exact hdone curEpoch cur _ _
        (mergeLoopBin_eq_limit ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 heq)
        hcur_le hcur_suf heq (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29]) (by dsimp only [sliceCursorAfter])
    · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
      have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2972#64)
      wp_steps 5
      refine SepWP.fold (epochLoop_cursor_to_epochErrFrame_placed H_inner A x cur cur.length cur.length curSt curEpoch s0)
        (by dsimp only [sliceCursorAfter]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne]) (by simp only [arm64_norm, hrun])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_corrupt_54038_placed hc.toDecodeStateCalleeContractsPlaced x curSt curEpoch s0 _ _ R post hpost
        (herr_of_none (mergeLoopBin_lt_limit ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 hlt))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx29]) (by ac_rfl))
  | succ fuel ih =>
    intro curEpoch cur s P hfuel hcur_le hcur_suf herr_of_none
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    by_cases hle : cur.length ≤ limitEpoch
    · subst hP
      dsimp only [decodeStatePlacedEntry, decodeStatePlacedProg, sliceCursorAfter] at hpc ⊢
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq heq
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 624#64)
        wp_steps 4
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq]) (by simp only [arm64_norm, hrun])
        exact hdone curEpoch cur _ _
          (mergeLoopBin_eq_limit ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 heq)
          hcur_le hcur_suf heq (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
          (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx28])
          (by simp only [arm64_norm, hx29]) (by dsimp only [sliceCursorAfter])
      · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
        have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2972#64)
        wp_steps 5
        refine SepWP.fold (epochLoop_cursor_to_epochErrFrame_placed H_inner A x cur cur.length cur.length curSt curEpoch s0)
          (by dsimp only [sliceCursorAfter]; sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne]) (by simp only [arm64_norm, hrun])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_corrupt_54038_placed hc.toDecodeStateCalleeContractsPlaced x curSt curEpoch s0 _ _ R post hpost
          (herr_of_none (mergeLoopBin_lt_limit ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 hlt))
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
          (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx29]) (by ac_rfl))
    · -- ¬ cur.length ≤ limitEpoch -> step to +996
      have ⟨hult, hule⟩ := cmp_len_limit_of_gt hle (by omega)
      subst hP
      dsimp only [decodeStatePlacedEntry, decodeStatePlacedProg, sliceCursorAfter] at hpc ⊢
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 996#64)
      wp_steps 3
      apply SepWP.done (by simp only [arm64_norm, hult, hule]) (by simp only [arm64_norm, hrun])
      refine decodeState_epoch_body_53880_placed (v20 := v20) hc x curSt curEpoch cur limitEpoch
        hle hcur_le hcur_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
        (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
        (by dsimp only [sliceCursorAfter]) ?_
      intro ep' rest2 sf P' hlt2 hle2 hsuf2 hmerge_eq
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
      exact ih ep' rest2 sf P' (by omega) hle2 hsuf2
        (fun hnone => herr_of_none (by rw [hmerge_eq, hnone]))
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
        (fun ep'' rest3 sf' P'' hok => hdone ep'' rest3 sf' P'' (by rw [hmerge_eq, hok]))

/-! ## Delimited `ChainEpochPB::merge` Entry (`+600`) -/

private theorem epoch_scratch_split_recv_240 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      ∃∗ w_recv : BitVec 64,
        memRegion (sp - 680#64) 48 ∗
        ((sp - 632#64) ↦₆₄ w_recv) ∗
        memRegion (sp - 624#64) 48 ∗
        memRegion (sp - 576#64) 240 := by
  have hs1 := ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
    (b' := sp - 632#64) rfl (by bv_omega) (by decide)
  have hs2 := ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 288)
    (b' := sp - 624#64) rfl (by bv_omega) (by decide)
  have hs3 := ProofLib.memRegion_split' (b := sp - 624#64) (n := 48) (k := 240)
    (b' := sp - 576#64) rfl (by bv_omega) (by decide)
  have hj := ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
    (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  rw [hs1, hs2, hs3, ProofLib.memRegion_eight (sp - 632#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w_recv
  refine Entails.sepExists_right w_recv ?_
  rw [hj]
  exact Entails.of_eq (by ac_rfl)

private theorem chainEpochPBCapOkAt_default_init (A : RustAlloc) (sp : BitVec 64) (remLen : Nat) :
    ((sp - 688#64) ↦₆₄ -1#64) ∗ memRegion (sp - 680#64) 48 ∗
      ((sp - 632#64) ↦₆₄ -1#64) ∗ memRegion (sp - 624#64) 48 ⊢
      chainEpochPBCapOkAt A (sp - 688#64) remLen default := by
  rw [chainEpochPB_default_eq, chainEpochPBCapOkAt_eq_placed]
  unfold optEpochDirectionPBCapOkAt
  dsimp only
  have ha1 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  have ha2 : sp - 632#64 + 8#64 = sp - 624#64 := by bv_omega
  have hnc : (-1#64 : BitVec 64) = noneCap := rfl
  rw [ha1, ha2, hnc]
  exact Entails.of_eq (by ac_rfl)

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

/-- Delimited `ChainEpochPB::merge` entry at `+600`, after `x0 = 2` has been checked,
reaching `+624` with the merged `ChainEpochPB` at `s0.sp - 688#64`. -/
theorem decodeState_epoch_merge_536f4_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8))
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hdone : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption =
        some (ep', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 624#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hdv_call := hc.decodeVarint2
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hdv_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  refine SepWP.fold (epoch_scratch_split_recv_240 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps 4
  refine SepWP.fold (chainEpochPBCapOkAt_default_init A s0.sp rest1.length) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
  refine SepWPpIPlaced.call_decodeVarint2 hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := (blkPl_325).base + 616#64)
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
    · -- rest2.length < len64 -> +2956
      have ⟨hult, hule⟩ := len_ult_of_lt hlt_len
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2956#64)
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      dsimp only [sliceCursorAfter]
      wp_steps 5
      refine SepWP.fold (epochLoop_cursor_to_epochErrFrame_placed H_inner A x rest2 rest1.length rest1.length
        curSt default s0)
        (by dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule]) (by simp only [arm64_norm, hrun1])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_truncated_54028_placed hc.toDecodeStateCalleeContractsPlaced x curSt default s0 _ _ R post hpost
        (herr_of_none (mergeMessage_toOption_of_lt ChainEpochPB.mergeField hdv hlt_len))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl))
    · -- rest2.length >= len64 -> +984
      have ⟨hult, hule⟩ := len_ult_of_ge hlt_len (by omega)
      have hsub_lim := bv_len_sub_limit hlt_len
      have hmm_eq := mergeMessage_toOption_of_ge protoPrefixStep_chainEpochPB_mergeField
        (m := default) (depth' := 98) hdv hlt_len
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      dsimp only [sliceCursorAfter]
      wp_steps 4
      refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
        (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
        (st := curSt) hle2) (by sep_focus) ?_
      refine SepWP.fold (chainEpochPBCapOkAt_mono (A := A)
        (a := s0.sp - 688#64) (rem1 := rest1.length) (rem2 := rest2.length)
        (ep := default) hle2) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule]) (by simp only [arm64_norm, hrun1])
      refine decodeState_epoch_loop_53874_placed (v20 := v20) hc x curSt (rest2.length - len64.toNat)
        (by omega) hlen_bound s0 R post hpost hs0A
        (rest2.length - (rest2.length - len64.toNat)) default rest2 _ _
        (Nat.le_refl _) hrest2_le hrest2_suf
        (fun hnone => herr_of_none (by rw [hmm_eq, hnone]; rfl))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
        (by simp only [arm64_norm, htr1])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsub_lim, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter]; rw [hsp1048]; ac_rfl) ?_
      intro ep' rest3 sf P' hloop_ok hrest3_le hrest3_suf hrest3_eq
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
          (Proto.mergeMessage ChainEpochPB.mergeField
            .lengthDelimited default rest1 99).toOption = some (ep', rest3) := by
        rw [hmm_eq, hloop_ok, ← hdrop]; rfl
      exact hdone ep' rest3 sf P' hok_mm hle3_1 hsuf3_1
  · intro s1 hdv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hcbz : (s1.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx1_ne
    have hcbnz : (s1.readReg64 (Reg.gpr 1#5) != 0#64) = true := bne_iff_ne.mpr hx1_ne
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1916#64)
    wp_steps 2
    have hfold := after_decodeVarint2_err_to_epochErrFrame_placed H_inner A x hrest1_le hrest1_suf curSt default s0
    dsimp only [decodeStateLoopCommonPlaced] at hfold
    refine SepWP.fold hfold (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_1, hcbz, hcbnz]) (by simp only [arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_drop_epoch_53c18_placed hc.toDecodeStateCalleeContractsPlaced x curSt default 0 (by decide)
      (s1.readReg64 (Reg.gpr 1#5)) s0 _ _ R post hpost
      (herr_of_none (mergeMessage_toOption_of_decodeVarint_none ChainEpochPB.mergeField hdv))
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_1, hcbz, hcbnz])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl))

end CryptoVerification.SpqrV1.Top.DecodeState
