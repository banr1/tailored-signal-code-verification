/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExact
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedA
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlaced
import ProofLib.SepLogic.WPp

/-!
# Relocatable `encode<PolynomialDecoder> [local#3]` Verification (Block `455`)

Proves `2^60`-cap (`encode_polyDecoder_1_{pinned_,}placed_ok*`) and exact `2^59`-cap
(`encode_polyDecoder_1_exact_pinned_placed_ok*`, `etv_polyDecoderEncode_1_exact_placed_ok*`)
contracts on CLI Block `455` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Prost.MessageEncode CryptoVerification.Cli.SpqrV1.Alloc.Placed
  CryptoVerification.Cli.SpqrV1.Varint.Placed CryptoVerification.Cli.SpqrV1.Varint
  CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced
  CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (encodeRepeated59SpecOf encodePolyDecoderExactSpecOf etvPolyDecoderExactSpecOf
   etv_polyDecoderEncode_exact_of_lscl step_msg48_encode_repeated59_call_placed
   cap_beq_len_false_of_lt_placed)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

@[local arm64_norm] private theorem blkPl_451_base_eq [LibsignalPlacement] : (blkPl_451).base = lsmpl.base 451 := rfl
@[local arm64_norm] private theorem blkPl_460_base_eq [LibsignalPlacement] : (blkPl_460).base = lsmpl.base 460 := rfl
@[local arm64_norm] private theorem blkPl_448_base_eq [LibsignalPlacement] : (blkPl_448).base = lsmpl.base 448 := rfl
@[local arm64_norm] private theorem blkPl_493_base_eq [LibsignalPlacement] : (blkPl_493).base = lsmpl.base 493 := rfl

/-! ## Part 1: `2^60` Cap (`encodePolyDecoderPinnedSpec[X]` & `encodePolyDecoderSpec[X]`) -/

private theorem step_ptsNeeded_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_pn : curBs.length + (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length ≤ curCap.toNat ∨
      curBs.length + (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 56#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 108#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At A v nextCap nextPtr (curBs ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_polyDecoder_check_ptsNeeded_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hpn : (pb.ptsNeeded == 0#32)
  · simp only [hpn, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pn, hge2_pn⟩ := ptsNeeded_field_len_of_ne_zero pb hpn
    refine step_reserve_64_1_placed hres A H hdoReserve decA v curCap curPtr sp curBs pb (by omega)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx19_1 hx20_1 hcs1
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F) (by ac_rfl) ?_
    intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2 hlt01 hge01 hpres01
    refine step_polyDecoder_push_ptsNeeded_tag_placed A H decA v cap01 ptr01 sp curBs pb hlt01
      hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x08#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.ptsNeeded.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x08#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_pn with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    refine step_msg48rep_encode_varint_call_placed hres A hencVarint
      (pb.ptsNeeded.zeroExtend 64) v cap01 ptr01 sp ((blkPl_455).base + 108#64) (curBs ++ [0x08#8]) hfit_v
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_ptsNeeded_of_ne_zero curBs pb hpn]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 (Nat.le_trans hge01 hge1) ?_)
    intro hle
    obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
    exact hpres1 (by rw [List.length_append, List.length_singleton]; omega)
  · simp only [hpn, ↓reduceIte] at hpc1
    rw [← bs_append_ptsNeeded_of_zero curBs pb hpn]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 curCap curPtr hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_polys_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_pl : curBs.length + (Proto.encodeUint32Field 2#32 pb.polys).length ≤ curCap.toNat ∨
      curBs.length + (Proto.encodeUint32Field 2#32 pb.polys).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 160#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Proto.encodeUint32Field 2#32 pb.polys).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At A v nextCap nextPtr (curBs ++ Proto.encodeUint32Field 2#32 pb.polys) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_polyDecoder_check_polys_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hpl : (pb.polys == 0#32)
  · simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pl, hge2_pl⟩ := polys_field_len_of_ne_zero pb hpl
    refine step_reserve_116_1_placed hres A H hdoReserve decA v curCap curPtr sp curBs pb (by omega)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx19_1 hx20_1 hcs1
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F) (by ac_rfl) ?_
    intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2 hlt01 hge01 hpres01
    refine step_polyDecoder_push_polys_tag_placed A H decA v cap01 ptr01 sp curBs pb hlt01
      hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x10#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.polys.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x10#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_pl with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    refine step_msg48rep_encode_varint_call_placed hres A hencVarint
      (pb.polys.zeroExtend 64) v cap01 ptr01 sp ((blkPl_455).base + 160#64) (curBs ++ [0x10#8]) hfit_v
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_polys_of_ne_zero curBs pb hpl]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 (Nat.le_trans hge01 hge1) ?_)
    intro hle
    obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
    exact hpres1 (by rw [List.length_append, List.length_singleton]; omega)
  · simp only [hpl, ↓reduceIte] at hpc1
    rw [← bs_append_polys_of_zero curBs pb hpl]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 curCap curPtr hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_pts_isComplete_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hencRep : subroutine_ok (lsProg_455 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (decA v curCap curPtr sp sv3 : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts_lt : pb.pts.length < 2 ^ 58)
    (hfit_pts : curBs.length + (encodeRepeatedBytes 3 pb.pts).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes 3 pb.pts).length + 10 < 2 ^ 62)
    (hfit_ic : ∀ nextCap : BitVec 64,
      (curBs.length + (encodeRepeatedBytes 3 pb.pts).length ≤ curCap.toNat → nextCap = curCap) →
      (curBs ++ encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length ≤ nextCap.toNat ∨
      (curBs ++ encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length + 10 < 2 ^ 62)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        vecU8At A v nextCap nextPtr
          ((curBs ++ encodeRepeatedBytes 3 pb.pts) ++ Proto.encodeBoolField 4#32 pb.isComplete) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_455 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  refine step_polyDecoder_prep_pts_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_msg48_encode_repeated_call_placed A hencRep 3 g.pts.ptr v curCap curPtr sp
    ((blkPl_455).base + 176#64) ptsElems curBs (by decide) (by decide) (by omega) (by rw [hpts_eq]; exact hfit_pts)
    (F := ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((decA + 28#64) ↦₃₂ pb.polys) ∗
      ((decA + 32#64) ↦₈ SpqrV1.Poly.boolByte pb.isComplete) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by dsimp only [polyDecoderElemsAt]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  rw [hpts_eq] at hpres2 ⊢
  let bs_pts := curBs ++ encodeRepeatedBytes 3 pb.pts
  refine step_polyDecoder_check_isComplete_placed hres H decA v sp sv3 g pb ptsElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At A v cap2 ptr2 bs_pts ∗ A.pool ∗ F)
    (by dsimp only [polyDecoderElemsAt, bs_pts]; ac_rfl) ?_ ?_
  · intro hc sf hpcf hrunf hspf htrf hccf hcsf
    have hq := hnext sf cap2 ptr2 hpcf hrunf hspf htrf hccf hcsf hge2 (fun hle => by
      rw [hc, protoEncodeBoolField_4_false, List.length_nil] at hle
      exact hpres2 (by omega))
    rw [hc, bs_append_boolField_4_false bs_pts] at hq
    have hEq :
        ((polyDecoderElemsAt decA g pb ptsElems ∗ vecU8At A v cap2 ptr2 bs_pts ∗
          A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (vecU8At A v cap2 ptr2 bs_pts ∗ A.pool ∗ F)) := by ac_rfl
    rwa [← hEq]
  · intro hc s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
    have hfit_ic2 := hfit_ic cap2 (fun h => (hpres2 h).1)
    have hlen_ic : (Proto.encodeBoolField 4#32 pb.isComplete).length = 2 := by
      rw [hc, protoEncodeBoolField_4_true]; rfl
    have hbs_pts_len : bs_pts.length = (curBs ++ encodeRepeatedBytes 3 pb.pts).length := rfl
    refine step_reserve_188_1_placed hres128 A H hdoReserve decA v cap2 ptr2 sp bs_pts
      (by rcases hfit_ic2 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
      hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by ac_rfl) ?_
    intro s4 cap3 ptr3 hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4 hlt3 hge3 hpres3
    refine step_polyDecoder_push_isComplete_tag_placed A H decA v cap3 ptr3 sp bs_pts hlt3
      hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4
      (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt decA g pb ptsElems ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by ac_rfl) ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5
    have hfit_val : (bs_pts ++ [0x20#8]).length + 1 ≤ cap3.toNat ∨
        (bs_pts ++ [0x20#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_ic2 with h | h
      · left; obtain ⟨rfl, _⟩ := hpres3 (by omega); omega
      · right; omega
    refine step_reserve_228_1_placed hres128 A H hdoReserve decA v cap3 ptr3 sp
      (bs_pts ++ [0x20#8]) hfit_val
      hpc5 hrun5 hsp5 halign htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by ac_rfl) ?_
    intro s6 cap4 ptr4 hpc6 hrun6 hsp6 htr6 hx9_6 hx10_6 hx19_6 _ hcs6 hlt4 hge4 hpres4
    refine step_polyDecoder_push_isComplete_val_epilogue_placed hres A H v cap4 ptr4 sp sv3
      (bs_pts ++ [0x20#8]) hlt4 hpc6 hrun6 hsp6 halign htr6 hx9_6 hx10_6 hx19_6 hcs6
      (F := A.pool ∗ polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by ac_rfl) ?_
    intro sf hpcf hrunf hspf htrf hccf hcsf
    have hq := hnext sf cap4 ptr4 hpcf hrunf hspf htrf hccf hcsf
      (Nat.le_trans hge2 (Nat.le_trans hge3 hge4)) (fun hle => by
        obtain ⟨rfl, rfl⟩ := hpres2 (by omega)
        obtain ⟨rfl, rfl⟩ := hpres3 (by dsimp [bs_pts]; rw [List.length_append]; omega)
        exact hpres4 (by dsimp [bs_pts]; rw [List.length_append, List.length_append, List.length_singleton]; omega))
    rw [hc, ← bs_append_boolField_4_true bs_pts] at hq
    have hEq :
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At A v cap4 ptr4 ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((vecU8At A v cap4 ptr4 ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (A.pool ∗ polyDecoderElemsAt decA g pb ptsElems ∗ F)) := by ac_rfl
    rwa [← hEq]

theorem polyDecoder1_gen_placed_ok [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {A : RustAlloc} {H : String → Option (State → State)}
    {x : EncodePolyDecoderPinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (lsProg_455 H) (blkPl_493).base
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (hencV : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hencR : subroutine_ok (lsProg_455 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (hdoR : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (hpc : s0.pc = (blkPl_455).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_455 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyDecoderPinnedSpec A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyDecoderPinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hx1, hx2, hpts58, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyDecoderMsg_len_split x.tag x.dec
  have hlen_le_msg := polynomialDecoderPBEncodedLen_le_msg_len x.tag x.dec
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialDecoderPBEncodedLen x.dec < 2 ^ 64 := by rcases hfit with h | h <;> omega
  have hfit_hdr : x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length ≤ x.cap.toNat ∨
      x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_hdr_1_placed hres A H hencLen hencV x.tag x.decA x.v x.cap x.ptr s0.sp x.g x.dec x.bs
    hlen_lt hfit_hdr (F := emp) rfl hpc hrun rfl halign rfl hw0 hx1 hx2 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 cap1 ptr1 ptsElems hpts_eq hpts_lt hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hge1 hpres1
  let bs_hdr := x.bs ++ polyDecoderHeaderBytes x.tag x.dec
  have hfit_pn : bs_hdr.length + (Proto.encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤ cap1.toNat ∨
      bs_hdr.length + (Proto.encodeUint32Field 1#32 x.dec.ptsNeeded).length + 10 < 2 ^ 62 := by
    dsimp [bs_hdr]; rw [List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega); omega
    · right; omega
  refine step_ptsNeeded_1_placed hres128 A H hencV hdoR x.decA x.v cap1 ptr1 s0.sp x.g x.dec
    ptsElems bs_hdr hfit_pn hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗ msgEnc48SavedFrame s0.sp (s0.readReg64 .fp)
      (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by dsimp [bs_hdr]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2
  let bs_pn := bs_hdr ++ Proto.encodeUint32Field 1#32 x.dec.ptsNeeded
  have hfit_pl : bs_pn.length + (Proto.encodeUint32Field 2#32 x.dec.polys).length ≤ cap2.toNat ∨
      bs_pn.length + (Proto.encodeUint32Field 2#32 x.dec.polys).length + 10 < 2 ^ 62 := by
    dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by dsimp [bs_hdr]; rw [List.length_append]; omega); omega
    · right; omega
  refine step_polys_1_placed hres128 A H hencV hdoR x.decA x.v cap2 ptr2 s0.sp x.g x.dec
    ptsElems bs_pn hfit_pl hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗ msgEnc48SavedFrame s0.sp (s0.readReg64 .fp)
      (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp) rfl ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hge3 hpres3
  let bs_pl := bs_pn ++ Proto.encodeUint32Field 2#32 x.dec.polys
  have hfit_pts : bs_pl.length + (encodeRepeatedBytes 3 x.dec.pts).length ≤ cap3.toNat ∨
      bs_pl.length + (encodeRepeatedBytes 3 x.dec.pts).length + 10 < 2 ^ 62 := by
    dsimp [bs_pl, bs_pn, bs_hdr]; rw [List.length_append, List.length_append, List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by dsimp [bs_hdr]; rw [List.length_append]; omega)
      obtain ⟨rfl, _⟩ := hpres3 (by dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega); omega
    · right; omega
  have hfit_ic : ∀ nextCap : BitVec 64,
      (bs_pl.length + (encodeRepeatedBytes 3 x.dec.pts).length ≤ cap3.toNat → nextCap = cap3) →
      (bs_pl ++ encodeRepeatedBytes 3 x.dec.pts).length +
        (Proto.encodeBoolField 4#32 x.dec.isComplete).length ≤ nextCap.toNat ∨
      (bs_pl ++ encodeRepeatedBytes 3 x.dec.pts).length +
        (Proto.encodeBoolField 4#32 x.dec.isComplete).length + 10 < 2 ^ 62 := by
    intro nextCap hpres_pts; dsimp [bs_pl, bs_pn, bs_hdr]
    rw [List.length_append, List.length_append, List.length_append, List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by dsimp [bs_hdr]; rw [List.length_append]; omega)
      obtain ⟨rfl, _⟩ := hpres3 (by dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega)
      have hnc := hpres_pts (by dsimp [bs_pl, bs_pn, bs_hdr]; rw [List.length_append, List.length_append, List.length_append]; omega)
      subst hnc; omega
    · right; omega
  refine step_pts_isComplete_1_placed hres A H hencR hdoR x.decA x.v cap3 ptr3 s0.sp sv3 x.g x.dec
    ptsElems bs_pl hpts_eq hpts58 hfit_pts hfit_ic hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗ emp) (by dsimp [bs_pl]; ac_rfl) ?_
  intro sf cap4 ptr4 hpcf hrunf hspf htrf hccf hcsf hge4 hpres4
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hge_all : x.cap.toNat ≤ cap4.toNat := Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 hge4))
  have hpres_all : x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
      cap4 = x.cap ∧ ptr4 = x.ptr := by
    intro hle; obtain ⟨rfl, rfl⟩ := hpres1 (by omega)
    obtain ⟨rfl, rfl⟩ := hpres2 (by dsimp [bs_hdr]; rw [List.length_append]; omega)
    obtain ⟨rfl, rfl⟩ := hpres3 (by dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega)
    exact hpres4 (by dsimp [bs_pl, bs_pn, bs_hdr]; rw [List.length_append, List.length_append, List.length_append]; omega)
  have hm_pack : sf.mem ⊨ (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      polyDecoderRestAt A x.decA x.g ptsElems) ∗
      (vecU8At A x.v cap4 ptr4 (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
        A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyDecoderMsg x.bs x.tag x.dec]
    convert hm using 1; dsimp [bs_pl, bs_pn, bs_hdr]; ac_rfl
  have hm_pinned := (satisfies_protoPolynomialDecoderPinnedAt_iff A x.g x.decA x.dec _ sf.mem).mpr
    ⟨ptsElems, hpts_eq, hpts_lt, hm_pack⟩
  dsimp only [encodePolyDecoderPinnedSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  rw [sepConj_left_comm (protoPolynomialDecoderPinnedAt A x.g x.decA x.dec)]
  simp only [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨cap4, ptr4, ?_⟩
  have hpure : (x.cap.toNat ≤ cap4.toNat ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat → cap4 = x.cap ∧ ptr4 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  rw [hpure, pure_true, emp_sepConj]; convert hm_pinned using 1; ac_rfl

theorem encode_polyDecoder_1_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpec A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := polyDecoder1_gen_placed_ok (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_of_plain_blk s0 hcl0
      (subroutine_ok_polyDecLenElemsOut_of_pinned
        (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H)))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_repeated_1_placed_ok h_panic hshim halloc hrealloc
        (show HookSat H spqrMemcpySym framelessMemcpySpec from hmc)))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyDecoder_1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderSpec A)) :=
  polyDecoder_unpinned_of_pinned_placed_x
    (encode_polyDecoder_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_polyDecoder_1_pinned_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecX A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := polyDecoder1_gen_placed_ok (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_of_plain_blk s0 hcl0
      (subroutine_ok_polyDecLenElemsOut_of_pinned
        (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H)))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_repeated_1_placed_ok_x h_panic hshim halloc hrealloc
        (show HookSat H spqrMemcpySym framelessMemcpySpec from hmc)))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyDecoder_1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderSpecX A)) :=
  polyDecoder_unpinned_of_pinned_placed_x
    (encode_polyDecoder_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem encode_polyDecoder_1_pinned_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    EncodePolyDecoder1PinnedPlacedOkExt A ext :=
  encode_polyDecoder_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc

theorem encode_polyDecoder_1_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    EncodePolyDecoder1PlacedOkExt A ext :=
  encode_polyDecoder_1_placed_ok h_panic hshim halloc hrealloc hmc

theorem encode_polyDecoder_1_pinned_placed_ok_ext_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    EncodePolyDecoder1PinnedPlacedOkExtX A (Rust.withPanics ext) :=
  encode_polyDecoder_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc

theorem encode_polyDecoder_1_placed_ok_ext_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    EncodePolyDecoder1PlacedOkExtX A (Rust.withPanics ext) :=
  encode_polyDecoder_1_placed_ok_x h_panic hshim halloc hrealloc hmc

/-! ## Part 2: Exact `2^59` Cap (`encodePolyDecoderExactSpecOf` & `etvPolyDecoderExactSpecOf`) -/

private theorem step_pd1_hdr_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_455 H) (blkPl_493).base
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (tag : BitVec 32) (decA v cap0 ptr0 sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (bs0 : List (BitVec 8))
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_455).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialDecoderPinnedAt A g decA pb ∗
      vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64)
      (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_455).base + 56#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt A decA g ptsElems ∗
          vecU8At A v cap0 ptr0 (bs0 ++ polyDecoderHeaderBytes tag pb) ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge_key, hge2⟩ := polyDecoderHeaderBytes_len_bounds tag pb
  refine step_polyDecoder_prologue_placed hres H tag decA v sp hhs0 hpc hrun hsp halign htr
    hw0 hx1 hx2 hcs
    (F := protoPolynomialDecoderPinnedAt A g decA pb ∗ vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hfit_key : bs0.length +
      (LibsignalProtoCodec.encodeVarint (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)).length ≤ cap0.toNat := by
    rw [encodeVarint_polyDecoder_tag_eq_proto]; omega
  refine step_msg48rep_encode_varint_call_placed hres128 A hencVarint
    (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) v cap0 ptr0 sp
    ((blkPl_455).base + 40#64) bs0 (Or.inl hfit_key)
    (F := protoPolynomialDecoderPinnedAt A g decA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 _ hpres01
  obtain ⟨hc01, hp01⟩ := hpres01 hfit_key
  subst cap01 ptr01
  rw [encodeVarint_polyDecoder_tag_eq_proto]
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x0_x20_40_placed H decA v sp hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_493).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  refine step_msg48rep_polyDecLen_call_placed hres128 A hencLen decA sp ((blkPl_455).base + 48#64) g pb hlen_lt
    (F := vecU8At A v cap0 ptr0 (bs0 ++ Proto.encodeKey tag .lengthDelimited) ∗ A.pool ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv3)
    (by ac_rfl) ?_
  intro s4 ptsElems hpts_eq hpts_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x1_x19_48_placed H decA v
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
  have hfit_len : (bs0 ++ Proto.encodeKey tag .lengthDelimited).length +
      (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).length ≤ cap0.toNat := by
    rw [List.length_append]; omega
  refine step_msg48rep_encode_varint_call_placed hres128 A hencVarint
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) v cap0 ptr0 sp ((blkPl_455).base + 56#64)
    (bs0 ++ Proto.encodeKey tag .lengthDelimited) (Or.inl hfit_len)
    (F := polyDecoderElemsAt decA g pb ptsElems ∗
      polyDecoderRestAt A decA g ptsElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs5.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv5)
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 _ hpres1
  obtain ⟨rfl, rfl⟩ := hpres1 hfit_len
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = decA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [bs0_append_polyDecoderHeaderBytes bs0 tag pb]
  exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s6 sv3 ptsElems hpts_eq hpts_lt hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6)

private theorem step_pd1_ptsNeeded_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_pn : curBs.length + (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length ≤ curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 56#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 108#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At A v curCap curPtr (curBs ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_polyDecoder_check_ptsNeeded_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hpn : (pb.ptsNeeded == 0#32)
  · simp only [hpn, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pn, hge2_pn⟩ := ptsNeeded_field_len_of_ne_zero pb hpn
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := cap_beq_len_false_of_lt_placed hlt0
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 80#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    rw [← vecHeader, ← EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs]
    refine step_polyDecoder_push_ptsNeeded_tag_placed A H decA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ A.pool ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x08#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.ptsNeeded.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_msg48rep_encode_varint_call_placed hres A hencVarint
      (pb.ptsNeeded.zeroExtend 64) v curCap curPtr sp ((blkPl_455).base + 108#64) (curBs ++ [0x08#8]) (Or.inl hfit_v)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_ptsNeeded_of_ne_zero curBs pb hpn]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hpn, ↓reduceIte] at hpc1
    rw [← bs_append_ptsNeeded_of_zero curBs pb hpn]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

private theorem step_pd1_polys_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_pl : curBs.length + (Proto.encodeUint32Field 2#32 pb.polys).length ≤ curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 160#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At A v curCap curPtr (curBs ++ Proto.encodeUint32Field 2#32 pb.polys) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_polyDecoder_check_polys_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hpl : (pb.polys == 0#32)
  · simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pl, hge2_pl⟩ := polys_field_len_of_ne_zero pb hpl
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := cap_beq_len_false_of_lt_placed hlt0
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 132#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    rw [← vecHeader, ← EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs]
    refine step_polyDecoder_push_polys_tag_placed A H decA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ A.pool ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x10#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.polys.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_msg48rep_encode_varint_call_placed hres A hencVarint
      (pb.polys.zeroExtend 64) v curCap curPtr sp ((blkPl_455).base + 160#64) (curBs ++ [0x10#8]) (Or.inl hfit_v)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_polys_of_ne_zero curBs pb hpl]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hpl, ↓reduceIte] at hpc1
    rw [← bs_append_polys_of_zero curBs pb hpl]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

private theorem step_pd1_pts_isComplete_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (hencRep : subroutine_ok (lsProg_455 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeated59SpecOf resStack A)))
    (decA v curCap curPtr sp sv3 : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts_lt : pb.pts.length < 2 ^ 59)
    (hfit_rest : curBs.length + (encodeRepeatedBytes 3 pb.pts).length +
      (Proto.encodeBoolField 4#32 pb.isComplete).length ≤ curCap.toNat)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        vecU8At A v curCap curPtr
          ((curBs ++ encodeRepeatedBytes 3 pb.pts) ++ Proto.encodeBoolField 4#32 pb.isComplete) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_455 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  have hfit_pts : curBs.length + (encodeRepeatedBytes 3 pb.pts).length ≤ curCap.toNat := by omega
  refine step_polyDecoder_prep_pts_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_msg48_encode_repeated59_call_placed A hencRep 3 g.pts.ptr v curCap curPtr sp
    ((blkPl_455).base + 176#64) ptsElems curBs (by decide) (by decide) (by omega) (by rw [hpts_eq]; exact Or.inl hfit_pts)
    (F := ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((decA + 28#64) ↦₃₂ pb.polys) ∗
      ((decA + 32#64) ↦₈ SpqrV1.Poly.boolByte pb.isComplete) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by dsimp only [polyDecoderElemsAt]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 _ hpres2
  rw [hpts_eq] at hpres2 ⊢
  obtain ⟨hcap2, hptr2⟩ := hpres2 hfit_pts
  subst cap2 ptr2
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  let bs_pts := curBs ++ encodeRepeatedBytes 3 pb.pts
  refine step_polyDecoder_check_isComplete_placed hres H decA v sp sv3 g pb ptsElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At A v curCap curPtr bs_pts ∗ A.pool ∗ F)
    (by dsimp only [polyDecoderElemsAt, bs_pts]; ac_rfl) ?_ ?_
  · intro hc sf hpcf hrunf hspf htrf hccf hcsf
    have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
    rw [hc, bs_append_boolField_4_false bs_pts] at hq
    have hEq :
        ((polyDecoderElemsAt decA g pb ptsElems ∗ vecU8At A v curCap curPtr bs_pts ∗
          A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (vecU8At A v curCap curPtr bs_pts ∗ A.pool ∗ F)) := by ac_rfl
    rwa [← hEq]
  · intro hc s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
    have hlen_ic : (Proto.encodeBoolField 4#32 pb.isComplete).length = 2 := by
      rw [hc, protoEncodeBoolField_4_true]; rfl
    have hbs_pts_len : bs_pts.length = curBs.length + (encodeRepeatedBytes 3 pb.pts).length :=
      List.length_append
    have hlt3 : bs_pts.length < curCap.toNat := by omega
    refine step_reserve_188_1_exact_placed A H decA v curCap curPtr sp bs_pts hlt3
      hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        A.pool ∗ F)
      (by ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4
    refine step_polyDecoder_push_isComplete_tag_placed A H decA v curCap curPtr sp bs_pts hlt3
      hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        A.pool ∗ F)
      (by ac_rfl) ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5
    have hlt4 : (bs_pts ++ [0x20#8]).length < curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_reserve_228_1_exact_placed A H decA v curCap curPtr sp (bs_pts ++ [0x20#8]) hlt4
      hpc5 hrun5 hsp5 htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        A.pool ∗ F)
      (by ac_rfl) ?_
    intro s6 hpc6 hrun6 hsp6 htr6 hx9_6 hx10_6 hx19_6 _ hcs6
    refine step_polyDecoder_push_isComplete_val_epilogue_placed hres A H v curCap curPtr sp sv3
      (bs_pts ++ [0x20#8]) hlt4 hpc6 hrun6 hsp6 halign htr6 hx9_6 hx10_6 hx19_6 hcs6
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ A.pool ∗ F)
      (by ac_rfl) ?_
    intro sf hpcf hrunf hspf htrf hccf hcsf
    have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
    rw [hc, ← bs_append_boolField_4_true bs_pts] at hq
    have hEq :
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At A v curCap curPtr ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((vecU8At A v curCap curPtr ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (polyDecoderElemsAt decA g pb ptsElems ∗ A.pool ∗ F)) := by ac_rfl
    rwa [← hEq]

theorem polyDecoder1_exact_gen_placed_ok [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks}
    {x : EncodePolyDecoderPinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (lsProg_455 H) (blkPl_493).base
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (hencV : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hencR : subroutine_ok (lsProg_455 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeated59SpecOf resStack A)))
    (hpc : s0.pc = (blkPl_455).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyDecoderExactSpecOf resStack A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_455 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyDecoderExactSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyDecoderExactSpecOf resStack A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyDecoderExactSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hx1, hx2, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyDecoderMsg_len_split x.tag x.dec
  have hlen_le_msg := polynomialDecoderPBEncodedLen_le_msg_len x.tag x.dec
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialDecoderPBEncodedLen x.dec < 2 ^ 64 := by omega
  refine step_pd1_hdr_exact_placed hres A H hencLen hencV x.tag x.decA x.v x.cap x.ptr s0.sp x.g x.dec x.bs
    hlen_lt (by omega) (F := emp) rfl hpc hrun rfl halign rfl hw0 hx1 hx2 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 ptsElems hpts_eq hpts_lt hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
  let bs_hdr := x.bs ++ polyDecoderHeaderBytes x.tag x.dec
  have hfit_pn : bs_hdr.length + (Proto.encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤ x.cap.toNat := by
    dsimp [bs_hdr]; rw [List.length_append]; omega
  refine step_pd1_ptsNeeded_exact_placed hres128 A H hencV x.decA x.v x.cap x.ptr s0.sp x.g x.dec
    ptsElems bs_hdr hfit_pn hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by dsimp [bs_hdr]; ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  let bs_pn := bs_hdr ++ Proto.encodeUint32Field 1#32 x.dec.ptsNeeded
  have hfit_pl : bs_pn.length + (Proto.encodeUint32Field 2#32 x.dec.polys).length ≤ x.cap.toNat := by
    dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega
  refine step_pd1_polys_exact_placed hres128 A H hencV x.decA x.v x.cap x.ptr s0.sp x.g x.dec
    ptsElems bs_pn hfit_pl hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    rfl ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
  let bs_pl := bs_pn ++ Proto.encodeUint32Field 2#32 x.dec.polys
  have hfit_rest : bs_pl.length + (encodeRepeatedBytes 3 x.dec.pts).length +
      (Proto.encodeBoolField 4#32 x.dec.isComplete).length ≤ x.cap.toNat := by
    dsimp [bs_pl, bs_pn, bs_hdr]; rw [List.length_append, List.length_append, List.length_append]; omega
  refine step_pd1_pts_isComplete_exact_placed hres A H hencR x.decA x.v x.cap x.ptr s0.sp sv3 x.g x.dec
    ptsElems bs_pl hpts_eq (by omega) hfit_rest
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗ emp) (by dsimp [bs_pl]; ac_rfl) ?_
  intro sf _ _ hspf htrf hccf _
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hm_pack : sf.mem ⊨ (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      polyDecoderRestAt A x.decA x.g ptsElems) ∗
      (vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
        A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyDecoderMsg x.bs x.tag x.dec]
    convert hm using 1; dsimp [bs_pl, bs_pn, bs_hdr]; ac_rfl
  have hm_pinned := (satisfies_protoPolynomialDecoderPinnedAt_iff A x.g x.decA x.dec _ sf.mem).mpr
    ⟨ptsElems, hpts_eq, hpts_lt, hm_pack⟩
  dsimp only [encodePolyDecoderExactSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm_pinned using 1; ac_rfl

theorem encode_polyDecoder_1_exact_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStack A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := polyDecoder1_exact_gen_placed_ok (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_of_plain_blk s0 hcl0
      (subroutine_ok_polyDecLenElemsOut_of_pinned
        (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H)))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_repeated_1_59_placed_ok h_panic hshim halloc hrealloc
        (show HookSat H spqrMemcpySym framelessMemcpySpec from hmc)))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyDecoder_1_exact_pinned_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := polyDecoder1_exact_gen_placed_ok (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_of_plain_blk s0 hcl0
      (subroutine_ok_polyDecLenElemsOut_of_pinned
        (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H)))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_repeated_1_59_placed_ok_x h_panic hshim halloc hrealloc
        (show HookSat H spqrMemcpySym framelessMemcpySpec from hmc)))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem etv_polyDecoderEncode_1_exact_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A)) :=
  etv_polyDecoderEncode_exact_of_lscl
    (encode_polyDecoder_1_exact_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem etv_polyDecoderEncode_1_exact_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_455 H) (blkPl_455).base
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A)) :=
  etv_polyDecoderEncode_exact_of_lscl
    (encode_polyDecoder_1_exact_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

abbrev etv_polyDecoderEncode_exact_placed_ok := @etv_polyDecoderEncode_1_exact_placed_ok
abbrev etv_polyDecoderEncode_exact_placed_ok_x := @etv_polyDecoderEncode_1_exact_placed_ok_x

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
