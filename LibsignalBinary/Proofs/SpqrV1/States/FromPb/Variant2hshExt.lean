/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2Ext
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsg
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsh
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2hsh` -/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open V1State.Chunked

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff

open CryptoVerification.SpqrV1.Alloc
attribute [local simp, local arm64_norm, local wp_norm] v2hsh_bv_add_add_lit

namespace Ext4K

theorem v2hsh_branch_enc_err_9100
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s1 : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (err : PolynomialError) (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = d_w0)
    (hx26_1 : s1.readReg64 .x26 = u8) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (s0.sp - 2400#64 + 1888#64) (.error err) ∗
        memRegion (s0.sp - 2400#64 + 1792#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1848#64) 40 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 1392#64) 400 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A dk u8 u16 u24
  have hd_r : vecU8Payload A u48 pa1 auth.rootKey ⊢ vecCapPtrDealloc A u48 pa1 := by
    rw [hu48]; exact vecU8Payload_entails_dealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hd_m : vecU8Payload A u72 pa2 auth.macKey ⊢ vecCapPtrDealloc A u72 pa2 := by
    rw [hu72]; exact vecU8Payload_entails_dealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  have hek_eq :
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 =
      v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 := rfl
  let Frame9100 : SepProp :=
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9100 :
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 ∗
        vecCapPtrDealloc A u48 pa1 ∗ vecCapPtrDealloc A u72 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
        A.pool ∗ Frame9100 := by
    rw [hek_eq]; dsimp only [Frame9100]
    refine Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
      v4b_vecU8Heap A dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗
       resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗
       ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80 ∗
       A.pool ∗
       (memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hd_r (sepConj_mono hd_m (sepConj_mono_left hd_dk)))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9100 ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9212#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1888#64) 400 ∗
      ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      memRegion (fsp + 1264#64) 80 ∗ A.pool ∗ Frame9100)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s2 s0)
    (v2hse2_enc_err_9100_to_9212 hA s0 s1 fsp out d_w0 u48 pa1 u48 u72 pa2 u72 u8 u16 u24 u80
      err Frame9100 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
  let Frame9212 : SepProp :=
    memRegion (fsp + 1888#64) 400 ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    memRegion (fsp + 1264#64) 80 ∗
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 2288#64) 16 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9212 :
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) 400 ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        memRegion (fsp + 1264#64) 80 ∗ A.pool ∗ Frame9100) =
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        v2hsc_optProtoPolyDecoderHeap A optDec d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212) := by
    dsimp only [Frame9100, Frame9212]
    rw [v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32,
        v2hstop_optProtoDecoderHeap_eq_v2hsc A optDec d_w0 d_w8 d_w16 d_w24 d_w32]
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre9212) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212)
    (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
      s3.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s3 s0)
    (v2hsc_cleanup_9212_to_9228 hA s0 s2 fsp out optDec d_w0 d_w8 d_w16
      (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 u72 Frame9212
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, htr3⟩
  have h960 := v2hsh_memRegion_1344_960_collapse fsp
  have hcol2304 := v2hsh_collapse_2304_from_9228 fsp u8 u16 u24 u40 u48 u72 u80 pa2
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpre9228 :
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
    rw [← v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32]
    dsimp only [Frame9212]
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16) ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1264#64) 80)) ∗
      (stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left
      (Entails.trans (sepConj_mono_left h960)
        (Entails.trans (Entails.of_eq (by ac_rfl)) hcol2304))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre9228 ?_
  have hx23_lo : (s3.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_3]; rfl
  have h9228 := v2hs_err_cleanup_9228 (A := A) (F := F) s0 s3 out .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx23_lo htr3
  exact SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
    ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
