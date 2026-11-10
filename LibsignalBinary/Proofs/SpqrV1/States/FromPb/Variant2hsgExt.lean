/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0Ext
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsg
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2hsg` -/

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

set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

open CryptoVerification.SpqrV1.Alloc

namespace Ext4K

theorem v2hstop_branch_sendingEk_none_9152
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = u8) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
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
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
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
  have hek_split :
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 =
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      (((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
       ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)) := by
    dsimp only [v2hs_ekSentWordsAt, fsp]; simp only [arm64_norm]; ac_rfl
  let EkRest : SepProp :=
    ((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
    ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
    ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)
  let Frame9152 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗
    v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗ EkRest ∗ memRegion (fsp + 1344#64) 960 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9152 :
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗ v4b_vecU8Heap A dk u8 u16 u24 ∗
        vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        vecCapPtrDealloc A u48 pa1 ∗ vecCapPtrDealloc A u72 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
        A.pool ∗ Frame9152 := by
    rw [hek_split]; dsimp only [Frame9152, EkRest]
    refine Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
      v4b_vecU8Heap A dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        (((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
         ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
         ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)) ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hd_r (sepConj_mono hd_m (sepConj_mono_left hd_dk)))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9152 ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9212#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool ∗ Frame9152)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
      s1.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s1 s0)
    (v2hsc_cleanup_9152_to_9212 hA s0 s fsp out d_w0 u48 pa1 u72 pa2 u8 u16 Frame9152
      hfsp_align hpc hrun hsp hx0 hx19 hx22 hx25 hx26 htr) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx22_1, htr1⟩
  let Frame9212 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 192 ∗
    v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
    memRegion (fsp + 1344#64) 960 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9212 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool ∗ Frame9152) =
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        v2hsc_optProtoPolyDecoderHeap A optDec d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212) := by
    dsimp only [Frame9152, Frame9212, EkRest]
    rw [hek_split,
        v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32,
        v2hstop_optProtoDecoderHeap_eq_v2hsc A optDec d_w0 d_w8 d_w16 d_w24 d_w32]
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre9212) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s2 s0)
    (v2hsc_cleanup_9212_to_9228 hA s0 s1 fsp out optDec d_w0 d_w8 d_w16
      (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 u72 Frame9212
      hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, htr2⟩
  have hcol2304 := v2hstop_collapse_2304_from_9228 fsp u8 u16 u24 u40 u48 u72 u80 pa1 pa2
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
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
       ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
       v2hs_stack896ScratchRest fsp ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 192 ∗
       v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
       memRegion (fsp + 1344#64) 960) ∗
      (stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hcol2304) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9228 ?_
  have hx23_lo : (s2.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_2]; rfl
  have h9228 := v2hs_err_cleanup_9228 (A := A) (F := F) s0 s2 out .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_lo htr2
  exact SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
    ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

theorem v2hstop_branch_bad_dk_3348
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (out : BitVec 64)
    (u : V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w184 w200 w216 w224 w232 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63) (hdk : (u24 == 2400#64) = false)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗
        v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A u.dk u8 u16 u24
  let Rest3348 : SepProp :=
    stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
    ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    vecCapPtrDealloc A u8 u16 ∗ v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest
  have hpre3348 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗
        v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest3348 := by
    dsimp only [Rest3348]
    refine Entails.trans (Entails.of_eq (show _ =
      v4b_vecU8Heap A u.dk u8 u16 u24 ∗
      (((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
       v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
       stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
       v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 1232 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hd_dk) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre3348 ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4660#64)
    (P_mid := ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest3348)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = u40 ∧ s1.readReg64 .x9 = u16 ∧
      s1.readReg64 .x19 = out ∧ s1.readReg64 .x22 = d_w0 ∧
      s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
      s1.readReg64 .x26 = u32 ∧ TraceCalleeSaved s1 s0)
    (v2hs_validate_err_dk_3348_to_4660 s0 s out d_w0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w96 w152 Rest3348 hsp0_align hu8 hdk hpc hrun hsp hx19 hx22 htr) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx9_1, hx19_1, hx22_1, hx24_1, hx25_1, hx26_1, htr1⟩
  let Frame4660 : SepProp :=
    memRegion (fsp - 5152#64) 1056 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
    memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre4660 :
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest3348) =
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A u8 u16 ∗ v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660) := by
    dsimp only [Rest3348, Frame4660]
    rw [stackAt_encoderFromPb_split_allocHook fsp]; ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre4660) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64)
    (P_mid := ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved s2 s0)
    (v2hs_err_uc_4660_to_4396 hA s0 s1 fsp out u8 u16 u32 u40 u48 u56 u64 u72 w176 w200 d_w0
      u.auth Frame4660 hfsp_align hpc1 hrun1 hsp1 hx0_1 hx9_1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx23_2, htr2⟩
  have hcol976 := v2hstop_collapse_976_from_err_uc fsp u24 u8 w184 w216 w224 w232
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have hpre4396 :
      (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 976 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest := by
    have hre :
        (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660) =
        (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
         ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
         v2hs_stack896ScratchRest fsp ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80) ∗
        ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) := by
      dsimp only [Frame4660]; ac_rfl
    rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
    exact Entails.trans (Entails.of_eq hre)
      (Entails.trans (sepConj_mono_left hcol976) (Entails.of_eq (by ac_rfl)))
  refine SepWP.weaken_pre hpre4396 ?_
  exact v2hs_epilogue_4396_ret (A := A) (F := F) hA s0 s2 out .stateDecode
    optEnc w0 w8 w16 w24 w32 w40 w48 optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 htr2

theorem v2hstop_branch_auth_none_3348
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8))
    (u8 u16 u24 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w184 w200 w216 w224 w232 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63) (hdk : (u24 == 2400#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A dk u8 u16 u24
  let Rest3348 : SepProp :=
    stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
    ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    vecCapPtrDealloc A u8 u16 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest
  have hpre3348 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest3348 := by
    dsimp only [Rest3348]
    refine Entails.trans (Entails.of_eq (show _ =
      v4b_vecU8Heap A dk u8 u16 u24 ∗
      (((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
       v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
       stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 1232 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hd_dk) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre3348 ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4720#64)
    (P_mid := ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest3348)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x9 = u16 ∧
      s1.readReg64 .x19 = out ∧ s1.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s1 s0)
    (v2hs_validate_err_auth_3348_to_4720 s0 s out d_w0 u8 u16 u24 u40 u48 u56 u64 u72 u80
      w96 w152 Rest3348 hsp0_align hu8 hdk hpc hrun hsp hx19 hx22 htr) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx9_1, hx19_1, hx22_1, htr1⟩
  let Frame4720 : SepProp :=
    memRegion (fsp - 5152#64) 1056 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
    memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre4720 :
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest3348) =
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A u8 u16 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame4720) := by
    dsimp only [Rest3348, Frame4720]
    rw [stackAt_encoderFromPb_split_allocHook fsp]; ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre4720) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64)
    (P_mid := ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame4720)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved s2 s0)
    (v2hs_err_uc_4720_to_4396 hA s0 s1 fsp out u8 u16 w176 w200 d_w0
      Frame4720 hfsp_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx22_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx23_2, htr2⟩
  have hcol976 := v2hstop_collapse_976_from_err_uc fsp u24 u8 w184 w216 w224 w232
    u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80
  have hpre4396 :
      (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame4720) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 976 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest := by
    have hre :
        (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame4720) =
        (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
         ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
         v2hs_stack896ScratchRest fsp ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80) ∗
        ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) := by
      dsimp only [Frame4720]; ac_rfl
    rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
    exact Entails.trans (Entails.of_eq hre)
      (Entails.trans (sepConj_mono_left hcol976) (Entails.of_eq (by ac_rfl)))
  refine SepWP.weaken_pre hpre4396 ?_
  exact v2hs_epilogue_4396_ret (A := A) (F := F) hA s0 s2 out .stateDecode
    optEnc w0 w8 w16 w24 w32 w40 w48 optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 htr2

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
