/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsaPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsf
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsfPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsg
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsh
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 2 (`HeaderSent`, `+508`) — Part I

Relocatable Block-`333` post-`<PolyEncoder>::from_pb` branches at `+9328` and `+9388`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1
open LibsignalBinary.Proofs.SpqrV1.States
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit v2hsh_bv_add_add_lit

/-! ## `receivingCt1 = none` Branch (`+9328 -> +9228 -> ret`) -/

theorem v2hsh_branch_none_dec_9328_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s2 : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (w8_e w16_e w24_e : BitVec 64) (hi32 : BitVec 32)
    (bs : { l : List (BitVec 8) // l.length = 384 })
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (P_enc_heap Rest : SepProp)
    (hsplit : (((s0.sp - 2400#64 + 1392#64) + 8#64) ↦ₛ bs.val) ∗
      (((s0.sp - 2400#64 + 1392#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) =
      (((s0.sp - 2400#64 + 1392#64) + 8#64) ↦₆₄ w8_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 16#64) ↦₆₄ w16_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 24#64) ↦₆₄ w24_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 32#64) ↦ₛ tail368.val))
    (hreloc : ((s0.sp - 2400#64 + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      (((s0.sp - 2400#64 + 1392#64) + 8#64) ↦ₛ bs.val) ∗
      (((s0.sp - 2400#64 + 1392#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap ⊢
      polyEncoderAt A (s0.sp - 2400#64 + 1392#64) enc)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hcl2 : LibsignalCodeLoaded lsmpl s2.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 9328#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out)
    (hx23_2 : s2.readReg64 .x23 = (s0.sp - 2400#64) + 1392#64)
    (hx26_2 : s2.readReg64 .x26 = u8)
    (hpstate2 : s2.pstate = addsPState64 noneCap 1#64)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64 + 1888#64) 400 ∗
        ((s0.sp - 2400#64 + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ w8_e) ∗
        ((s0.sp - 2400#64 + 1408#64) ↦₆₄ w16_e) ∗
        ((s0.sp - 2400#64 + 1416#64) ↦₆₄ w24_e) ∗
        ((s0.sp - 2400#64 + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 24 ∗
        ((s0.sp - 2400#64 + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        P_enc_heap ∗
        memRegion (s0.sp - 2400#64 + 1792#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1848#64) 40 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        memRegion (s0.sp - 2400#64 + 264#64) 712 ∗
        memRegion (s0.sp - 2400#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 64#64) 32 ∗
        memRegion (s0.sp - 2400#64 + 104#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 160#64) 16 ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have henc_pack := v2hsh_polyEncoderAt_pack_from_words A fsp w8_e w16_e w24_e (hi32 ++ enc.idx)
    bs.val enc P_enc_heap tail368 hsplit hreloc
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
  have hscratch := v2hsh_stack896ScratchRest_pack_56 fsp (v2hse2_polyEncoderTag enc)
  have h240_col := v2hsh_memRegion_240_24_712_collapse fsp
  let Frame9328 : SepProp :=
    memRegion (fsp + 1888#64) 400 ∗
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 2288#64) 16 ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗ EkRest ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9328 :
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) 400 ∗
        ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
        ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 240#64) 24 ∗ ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        P_enc_heap ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 2288#64) 16 ∗
        memRegion (fsp + 264#64) 712 ∗
        memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
        memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
        memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        vecCapPtrDealloc A u48 pa1 ∗ vecCapPtrDealloc A u72 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
        A.pool ∗ Frame9328 := by
    rw [hek_split]; dsimp only [Frame9328, EkRest]
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
       ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
       ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗ P_enc_heap) ∗
      (memRegion (fsp + 240#64) 24 ∗ memRegion (fsp + 264#64) 712) ∗
      (memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
       memRegion (fsp + 64#64) 32 ∗ memRegion (fsp + 104#64) 48 ∗
       memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
       memRegion (fsp + 208#64) 8) ∗
      vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
      v4b_vecU8Heap A dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       A.pool ∗
       (memRegion (fsp + 1888#64) 400 ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        (((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
         ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
         ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)) ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono henc_pack (sepConj_mono h240_col (sepConj_mono hscratch
        (sepConj_mono hd_r (sepConj_mono hd_m (sepConj_mono_left hd_dk))))))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9328 ?_
  refine seq_clean_lscl hcl2
    (mid := lsmpl.base 333 + 9228#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1392#64) 400 ∗
      ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool ∗ Frame9328)
    (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
      s3.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s3 s0)
    (v2hse3_none_dec_9328_to_9228_placed hA s0 s2 fsp out u48 pa1 u72 pa2 u8 u16 enc Frame9328
      hcl2 hfsp_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hpstate2 htr2) ?_
  intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx23_3, htr3⟩
  have h960 := v2hsh_memRegion_1344_960_collapse fsp
  have hek80 := v2hstop_ekSentWordsAt_entails_80 (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80
  rw [hek_split] at hek80
  have hcol2304 := v2hsh_collapse_2304_from_9228 fsp u8 u16 u24 u40 u48 u72 u80 pa2
    w0 w8 w16 w24 w32 w40 w48 noneCap d_w8 d_w16 d_w24 d_w32
  have hpre9228 :
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1392#64) 400 ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool ∗ Frame9328) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
    dsimp only [Frame9328]
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16) ∗
       (((fsp + 1272#64) ↦₆₄ pa1) ∗ EkRest) ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192)) ∗
      (stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left
      (Entails.trans (sepConj_mono h960 (sepConj_mono_left hek80))
        (Entails.trans (Entails.of_eq (by ac_rfl)) hcol2304))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre9228 ?_
  have hx23_lo : (s3.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_3]; rfl
  have h9228 := v2hs_err_cleanup_9228_placed (A := A) (F := F) (ext := ext)
    s0 s3 out .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx23_lo htr3
  exact SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
    ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

/-! ## `<PolyDecoder>::from_pb = Err` Branch (`+9388 -> +9228 -> ret`) -/

theorem v2hsh_branch_err_dec_9388_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s4 : State) (out : BitVec 64)
    (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (w8_e w16_e w24_e : BitVec 64) (hi32 : BitVec 32)
    (bs : { l : List (BitVec 8) // l.length = 384 })
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (err : PolynomialError) (P_enc_heap Rest : SepProp)
    (hsplit : (((s0.sp - 2400#64 + 1392#64) + 8#64) ↦ₛ bs.val) ∗
      (((s0.sp - 2400#64 + 1392#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) =
      (((s0.sp - 2400#64 + 1392#64) + 8#64) ↦₆₄ w8_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 16#64) ↦₆₄ w16_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 24#64) ↦₆₄ w24_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 32#64) ↦ₛ tail368.val))
    (hreloc : ((s0.sp - 2400#64 + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      (((s0.sp - 2400#64 + 1392#64) + 8#64) ↦ₛ bs.val) ∗
      (((s0.sp - 2400#64 + 1392#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap ⊢
      polyEncoderAt A (s0.sp - 2400#64 + 1392#64) enc)
    (hdk_len : u.dk.length = 2400) (hu24 : u24 = 2400#64)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hu80 : u80 = u.epoch)
    (hcl4 : LibsignalCodeLoaded lsmpl s4.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 333 + 9388#64)
    (hrun4 : s4.status = .Running) (hsp4 : s4.sp = s0.sp - 2400#64)
    (hx19_4 : s4.readReg64 .x19 = out) (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s4
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A (s0.sp - 2400#64 + 1888#64) (.error err) ∗
        memRegion (s0.sp - 2400#64 + 1848#64) protoPolynomialDecoderSize ∗
        A.pool ∗
        ((s0.sp - 2400#64 + 1032#64) ↦₆₄ d_w0) ∗
        ((s0.sp - 2400#64 + 1040#64) ↦₆₄ d_w8) ∗
        ((s0.sp - 2400#64 + 1048#64) ↦₆₄ d_w16) ∗
        ((s0.sp - 2400#64 + 1056#64) ↦₆₄ d_w24) ∗
        ((s0.sp - 2400#64 + 1064#64) ↦₆₄ d_w32) ∗
        ((s0.sp - 2400#64 + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ w8_e) ∗
        ((s0.sp - 2400#64 + 1408#64) ↦₆₄ w16_e) ∗
        ((s0.sp - 2400#64 + 1416#64) ↦₆₄ w24_e) ∗
        ((s0.sp - 2400#64 + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 24 ∗
        ((s0.sp - 2400#64 + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        P_enc_heap ∗
        memRegion (s0.sp - 2400#64 + 1792#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        memRegion (s0.sp - 2400#64 + 264#64) 712 ∗
        memRegion (s0.sp - 2400#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 64#64) 32 ∗
        memRegion (s0.sp - 2400#64 + 104#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 160#64) 16 ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have henc_pack := v2hsh_polyEncoderAt_pack_from_words A fsp w8_e w16_e w24_e (hi32 ++ enc.idx)
    bs.val enc P_enc_heap tail368 hsplit hreloc
  have huc_pack := v2hsh_unchunkedEkSentAt_pack A F (fsp + 1264#64) u auth
    u8 u16 u24 u48 u72 u80 pa1 pa2 hdk_len hu24 hu48 hu72 hu80
  have hscratch := v2hsh_stack896ScratchRest_pack_56 fsp (v2hse2_polyEncoderTag enc)
  have h240_col := v2hsh_memRegion_240_24_712_collapse fsp
  have hdec_words :
      ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
      ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
      ((fsp + 1064#64) ↦₆₄ d_w32) =
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 := by
    dsimp only [v2hs_optProtoDecoderWordsAt]; simp only [arm64_norm]
  let Frame9388 : SepProp :=
    memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1344#64) 48 ∗
    memRegion (fsp + 2288#64) 16 ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9388 :
      (stackAt fsp encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        memRegion (fsp + 1848#64) protoPolynomialDecoderSize ∗
        A.pool ∗
        ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
        ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
        ((fsp + 1064#64) ↦₆₄ d_w32) ∗
        ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
        ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 240#64) 24 ∗ ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        P_enc_heap ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1344#64) 48 ∗
        memRegion (fsp + 2288#64) 16 ∗ memRegion (fsp + 264#64) 712 ∗
        memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
        memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
        memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A (F := F) (fsp + 1264#64)
          { auth := { rootKey := auth.rootKey, macKey := auth.macKey }, dk := u.dk, epoch := u.epoch } ∗
        A.pool ∗ Frame9388 := by
    dsimp only [protoPolynomialDecoderSize, Frame9388]
    rw [← hdec_words]
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
       ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
       ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗ P_enc_heap) ∗
      (v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
       v4b_vecU8Heap A u.dk u8 u16 u24 ∗
       vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey) ∗
      (memRegion (fsp + 240#64) 24 ∗ memRegion (fsp + 264#64) 712) ∗
      (memRegion fsp 56 ∗ ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
       memRegion (fsp + 64#64) 32 ∗ memRegion (fsp + 104#64) 48 ∗
       memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
       memRegion (fsp + 208#64) 8) ∗
      (stackAt fsp encoderFromPbStack ∗
       resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ∗
       ((fsp + 216#64) ↦₆₄ u40) ∗ A.pool ∗
       (memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1344#64) 48 ∗
        memRegion (fsp + 2288#64) 16 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        (((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
         ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
         ((fsp + 1064#64) ↦₆₄ d_w32)) ∗
        memRegion (fsp + 1072#64) 192 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono henc_pack (sepConj_mono huc_pack (sepConj_mono h240_col (sepConj_mono_left hscratch))))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9388 ?_
  refine seq_clean_lscl hcl4
    (mid := lsmpl.base 333 + 9228#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1888#64) 400 ∗
      ((fsp + 216#64) ↦₆₄ noneCap) ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1264#64) 80 ∗
      A.pool ∗ Frame9388)
    (Q := fun s5 => s5.sp = fsp ∧ s5.readReg64 .x19 = out ∧
      s5.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s5 s0)
    (v2hse3_err_dec_9388_to_9228_placed hA s0 s4 fsp out u40 enc
      { auth := { rootKey := auth.rootKey, macKey := auth.macKey }, dk := u.dk, epoch := u.epoch }
      err Frame9388 hcl4 hfsp_align hpc4 hrun4 hsp4 hx19_4 htr4) ?_
  intro s5 hpc5 hrun5 hcl5 ⟨hsp5, hx19_5, hx23_5, htr5⟩
  have h960 := v2hsh_memRegion_1344_960_collapse fsp
  have hcol2304 := v2hsh_collapse_2304_from_9228 fsp u8 u16 u24 noneCap u48 u72 u80 pa2
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpre9228 :
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) 400 ∗
        ((fsp + 216#64) ↦₆₄ noneCap) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 1264#64) 80 ∗
        A.pool ∗ Frame9388) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
    dsimp only [Frame9388]
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion (fsp + 1344#64) 48 ∗ memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40 ∗
        memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16) ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ noneCap) ∗
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
  have hx23_lo : (s5.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_5]; rfl
  have h9228 := v2hs_err_cleanup_9228_placed (A := A) (F := F) (ext := ext)
    s0 s5 out .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc5 hrun5 hsp5 hx19_5 hx23_lo htr5
  exact SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
    ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

/-! ## `<PolyDecoder>::from_pb = Ok dec` Branch (`+9388 -> +9404 -> ret`) -/

set_option maxHeartbeats 800000 in
theorem v2hsh_branch_ok_dec_9388_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s4 : State) (out : BitVec 64)
    (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (w8_e w16_e w24_e : BitVec 64) (hi32 : BitVec 32)
    (bs : { l : List (BitVec 8) // l.length = 384 })
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (dec : PolyDecoder) (P_enc_heap Rest : SepProp)
    (hsplit : (((s0.sp - 2400#64 + 1392#64) + 8#64) ↦ₛ bs.val) ∗
      (((s0.sp - 2400#64 + 1392#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) =
      (((s0.sp - 2400#64 + 1392#64) + 8#64) ↦₆₄ w8_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 16#64) ↦₆₄ w16_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 24#64) ↦₆₄ w24_e) ∗
      (((s0.sp - 2400#64 + 1392#64) + 32#64) ↦ₛ tail368.val))
    (hreloc_out : ((out + 8#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
      (((out + 8#64) + 8#64) ↦ₛ bs.val) ∗
      (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap ⊢
      polyEncoderAt A (out + 8#64) enc)
    (hdk_len : u.dk.length = 2400) (hu24 : u24 = 2400#64)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hu80 : u80 = u.epoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 333 + 9388#64)
    (hrun4 : s4.status = .Running) (hsp4 : s4.sp = s0.sp - 2400#64)
    (hx19_4 : s4.readReg64 .x19 = out)
    (hx20_4 : s4.readReg64 .x20 = (loByte (v1_wordAt bs.val 0)).zeroExtend 64)
    (hx21_4 : s4.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_4 : s4.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64)
    (hx23_4 : s4.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_4 : s4.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26_4 : s4.readReg64 .x26 = u8)
    (hx28_4 : s4.readReg64 .x28 = u.epoch)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s4
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A (s0.sp - 2400#64 + 1888#64) (.ok dec) ∗
        memRegion (s0.sp - 2400#64 + 1848#64) protoPolynomialDecoderSize ∗
        A.pool ∗
        ((s0.sp - 2400#64 + 1032#64) ↦₆₄ d_w0) ∗
        ((s0.sp - 2400#64 + 1040#64) ↦₆₄ d_w8) ∗
        ((s0.sp - 2400#64 + 1048#64) ↦₆₄ d_w16) ∗
        ((s0.sp - 2400#64 + 1056#64) ↦₆₄ d_w24) ∗
        ((s0.sp - 2400#64 + 1064#64) ↦₆₄ d_w32) ∗
        ((s0.sp - 2400#64 + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ w8_e) ∗
        ((s0.sp - 2400#64 + 1408#64) ↦₆₄ w16_e) ∗
        ((s0.sp - 2400#64 + 1416#64) ↦₆₄ w24_e) ∗
        ((s0.sp - 2400#64 + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 24 ∗
        ((s0.sp - 2400#64 + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        P_enc_heap ∗
        memRegion (s0.sp - 2400#64 + 1792#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        memRegion (s0.sp - 2400#64 + 264#64) 712 ∗
        memRegion (s0.sp - 2400#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 64#64) 32 ∗
        memRegion (s0.sp - 2400#64 + 104#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 160#64) 16 ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
          (.ok (.headerSent
            { uc := { auth := { rootKey := auth.rootKey, macKey := auth.macKey }, dk := u.dk, epoch := u.epoch },
              sending_ek := enc, receiving_ct1 := dec })) ∗
          (A.pool ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdec_rel := v2hsf_polyDecoderAt_relocate_328 A (fsp + 1888#64) (out + 488#64) dec
  dsimp only [resultPolyDecoderFromPbAt]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left hdec_rel)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro dw0
  apply ProofLib.SepWP.exists_left; intro dw8
  apply ProofLib.SepWP.exists_left; intro dw16
  apply ProofLib.SepWP.exists_left; intro dw24
  apply ProofLib.SepWP.exists_left; intro dw32
  apply ProofLib.SepWP.exists_left; intro dw40
  apply ProofLib.SepWP.exists_left; intro dw48
  apply ProofLib.SepWP.exists_left; intro dw56
  apply ProofLib.SepWP.exists_left; intro dw64
  apply ProofLib.SepWP.exists_left; intro dbs328
  apply ProofLib.SepWP.exists_left; intro P_dec_heap
  rw [sepConj_left_comm]
  apply ProofLib.SepWP.pure_elim; rintro ⟨hdw0, hdec_reloc⟩
  conv => arg 4; simp only [v2hsh_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  let Frame9388 : SepProp :=
    stackAt fsp encoderFromPbStack ∗
    ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
    ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗
    ((fsp + 1928#64) ↦₆₄ dw40) ∗ ((fsp + 1936#64) ↦₆₄ dw48) ∗
    ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
    ((fsp + 1960#64) ↦ₛ dbs328.val) ∗ P_dec_heap ∗
    memRegion (fsp + 1848#64) protoPolynomialDecoderSize ∗
    A.pool ∗
    ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
    ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
    ((fsp + 1064#64) ↦₆₄ d_w32) ∗
    ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
    ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
    ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
    memRegion (fsp + 240#64) 24 ∗ ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
    P_enc_heap ∗
    memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1344#64) 48 ∗
    memRegion (fsp + 2288#64) 16 ∗ memRegion (fsp + 264#64) 712 ∗
    memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
    memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
    memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
    ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
    v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
    vecU8Payload A u72 pa2 auth.macKey ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 192 ∗
    v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9388 :
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗
        ((fsp + 1904#64) ↦₆₄ dw16) ∗ ((fsp + 1912#64) ↦₆₄ dw24) ∗
        ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
        ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗
        ((fsp + 1952#64) ↦₆₄ dw64) ∗ ((fsp + 1960#64) ↦ₛ dbs328.val) ∗
        P_dec_heap ∗
        memRegion (fsp + 1848#64) protoPolynomialDecoderSize ∗
        A.pool ∗
        ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
        ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
        ((fsp + 1064#64) ↦₆₄ d_w32) ∗
        ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
        ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 240#64) 24 ∗ ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        P_enc_heap ∗
        memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1344#64) 48 ∗
        memRegion (fsp + 2288#64) 16 ∗ memRegion (fsp + 264#64) 712 ∗
        memRegion fsp 56 ∗ memRegion (fsp + 64#64) 32 ∗
        memRegion (fsp + 104#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗
        memRegion (fsp + 192#64) 8 ∗ memRegion (fsp + 208#64) 8 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) =
      (((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ Frame9388) := by
    dsimp only [Frame9388]; ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre9388) ?_
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 9404#64)
    (P_mid := ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 216#64) ↦₆₄ dw0) ∗ Frame9388)
    (Q := fun s5 => s5.sp = fsp ∧ s5.readReg64 .x8 = dw0 ∧ s5.readReg64 .x19 = out ∧
      s5.readReg64 .x20 = (loByte (v1_wordAt bs.val 0)).zeroExtend 64 ∧
      s5.readReg64 .x21 = fsp + 1392#64 ∧ s5.readReg64 .x22 = fsp + 1888#64 ∧
      s5.readReg64 .x23 = fsp + 848#64 ∧ s5.readReg64 .x25 = fsp + 1792#64 ∧
      s5.readReg64 .x26 = u8 ∧ s5.readReg64 .x28 = u.epoch ∧ TraceCalleeSaved s5 s0)
    (v2hse3_ok_dec_9388_to_9404_placed (ext := ext) s0 s4 fsp out
      ((loByte (v1_wordAt bs.val 0)).zeroExtend 64) (fsp + 1392#64) u8 u.epoch dw0 u40
      Frame9388 hfsp_align hdw0 hpc4 hrun4 hsp4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx25_4 hx26_4 hx28_4 htr4) ?_
  intro s5 hpc5 hrun5 ⟨hsp5, _, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx25_5, hx26_5, hx28_5, htr5⟩
  have h104_72 := v2hsh_memRegion_104_72_collapse fsp u8
  have h1792_96 := v2hsh_memRegion_1792_96_collapse fsp
  have henc_cells := v2hsh_enc_words_to_encCellsAt fsp w8_e w16_e w24_e (hi32 ++ enc.idx)
    bs.val bs.property tail368 hsplit
  have h976_56 := v1_optProtoPolyEncoderWordsAt_entails_56 (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48
  have hdec_words :
      ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
      ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
      ((fsp + 1064#64) ↦₆₄ d_w32) =
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 := by
    dsimp only [v2hs_optProtoDecoderWordsAt]; simp only [arm64_norm]
  have hmid_col := v2hsh_ok_dec_mid_stack_collapse fsp d_w0 d_w8 d_w16 d_w24 d_w32
    u48 pa1 u72 pa2 u8 u16 u24 u80 (v2hse2_polyEncoderTag enc)
  have hdk_pay := v2hsh_vecU8Heap_entails_payload A u.dk u8 u16 u24
  have hpre9404 :
      (((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 216#64) ↦₆₄ dw0) ∗ Frame9388) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 56 ∗
        ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗ memRegion (fsp + 64#64) 32 ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ memRegion (fsp + 104#64) 72 ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
        memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ dw0) ∗
        memRegion (fsp + 224#64) 8 ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 1032 ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗
        memRegion (fsp + 1280#64) 120 ∗ v1_encCellsAt (fsp + 1392#64) bs.val ∗
        ((fsp + 1784#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (fsp + 1792#64) 96 ∗
        ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗
        ((fsp + 1904#64) ↦₆₄ dw16) ∗ ((fsp + 1912#64) ↦₆₄ dw24) ∗
        ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
        ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗
        ((fsp + 1952#64) ↦₆₄ dw64) ∗ ((fsp + 1960#64) ↦ₛ dbs328.val) ∗
        memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
        vecU8Payload A u8 u16 u.dk ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗ (A.pool ∗ Rest) := by
    dsimp only [Frame9388, protoPolynomialDecoderSize]
    have h224_8 := Drop.pointsTo64_entails_memRegion (fsp + 224#64) u80
    have hmid_step :
        memRegion (fsp + 240#64) 24 ∗ memRegion (fsp + 264#64) 712 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        (((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
         ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
         ((fsp + 1064#64) ↦₆₄ d_w32)) ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (fsp + 1344#64) 48 ∗
        ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ⊢
        memRegion (fsp + 240#64) 1032 ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ memRegion (fsp + 1280#64) 120 := by
      rw [hdec_words]
      exact Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h976_56))) hmid_col
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (fsp + 104#64) 48 ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 160#64) 16) ∗
      ((fsp + 224#64) ↦₆₄ u80) ∗
      (memRegion (fsp + 240#64) 24 ∗ memRegion (fsp + 264#64) 712 ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       (((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
        ((fsp + 1048#64) ↦₆₄ d_w16) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗
        ((fsp + 1064#64) ↦₆₄ d_w32)) ∗
       memRegion (fsp + 1072#64) 192 ∗
       v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
       memRegion (fsp + 1344#64) 48 ∗
       ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc)) ∗
      (((fsp + 1400#64) ↦₆₄ w8_e) ∗ ((fsp + 1408#64) ↦₆₄ w16_e) ∗
       ((fsp + 1416#64) ↦₆₄ w24_e) ∗ ((fsp + 1424#64) ↦ₛ tail368.val)) ∗
      (memRegion (fsp + 1792#64) 56 ∗ memRegion (fsp + 1848#64) 40) ∗
      v4b_vecU8Heap A u.dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗ memRegion fsp 56 ∗
       ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗ memRegion (fsp + 64#64) 32 ∗
       ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
       memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ dw0) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
       ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗
       ((fsp + 1904#64) ↦₆₄ dw16) ∗ ((fsp + 1912#64) ↦₆₄ dw24) ∗
       ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
       ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗
       ((fsp + 1952#64) ↦₆₄ dw64) ∗ ((fsp + 1960#64) ↦ₛ dbs328.val) ∗
       memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
       vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
       (A.pool ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono h104_72 (sepConj_mono h224_8 (sepConj_mono hmid_step
        (sepConj_mono henc_cells (sepConj_mono h1792_96 (sepConj_mono_left hdk_pay))))))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9404 ?_
  have hu24_dk : u24 = BitVec.ofNat 64 u.dk.length := by rw [hu24, hdk_len]
  exact v2hsf_headerSent_ok_9404_to_ret_placed hA s0 s5 out (v2hse2_polyEncoderTag enc)
    u48 pa1 u72 pa2 u8 u16 u24 u.epoch bs.val bs.property hi32 enc P_enc_heap hreloc_out
    u.dk auth.rootKey auth.macKey hu24_dk hu48 hu72
    dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 dbs328.val dbs328.property dec P_dec_heap hdec_reloc
    (A.pool ∗ Rest) hsp0_align hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx25_5 hx26_5 hx28_5 htr5

end CryptoVerification.SpqrV1.States.FromPb
