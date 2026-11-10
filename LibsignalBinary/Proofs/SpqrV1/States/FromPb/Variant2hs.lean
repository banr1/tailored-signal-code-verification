/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsg
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Proof
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsj
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`)

Top-level composition and `subroutine_ok` contract for `InnerState.headerSent`.
-/

@[expose] public section

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
set_option maxHeartbeats 800000 in
theorem v2hstop_headerSent_3436_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036Hyp A F b ext s)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true)
    (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator)
    (huc : s.uc = some u) (hdk_len : u.dk.length = 2400) (hauth : u.auth = some auth)
    (s0 s2 : State) (out pbA : BitVec 64) (R : SepProp)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w184 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (hu8_lt : u8.toNat < 2 ^ 63) (hu24_val : u24 = 2400#64)
    (hu48_eq : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72_eq : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hu80_eq : u80 = u.epoch) (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3436#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out) (hx20_2 : s2.readReg64 .x20 = u48)
    (hx21_2 : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_2 : s2.readReg64 .x22 = d_w0) (hx24_2 : s2.readReg64 .x24 = u56)
    (hx25_2 : s2.readReg64 .x25 = u64) (hx26_2 : s2.readReg64 .x26 = u32)
    (hx27_2 : s2.readReg64 .x27 = pbA)
    (hx28_2 : s2.readReg64 .x28 = u80) (htr2 : TraceCalleeSaved s2 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u32 u40 auth.rootKey ∗
        vecU8Payload A u56 u64 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hx20_2' : s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length := by rw [hx20_2, hu48_eq]
  let Frame3436 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
    v2hs_stack896ScratchRest fsp ∗ v4b_vecU8Heap A u.dk u8 u16 u24 ∗
    vecU8Payload A u56 u64 auth.macKey ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    vecU8Payload A u32 u40 auth.rootKey ∗ A.pool ∗ Frame3436 by
    dsimp only [Frame3436, fsp]; ac_rfl)) ?_
  refine v2hs_auth_from_pb_step1_3436_8700 hA s0 s2 (s0.readReg64 .x30) fsp out d_w0
    u32 u40 u56 u64 u80 auth Frame3436 R _ hfsp_align hpc2 hrun2 hsp2
    hx19_2 hx20_2' hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2 ?_
  intro pa1 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
  let Frame8700 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecCapPtrDealloc A u32 u40 ∗
    vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 232#64) ↦₆₄ u72) ∗ vecU8Payload A u56 u64 auth.macKey ∗
    A.pool ∗ Frame8700 by dsimp only [Frame3436, Frame8700]; ac_rfl)) ?_
  refine v2hs_auth_from_pb_step2_8700_8884 hA s0 s3 (s0.readReg64 .x30) fsp out d_w0 pa1 w184
    u32 u56 u64 u72 auth Frame8700 R _ hfsp_align hpc3 hrun3 hsp3
    hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hu72_eq htr3 ?_
  intro pa2 s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, htr4⟩
  let Rest8884 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
    v2hs_stack896ScratchRest fsp ∗ v4b_vecU8Heap A u.dk u8 u16 u24 ∗
    vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt fsp encoderFromPbStack ∗ ((fsp + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ Rest8884 by
    dsimp only [Frame8700, Rest8884]; rw [← hu48_eq, ← hu72_eq]; ac_rfl)) ?_
  refine sepWPp_seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8944#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      ((fsp + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ A.pool ∗ Rest8884)
    (Q_regs := fun s5 => s5.sp = fsp ∧ s5.readReg64 .x19 = out ∧ s5.readReg64 .x21 = s4.readReg64 .x21 ∧
      s5.readReg64 .x22 = d_w0 ∧ s5.readReg64 .x23 = pa1 ∧
      s5.readReg64 .x25 = BitVec.ofNat 64 auth.rootKey.length ∧
      s5.readReg64 .x26 = pa1 >>> 8 ∧ s5.readReg64 .x27 = s4.readReg64 .x27 ∧
      s5.readReg64 .x28 = u80 ∧ TraceCalleeSaved s5 s0)
    (v2hs_auth_from_pb_step3_8884_8944 hA s0 s4 out d_w0 pa1 u32 u40 u56 u64 u80 auth Rest8884
      hr_lt63 hsp0_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 htr4) ?_
  intro s5 hpc5 hrun5 ⟨hsp5, hx19_5, hx21_5, hx22_5, hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, htr5⟩
  have hx25_5' : s5.readReg64 .x25 = u48 := by rw [hx25_5, hu48_eq]
  let Rest8944 : SepProp :=
    stackAt fsp encoderFromPbStack ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
    vecU8Payload A u72 pa2 auth.macKey ∗
    v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 1232 ∗ Rest8944 by
    dsimp only [Rest8884, Rest8944]; rw [← hu48_eq]; ac_rfl)) ?_
  refine sepWPp_seq_clean
    (mid := if (w0 + 1#64 == 0#64) = true
            then (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9152#64
            else (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9036#64)
    (P_mid := ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
      ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (fsp + 1072#64) 192 ∗
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
      memRegion (fsp + 1344#64) 960 ∗ Rest8944)
    (Q_regs := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x8 = w0 ∧
      sm.readReg64 .x9 = u24 ∧ sm.readReg64 .x10 = fsp + 1264#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = s5.readReg64 .x21 ∧ sm.readReg64 .x22 = d_w0 ∧
      sm.readReg64 .x23 = pa1 ∧ sm.readReg64 .x25 = u48 ∧ sm.readReg64 .x26 = u8 ∧
      sm.readReg64 .x27 = s5.readReg64 .x27 ∧ sm.readReg64 .x28 = u80 ∧ TraceCalleeSaved sm s0)
    (v2hs_assemble_ekSent_8944_9032 s0 s5 out d_w0 pa1 pa2 u8 u16 u24 u48 u72 u80
      w0 w8 w16 w24 w32 w40 w48 Rest8944 hsp0_align hpc5 hrun5 hsp5
      hx19_5 hx22_5 hx23_5 hx25_5' hx26_5 hx28_5 htr5) ?_
  intro sm hpcm hrunm ⟨hspm, hx0m, hx8m, hx9m, hx10m, hx19m, hx21m, hx22m, hx23m, hx25m, hx26m, hx27m, hx28m, htrm⟩
  have hx21m' : sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by
    rw [hx21m, hx21_5, hx21_4, hx21_3, hx21_2]
  have hx27m' : sm.readReg64 .x27 = pbA := by
    rw [hx27m, hx27_5, hx27_4, hx27_3, hx27_2]
  cases henc : s.sendingEk with
  | none =>
    rw [v2hs_from_pb_headerSent_sendingEk_none_eq F s u auth hdec_ok huc hdk_len hauth henc]
    dsimp only [Rest8944]
    rw [henc, show (none : Option PolynomialEncoder).map pbToProtoPolyEncoder = none from rfl]
    dsimp only [v1_optProtoPolyEncoderHeap]
    have hpb_col := v2hstop_pbEncTailAt_entails_full_224 pbA w8 w16 w24 w32 w40 w48
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
      (⌜w0 = noneCap⌝ ∗
       (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
        statesFromPbJumpTableAt b)) by ac_rfl))
      (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (show _ =
        ⌜w0 = noneCap⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
         ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
         ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
         memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
         v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
         vecU8Payload A u72 pa2 auth.macKey ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 192 ∗
         v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
         memRegion (fsp + 1344#64) 960 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
         (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) by ac_rfl)))) ?_
    refine SepWPp.pure_elim fun hw0 => ?_
    have hw0_beq : (w0 + 1#64 == 0#64) = true := by rw [hw0]; exact noneCap_add_one_beq_zero
    simp only [hw0_beq, ↓reduceIte] at hpcm
    apply SepWPp.of_sepWP_ret
    have hret := v2hstop_branch_sendingEk_none_9152 (A := A) (F := F) hA s0 sm out u.dk auth
      u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
      (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hu48_eq hu72_eq hsp0_align hpcm hrunm hspm hx0m hx19m hx22m hx25m hx26m htrm
    exact SepWP.mono hret fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩
  | some pbEnc =>
    dsimp only [Rest8944]
    rw [henc, show (some pbEnc : Option PolynomialEncoder).map pbToProtoPolyEncoder = some (pbToProtoPolyEncoder pbEnc) from rfl]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
       ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
       memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
       v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
       vecU8Payload A u72 pa2 auth.macKey ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 192 ∗
       v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
       memRegion (fsp + 1344#64) 960 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl))
      (sepConj_mono_left (v1_optProtoPolyEncoderHeap_extract_w0 A (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48))) ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_lt => ?_
    have hw0_beq : (w0 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hw0_lt)
    simp only [hw0_beq, Bool.false_eq_true, ↓reduceIte] at hpcm
    exact SepWPp.weaken_pre (Entails.of_eq (by dsimp only [fsp]; ac_rfl))
      (hsome_enc_9036 s0 sm out pbA R u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
        hpts hdec_ok huc hdk_len hauth henc hu8_lt hu24_val hu48_eq hu72_eq hu80_eq hr_lt63
        hsp0_align hpcm hrunm hspm hx0m hx8m hx9m hx10m hx19m hx21m' hx22m hx23m hx25m hx26m hx27m' hx28m htrm)

set_option maxHeartbeats 800000 in
theorem v2hstop_headerSent_3348_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036Hyp A F b ext s)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true)
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = d_w0) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hpb_col := v2hstop_pbEncTailAt_entails_full_224 pbA w8 w16 w24 w32 w40 w48
  cases huc : s.uc with
  | none =>
    rw [v2hs_from_pb_headerSent_uc_none_eq F s hdec_ok huc]
    dsimp only [v2hs_optProtoUcHeap]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
      (⌜u8 = noneCap⌝ ∗
       (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        (stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool ∗ statesFromPbJumpTableAt b))) by dsimp only [fsp]; ac_rfl))
      (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (show _ =
        ⌜u8 = noneCap⌝ ∗
        (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
         (stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          A.pool ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b))) by ac_rfl)))) ?_
    refine SepWPp.pure_elim fun hu8 => ?_
    subst hu8
    apply SepWPp.of_sepWP_ret
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4392#64)
      (P_mid := v2hs_ucWordsAt (fsp + 896#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        (stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)))
      (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s2 s0)
      (v2hs_uc_none_3348_to_4392 s0 s1 out d_w0 u16 u24 u32 u40 u48 u56 u64 u72 u80 _
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1) ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
    have h976 := v2hs_memRegion_896_ucWords_to_976 fsp noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80
    have hret := v2hs_epilogue_4392_ret (A := A) (F := F) hA s0 s2 out
      (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
      (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2
    exact SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        (memRegion fsp 896 ∗ v2hs_ucWordsAt (fsp + 896#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80) ∗
        (stackAt fsp encoderFromPbStack ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) by ac_rfl))
       (Entails.trans (sepConj_mono_left h976) (Entails.of_eq (by dsimp only [fsp]; ac_rfl))))
      (SepWP.mono hret fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩)
  | some u =>
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono (v2hs_memRegion_896_split_scratch fsp)
        (sepConj_mono_right (sepConj_mono_left
          (v2hstop_optProtoUcHeap_some_extract A u u8 u16 u24 u32 u40 u48 u56 u64 u72 u80))))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWPp.exists_elim; intro w232; apply SepWPp.exists_elim; intro w224
    apply SepWPp.exists_elim; intro w216; apply SepWPp.exists_elim; intro w200
    apply SepWPp.exists_elim; intro w184; apply SepWPp.exists_elim; intro w176
    apply SepWPp.exists_elim; intro w152; apply SepWPp.exists_elim; intro w96
    refine SepWPp.pure_elim fun ⟨hu8_lt, hu24_eq, hdk_lt63, hu80_eq⟩ => ?_
    by_cases hdk : (u24 == 2400#64) = true
    · have hu24_val : u24 = 2400#64 := beq_iff_eq.mp hdk
      have hdk_len : u.dk.length = 2400 := by
        have h1 : (BitVec.ofNat 64 u.dk.length).toNat = (2400#64 : BitVec 64).toNat := by
          rw [← hu24_eq, hu24_val]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1; exact h1
      cases hauth : u.auth with
      | none =>
        rw [v2hs_from_pb_headerSent_auth_none_eq F s u hdec_ok huc hdk_len hauth]
        dsimp only [v1_optProtoAuthHeap]
        refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
          v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
          (⌜u32 = noneCap⌝ ∗
           (stackAt fsp encoderFromPbStack ∗
            ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
            ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
            ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
            memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
            v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
            v4b_vecU8Heap A u.dk u8 u16 u24 ∗
            v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
            v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
            v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
            A.pool ∗ statesFromPbJumpTableAt b)) by dsimp only [fsp]; ac_rfl))
          (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (show _ =
            ⌜u32 = noneCap⌝ ∗
            (stackAt fsp encoderFromPbStack ∗
             ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
             ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
             ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
             memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
             v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
             v4b_vecU8Heap A u.dk u8 u16 u24 ∗
             v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
             v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
             v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
             memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             A.pool ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) by ac_rfl)))) ?_
        refine SepWPp.pure_elim fun hu32 => ?_
        subst hu32
        apply SepWPp.of_sepWP_ret
        have hret := v2hstop_branch_auth_none_3348 (A := A) (F := F) hA s0 s1 out u.dk
          u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 w176 w184 w200 w216 w224 w232
          (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
          (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
          hsp0_align hu8_lt hdk hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
        exact SepWP.mono hret fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩
      | some auth =>
        refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
          v1_optProtoAuthHeap A (some auth) u32 u40 u48 u56 u64 u72 ∗
          (stackAt fsp encoderFromPbStack ∗
           ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
           ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
           ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
           memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
           v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
           v4b_vecU8Heap A u.dk u8 u16 u24 ∗
           v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool) by
          dsimp only [fsp]; ac_rfl))
          (sepConj_mono_left (v2hstop_optProtoAuthHeap_some_extract A auth u32 u40 u48 u56 u64 u72))) ?_
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hu32_lt, hu48_eq, hu72_eq, hr_lt63⟩ => ?_
        let RestOk : SepProp :=
          stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗ v2hs_stack896ScratchRest fsp ∗
          v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u32 u40 auth.rootKey ∗
          vecU8Payload A u56 u64 auth.macKey ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
          ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
          v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ RestOk by
          dsimp only [RestOk, fsp]; ac_rfl)) ?_
        refine sepWPp_seq_clean
          (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3436#64)
          (P_mid := ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
            ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
            ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗ RestOk)
          (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x0 = u40 ∧ s2.readReg64 .x8 = u72 ∧
            s2.readReg64 .x9 = u16 ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x20 = u48 ∧
            s2.readReg64 .x21 = s1.readReg64 .x21 ∧ s2.readReg64 .x22 = d_w0 ∧
            s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧ s2.readReg64 .x26 = u32 ∧
            s2.readReg64 .x27 = s1.readReg64 .x27 ∧ s2.readReg64 .x28 = u80 ∧ TraceCalleeSaved s2 s0)
          (v2hs_validate_ok_3348_3436 s0 s1 out d_w0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
            w96 w152 w176 w200 w216 w224 w232 RestOk hsp0_align hu8_lt hdk hu32_lt
            hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1) ?_
        intro s2 hpc2 hrun2 ⟨hsp2, _, _, _, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
        have hx21_2' : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by rw [hx21_2, hx21_1]
        have hx27_2' : s2.readReg64 .x27 = pbA := by rw [hx27_2, hx27_1]
        exact SepWPp.weaken_pre (Entails.of_eq (by dsimp only [RestOk, fsp]; ac_rfl))
          (v2hstop_headerSent_3436_to_ret hA s hsome_enc_9036 hpts hdec_ok u auth huc hdk_len hauth
            s0 s2 out pbA R u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w184
            w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
            hu8_lt hu24_val hu48_eq hu72_eq hu80_eq hr_lt63
            hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2' hx22_2 hx24_2 hx25_2 hx26_2 hx27_2' hx28_2 htr2)
    · have hdk_f : (u24 == 2400#64) = false := Bool.eq_false_iff.mpr hdk
      have hdk_eq_f : (BitVec.ofNat 64 u.dk.length == 2400#64) = false := by
        rw [← hu24_eq]; exact hdk_f
      rw [v2hs_from_pb_headerSent_bad_dk_eq F s u hdec_ok huc hdk_eq_f]
      apply SepWPp.of_sepWP_ret
      have hret := v2hstop_branch_bad_dk_3348 (A := A) (F := F) hA s0 s1 out u
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 w176 w184 w200 w216 w224 w232
        (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
        (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
        hsp0_align hu8_lt hdk_f hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
      exact SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
         ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
         memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
         v4b_vecU8Heap A u.dk u8 u16 u24 ∗
         v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool ∗ statesFromPbJumpTableAt b) by dsimp only [fsp]; ac_rfl))
        (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (by dsimp only [fsp]; ac_rfl))))
        (SepWP.mono hret fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩)

set_option maxHeartbeats 800000 in
/-- Post-dispatch step for `InnerState.headerSent s` at `+508#64`,
reducing the entire variant to the `+9036 -> s0.x30` (`sendingEk = some pbEnc`) continuation `hsome_enc_9036`. -/
theorem states_from_pb_headerSent_508_of_some_enc
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036Hyp A F b ext s)
    (hpts : optEncoderPtsBound s.sendingEk)
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 508#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.headerSent s)) ∗
        statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  let fsp := s0.sp - 2400#64
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v2hstop_optProtoInnerStateAt_headerSent_unpack A pbA s)))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro u8; apply SepWPp.exists_elim; intro u16
  apply SepWPp.exists_elim; intro u24; apply SepWPp.exists_elim; intro u32
  apply SepWPp.exists_elim; intro u40; apply SepWPp.exists_elim; intro u48
  apply SepWPp.exists_elim; intro u56; apply SepWPp.exists_elim; intro u64
  apply SepWPp.exists_elim; intro u72; apply SepWPp.exists_elim; intro u80
  apply SepWPp.exists_elim; intro w0; apply SepWPp.exists_elim; intro w8
  apply SepWPp.exists_elim; intro w16; apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w32; apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro d_w0; apply SepWPp.exists_elim; intro d_w8
  apply SepWPp.exists_elim; intro d_w16; apply SepWPp.exists_elim; intro d_w24
  apply SepWPp.exists_elim; intro d_w32
  let Rest508 : SepProp :=
    (pbA ↦₆₄ 0x8000000000000002#64) ∗ memRegion (pbA + 184#64) 40 ∗
    stackAt fsp encoderFromPbStack ∗
    v2hs_optProtoUcHeap A s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
    v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    statesFromPbJumpTableAt b ∗ A.pool
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    memRegion fsp 2304 ∗
    v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    Rest508 by dsimp only [Rest508, fsp]; ac_rfl)) ?_
  refine sepWPp_seq_clean
    (mid := if (d_w0 + 1#64 == 0#64) = true
            then (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64
            else (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 592#64)
    (P_mid := memRegion fsp 896 ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 1232 ∗
      v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest508)
    (Q_regs := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = s1.readReg64 .x21 ∧
      s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s2 s0)
    (v2hs_copy_pb_to_stack_508 s0 s1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 Rest508
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx27_2, hx22_2, htr2⟩
  have hx21_2' : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by rw [hx21_2, hx21_1]
  have hpb_tail := v2hstop_pb128_entails_pbEncTailAt pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpb_col := v2hstop_pbEncTailAt_entails_full_224 pbA w8 w16 w24 w32 w40 w48
  have hcol_pb :
      (memRegion fsp 896 ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest508) ⊢
      v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      (v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       (stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool)) := by
    dsimp only [Rest508]
    refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x8000000000000002#64) ∗
       v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
         w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (pbA + 184#64) 40) ∗
      (v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
       v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
       v2hs_optProtoUcHeap A s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb_tail) (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hcol_pb ?_
  cases hdec : s.receivingCt1 with
  | none =>
    have hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true := by
      rw [hdec]; trivial
    rw [show (none : Option PolynomialDecoder).map pbToProtoPolyDecoder = none from rfl]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v2hstop_optProtoDecoderHeap_none_extract A d_w0 d_w8 d_w16 d_w24 d_w32)) ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hd_w0 => ?_
    have hd_w0_beq : (d_w0 + 1#64 == 0#64) = true := by rw [hd_w0]; exact noneCap_add_one_beq_zero
    simp only [hd_w0_beq, ↓reduceIte] at hpc2
    exact SepWPp.weaken_pre (Entails.of_eq (by
      dsimp only [fsp]; rw [hdec, show (none : Option PolynomialDecoder).map pbToProtoPolyDecoder = none from rfl]
      ac_rfl))
      (v2hstop_headerSent_3348_to_ret hA s hsome_enc_9036 hpts hdec_ok
        s0 s2 out pbA R u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2' hx22_2 hx27_2 htr2)
  | some d =>
    rw [show (some d : Option PolynomialDecoder).map pbToProtoPolyDecoder = some (pbToProtoPolyDecoder d) from rfl]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v2hstop_optProtoDecoderHeap_some_extract A d d_w0 d_w8 d_w16 d_w24 d_w32)) ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hd_cap, hd_pts⟩ => ?_
    have hd_w0_beq : (d_w0 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (v4_ptsCap_add_one_ne_zero hd_cap)
    simp only [hd_w0_beq, Bool.false_eq_true, ↓reduceIte] at hpc2
    let Rest592 : SepProp :=
      v2hs_optProtoDecoderHeap A (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
      v2hs_optProtoUcHeap A s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest592 by
      dsimp only [Rest592, fsp]; ac_rfl)) ?_
    refine sepWPp_seq_clean
      (mid := if (d_w24.extractLsb' 0 32 == 480#32) = true
              then (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64
              else (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 604#64)
      (P_mid := v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest592)
      (Q_regs := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧ s3.readReg64 .x22 = d_w0 ∧
        s3.readReg64 .x27 = s2.readReg64 .x27 ∧ TraceCalleeSaved s3 s0)
      (v2hs_check_ptsNeeded_592 s0 s2 out d_w0 d_w8 d_w16 d_w24 d_w32 Rest592
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2) ?_
    intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hx22_3, hx27_3, htr3⟩
    have hx21_3' : s3.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by rw [hx21_3, hx21_2']
    have hx27_3' : s3.readReg64 .x27 = pbA := by rw [hx27_3, hx27_2]
    by_cases hpts_dec : (d.ptsNeeded == 480#32) = true
    · have hpts_dw24 : (d_w24.extractLsb' 0 32 == 480#32) = true := by rw [hd_pts]; exact hpts_dec
      simp only [hpts_dw24, ↓reduceIte] at hpc3
      have hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true := by
        rw [hdec]; exact hpts_dec
      exact SepWPp.weaken_pre (Entails.of_eq (by
        dsimp only [Rest592, fsp]
        rw [hdec, show (some d : Option PolynomialDecoder).map pbToProtoPolyDecoder = some (pbToProtoPolyDecoder d) from rfl]
        ac_rfl))
        (v2hstop_headerSent_3348_to_ret hA s hsome_enc_9036 hpts hdec_ok
          s0 s3 out pbA R u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx21_3' hx22_3 hx27_3' htr3)
    · have hpts_f : (d.ptsNeeded == 480#32) = false := Bool.eq_false_iff.mpr hpts_dec
      have hpts_dw24 : (d_w24.extractLsb' 0 32 == 480#32) = false := by rw [hd_pts]; exact hpts_f
      simp only [hpts_dw24, Bool.false_eq_true, ↓reduceIte] at hpc3
      rw [v2hs_from_pb_headerSent_bad_pts_eq F s d hdec hpts_f]
      apply SepWPp.of_sepWP_ret
      have hret := v2hs_err_uc_604_to_ret (A := A) (F := F) hA s0 s3 out s.uc
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
        (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 htr3
      exact SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
        (v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
         v2hs_optProtoUcHeap A s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTableAt b ∗ A.pool) by dsimp only [Rest592, fsp]; ac_rfl))
        (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (by dsimp only [fsp]; ac_rfl))))
        (SepWP.mono hret fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩)

/-- Unconditional post-dispatch step for `InnerState.headerSent s` at `+508#64`. -/
theorem states_from_pb_headerSent_508
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (henc : EncoderFromPbOkExt b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s : V1State.Chunked.HeaderSent)
    (hpts : optEncoderPtsBound s.sendingEk)
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 508#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.headerSent s)) ∗
        statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  states_from_pb_headerSent_508_of_some_enc hA s
    (v2hstop_some_enc_9036_to_ret hA henc hdec s)
    hpts s0 s1 out pbA R hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx27_1 htr1

/-- Variant 2 (`InnerState.headerSent`, `+508`) of `<States>::from_pb`. -/
theorem states_from_pb_headerSent_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (henc : EncoderFromPbOkExt b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s : V1State.Chunked.HeaderSent) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.headerSent s) }) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesFromPbVariantSpec, v1StatePtsBound, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align, hpts⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A pbA (some (.headerSent s)) ∗
       statesFromPbJumpTableAt b ∗
       A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_from_pb_prologue (b := b) (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A pbA (some (.headerSent s)) ∗
     statesFromPbJumpTableAt b ∗
     A.pool)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  have htag_eq : optProtoInnerStateAt A pbA (some (.headerSent s)) =
      (pbA ↦₆₄ 0x8000000000000002#64) ∗
      (protoChunkedHeaderSentAt A (pbA + 8#64) s ∗
       memRegion (pbA + 184#64) 40) := rfl
  have hfsp := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
    ((pbA ↦₆₄ 0x8000000000000002#64) ∗
     statesFromPbJumpTableAt b ∗
     (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (protoChunkedHeaderSentAt A (pbA + 8#64) s ∗
       memRegion (pbA + 184#64) 40) ∗
      A.pool)) by rw [htag_eq]; ac_rfl))
    (sepConj_mono_left hfsp)) ?_
  refine sepWPp_seq_clean
    (states_from_pb_dispatch_tagged s0 s1 out pbA 0x8000000000000002#64 508#64
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (protoChunkedHeaderSentAt A (pbA + 8#64) s ∗
        memRegion (pbA + 184#64) 40) ∗
       A.pool)
      TaggedVariantDispatch.headerSent hb_align hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1 |>
      SepWP.weaken_pre (Entails.of_eq (by ac_rfl))) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, _, _, hx21_2, _, hx23_2, htr2⟩
  have hx21_2' : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by
    rw [hx21_2]; bv_omega
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
    memRegion (s0.sp - 2400#64) 2304 ∗
    statesFromPbSavedCells s0 ∗
    memRegion out chunkedStatesSize ∗
    optProtoInnerStateAt A pbA (some (.headerSent s)) ∗
    statesFromPbJumpTableAt b ∗
    A.pool by rw [htag_eq]; ac_rfl)) ?_
  exact sfpProof_sepWPp_of_states_body s0 s2 out pbA { innerState := some (.headerSent s) } _ R
    (states_from_pb_headerSent_508 hA henc hdec s hpts s0 s2 out pbA R
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2' hx23_2' hx27_2 htr2)

end CryptoVerification.SpqrV1.States.FromPb

