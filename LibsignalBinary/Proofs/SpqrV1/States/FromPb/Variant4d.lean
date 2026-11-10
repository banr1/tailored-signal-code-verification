/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 4 (`EkSentCt1Received`, `+248`) — Part D

Early `ptsNeeded ≠ 80` error path (`+248 -> +304 -> ret`), `uc = none` error path, and
post-`<EkSentCt1Received>::from_pb` continuations (`+2308 -> ret`).
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## Pure & Stack Helpers (`v4d_*`) -/

theorem v4d_sepWP_pure_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : Prop} {Q : SepProp} {post : State → SepProp → Prop}
    (h : P → SepWP prog target_pc s Q post) :
    SepWP prog target_pc s (⌜P⌝ ∗ Q) post :=
  ProofLib.SepWP.pure_elim h

theorem v4d_seq_clean_weaken {prog : Program} {mid_pc target_pc : BitVec 64} {s : State}
    {P1 P1' P2 : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid_pc s P1' (fun s' P' => (P' ⊢ P2) ∧ Q s'))
    (hpre : P1 ⊢ P1')
    (h2 : ∀ s2, s2.pc = mid_pc → s2.status = .Running → Q s2 →
      SepWP prog target_pc s2 P2 post) :
    SepWP prog target_pc s P1 post :=
  SepWP.weaken_pre hpre (EncoderFromPb.seq_clean h1 h2)

theorem v4d_fsp_aligned (sp0 : BitVec 64) (h : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 2400#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_kernel

theorem v4d_sp_sub_1136_eq (sp0 : BitVec 64) :
    sp0 - 1136#64 = (sp0 - 2400#64) + 1264#64 := by bv_omega

theorem v4d_memRegion_2304_split_2228 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      ∃∗ v224 : BitVec 64, ∃∗ v232 : BitVec 32,
      ∃∗ s0_u : BitVec 64, ∃∗ s8_u : BitVec 64, ∃∗ s16_u : BitVec 64,
      ∃∗ s24_u : BitVec 64, ∃∗ s32_u : BitVec 64, ∃∗ s40_u : BitVec 64,
      ∃∗ s48_u : BitVec 64, ∃∗ s56_u : BitVec 64, ∃∗ s64_u : BitVec 64,
      ∃∗ s72_u : BitVec 64, ∃∗ s80_u : BitVec 64, ∃∗ s88_u : BitVec 64,
      ∃∗ s96_u : BitVec 64,
        ((fsp + 224#64) ↦₆₄ v224) ∗
        ((fsp + 232#64) ↦₃₂ v232) ∗
        v4b_optProtoUcWordsAt (fsp + 1392#64)
          s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u ∗
        memRegion fsp 224 ∗
        memRegion (fsp + 236#64) 1156 ∗
        memRegion (fsp + 1496#64) 392 ∗
        memRegion (fsp + 1888#64) 104 ∗
        memRegion (fsp + 1992#64) 312 := by
  have hsplit : memRegion fsp 2304 ⊢
      memRegion fsp 224 ∗
      (∃∗ v224 : BitVec 64, (fsp + 224#64) ↦₆₄ v224) ∗
      (∃∗ v232 : BitVec 32, (fsp + 232#64) ↦₃₂ v232) ∗
      memRegion (fsp + 236#64) 1156 ∗
      memRegion (fsp + 1392#64) 104 ∗
      memRegion (fsp + 1496#64) 392 ∗
      memRegion (fsp + 1888#64) 104 ∗
      memRegion (fsp + 1992#64) 312 := by
    exact split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem32_entails _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      Entails.refl _
  refine Entails.trans hsplit ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (v4b_memRegion_104_to_ucWordsAt (fsp + 1392#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro s0_u
  apply Entails.sepExists_elim; intro s8_u
  apply Entails.sepExists_elim; intro s16_u
  apply Entails.sepExists_elim; intro s24_u
  apply Entails.sepExists_elim; intro s32_u
  apply Entails.sepExists_elim; intro s40_u
  apply Entails.sepExists_elim; intro s48_u
  apply Entails.sepExists_elim; intro s56_u
  apply Entails.sepExists_elim; intro s64_u
  apply Entails.sepExists_elim; intro s72_u
  apply Entails.sepExists_elim; intro s80_u
  apply Entails.sepExists_elim; intro s88_u
  apply Entails.sepExists_elim; intro s96_u
  apply Entails.sepExists_elim; intro v232
  apply Entails.sepExists_elim; intro v224
  refine Entails.sepExists_right v224 (Entails.sepExists_right v232
    (Entails.sepExists_right s0_u (Entails.sepExists_right s8_u
      (Entails.sepExists_right s16_u (Entails.sepExists_right s24_u
        (Entails.sepExists_right s32_u (Entails.sepExists_right s40_u
          (Entails.sepExists_right s48_u (Entails.sepExists_right s56_u
            (Entails.sepExists_right s64_u (Entails.sepExists_right s72_u
              (Entails.sepExists_right s80_u (Entails.sepExists_right s88_u
                (Entails.sepExists_right s96_u ?_))))))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem v4d_memRegion_1156_104_392_entails_1652 (fsp : BitVec 64) :
    memRegion (fsp + 236#64) 1156 ∗
      memRegion (fsp + 1392#64) 104 ∗
      memRegion (fsp + 1496#64) 392 ⊢
    memRegion (fsp + 236#64) 1652 := by
  exact collapse_top <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v4d_stack_2308_err_entails_2304 (fsp d32 : BitVec 64) (d28 : BitVec 32)
    (w1896 w1904 w1912 : BitVec 64) :
    memRegion fsp 224 ∗
      ((fsp + 224#64) ↦₆₄ d32) ∗
      ((fsp + 232#64) ↦₃₂ d28) ∗
      memRegion (fsp + 236#64) 1652 ∗
      ((fsp + 1888#64) ↦₆₄ noneCap) ∗
      ((fsp + 1896#64) ↦₆₄ w1896) ∗
      ((fsp + 1904#64) ↦₆₄ w1904) ∗
      ((fsp + 1912#64) ↦₆₄ w1912) ∗
      memRegion (fsp + 1920#64) 72 ∗
      memRegion (fsp + 1992#64) 312 ⊢
    memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v4d_stack_6860_entails_2304 (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 d32 : BitVec 64) (d28 : BitVec 32)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    memRegion fsp 32 ∗
      memRegion (fsp + 64#64) 8 ∗
      memRegion (fsp + 88#64) 40 ∗
      memRegion (fsp + 152#64) 64 ∗
      v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
      ((fsp + 224#64) ↦₆₄ d32) ∗
      ((fsp + 232#64) ↦₃₂ d28) ∗
      memRegion (fsp + 236#64) 1652 ∗
      v4b_optProtoUcWordsAt (fsp + 1888#64) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 ∗
      memRegion (fsp + 1992#64) 312 ⊢
    memRegion fsp 2304 := by
  have h1888 := v4c_ucWords_312_entails_400_16 fsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h1888)))))))) ?_
  exact v4c_err_8500_stack_collapse fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 d32 d28

/-! ## Shared `+5264 -> +5348 -> ret` Error Cleanup -/

/-- From `+5264`, deallocate `optDec : Option ProtoPolynomialDecoder` (`d0, d8, d16, d24, d28, d32`)
    and exit via `+5348` with `.error (.err err)`. -/
theorem v4d_dealloc_opt_dec_5264_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (out d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (err : LibsignalSpqrV1.Error)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0)
    (hx26 : (s.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (v4b_optProtoPolyDecoderHeap A optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          (A.pool ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    v4d_fsp_aligned s0.sp hsp0_align
  cases optDec with
  | none =>
    dsimp only [v4b_optProtoPolyDecoderHeap]
    apply v4d_sepWP_pure_left; rintro rfl
    refine EncoderFromPb.seq_clean
      (v4_states_from_pb_dealloc_none_proto_decoder_5264 s0 s (s0.sp - 2400#64) out d8 (s.readReg64 .x26)
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          (A.pool ∗ Rest))
        hpc hrun hsp hx19 hx24 hx28 rfl htr)
      ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, _, _, hx26_1, htr1⟩
    have hx26_1' : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err := by
      rw [hx26_1, hx26]
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (v4_states_from_pb_err_5348 (A := A) (F := F) s0 s1 out err (A.pool ∗ Rest)
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1' htr1)
  | some pb =>
    dsimp only [v4b_optProtoPolyDecoderHeap]
    rw [sepConj_assoc]
    apply v4d_sepWP_pure_left; rintro ⟨rfl, rfl, rfl, hle, hcap, _, _⟩
    have hpre_split :
        (if d0 = 0#64 then emp
         else A.live d8 (d0.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 d8 pb.pts ∗
           memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool ∗ Rest ⊢
        (if d0 = 0#64 then emp
         else A.live d8 (d0.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 d8 pb.pts ∗
           memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
          A.pool ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           Rest) := by
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)))) ?_
      exact Entails.of_eq (by ac_rfl)
    refine SepWP.weaken_pre hpre_split ?_
    refine EncoderFromPb.seq_clean
      (v4_states_from_pb_dealloc_some_proto_decoder_5264 hA s0 s (s0.sp - 2400#64) out
        d8 d0 (s.readReg64 .x26) pb.pts
        (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest)
        hfsp_align hle hcap hpc hrun hsp hx19 hx24 hx28 rfl hx20 htr)
      ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, _, _, hx26_1, htr1⟩
    have hx26_1' : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err := by
      rw [hx26_1, hx26]
    have hpre_join :
        A.pool ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           Rest) ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          (A.pool ∗ Rest) := by
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
          (memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           (A.pool ∗ Rest)) by ac_rfl)) ?_
      exact sepConj_mono_left (v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    exact SepWP.weaken_pre hpre_join
      (v4_states_from_pb_err_5348 (A := A) (F := F) s0 s1 out err (A.pool ∗ Rest)
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1' htr1)

/-! ## Early Error Path (`s.receivingCt2 = some d`, `d.ptsNeeded ≠ 80#32`, `+248 -> +304 -> +5276 -> +5348 -> ret`) -/

/-- From `+304`, drop `optUc : Option V1State.Unchunked.EkSentCt1Received` and reach `+5276`
    with `x26 = 2#64` (`spqrErrorByte .msgDecode`). -/
theorem v4d_drop_opt_uc_304_to_5276
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x20_val : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSentCt1Received)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u56)
    (hx1 : s.readReg64 .x1 = u48)
    (hx11 : s.readReg64 .x11 = u8)
    (hx12 : s.readReg64 .x12 = u32)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = u24)
    (hx22 : s.readReg64 .x22 = u0)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx25 : s.readReg64 .x25 = u80)
    (hx26 : s.readReg64 .x26 = u72)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5276#64) s
      (v4b_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  cases optUc with
  | none =>
    dsimp only [v4b_optProtoUcHeap]
    apply v4d_sepWP_pure_left; rintro rfl
    exact v4_states_from_pb_drop_proto_uc_none_304 s0 s fsp out ptsPtr ptsCap x20_val
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc hrun hsp hx19 hx20 hx22 hx24 hx28 htr
  | some u =>
    cases hauth : u.auth with
    | none =>
      dsimp only [v4b_optProtoUcHeap]
      rw [hauth]
      dsimp only [v4b_optProtoAuthHeap]
      have hdealloc :
          (v4b_vecU8Heap A u.dk u0 u8 u16 ∗
           v4b_vecU8Heap A u.ct1 u24 u32 u40 ∗
           ⌜u48 = noneCap⌝ ∗ ⌜u96 = u.epoch⌝) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame ⊢
          ⌜u0.toNat < 2 ^ 63 ∧ u48 = noneCap⌝ ∗
          (vecCapPtrDealloc A u0 u8 ∗
           vecCapPtrDealloc A u24 u32 ∗
           A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
        refine Entails.trans
          (sepConj_mono_left
            (sepConj_mono (v4b_vecU8Heap_entails_dealloc A u.dk u0 u8 u16)
              (sepConj_mono_left (v4b_vecU8Heap_entails_dealloc A u.ct1 u24 u32 u40)))) ?_
        refine Entails.trans (Entails.of_eq (show _ =
          ⌜u0.toNat < 2 ^ 63⌝ ∗ ⌜u24.toNat < 2 ^ 63⌝ ∗ ⌜u48 = noneCap⌝ ∗ ⌜u96 = u.epoch⌝ ∗
          (vecCapPtrDealloc A u0 u8 ∗ vecCapPtrDealloc A u24 u32 ∗
           A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        apply Entails.pure_left; intro hu0
        apply Entails.pure_left; intro _
        apply Entails.pure_left; intro hu48
        apply Entails.pure_left; intro _
        exact Entails.pure_right ⟨hu0, hu48⟩ (Entails.refl _)
      refine SepWP.weaken_pre hdealloc ?_
      apply v4d_sepWP_pure_left; rintro ⟨hu0_lt, rfl⟩
      exact v4_states_from_pb_drop_proto_uc_none_auth_304 hA s0 s
        fsp out ptsPtr ptsCap x20_val u8 u0 u32 u24 Frame
        hfsp_align hu0_lt hpc hrun hsp hx1 hx11 hx12 hx19 hx20 hx21 hx22 hx24 hx28 htr
    | some auth =>
      dsimp only [v4b_optProtoUcHeap]
      rw [hauth]
      dsimp only [v4b_optProtoAuthHeap]
      have hdealloc :
          (v4b_vecU8Heap A u.dk u0 u8 u16 ∗
           v4b_vecU8Heap A u.ct1 u24 u32 u40 ∗
           (v4b_vecU8Heap A auth.rootKey u48 u56 u64 ∗
            v4b_vecU8Heap A auth.macKey u72 u80 u88) ∗
           ⌜u96 = u.epoch⌝) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame ⊢
          ⌜u0.toNat < 2 ^ 63 ∧ u48.toNat < 2 ^ 63⌝ ∗
          (vecCapPtrDealloc A u48 u56 ∗
           vecCapPtrDealloc A u72 u80 ∗
           vecCapPtrDealloc A u0 u8 ∗
           vecCapPtrDealloc A u24 u32 ∗
           A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
        refine Entails.trans
          (sepConj_mono_left
            (sepConj_mono (v4b_vecU8Heap_entails_dealloc A u.dk u0 u8 u16)
              (sepConj_mono (v4b_vecU8Heap_entails_dealloc A u.ct1 u24 u32 u40)
                (sepConj_mono_left
                  (sepConj_mono (v4b_vecU8Heap_entails_dealloc A auth.rootKey u48 u56 u64)
                    (v4b_vecU8Heap_entails_dealloc A auth.macKey u72 u80 u88)))))) ?_
        refine Entails.trans (Entails.of_eq (show _ =
          ⌜u0.toNat < 2 ^ 63⌝ ∗ ⌜u24.toNat < 2 ^ 63⌝ ∗ ⌜u48.toNat < 2 ^ 63⌝ ∗
          ⌜u72.toNat < 2 ^ 63⌝ ∗ ⌜u96 = u.epoch⌝ ∗
          (vecCapPtrDealloc A u48 u56 ∗ vecCapPtrDealloc A u72 u80 ∗
           vecCapPtrDealloc A u0 u8 ∗ vecCapPtrDealloc A u24 u32 ∗
           A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        apply Entails.pure_left; intro hu0
        apply Entails.pure_left; intro _
        apply Entails.pure_left; intro hu48
        apply Entails.pure_left; intro _
        apply Entails.pure_left; intro _
        exact Entails.pure_right ⟨hu0, hu48⟩ (Entails.refl _)
      refine SepWP.weaken_pre hdealloc ?_
      apply v4d_sepWP_pure_left; rintro ⟨hu0_lt, hu48_lt⟩
      exact v4_states_from_pb_drop_proto_uc_some_auth_304 hA s0 s
        fsp out ptsPtr ptsCap x20_val u56 u48 u80 u72 u8 u0 u32 u24 Frame
        hfsp_align hu0_lt hu48_lt hpc hrun hsp
        hx0 hx1 hx11 hx12 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 htr

/-- Complete `+248 -> ret` execution when `s.receivingCt2 = some d` and `d.ptsNeeded ≠ 80#32`. -/
theorem v4d_ekSent_err_ptsNeeded_ne_248
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSentCt1Received)
    (d : PolynomialDecoder)
    (hne : d.ptsNeeded ≠ 80#32)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 248#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (v4b_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
        (pbA ↦₆₄ 0x8000000000000004#64) ∗
        memRegion (pbA + 152#64) 72 ∗
        v4b_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ekSentCt1Received { uc := optUc, receivingCt2 := some d }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    v4d_fsp_aligned s0.sp hsp0_align
  rw [v4b_states_from_pb_ekSentCt1Received_ptsNeeded_ne F optUc d hne]
  dsimp only [v4b_optProtoPolyDecoderHeap, pbToProtoPolyDecoder]
  rw [sepConj_assoc]
  apply v4d_sepWP_pure_left; rintro ⟨rfl, rfl, rfl, hle, hcap, _, _⟩
  have hd0_lt : d0.toNat < 2 ^ 63 := by omega
  let PtsBuf : SepProp :=
    if d0 = 0#64 then emp
    else A.live d8 (d0.toNat * 24) 8 ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 d8 d.pts ∗
      memRegion (d8 + BitVec.ofNat 64 (d.pts.length * 24)) ((d0.toNat - d.pts.length) * 24)
  change SepWP _ _ s1 (PtsBuf ∗ _) _
  have h248 := v4b_step_248_some_ne_to_304 s1 pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
    d0 d8 (BitVec.ofNat 64 d.pts.length) d.ptsNeeded d.polys d32
    ((pbA ↦₆₄ 0x8000000000000004#64) ∗ memRegion (pbA + 152#64) 72 ∗
     v4b_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
     PtsBuf ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
    hd0_lt hne hpc1 hrun1 hx27_1
  refine SepWP.weaken_pre ?_ (EncoderFromPb.seq_clean h248 ?_)
  · exact Entails.of_eq (by ac_rfl)
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, _, _, _, hx11_2, hx12_2, _, _, _, hx19_2,
      hx20_2, hx21_2, hx22_2, _, hx24_2, hx25_2, hx26_2, _, hx28_2, htr2⟩
    rw [hsp1] at hsp2; rw [hx19_1] at hx19_2; have htr2 := htr2.trans htr1
    have hpb := v4b_pbA_all_words_entails_memRegion pbA 0x8000000000000004#64
      u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
      d0 d8 (BitVec.ofNat 64 d.pts.length) d.ptsNeeded d.polys d32
    have hst := v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
    have h304 := v4d_drop_opt_uc_304_to_5276 hA s0 s2 (s0.sp - 2400#64) out d8 d0 (BitVec.ofNat 64 d.pts.length)
      u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 optUc
      (PtsBuf ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTableAt b)
      hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx11_2 hx12_2 hx19_2 hx20_2
      hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2
    refine SepWP.weaken_pre ?_ (EncoderFromPb.seq_clean h304 ?_)
    · refine Entails.trans
        (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 0x8000000000000004#64) ∗
           v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
           v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 (BitVec.ofNat 64 d.pts.length) d.ptsNeeded d.polys d32 ∗
           memRegion (pbA + 152#64) 72) ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (v4b_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
           A.pool ∗ PtsBuf ∗ memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           statesFromPbJumpTableAt b) by ac_rfl))
        (Entails.trans (sepConj_mono hpb (sepConj_mono_left hst)) (Entails.of_eq (by ac_rfl)))
    · intro s3 hpc3 hrun3 ⟨hpres3, hx20_3⟩
      have h5276 := v4_states_from_pb_dealloc_proto_decoder_5276 hA s0 s3 (s0.sp - 2400#64) out d8 d0 2#64 d.pts
        (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
         memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTableAt b)
        hfsp_align hle hcap hpc3 hrun3 hpres3 hx20_3
      refine v4d_seq_clean_weaken h5276 ?_ ?_
      · dsimp only [PtsBuf]; exact Entails.of_eq (by ac_rfl)
      · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, _, _, hx26_4, htr4⟩
        have hx26_4' : (s4.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .msgDecode := by
          rw [hx26_4]; rfl
        have herr := v4_states_from_pb_err_5348 (A := A) (F := F) s0 s4 out .msgDecode
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
          hsp0_align hpc4 hrun4 hsp4 hx19_4 hx26_4' htr4
        refine SepWP.weaken_pre ?_ (SepWP.mono herr ?_)
        · refine Entails.trans
            (Entails.of_eq (show _ =
              (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
              (memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl))
            (sepConj_mono_left (v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)))
        · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
          exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-! ## `+2228 -> +5264 -> ret` (`s.uc = none`) and `+2308 -> ret` Post-Call Branches -/

/-- From `+2228`, when `s.uc = none` (`u0 = noneCap`), branches to `+5264`, deallocates `optDec`,
    and exits with `.error (.err .stateDecode)`. -/
theorem v4d_ekSent_uc_none_2228_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s2 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2228#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out)
    (hx20_2 : s2.readReg64 .x20 = d16)
    (hx22_2 : s2.readReg64 .x22 = noneCap)
    (hx24_2 : s2.readReg64 .x24 = d8)
    (hx28_2 : s2.readReg64 .x28 = d0)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      (v4b_optProtoPolyDecoderHeap A optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b))
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean (v4b_step_2228_none_to_5264 s2 _ hpc2 hrun2 hx22_2) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, _, _, hx19_3, hx20_3, hx24_3, hx26_3, hx28_3, htr3⟩
  rw [hsp2] at hsp3; rw [hx19_2] at hx19_3; rw [hx20_2] at hx20_3
  rw [hx24_2] at hx24_3; rw [hx28_2] at hx28_3; have htr3 := htr3.trans htr2
  have hx26_3' : (s3.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx26_3]; rfl
  have hret := v4d_dealloc_opt_dec_5264_to_ret (A := A) (F := F) hA s0 s3 out d0 d8 d16 d32 d24 d28
    optDec .stateDecode (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx24_3 hx28_3 hx26_3' htr3
  refine SepWP.mono hret ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-- From `+2308`, when `EkSentCt1Received.from_pb` returned `.error e`:
    steps `+2308 -> +5264`, deallocates `optDec`, and exits with `.error (.err .stateDecode)`. -/
theorem v4d_ekSent_2308_err_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s3 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (e : StatesError)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx20_3 : s3.readReg64 .x20 = d16)
    (hx24_3 : s3.readReg64 .x24 = d8)
    (hx28_3 : s3.readReg64 .x28 = d0)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        v4b_optProtoPolyDecoderHeap A optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTableAt b)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := v4d_fsp_aligned s0.sp hsp0_align
  have h1896 :
      ekSentCt1ReceivedResultAt A (F := F) (fsp + 1888#64) (.error e) ⊢
      ∃∗ w1896 : BitVec 64, ∃∗ w1904 : BitVec 64, ∃∗ w1912 : BitVec 64,
        ⌜w1896.extractLsb' 0 8 = 0#8⌝ ∗
        ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
        memRegion (fsp + 1920#64) 72 := by
    dsimp only [ekSentCt1ReceivedResultAt]
    have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
    have ha1897 : (fsp + 1888#64) + 9#64 = (fsp + 1896#64) + 1#64 := by bv_omega
    rw [ha1896, ha1897]
    refine Entails.trans (sepConj_mono_right (v4b_byte_region95_to_words (fsp + 1896#64) 0#8)) ?_
    simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro w1896
    apply Entails.sepExists_elim; intro w1904
    apply Entails.sepExists_elim; intro w1912
    refine Entails.sepExists_right w1896
      (Entails.sepExists_right w1904 (Entails.sepExists_right w1912 (Entails.of_eq (by ac_rfl))))
  refine SepWP.weaken_pre (sepConj_mono_left h1896) ?_
  wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w1896
  apply ProofLib.SepWP.exists_left; intro w1904
  apply ProofLib.SepWP.exists_left; intro w1912
  apply v4d_sepWP_pure_left; intro hw1896
  have h2308 := v4b_step_2308_err_to_5264 s3 fsp out d0 d8 d16 d28 w1896 w1904 w1912
    (memRegion fsp 224 ∗ ((fsp + 224#64) ↦₆₄ d32) ∗ memRegion (fsp + 236#64) 1652 ∗
     memRegion (fsp + 1920#64) 72 ∗ memRegion (fsp + 1992#64) 312 ∗
     v4b_optProtoPolyDecoderHeap A optDec d0 d8 d16 d24 d28 d32 ∗
     stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ A.pool ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
    hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx24_3 hx28_3
  refine v4d_seq_clean_weaken h2308 ?_ ?_
  · dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)
  · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx20_4, hx24_4, hx26_4, hx28_4, htr4⟩
    have htr4 := htr4.trans htr3
    have hx26_4' : (s4.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx26_4, hw1896]; rfl
    have h2304 := v4d_stack_2308_err_entails_2304 fsp d32 d28 w1896 w1904 w1912
    have hret := v4d_dealloc_opt_dec_5264_to_ret (A := A) (F := F) hA s0 s4 out d0 d8 d16 d32 d24 d28
      optDec .stateDecode (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc4 hrun4 hsp4 hx19_4 hx20_4 hx24_4 hx28_4 hx26_4' htr4
    refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
    · refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion fsp 224 ∗ ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
           memRegion (fsp + 236#64) 1652 ∗ ((fsp + 1888#64) ↦₆₄ noneCap) ∗
           ((fsp + 1896#64) ↦₆₄ w1896) ∗ ((fsp + 1904#64) ↦₆₄ w1904) ∗
           ((fsp + 1912#64) ↦₆₄ w1912) ∗ memRegion (fsp + 1920#64) 72 ∗
           memRegion (fsp + 1992#64) 312) ∗
          (v4b_optProtoPolyDecoderHeap A optDec d0 d8 d16 d24 d28 d32 ∗
           stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ A.pool ∗
           (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) by ac_rfl))
        (Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by dsimp only [fsp]; ac_rfl)))
    · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-- From `+2308`, when `EkSentCt1Received.from_pb` returned `.ok uc` and `s.receivingCt2 = none`
    (`x28 = noneCap`): steps `+2308 -> +6860 -> +5348 -> ret` with `.error (.err .stateDecode)`. -/
theorem v4d_ekSent_2308_ok_none_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s3 : State) (out pbA d32 : BitVec 64) (d28 : BitVec 32)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx28_3 : s3.readReg64 .x28 = noneCap)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTableAt b)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := v4d_fsp_aligned s0.sp hsp0_align
  dsimp only [ekSentCt1ReceivedResultAt]
  refine SepWP.weaken_pre
    (sepConj_mono (v4b_ekSentCt1ReceivedAt_unpack A (fsp + 1888#64) uc)
      (sepConj_mono_left (v4c_memRegion_224_to_ucSpillSlots fsp))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v32; apply ProofLib.SepWP.exists_left; intro v40
  apply ProofLib.SepWP.exists_left; intro v48; apply ProofLib.SepWP.exists_left; intro v56
  apply ProofLib.SepWP.exists_left; intro v72; apply ProofLib.SepWP.exists_left; intro v80
  apply ProofLib.SepWP.exists_left; intro v128; apply ProofLib.SepWP.exists_left; intro v136
  apply ProofLib.SepWP.exists_left; intro v144; apply ProofLib.SepWP.exists_left; intro v216
  apply ProofLib.SepWP.exists_left; intro rkCap; apply ProofLib.SepWP.exists_left; intro rkPtr
  apply ProofLib.SepWP.exists_left; intro rkLen; apply ProofLib.SepWP.exists_left; intro mkCap
  apply ProofLib.SepWP.exists_left; intro mkPtr; apply ProofLib.SepWP.exists_left; intro mkLen
  apply ProofLib.SepWP.exists_left; intro dkCap; apply ProofLib.SepWP.exists_left; intro dkPtr
  apply ProofLib.SepWP.exists_left; intro dkLen; apply ProofLib.SepWP.exists_left; intro ct1Cap
  apply ProofLib.SepWP.exists_left; intro ct1Ptr; apply ProofLib.SepWP.exists_left; intro ct1Len
  have hdealloc := v4b_ekSentCt1ReceivedHeap_entails_dealloc A
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left hdealloc)) ?_
  wp_simp_pre [sepConj_assoc]
  refine SepWP.weaken_pre (Entails.of_eq (sepConj_left_comm _ _ _)) ?_
  apply v4d_sepWP_pure_left; intro hrk_lt
  have h6860 := v4b_step_2308_ok_none_to_6860 s3 fsp out
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
    v72 v128 v144
    (vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗
     vecCapPtrDealloc A dkCap dkPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr ∗
     ((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
     ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗
     ((fsp + 216#64) ↦₆₄ v216) ∗ memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
     memRegion (fsp + 88#64) 40 ∗ memRegion (fsp + 152#64) 64 ∗
     ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
     memRegion (fsp + 236#64) 1652 ∗ memRegion (fsp + 1992#64) 312 ∗
     stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ A.pool ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
    hfsp_align hrk_lt hpc3 hrun3 hsp3 hx19_3 hx28_3
  refine v4d_seq_clean_weaken h6860 ?_ ?_
  · dsimp only [fsp, v4c_ucSpillSlots]; exact Entails.of_eq (by ac_rfl)
  · intro s4 hpc4 hrun4 ⟨hsp4, hx0_4, hx1_4, hx9_4, hx19_4, hx22_4, hx26_4, htr4⟩
    have htr4 := htr4.trans htr3
    have hst := v4_stackAt_encoderFromPbStack_to_allocHook fsp
    have hdrop := v4_states_from_pb_drop_uc_6860 hA s0 s4 fsp out
      rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap
      (memRegion (fsp - 5152#64) 1056 ∗
       v4b_optProtoUcWordsAt (fsp + 1888#64)
         rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
       ((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
       ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗
       ((fsp + 216#64) ↦₆₄ v216) ∗ memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
       memRegion (fsp + 88#64) 40 ∗ memRegion (fsp + 152#64) 64 ∗
       ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
       memRegion (fsp + 236#64) 1652 ∗ memRegion (fsp + 1992#64) 312 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hfsp_align hpc4 hrun4 hsp4 hx0_4 hx1_4 hx9_4 hx19_4 hx22_4 hx26_4 htr4
    refine SepWP.weaken_pre ?_ (EncoderFromPb.seq_clean hdrop ?_)
    · refine Entails.trans
        (Entails.of_eq (show _ =
          stackAt fsp encoderFromPbStack ∗
          (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗ ((fsp + 144#64) ↦₆₄ dkPtr) ∗
           vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗
           vecCapPtrDealloc A dkCap dkPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr ∗ A.pool ∗
           v4b_optProtoUcWordsAt (fsp + 1888#64)
             rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
           ((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
           ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗
           ((fsp + 216#64) ↦₆₄ v216) ∗ memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
           memRegion (fsp + 88#64) 40 ∗ memRegion (fsp + 152#64) 64 ∗
           ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
           memRegion (fsp + 236#64) 1652 ∗ memRegion (fsp + 1992#64) 312 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl))
        (Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl)))
    · intro s5 hpc5 hrun5 ⟨hsp5, hx19_5, hx26_5, htr5⟩
      have hx26_5' : (s5.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
        rw [hx26_5]; rfl
      have hst_back := v4_stackAt_allocHook_to_encoderFromPbStack fsp
      have h2304 := v4d_stack_6860_entails_2304 fsp
        v32 v40 v48 v56 ct1Ptr v80 ct1Cap v136 dkPtr v216 d32 d28
        rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
      dsimp only [v4c_ucSpillSlots] at h2304
      have herr := v4_states_from_pb_err_5348 (A := A) (F := F) s0 s5 out .stateDecode
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
        hsp0_align hpc5 hrun5 hsp5 hx19_5 hx26_5' htr5
      refine SepWP.weaken_pre ?_ (SepWP.mono herr ?_)
      · refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
             memRegion (fsp + 152#64) 64 ∗
             (((fsp + 32#64) ↦₆₄ v32) ∗ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
              ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 80#64) ↦₆₄ v80) ∗
              ((fsp + 128#64) ↦₆₄ ct1Cap) ∗ ((fsp + 136#64) ↦₆₄ v136) ∗
              ((fsp + 144#64) ↦₆₄ dkPtr) ∗ ((fsp + 216#64) ↦₆₄ v216)) ∗
             ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
             memRegion (fsp + 236#64) 1652 ∗
             v4b_optProtoUcWordsAt (fsp + 1888#64)
               rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
             memRegion (fsp + 1992#64) 312) ∗
            (statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl))
          (sepConj_mono hst_back (sepConj_mono_left h2304))
      · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v4d_sepWPp_exists_left {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Q : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ x, SepWPp prog target_pc s (P x ∗ Q) post Qp) :
    SepWPp prog target_pc s ((∃∗ x, P x) ∗ Q) post Qp := by
  intro R' hm
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R' hmx

theorem v4d_sepWPp_pure_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : Prop} {Q : SepProp} {post Qp : State → SepProp → Prop}
    (h : P → SepWPp prog target_pc s Q post Qp) :
    SepWPp prog target_pc s (⌜P⌝ ∗ Q) post Qp := by
  intro R' hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R' hm.2

theorem v4d_seq_clean_p_weaken {prog : Program} {mid_pc target_pc : BitVec 64} {s : State}
    {P1 P1' P2 : SepProp} {Q : State → Prop} {post Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid_pc s P1' (fun s' P' => (P' ⊢ P2) ∧ Q s'))
    (hpre : P1 ⊢ P1')
    (h2 : ∀ s2, s2.pc = mid_pc → s2.status = .Running → Q s2 →
      SepWPp prog target_pc s2 P2 post Qp) :
    SepWPp prog target_pc s P1 post Qp :=
  SepWPp.weaken_pre hpre (v4_sepWPp_seq_clean h1 h2)

theorem v4d_pull_pures {P1 P2 : Prop} {A B C : SepProp} :
    (⌜P1⌝ ∗ A) ∗ (⌜P2⌝ ∗ B) ∗ C = ⌜P1⌝ ∗ ⌜P2⌝ ∗ (A ∗ B ∗ C) := by ac_rfl

theorem v4d_sepWPp_call {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    hnext

theorem v4d_vecU8Heap_cap_lt (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) :
    v4b_vecU8Heap A bs cap ptr len ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ v4b_vecU8Heap A bs cap ptr len := by
  unfold v4b_vecU8Heap
  apply Entails.pure_left; rintro ⟨h1, hcap⟩
  exact Entails.pure_right hcap (Entails.pure_right ⟨h1, hcap⟩ (Entails.refl _))

theorem v4d_ekSentCt1ReceivedHeap_rk_lt (A : RustAlloc) {F : ShaCompress}
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    v4b_ekSentCt1ReceivedHeap A
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ⊢
    ⌜rkCap.toNat < 2 ^ 63⌝ ∗
    v4b_ekSentCt1ReceivedHeap A
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc := by
  unfold v4b_ekSentCt1ReceivedHeap
  exact Entails.trans (sepConj_mono_left (v4d_vecU8Heap_cap_lt A uc.auth.rootKey rkCap rkPtr rkLen))
    (Entails.of_eq (sepConj_assoc _ _ _))

theorem v4d_optProtoPolyDecoderHeap_some_d0_lt (A : RustAlloc) (pb : ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64) :
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 ⊢
    ⌜d0.toNat < 2 ^ 63⌝ ∗
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 := by
  unfold v4b_optProtoPolyDecoderHeap
  apply Entails.pure_left; rintro ⟨h1, h2, h3, hle, hcap, h6, h7⟩
  have hd0 : d0.toNat < 2 ^ 63 := by omega
  exact Entails.pure_right hd0 (Entails.pure_right ⟨h1, h2, h3, hle, hcap, h6, h7⟩ (Entails.refl _))

theorem v4d_optProtoUcHeap_some_u0_lt (A : RustAlloc) (u : V1State.Unchunked.EkSentCt1Received)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64) :
    v4b_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ⊢
    ⌜u0.toNat < 2 ^ 63⌝ ∗
    v4b_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 := by
  dsimp only [v4b_optProtoUcHeap]
  exact Entails.trans (sepConj_mono_left (v4d_vecU8Heap_cap_lt A u.dk u0 u8 u16))
    (Entails.of_eq (sepConj_assoc _ _ _))

theorem v4d_ekSent_from_pb_error_eq (F : ShaCompress)
    (u : V1State.Unchunked.EkSentCt1Received) (e : StatesError)
    (h : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .error e) :
    e = .err .stateDecode := by
  unfold Unchunked.SendEk.EkSentCt1Received.from_pb at h
  split at h
  · rcases hauth : u.auth with _ | a <;> simp [hauth] at h
    exact h.symm
  · simp at h; exact h.symm

theorem v4d_rot3 (A B C D : SepProp) : A ∗ B ∗ C ∗ D = C ∗ A ∗ B ∗ D := by ac_rfl

theorem v4d_rot4 (A1 A2 A3 B C : SepProp) :
    A1 ∗ A2 ∗ A3 ∗ B ∗ C = B ∗ A1 ∗ A2 ∗ A3 ∗ C := by ac_rfl

/-- From `+2308`, when `EkSentCt1Received.from_pb` returned `.ok uc` and `s.receivingCt2 = some d`:
    steps `+2308 -> +35448` (`decoderFromPb`), then `+2472 -> +8180 / +8500 -> ret`. -/
theorem v4d_ekSent_2308_ok_some_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s0 s3 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (d : PolynomialDecoder) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2308#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx20_3 : s3.readReg64 .x20 = d16)
    (hx23_3 : s3.readReg64 .x23 = d24.zeroExtend 64)
    (hx24_3 : s3.readReg64 .x24 = d8)
    (hx28_3 : s3.readReg64 .x28 = d0)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s3
      (ekSentCt1ReceivedResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
        memRegion (s0.sp - 2400#64) 224 ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        v4b_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTableAt b)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (match decoderFromPbResult (pbToProtoPolyDecoder d) with
             | .error _ => .error (.err .stateDecode)
             | .ok dec => .ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := v4d_fsp_aligned s0.sp hsp0_align
  dsimp only [ekSentCt1ReceivedResultAt]
  refine SepWPp.weaken_pre (sepConj_mono_left (v4b_ekSentCt1ReceivedAt_unpack A (fsp + 1888#64) uc)) ?_
  apply v4d_sepWPp_exists_left; intro rkCap; apply v4d_sepWPp_exists_left; intro rkPtr
  apply v4d_sepWPp_exists_left; intro rkLen; apply v4d_sepWPp_exists_left; intro mkCap
  apply v4d_sepWPp_exists_left; intro mkPtr; apply v4d_sepWPp_exists_left; intro mkLen
  apply v4d_sepWPp_exists_left; intro dkCap; apply v4d_sepWPp_exists_left; intro dkPtr
  apply v4d_sepWPp_exists_left; intro dkLen; apply v4d_sepWPp_exists_left; intro ct1Cap
  apply v4d_sepWPp_exists_left; intro ct1Ptr; apply v4d_sepWPp_exists_left; intro ct1Len
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _))
    (Entails.trans (Entails.of_eq (v4d_rot3 _ _ _ _))
      (sepConj_mono_left (v4c_memRegion_224_to_ucSpillSlots fsp)))) ?_
  apply v4d_sepWPp_exists_left; intro v32; apply v4d_sepWPp_exists_left; intro v40
  apply v4d_sepWPp_exists_left; intro v48; apply v4d_sepWPp_exists_left; intro v56
  apply v4d_sepWPp_exists_left; intro v72; apply v4d_sepWPp_exists_left; intro v80
  apply v4d_sepWPp_exists_left; intro v128; apply v4d_sepWPp_exists_left; intro v136
  apply v4d_sepWPp_exists_left; intro v144; apply v4d_sepWPp_exists_left; intro v216
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (v4d_rot4 _ _ _ _ _))
      (sepConj_mono_left (v4c_memRegion_1652_split_896 fsp))) ?_
  apply v4d_sepWPp_exists_left; intro s896; apply v4d_sepWPp_exists_left; intro s904
  apply v4d_sepWPp_exists_left; intro s912; apply v4d_sepWPp_exists_left; intro s920
  apply v4d_sepWPp_exists_left; intro s924; apply v4d_sepWPp_exists_left; intro s928
  have hrk := v4d_ekSentCt1ReceivedHeap_rk_lt A
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc
  have hd0 := v4d_optProtoPolyDecoderHeap_some_d0_lt A (pbToProtoPolyDecoder d) d0 d8 d16 d24 d28 d32
  have h35448 := v4c_step_2308_ok_some_to_35448 (b := b) (ext := ext) s3 fsp out d0 d8 d16 d32 d24 d28
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
    v32 v40 v48 v56 v72 v80 v128 v136 v144 v216
    s896 s904 s912 s920 s924 s928
    (v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
     v4b_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
     memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
     memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
     memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1992#64) 312 ∗
     stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ A.pool ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
    hfsp_align
  refine SepWPp.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
        v4b_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
        (v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         v4b_optProtoPolyDecoderWordsAt (fsp + 896#64) s896 s904 s912 s920 s924 s928 ∗
         v4b_optProtoUcWordsAt (fsp + 1888#64)
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
         memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
         memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
         memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1992#64) 312 ∗
         stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ A.pool ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by dsimp only [fsp]; ac_rfl))
      (Entails.trans (sepConj_mono hrk (sepConj_mono_left hd0)) (Entails.of_eq v4d_pull_pures))) ?_
  apply v4d_sepWPp_pure_left; intro hrk_lt
  apply v4d_sepWPp_pure_left; intro hd0_lt
  refine v4d_seq_clean_p_weaken
    (h35448 hrk_lt hd0_lt hpc3 hrun3 hsp3 hx19_3 hx20_3 hx23_3 hx24_3 hx28_3) ?_ ?_
  · dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)
  intro sm hpcm hrunm ⟨hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m,
    hx24_m, hx25_m, hx26_m, hx27_m, hx30_m, htr_m⟩
  have htr_m := htr_m.trans htr3
  have hsp_align_m : sm.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact hfsp_align
  have hpack_dec := v4b_protoPolyDecoderAt_pack A (fsp + 896#64) (pbToProtoPolyDecoder d) d0 d8 d16 d24 d28 d32
  have h1888_400 := v4c_ucWords_312_entails_400_16 fsp
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
  refine SepWPp.weaken_pre ?_
    (v4_sepWPp_call_ret (v4_sub_ok_decoder_from_pb hdec)
      (x := ⟨fsp + 1888#64, fsp + 896#64, pbToProtoPolyDecoder d⟩)
      (P_step := memRegion (fsp + 1888#64) polyDecoderSize ∗
        protoPolynomialDecoderAt A (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
        A.pool ∗ stackAt fsp decoderFromPbStack)
      (F := v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
          mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
        ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
        memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
        memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗
        v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
        statesFromPbJumpTableAt b)
      hpcm hrunm hsp_align_m hx30_m ?_ ?_ (fun _ _ => rfl) ?_)
  · dsimp only [polyDecoderSize, decoderFromPbStack]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (v4b_optProtoUcWordsAt (fsp + 1888#64)
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
         memRegion (fsp + 1992#64) 312) ∗
        (v4b_optProtoPolyDecoderWordsAt (fsp + 896#64) d0 d8 d16 d24 d28 d32 ∗
         v4b_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32) ∗
        (A.pool ∗ stackAt fsp encoderFromPbStack ∗
         v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
           mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
         memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
         memRegion (fsp + 936#64) 952 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗
         v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
         statesFromPbJumpTableAt b) by ac_rfl))
      (Entails.trans (sepConj_mono h1888_400 (sepConj_mono_left hpack_dec)) (Entails.of_eq (by ac_rfl)))
  · intro R' hm'
    dsimp only [decoderFromPbSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_m, hx1_m⟩, Satisfies.mono (Entails.of_eq (by rw [hsp_m])) hm'⟩
  · intro sf
    dsimp only [decoderFromPbSpec, encoderFromPbOnPanic, statesFromPbOnPanic]
    exact v4_onPanic_frame_entails htr_m
  · intro s4 hpc4 hrun4 hsp4 hcs4
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, _, _, hvregs_4⟩
    rw [hx19_m] at hx19_4; rw [hx20_m] at hx20_4; rw [hx21_m] at hx21_4
    rw [hx22_m] at hx22_4; rw [hx23_m] at hx23_4; rw [hx24_m] at hx24_4
    rw [hx25_m] at hx25_4; rw [hx26_m] at hx26_4; rw [hx27_m] at hx27_4
    rw [hsp_m] at hsp4
    dsimp only [decoderFromPbSpec, protoPolynomialDecoderSize, decoderFromPbStack]
    rw [sepConj_assoc]
    apply v4d_sepWP_pure_left; intro htr4_m
    have htr4 : TraceCalleeSaved s4 s0 := ⟨htr4_m.trans htr_m.1, hvregs_4.trans htr_m.2⟩
    have h1652 := v4c_memRegion_660_40_952_entails_1652 fsp
    have hpost_merge :
        (resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
          memRegion (fsp + 896#64) 40 ∗ A.pool ∗ stackAt sm.sp encoderFromPbStack) ∗
        (v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
           mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 40 ∗
         memRegion (fsp + 152#64) 64 ∗ memRegion (fsp + 236#64) 660 ∗
         memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗
         v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
         statesFromPbJumpTableAt b) ⊢
        resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
          memRegion (fsp + 152#64) 64 ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
          memRegion (fsp + 236#64) 1652 ∗
          stackAt fsp encoderFromPbStack ∗
          memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
          memRegion (fsp + 88#64) 40 ∗
          v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
            mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
          memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
          v4b_ekSentCt1ReceivedHeap A
            rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
          statesFromPbJumpTableAt b ∗ A.pool := by
      rw [hsp_m]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion (fsp + 236#64) 660 ∗ memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952) ∗
          (resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
           memRegion (fsp + 152#64) 64 ∗
           ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
           stackAt fsp encoderFromPbStack ∗
           memRegion fsp 32 ∗ memRegion (fsp + 64#64) 8 ∗
           memRegion (fsp + 88#64) 40 ∗
           v4c_ucSpillSlots fsp ((ct1Len.extractLsb' 0 8).zeroExtend 64)
             mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
           memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
           v4b_ekSentCt1ReceivedHeap A
             rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
           statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl))
        (Entails.trans (sepConj_mono_left h1652) (Entails.of_eq (by ac_rfl)))
    refine SepWP.weaken_pre hpost_merge ?_
    cases hres : decoderFromPbResult (pbToProtoPolyDecoder d) with
    | error e =>
      exact v4c_step_2472_err_to_ret hA s0 s4 out pbA
        rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len
        uc e d32 d28 hsp0_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx26_4 htr4
    | ok dec =>
      dsimp only [resultPolyDecoderFromPbAt]
      refine SepWP.weaken_pre (sepConj_mono_left (v4c_polyDecoderAt_unpack A (fsp + 1888#64) dec)) ?_
      apply v4c_wp_exists_left; intro dw
      have hok := v4c_step_2472_ok_to_ret hA s0 s4 out pbA
        rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len
        uc dec dw d32 d28 hsp0_align hpc4 hrun4 hsp4
        hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 htr4
      refine SepWP.weaken_pre ?_ hok
      exact Entails.of_eq (by dsimp only [fsp]; ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
