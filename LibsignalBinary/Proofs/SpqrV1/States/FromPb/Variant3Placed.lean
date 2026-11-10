/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4cPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 3 (`Ct1Received`, `+692`)

Relocatable Block-`333` top-level composition and `subroutine_ok` contract for
`InnerState.ct1Received`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

section

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-! ## Post-`EkSentCt1Received.from_pb` Continuation (`+860 -> s0.x30`) -/

set_option maxHeartbeats 1200000 in
/-- Post-`EkSentCt1Received::from_pb` continuation at `+860` (`lsmpl.base 333 + 860`) to `s0.x30`. -/
theorem v3_ct1Received_post_uc_860_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hEnc : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (optEnc : Option PolynomialEncoder)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (R : SepProp)
    (hpts : ∀ pbEnc, optEnc = some pbEnc → ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        ekSentCt1ReceivedResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64)
          (Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u) ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Received { uc := some u, sendingEk := optEnc }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u with
  | error e =>
    have he := v3cr_ekSentCt1Received_from_pb_err_eq u e huc
    subst he
    rw [v3cr_states_from_pb_ct1Received_uc_err_eq u optEnc huc]
    have herr := v3cr_ekResult_err_unpack A (F := F) ((s0.sp - 2400#64) + 1888#64) (.err .stateDecode)
    simp only [v3cr_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at herr
    have hpack_enc := v3cr_optProtoPolyEncoderAt_pack A ((s0.sp - 2400#64) + 1496#64)
      (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
    have hpb224 := v3_collapse_pbA_112_224 pbA w0 w8 w16 w24 w32 w40 w48
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      ekSentCt1ReceivedResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.error (.err .stateDecode)) ∗
      (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48) ∗
      (memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1496 ∗
       memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl))
      (sepConj_mono herr (sepConj_mono hpack_enc (sepConj_mono_left hpb224)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w1896 => SepWPp.exists_elim fun w1904 => SepWPp.exists_elim fun w1912 => ?_
    refine SepWPp.pure_elim fun hw1896 => ?_
    refine v3_sepWPp_seq_clean_lscl hcl1
      (v3cr_post_uc_860_err_placed (ext := ext) s1 (s0.sp - 2400#64) out w1896 w1904 w1912 _
        hfsp_align hpc1 hrun1 hsp1 hx19_1) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
    have h752 := v3_collapse_1552_752_err (s0.sp - 2400#64) w1896 w1904 w1912
    have hpre2 :
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap) ∗ (((s0.sp - 2400#64) + 1896#64) ↦₆₄ w1896) ∗
        (((s0.sp - 2400#64) + 1904#64) ↦₆₄ w1904) ∗ (((s0.sp - 2400#64) + 1912#64) ↦₆₄ w1912) ∗
        memRegion ((s0.sp - 2400#64) + 1920#64) 72 ∗
        optProtoPolynomialEncoderAt A ((s0.sp - 2400#64) + 1496#64) (optEnc.map pbToProtoPolyEncoder) ∗
        memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗ memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        optProtoPolynomialEncoderAt A ((s0.sp - 2400#64) + 1496#64) (optEnc.map pbToProtoPolyEncoder) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
         (((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap) ∗ (((s0.sp - 2400#64) + 1896#64) ↦₆₄ w1896) ∗
         (((s0.sp - 2400#64) + 1904#64) ↦₆₄ w1904) ∗ (((s0.sp - 2400#64) + 1912#64) ↦₆₄ w1912) ∗
         memRegion ((s0.sp - 2400#64) + 1920#64) 72 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1496 ∗
         optProtoPolynomialEncoderAt A ((s0.sp - 2400#64) + 1496#64) (optEnc.map pbToProtoPolyEncoder) ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
         (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h752) (Entails.of_eq (by ac_rfl))
    have hx22_byte : (s2.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx22_2, hw1896]; rfl
    have h4176 := v3cr_states_from_pb_err_4176_placed (F := F) hA s0 s2 hcl2 out .stateDecode optEnc
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_byte (htr2.trans htr1)
    refine SepWPp.weaken_pre hpre2 (SepWPp.of_sepWP_ret (SepWP.mono h4176 ?_))
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | ok ucSt =>
    dsimp only [ekSentCt1ReceivedResultAt]
    rw [v3_ekSentCt1ReceivedAt_eq_unchunked]
    have hopen := v3cr_unchunkedEkSentCt1ReceivedAt_open A (F := F) ((s0.sp - 2400#64) + 1888#64) ucSt
    refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hopen))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun ca1 => SepWPp.exists_elim fun pa1 => SepWPp.exists_elim fun la1 =>
      SepWPp.exists_elim fun ca2 => SepWPp.exists_elim fun pa2 => SepWPp.exists_elim fun la2 =>
      SepWPp.exists_elim fun ca3 => SepWPp.exists_elim fun pa3 => SepWPp.exists_elim fun la3 =>
      SepWPp.exists_elim fun ca4 => SepWPp.exists_elim fun pa4 => SepWPp.exists_elim fun la4 =>
      SepWPp.exists_elim fun uc_ep => ?_
    have hca1_ext := v3cr_unchunkedHeap_ca1_lt A (F := F) ucSt
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    have hw0_ext := v1_optProtoPolyEncoderHeap_extract_w0 A (optEnc.map pbToProtoPolyEncoder)
      w0 w8 w16 w24 w32 w40 w48
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1496 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
       v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl))
      (sepConj_mono hca1_ext (sepConj_mono_left hw0_ext))) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hca1_lt => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜match optEnc.map pbToProtoPolyEncoder with | none => w0 = noneCap | some _ => w0.toNat < 2 ^ 63⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1496 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
       v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
    refine SepWPp.pure_elim fun hw0_prop => ?_
    cases optEnc with
    | none =>
      dsimp only [Option.map_none] at hw0_prop
      subst hw0_prop
      rw [v3cr_states_from_pb_ct1Received_sendingEk_none_eq u ucSt huc]
      have h1496 := v3_split_1496_none (s0.sp - 2400#64)
      have hdealloc := v3cr_unchunkedHeap_entails_dealloc A (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      have hpb224 := v3_collapse_pbA_112_224 pbA noneCap w8 w16 w24 w32 w40 w48
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        memRegion (s0.sp - 2400#64) 1496 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        (memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 168#64) 56) ∗
        v1_optProtoPolyEncoderHeap A none noneCap w8 w16 w24 w32 w40 w48 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) noneCap w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
         v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
         memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl))
        (sepConj_mono h1496 (sepConj_mono hdealloc (sepConj_mono_left hpb224)))) ?_
      dsimp only [v1_optProtoPolyEncoderHeap]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun v224 => SepWPp.exists_elim fun v176 => ?_
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        ⌜True⌝ ∗
        ((((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
         v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) noneCap w8 w16 w24 w32 w40 w48 ∗
         v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
         (memRegion (s0.sp - 2400#64) 176 ∗ memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
          memRegion ((s0.sp - 2400#64) + 232#64) 1264 ∗
          vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
          vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
          memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl)) ?_
      refine SepWPp.pure_elim fun _ => ?_
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      simp only [sepConj_assoc]
      refine EncoderFromPb.sepWPp_seq_clean
        (v3cr_post_uc_860_ok_none_placed (ext := ext) s1 (s0.sp - 2400#64) out
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep v176 v224
          ((((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
           (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
           (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
           (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
           (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
           (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48) ∗
           memRegion (s0.sp - 2400#64) 176 ∗ memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
           memRegion ((s0.sp - 2400#64) + 232#64) 1264 ∗
           vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
           vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
           memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           statesFromPbJumpTablePlacedAt ∗ A.pool)
          hfsp_align hca1_lt hpc1 hrun1 hsp1 hx19_1 |>
          SepWP.weaken_pre (Entails.of_eq (by ac_rfl))) ?_
      intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩
      have h2072 := v3_collapse_232_2072_none (s0.sp - 2400#64)
        noneCap w8 w16 w24 w32 w40 w48 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      dsimp only [v1_optProtoPolyEncoderWordsAt] at h2072
      have hpre2 :
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          (((s0.sp - 2400#64) + 1496#64) ↦₆₄ noneCap) ∗
          v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
          ((((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
           (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
           (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
           (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
           (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
           (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48) ∗
           memRegion (s0.sp - 2400#64) 176 ∗ memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
           memRegion ((s0.sp - 2400#64) + 232#64) 1264 ∗
           vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
           vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
           memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           statesFromPbJumpTablePlacedAt ∗ A.pool) ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 176 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
          vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
          vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ statesFromPbJumpTablePlacedAt := by
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion ((s0.sp - 2400#64) + 232#64) 1264 ∗
           ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ noneCap) ∗
            (((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
            (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
            (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
            (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
            (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
            (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48)) ∗
           memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
           v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
           memRegion ((s0.sp - 2400#64) + 1992#64) 312) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 176 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
           memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
           vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
           vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left h2072) (Entails.of_eq (by ac_rfl))
      have h4884 := v3_ct1Received_err_4884_to_exit_placed (F := F) hA s0 s2 out pbA
        ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 statesFromPbJumpTablePlacedAt
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx1_2 hx22_2 hx0_2 hx28_2 hx26_2 hx21_2 (htr2.trans htr1)
      refine SepWPp.weaken_pre hpre2 (SepWPp.of_sepWP_ret (SepWP.mono h4884 ?_))
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | some pbEnc =>
      dsimp only [Option.map_some] at hw0_prop ⊢
      have h1496 := v3_split_1496_some (s0.sp - 2400#64)
      have h312 : memRegion ((s0.sp - 2400#64) + 1992#64) 312 =
          memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16 :=
        ProofLib.memRegion_split' (b := (s0.sp - 2400#64) + 1992#64) (n := 296) (k := 16)
          (b' := (s0.sp - 2400#64) + 2288#64) rfl (by bv_omega) (by decide)
      rw [h312]
      refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left h1496)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e8 =>
        SepWPp.exists_elim fun e16 => SepWPp.exists_elim fun e24 =>
        SepWPp.exists_elim fun e32 => SepWPp.exists_elim fun e40 =>
        SepWPp.exists_elim fun e48 => SepWPp.exists_elim fun v224 =>
        SepWPp.exists_elim fun v200 => SepWPp.exists_elim fun v192 =>
        SepWPp.exists_elim fun v184 => SepWPp.exists_elim fun v176 =>
        SepWPp.exists_elim fun v96 => SepWPp.exists_elim fun v64 => ?_
      have h1496_w0 :
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 =
          (((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗
          ((((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
           (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
           (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
           (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
           (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
           (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48)) := rfl
      rw [h1496_w0]
      refine v3_sepWPp_seq_clean_lscl hcl1
        (v3cr_post_uc_860_ok_some_placed (ext := ext) s1 (s0.sp - 2400#64) out pbA
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep w0 v176 v224
          ((((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
           (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
           (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
           (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
           (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
           (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48) ∗
           memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
           memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ v96) ∗
           memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
           memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
           memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
           memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
           v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
             ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
           v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 168#64) 56 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
          hfsp_align hca1_lt hw0_prop hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1 |>
          SepWP.weaken_pre (Entails.of_eq (by ac_rfl))) ?_
      intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, hx8_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, htr2⟩
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [h1496_w0]; ac_rfl))
        (v3_ct1Received_some_enc_924_placed hA hEnc s0 s2 hcl2 out pbA u ucSt pbEnc
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
          w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200 R
          huc (hpts pbEnc rfl) hsp0_align hpc2 hrun2 hsp2
          hx0_2 hx1_2 hx8_2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
          (htr2.trans htr1))

/-! ## Entry-to-Exit Proof for Variant 3 (`Ct1Received`, `+692 -> s0.x30`) -/

set_option maxHeartbeats 1200000 in
/-- Entry-to-exit proof for Variant 3 (`Ct1Received`) from `+692` (`lsmpl.base 333 + 692`) to `s0.x30`. -/
theorem states_from_pb_ct1Received_692_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hEnc : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (s : V1State.Chunked.Ct1Received) (R : SepProp)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.ct1Received s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Received s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases s with | mk uc sendingEk =>
  have hpts_fn : ∀ pbEnc, sendingEk = some pbEnc → ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555 := by
    intro pbEnc henc
    dsimp only at hpts
    rw [henc] at hpts
    exact hpts
  dsimp only [optProtoInnerStateAt, protoInnerStateAt]
  refine SepWPp.weaken_pre (Entails.trans
    (sepConj_mono_right (sepConj_mono (v3_split_2304_692 (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_left
          (v3cr_chunkedCt1ReceivedAt_unpack A pbA ⟨uc, sendingEk⟩))))))))
    (Entails.of_eq (by ac_rfl))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e8 =>
    SepWPp.exists_elim fun e16 => SepWPp.exists_elim fun e24 =>
    SepWPp.exists_elim fun e32 => SepWPp.exists_elim fun e40 =>
    SepWPp.exists_elim fun e48 =>
    SepWPp.exists_elim fun d8 => SepWPp.exists_elim fun d16 =>
    SepWPp.exists_elim fun d24 => SepWPp.exists_elim fun d32 =>
    SepWPp.exists_elim fun d40 => SepWPp.exists_elim fun d48 =>
    SepWPp.exists_elim fun d56 => SepWPp.exists_elim fun d64 =>
    SepWPp.exists_elim fun d72 => SepWPp.exists_elim fun d80 =>
    SepWPp.exists_elim fun d88 => SepWPp.exists_elim fun d96 =>
    SepWPp.exists_elim fun d104 =>
    SepWPp.exists_elim fun u8 => SepWPp.exists_elim fun u16 =>
    SepWPp.exists_elim fun u24 => SepWPp.exists_elim fun u32 =>
    SepWPp.exists_elim fun u40 => SepWPp.exists_elim fun u48 =>
    SepWPp.exists_elim fun u56 => SepWPp.exists_elim fun u64 =>
    SepWPp.exists_elim fun u72 => SepWPp.exists_elim fun u80 =>
    SepWPp.exists_elim fun u88 => SepWPp.exists_elim fun u96 =>
    SepWPp.exists_elim fun u104 =>
    SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w8 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w48 => ?_
  rw [← v1_uc_and_enc_words_eq_pb128]
  cases uc with
  | none =>
    dsimp only [v3cr_optProtoUcHeap]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜u8 = noneCap⌝ ∗
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗
       ((pbA ↦₆₄ 0x8000000000000003#64) ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool)) by ac_rfl)) ?_
    refine SepWPp.pure_elim fun hu8 => ?_
    subst hu8
    refine v3_sepWPp_seq_clean_lscl hcl1
      (v3cr_copy_pb_692_none_placed (ext := ext) s1 (s0.sp - 2400#64) out pbA
        u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48
        d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
        e0 e8 e16 e24 e32 e40 e48
        ((pbA ↦₆₄ 0x8000000000000003#64) ∗
         memRegion (pbA + 168#64) 56 ∗
         v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 1392 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt ∗
         A.pool)
        hfsp_align hpc1 hrun1 hsp1 hx19_1 hx27_1 |>
        SepWP.weaken_pre (Entails.of_eq (by ac_rfl))) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
    have h1496 := v3_collapse_1392_ucWords_1496 (s0.sp - 2400#64)
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have hpack_enc := v3cr_optProtoPolyEncoderAt_pack A (s0.sp - 2400#64 + 1496#64)
      (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
    have hpb112 := v3_collapse_pbA_tag_ucWords_112 pbA 0x8000000000000003#64
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have hpb224 := Entails.trans (sepConj_mono_left hpb112)
      (v3_collapse_pbA_112_224 pbA w0 w8 w16 w24 w32 w40 w48)
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48) ∗
      (((pbA ↦₆₄ 0x8000000000000003#64) ∗
        v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool) by ac_rfl))
      (Entails.trans (sepConj_mono h1496 (sepConj_mono hpack_enc (sepConj_mono_left hpb224)))
        (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 1496 ∗
          optProtoPolynomialEncoderAt A (s0.sp - 2400#64 + 1496#64) (sendingEk.map pbToProtoPolyEncoder) ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)))) ?_
    have hx22_byte : (s2.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx22_2]; rfl
    have herr := v3cr_states_from_pb_err_4176_placed (A := A) (F := F) hA s0 s2 hcl2 out .stateDecode
      sendingEk (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_byte (htr2.trans htr1)
    refine SepWPp.of_sepWP_ret (SepWP.mono herr fun sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    rw [v3cr_states_from_pb_ct1Received_uc_none_eq sendingEk]
    exact Entails.of_eq (by ac_rfl)
  | some u =>
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v3cr_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗
       ((pbA ↦₆₄ 0x8000000000000003#64) ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool)) by ac_rfl))
      (Entails.trans (sepConj_mono_left (v3_optProtoUcHeap_some_cap_lt A u
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104))
        (Entails.of_eq (by ac_rfl)))) ?_
    refine SepWPp.pure_elim fun hu8_lt => ?_
    refine v3_sepWPp_seq_clean_lscl hcl1
      (v3cr_copy_pb_692_some_placed (ext := ext) s1 (s0.sp - 2400#64) out pbA
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48
        d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
        e0 e8 e16 e24 e32 e40 e48
        (v3cr_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
         (pbA ↦₆₄ 0x8000000000000003#64) ∗
         memRegion (pbA + 168#64) 56 ∗
         v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 1392 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt ∗
         A.pool)
        hfsp_align hu8_lt hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1 |>
        SepWP.weaken_pre (Entails.of_eq (by ac_rfl))) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx8_2, hx19_2, hx23_2, hx25_2, hx27_2, hx29_2, htr2⟩
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      memRegion (s0.sp - 2400#64) 1392 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v3cr_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       (pbA ↦₆₄ 0x8000000000000003#64) ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool) by ac_rfl))
      (sepConj_mono (v3_split_1392_896 (s0.sp - 2400#64))
        (sepConj_mono_left (v3_split_752_1888 (s0.sp - 2400#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c16 =>
      SepWPp.exists_elim fun c24 => SepWPp.exists_elim fun c32 =>
      SepWPp.exists_elim fun c40 => SepWPp.exists_elim fun c48 =>
      SepWPp.exists_elim fun c56 => SepWPp.exists_elim fun c64 =>
      SepWPp.exists_elim fun c72 => SepWPp.exists_elim fun c80 =>
      SepWPp.exists_elim fun c88 => SepWPp.exists_elim fun c96 =>
      SepWPp.exists_elim fun c104 => ?_
    have huc1392_split :
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 =
          ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
          (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
           ((s0.sp - 2400#64 + 1408#64) ↦₆₄ u24) ∗
           ((s0.sp - 2400#64 + 1416#64) ↦₆₄ u32) ∗
           ((s0.sp - 2400#64 + 1424#64) ↦₆₄ u40) ∗
           ((s0.sp - 2400#64 + 1432#64) ↦₆₄ u48) ∗
           ((s0.sp - 2400#64 + 1440#64) ↦₆₄ u56) ∗
           ((s0.sp - 2400#64 + 1448#64) ↦₆₄ u64) ∗
           ((s0.sp - 2400#64 + 1456#64) ↦₆₄ u72) ∗
           ((s0.sp - 2400#64 + 1464#64) ↦₆₄ u80) ∗
           ((s0.sp - 2400#64 + 1472#64) ↦₆₄ u88) ∗
           ((s0.sp - 2400#64 + 1480#64) ↦₆₄ u96) ∗
           ((s0.sp - 2400#64 + 1488#64) ↦₆₄ u104)) := by
      unfold v1_ucWordsAt
      simp only [arm64_norm]
      ac_rfl
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
      ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
      v1_ucWordsAt (s0.sp - 2400#64 + 896#64) c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 ∗
      ((((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 1408#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 1416#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 1424#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 1432#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 1440#64) ↦₆₄ u56) ∗
        ((s0.sp - 2400#64 + 1448#64) ↦₆₄ u64) ∗
        ((s0.sp - 2400#64 + 1456#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 1464#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1472#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 1480#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 1488#64) ↦₆₄ u104)) ∗
       memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
       memRegion (s0.sp - 2400#64 + 1888#64) 104 ∗
       memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
       (pbA ↦₆₄ 0x8000000000000003#64) ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v3cr_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
       v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool) by rw [huc1392_split]; ac_rfl)) ?_
    refine v3_sepWPp_seq_clean_lscl hcl2
      (v3cr_copy_uc_to_call_784_placed (ext := ext) s2 (s0.sp - 2400#64) out pbA
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104
        ((((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 1408#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 1416#64) ↦₆₄ u32) ∗
          ((s0.sp - 2400#64 + 1424#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 1432#64) ↦₆₄ u48) ∗
          ((s0.sp - 2400#64 + 1440#64) ↦₆₄ u56) ∗
          ((s0.sp - 2400#64 + 1448#64) ↦₆₄ u64) ∗
          ((s0.sp - 2400#64 + 1456#64) ↦₆₄ u72) ∗
          ((s0.sp - 2400#64 + 1464#64) ↦₆₄ u80) ∗
          ((s0.sp - 2400#64 + 1472#64) ↦₆₄ u88) ∗
          ((s0.sp - 2400#64 + 1480#64) ↦₆₄ u96) ∗
          ((s0.sp - 2400#64 + 1488#64) ↦₆₄ u104)) ∗
         memRegion (s0.sp - 2400#64) 896 ∗
         memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
         memRegion (s0.sp - 2400#64 + 1888#64) 104 ∗
         memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
         (pbA ↦₆₄ 0x8000000000000003#64) ∗
         v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 168#64) 56 ∗
         v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v3cr_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
         v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt ∗
         A.pool)
        hfsp_align hpc2 hrun2 hsp2 hx8_2 hx19_2 hx23_2 hx25_2 hx27_2 |>
        SepWP.weaken_pre (Entails.of_eq (by ac_rfl))) ?_
    intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx0_3, hx1_3, hx19_3, hx23_3, hx25_3, hx27_3, hx29_3, hx30_3, htr3⟩
    have hpack_uc := v3cr_protoUc_pack A (s0.sp - 2400#64 + 896#64) u
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have hpb112 := v3_collapse_pbA_tag_ucWords_112 pbA 0x8000000000000003#64
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    rw [v3_stackAt_encoder_split_ekSent (s0.sp - 2400#64)]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (v1_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v3cr_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      ((pbA ↦₆₄ 0x8000000000000003#64) ∗
        v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      (((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
       (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 1408#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 1416#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 1424#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 1432#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 1440#64) ↦₆₄ u56) ∗
        ((s0.sp - 2400#64 + 1448#64) ↦₆₄ u64) ∗
        ((s0.sp - 2400#64 + 1456#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 1464#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1472#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 1480#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 1488#64) ↦₆₄ u104))) ∗
      (memRegion (s0.sp - 2400#64 + 1888#64) 104 ∗
       A.pool ∗
       stackAt (s0.sp - 2400#64) ekSentCt1ReceivedFromPbStack ∗
       memRegion (s0.sp - 2400#64 - 5152#64) 848 ∗
       memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
       memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt) by ac_rfl))
      (Entails.trans (sepConj_mono hpack_uc (sepConj_mono_left hpb112))
        (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64 + 1888#64) 104 ∗
           protoUnchunkedEkSentCt1ReceivedAt A (s0.sp - 2400#64 + 896#64) u ∗
           A.pool ∗
           stackAt (s0.sp - 2400#64) ekSentCt1ReceivedFromPbStack) ∗
          (memRegion (s0.sp - 2400#64 - 5152#64) 848 ∗
           memRegion (s0.sp - 2400#64) 896 ∗
           memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
           v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
           memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
           memRegion pbA 112 ∗
           v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 168#64) 56 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           statesFromPbJumpTablePlacedAt) by rw [huc1392_split]; ac_rfl)))) ?_
    have hs3_align : s3.spAligned = true := by
      simp only [State.spAligned, hsp3, hfsp_align]
    have htr3_0 : TraceCalleeSaved s3 s0 := htr3.trans (htr2.trans htr1)
    refine v3_sepWPp_call_lscl
      (v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok (F := F) hA)
      (x := ⟨s0.sp - 2400#64 + 1888#64, s0.sp - 2400#64 + 896#64, u⟩)
      hcl3 hpc3 hrun3 hs3_align hx30_3
      (fun R' hm => by
        dsimp only [ekSentCt1ReceivedFromPbSpec]
        rw [hsp3, sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0_3, hx1_3⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩)
      (fun sf => v3_encoderFromPbOnPanic_entails s0 s3 sf _ htr3_0)
      (fun _ _ => rfl)
      ?_
    intro s4 hpc4 hrun4 hsp4 hcs4 hcl4
    dsimp only [ekSentCt1ReceivedFromPbSpec]
    rw [hsp3] at hsp4 ⊢
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜s4.trace = s3.trace⌝ ∗
      ((stackAt (s0.sp - 2400#64) ekSentCt1ReceivedFromPbStack ∗
        memRegion (s0.sp - 2400#64 - 5152#64) 848) ∗
       (memRegion (s0.sp - 2400#64) 896 ∗
        memRegion (s0.sp - 2400#64 + 896#64) 104 ∗
        memRegion (s0.sp - 2400#64 + 1000#64) 392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
       ekSentCt1ReceivedResultAt A (F := F) (s0.sp - 2400#64 + 1888#64)
         (Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u) ∗
       memRegion (s0.sp - 2400#64 + 1992#64) 312 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       memRegion pbA 112 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗
       v1_optProtoPolyEncoderHeap A (sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool) by ac_rfl)) ?_
    refine SepWPp.pure_elim fun htr4 => ?_
    rw [← v3_stackAt_encoder_split_ekSent (s0.sp - 2400#64)]
    have h1496 := v3_collapse_896_104_392_ucWords_1496 (s0.sp - 2400#64)
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_left h1496)) ?_
    have hx19_4 : s4.readReg64 .x19 = out := (hcs4.1).trans hx19_3
    have hx23_4 : s4.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 :=
      (hcs4.2.2.2.2.1).trans hx23_3
    have hx25_4 : s4.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 :=
      (hcs4.2.2.2.2.2.2.1).trans hx25_3
    have hx27_4 : s4.readReg64 .x27 = pbA :=
      (hcs4.2.2.2.2.2.2.2.2.1).trans hx27_3
    exact v3_ct1Received_post_uc_860_placed hA hEnc s0 s4 hcl4 out pbA u sendingEk
      w0 w8 w16 w24 w32 w40 w48 R hpts_fn hsp0_align hpc4 hrun4 hsp4
      hx19_4 hx23_4 hx25_4 hx27_4 ⟨htr4.trans htr3_0.1, hcs4.2.2.2.2.2.2.2.2.2.2.2.trans htr3_0.2⟩

/-- `subroutine_ok` for Variant 3 (`pb = { innerState := some (.ct1Received s) }`, `[LibsignalPlacement]`). -/
theorem states_from_pb_ct1Received_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hEnc : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s : V1State.Chunked.Ct1Received) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F { innerState := some (.ct1Received s) })) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [statesFromPbVariantPlacedSpec, v1StatePtsBound, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hpts⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A pbA (some (.ct1Received s)) ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_from_pb_prologue_placed (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A pbA (some (.ct1Received s)) ∗
     statesFromPbJumpTablePlacedAt ∗
     A.pool)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean_lscl hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  have htag_eq : optProtoInnerStateAt A pbA (some (.ct1Received s)) =
      (pbA ↦₆₄ 0x8000000000000003#64) ∗
      (protoChunkedCt1ReceivedAt A (pbA + 8#64) s ∗
       memRegion (pbA + 168#64) 56) := rfl
  have hfsp := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
    ((pbA ↦₆₄ 0x8000000000000003#64) ∗
     statesFromPbJumpTablePlacedAt ∗
     (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (protoChunkedCt1ReceivedAt A (pbA + 8#64) s ∗
       memRegion (pbA + 168#64) 56) ∗
      A.pool)) by rw [htag_eq]; ac_rfl))
    (sepConj_mono_left hfsp)) ?_
  refine sepWPp_seq_clean_lscl hcl1
    (states_from_pb_dispatch_tagged_placed (ext := ext) s0 s1 out pbA 0x8000000000000003#64 692#64
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (protoChunkedCt1ReceivedAt A (pbA + 8#64) s ∗
        memRegion (pbA + 168#64) 56) ∗
       A.pool)
      TaggedVariantDispatch.ct1Received hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1 |>
      SepWP.weaken_pre (Entails.of_eq (by ac_rfl))) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx27_2, _, hx25_2, _, _, hx23_2, htr2⟩
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hx25_2' : s2.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 := by
    rw [hx25_2]; bv_omega
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
    memRegion (s0.sp - 2400#64) 2304 ∗
    statesFromPbSavedCells s0 ∗
    memRegion out chunkedStatesSize ∗
    optProtoInnerStateAt A pbA (some (.ct1Received s)) ∗
    statesFromPbJumpTablePlacedAt ∗
    A.pool by rw [htag_eq]; ac_rfl)) ?_
  exact sfpProof_sepWPp_of_states_body_cl_placed s0 s2 out pbA { innerState := some (.ct1Received s) } _ R
    (states_from_pb_ct1Received_692_placed (A := A) (F := F) hA hEnc s0 s2 hcl2 out pbA s R
      hpts hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2' hx25_2' hx27_2 htr2)

abbrev states_from_pb_variant2_placed := @states_from_pb_ct1Received_ok_ext_placed

end

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v3_ct1Received_post_uc_860_placed
  states_from_pb_ct1Received_692_placed
  states_from_pb_ct1Received_ok_ext_placed
  states_from_pb_variant2_placed
)
end CryptoVerification.SpqrV1.States.FromPb
