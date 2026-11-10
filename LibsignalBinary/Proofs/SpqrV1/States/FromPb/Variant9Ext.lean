/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dExt
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant9`

Lifts `Variant9` (`AllocContracts` -> `AllocContracts4K`) inside
`CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

namespace CryptoVerification.SpqrV1.States.FromPb.Ext4K

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.States.FromPb

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

set_option maxHeartbeats 800000 in
/-- From `+2864` (after `ct1SentFromPb` returns) to `s0.x30`. -/
theorem v9_tail_2864_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (hDec : DecoderFromPbOkExt b A ext)
    (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (optDec : Option PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = w8)
    (hx21 : s.readReg64 .x21 = w0) (hx22 : s.readReg64 .x22 = w16)
    (hx23 : s.readReg64 .x23 = w32) (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA)
    (htr : TraceCalleeSaved s s0)
    (hpts : ∀ d, optDec = some d → (d.ptsNeeded == 576#32) = true) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (ct1SentResultAt A (fsp + 1888#64) (Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u) ∗
        (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
        v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
        A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := optDec }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases hres : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u with
  | error e =>
    have he : e = .err .stateDecode := v9_ct1Sent_from_pb_err_eq u hres
    subst he
    have hmod :
        States.from_pb spqrPolyApi (spqrAuthApi F)
          { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := optDec }) } =
        .error (.err .stateDecode) := by
      cases optDec with
      | none =>
        rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_none u, hres]
      | some d =>
        rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_some u d (hpts d rfl), hres]
    rw [hmod]
    apply SepWPp.of_sepWP_ret
    dsimp only [ct1SentResultAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hbw := v9_byte_region119_to_words (fsp + 1896#64) 0#8
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbw
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1896#64) ↦₈ 0#8) ∗ memRegion (fsp + 1897#64) 119) ∗
        (((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
          memRegion (pbA + 176#64) 48) ∗
         ((fsp + 1888#64) ↦₆₄ noneCap) ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
         A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
      (sepConj_mono hbw
        (sepConj_mono_left (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32)))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w1896
    apply ProofLib.SepWP.exists_left; intro w1904
    apply ProofLib.SepWP.exists_left; intro w1912
    apply SepWP.pure_elim; intro hw1896
    refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64)
      (P_mid := v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (Q := fun s1 => v9_Saved5368Preserved s0 s1 fsp out w8 w0 w1896 ∧ s1.readReg64 .x22 = w16) ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
        (memRegion (fsp + 1920#64) 96 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
        (SepWP.strengthen_entails_const ?_
          (v9_step_2864_err_to_5360 s0 s fsp out w8 w0 w16 w1896 w1904 w1912 _
            hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 htr))
      refine Entails.trans (Entails.of_eq (show _ =
        v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        (memRegion fsp 1888 ∗
         (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
          memRegion (fsp + 1920#64) 96) ∗
         memRegion (fsp + 2016#64) 288) ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize by ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (v9_fsp_1888_err_entails_2304 fsp noneCap w1896 w1904 w1912)))))
    · rintro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
      exact v9_tail_5360_to_ret hA s0 s1 fsp out pbA w0 w8 w16 d24 d28 w32 w1896
        (optDec.map pbToProtoPolyDecoder) .stateDecode hsp0_align hfsp_eq hpc1 hrun1 hpres1 hx22_1 hw1896
  | ok uc =>
    dsimp only [ct1SentResultAt]
    refine SepWPp.weaken_pre (sepConj_mono_left (v9_ct1SentAt_unpack A (fsp + 1888#64) uc)) ?_
    simp only [sepExists_sepConj_left]
    apply v9_sepWPp_exists_left; intro rkCap; apply v9_sepWPp_exists_left; intro rkPtr
    apply v9_sepWPp_exists_left; intro rkLen; apply v9_sepWPp_exists_left; intro mkCap
    apply v9_sepWPp_exists_left; intro mkPtr; apply v9_sepWPp_exists_left; intro mkLen
    apply v9_sepWPp_exists_left; intro hdrCap; apply v9_sepWPp_exists_left; intro hdrPtr
    apply v9_sepWPp_exists_left; intro hdrLen; apply v9_sepWPp_exists_left; intro esCap
    apply v9_sepWPp_exists_left; intro esPtr; apply v9_sepWPp_exists_left; intro esLen
    apply v9_sepWPp_exists_left; intro ct1Cap; apply v9_sepWPp_exists_left; intro ct1Ptr
    apply v9_sepWPp_exists_left; intro ct1Len
    refine SepWPp.weaken_pre
      (Entails.trans
        (sepConj_mono_left
          (sepConj_mono_right
            (v9_ct1SentHeap_rkCap_lt A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
              esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc)))
        (Entails.of_eq (show _ =
          ⌜rkCap.toNat < 2 ^ 63⌝ ∗
          (v9_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
           v9_ct1SentHeap A
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
           v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
           memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
           A.pool ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
    apply v9_sepWPp_pure_left; intro hrk_lt
    cases optDec with
    | none =>
      rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_none u, hres]
      apply SepWPp.of_sepWP_ret
      dsimp only [Option.map, v9_optProtoPolyDecoderHeap]
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          ⌜w0 = noneCap⌝ ∗
          (((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
            v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
            memRegion (pbA + 176#64) 48) ∗
           memRegion fsp 1888 ∗
           (v9_optProtoUcWordsAt (fsp + 1888#64)
              rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
              esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
            v9_ct1SentHeap A
              rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
              esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
            memRegion (fsp + 2016#64) 288 ∗
            A.pool ∗ stackAt fsp encoderFromPbStack ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
        (sepConj_mono_right
          (sepConj_mono (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32)
            (sepConj_mono_left (v9_memRegion_1888_split_none fsp))))) ?_
      apply SepWP.pure_elim; rintro rfl
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro w248; apply ProofLib.SepWP.exists_left; intro w240
      apply ProofLib.SepWP.exists_left; intro w152; apply ProofLib.SepWP.exists_left; intro w144
      apply ProofLib.SepWP.exists_left; intro w128; apply ProofLib.SepWP.exists_left; intro d96
      apply ProofLib.SepWP.exists_left; intro w72
      refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6904#64)
        (P_mid := memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
          v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = mkPtr ∧ s1.readReg64 .x1 = mkCap ∧
          s1.readReg64 .x10 = rkCap ∧ s1.readReg64 .x13 = ct1Cap ∧ s1.readReg64 .x14 = ct1Ptr ∧
          s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗ ((fsp + 128#64) ↦₆₄ w128) ∗
          ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
          ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗
          v9_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
          (memRegion fsp 72 ∗ memRegion (fsp + 80#64) 16 ∗ memRegion (fsp + 100#64) 28 ∗
           memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 80 ∗ memRegion (fsp + 255#64) 1633 ∗
           memRegion (fsp + 2016#64) 288 ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
          (SepWP.strengthen_entails_const ?_
            (v9_step_2864_ok_none_to_6904 s0 s fsp out
              rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
              esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
              w72 w128 w144 w152 w240 w248 d96 _
              hfsp_align hrk_lt hpc hrun hsp hx19 hx21 hx25 htr))
        have hcol := v9_fsp_2864_none_collapse fsp
          (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) uc.epoch
          ((EncoderFromPb.loByte ct1Len).zeroExtend 32)
        refine Entails.trans (Entails.of_eq (show _ =
          ((memRegion (fsp + 80#64) 16 ∗
            ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
            memRegion (fsp + 100#64) 28) ∗
           (memRegion (fsp + 160#64) 80 ∗
            ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7
              (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
            ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
            memRegion (fsp + 255#64) 1633 ∗
            memRegion (fsp + 1888#64) 128 ∗
            memRegion (fsp + 2016#64) 288)) ∗
          (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗
           memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hcol) (Entails.of_eq (by ac_rfl))
      · rintro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx10_1, hx13_1, hx14_1, hx19_1, hx28_1, htr1⟩
        exact v9_tail_6904_to_ret hA s0 s1 fsp out pbA
          rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
          hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx0_1 hx1_1 hx10_1 hx13_1 hx14_1 hx19_1 hx28_1 htr1
    | some d =>
      rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_some u d (hpts d rfl), hres]
      dsimp only [Option.map]
      refine SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
          memRegion fsp 1888 ∗
          (v9_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
           v9_ct1SentHeap A
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
           memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗
           A.pool ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
        (sepConj_mono
          (v9_optProtoPolyDecoderHeap_some_cap_lt A (pbToProtoPolyDecoder d) w0 w8 w16 d24 d28 w32)
          (sepConj_mono_left (v9_memRegion_1888_split_some fsp)))) ?_
      rw [sepConj_assoc]
      apply v9_sepWPp_pure_left; rintro ⟨hw0_lt, _⟩
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply v9_sepWPp_exists_left; intro w248; apply v9_sepWPp_exists_left; intro w240
      apply v9_sepWPp_exists_left; intro w216; apply v9_sepWPp_exists_left; intro w200
      apply v9_sepWPp_exists_left; intro w152; apply v9_sepWPp_exists_left; intro w144
      apply v9_sepWPp_exists_left; intro w136; apply v9_sepWPp_exists_left; intro w128
      apply v9_sepWPp_exists_left; intro d96; apply v9_sepWPp_exists_left; intro w80
      apply v9_sepWPp_exists_left; intro w72; apply v9_sepWPp_exists_left; intro w56
      apply v9_sepWPp_exists_left; intro w48; apply v9_sepWPp_exists_left; intro w40
      refine v9_sepWPp_seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64)
        (P_mid := (protoPolynomialDecoderAt A (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
            memRegion (fsp + 1888#64) 400 ∗ A.pool ∗ stackAt fsp decoderFromPbStack) ∗
          (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
           ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
           ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
           ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
           ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
           ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7
             (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
           ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
           memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
           memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
           memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 936#64) 952 ∗
           memRegion (fsp + 2288#64) 16 ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           memRegion pbA optProtoInnerStateSize ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize))
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧
          s1.readReg64 .x1 = fsp + 896#64 ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x21 = fsp + 848#64 ∧ s1.readReg64 .x24 = fsp + 1888#64 ∧
          s1.readReg64 .x25 = esLen ∧ s1.readReg64 .x26 = rkLen ∧ s1.readReg64 .x28 = rkPtr ∧
          s1.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3044#64 ∧
          TraceCalleeSaved s1 s0) ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
          ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗
          ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗ ((fsp + 144#64) ↦₆₄ w144) ∗
          ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
          ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗
          memRegion (fsp + 896#64) 40 ∗
          v9_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
          v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
          ((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗
           memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
           memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
           memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 936#64) 952 ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           A.pool ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
        refine SepWP.mono
          (v9_step_2864_ok_some_to_3040 s0 s fsp out pbA
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
            w0 w8 w16 d24 d28 w32 d
            w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 d96 _
            hfsp_align hrk_lt hw0_lt hpc hrun hsp hx19 hx20 hx21 hx23 hx25 hx27 htr) ?_
        rintro s1 P1 _ _ ⟨hP1, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        rw [hx24] at hx24_1
        refine ⟨Entails.trans hP1 ?_,
          hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        refine Entails.trans (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
           memRegion (pbA + 176#64) 48) ∗
          (memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288) ∗
          stackAt fsp decoderFromPbStack ∗
          (protoPolynomialDecoderAt A (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
           A.pool ∗
           ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
           ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
           ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
           ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
           ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
           ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7
             (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
           ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
           memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
           memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
           memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 936#64) 952 ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
        rw [v9_memRegion_1888_2016_eq_400_16 fsp]
        exact Entails.trans
          (sepConj_mono_left (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32))
          (Entails.of_eq (by ac_rfl))
      · rintro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        have hsp1_align : s1.spAligned = true := by
          unfold State.spAligned; rw [hsp1]; exact hfsp_align
        refine v9_sepWPp_call_ret_entails (v9_sub_ok_decoder_from_pb hDec)
          (x := ⟨fsp + 1888#64, fsp + 896#64, pbToProtoPolyDecoder d⟩)
          (Qpan := statesFromPbOnPanic s0)
          hpc1 hrun1 hsp1_align hx30_1
          (by
            dsimp only [decoderFromPbSpec, polyDecoderSize]
            rw [hsp1]
            exact Entails.pure_right ⟨hx0_1, hx1_1⟩ (Entails.of_eq (by ac_rfl)))
          (fun sf => by dsimp only [decoderFromPbSpec]; exact v9_onPanic_frame_entails htr1)
          (fun _ _ => rfl) ?_
        intro s2 hpc2 hrun2 hsp2 hcs2
        obtain ⟨hx19_2, _, hx21_2, _, _, hx24_2, hx25_2, hx26_2, _, hx28_2, _, hvregs_2⟩ := hcs2
        rw [hsp1] at hsp2; rw [hx19_1] at hx19_2; rw [hx21_1] at hx21_2
        rw [hx24_1] at hx24_2; rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2
        rw [hx28_1] at hx28_2
        dsimp only [decoderFromPbSpec, protoPolynomialDecoderSize]
        rw [hsp1, sepConj_assoc]
        apply SepWP.pure_elim; intro htr2
        have htr2 : TraceCalleeSaved s2 s0 := ⟨htr2.trans htr1.1, hvregs_2.trans htr1.2⟩
        refine SepWP.weaken_pre (Entails.of_eq (show _ =
          resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
          ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
          ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7
            (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
          ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
          memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
          memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
          memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
          memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
          v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize by ac_rfl))
          (v9_tail_3044_to_ret hA s0 s2 fsp out pbA
            rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc d
            hsp0_align hfsp_eq hpc2 hrun2 hsp2 hx19_2 hx21_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2)

set_option maxHeartbeats 800000 in
/-- From `+2768` (after checking `receivingEk`) to `s0.x30`. -/
theorem v9_tail_2768_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (hDec : DecoderFromPbOkExt b A ext)
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) (optDec : Option PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2768#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = u0)
    (hx9 : s.readReg64 .x9 = ((EncoderFromPb.loByte u8).zeroExtend 32).zeroExtend 64)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = w8)
    (hx21 : s.readReg64 .x21 = w0) (hx22 : s.readReg64 .x22 = w16)
    (hx23 : s.readReg64 .x23 = w32) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0)
    (hpts : ∀ d, optDec = some d → (d.ptsNeeded == 576#32) = true) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      ((pbA ↦₆₄ 0x8000000000000009#64) ∗
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
        v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
        A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Acknowledged { uc := optUc, receivingEk := optDec }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases optUc with
  | none =>
    have hmod :
        States.from_pb spqrPolyApi (spqrAuthApi F)
          { innerState := some (.ct1Acknowledged { uc := none, receivingEk := optDec }) } =
        .error (.err .stateDecode) := by
      cases optDec with
      | none => exact v9_states_from_pb_ct1Acknowledged_uc_none_dec_none
      | some d => exact v9_states_from_pb_ct1Acknowledged_uc_none_dec_some d (hpts d rfl)
    rw [hmod]
    apply SepWPp.of_sepWP_ret
    dsimp only [v9_optProtoUcHeap]
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        ⌜u0 = noneCap⌝ ∗
        (((pbA ↦₆₄ 0x8000000000000009#64) ∗
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
          memRegion (pbA + 176#64) 48) ∗
         (v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
          A.pool ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
      (sepConj_mono_right
        (sepConj_mono_left
          (v9_pbA_entails_224 pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
            w0 w8 w16 d24 d28 w32)))) ?_
    apply SepWP.pure_elim; rintro rfl
    refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64)
      (P_mid := v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (Q := fun s1 => v9_Saved5368Preserved s0 s1 fsp out w8 w0 0#64 ∧ s1.readReg64 .x22 = w16) ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (v9_states_from_pb_uc_none_2768 s0 s fsp out w8 w0 w16 _
          hpc hrun hsp hx8 hx19 hx20 hx21 hx22 htr)
    · rintro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
      exact v9_tail_5360_to_ret hA s0 s1 fsp out pbA w0 w8 w16 d24 d28 w32 0#64
        (optDec.map pbToProtoPolyDecoder) .stateDecode hsp0_align hfsp_eq hpc1 hrun1 hpres1 hx22_1 rfl
  | some u =>
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        memRegion fsp 2304 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗
         A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
      (sepConj_mono
        (v9_optProtoUcHeap_some_cap_lt A u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
        (sepConj_mono_left (v9_memRegion_2304_split_2768 fsp)))) ?_
    rw [sepConj_assoc]
    apply v9_sepWPp_pure_left; intro hu0_lt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply v9_sepWPp_exists_left; intro z1512; apply v9_sepWPp_exists_left; intro z1504
    apply v9_sepWPp_exists_left; intro z1496; apply v9_sepWPp_exists_left; intro z1488
    apply v9_sepWPp_exists_left; intro z1480; apply v9_sepWPp_exists_left; intro z1472
    apply v9_sepWPp_exists_left; intro z1464; apply v9_sepWPp_exists_left; intro z1456
    apply v9_sepWPp_exists_left; intro z1448; apply v9_sepWPp_exists_left; intro z1440
    apply v9_sepWPp_exists_left; intro z1432; apply v9_sepWPp_exists_left; intro z1424
    apply v9_sepWPp_exists_left; intro z1417; apply v9_sepWPp_exists_left; intro z1409
    apply v9_sepWPp_exists_left; intro z1401; apply v9_sepWPp_exists_left; intro b1400
    apply v9_sepWPp_exists_left; intro z1392
    refine v9_sepWPp_seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 15272#64)
      (P_mid := (protoUnchunkedCt1SentAt A (fsp + 1392#64) u ∗
          memRegion (fsp + 1888#64) 128 ∗ A.pool ∗ stackAt fsp ct1SentFromPbStack) ∗
        (memRegion (fsp - 5152#64) 816 ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗
         memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗ memRegion (fsp + 2016#64) 288 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize))
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧
        s1.readReg64 .x1 = fsp + 1392#64 ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = w8 ∧ s1.readReg64 .x21 = w0 ∧ s1.readReg64 .x22 = w16 ∧
        s1.readReg64 .x23 = w32 ∧ s1.readReg64 .x24 = fsp + 1888#64 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x27 = pbA ∧
        s1.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2864#64 ∧
        TraceCalleeSaved s1 s0) ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        ((fsp + 1392#64) ↦₆₄ z1392) ∗ ((fsp + 1400#64) ↦₈ b1400) ∗ ((fsp + 1401#64) ↦₆₄ z1401) ∗
        ((fsp + 1409#64) ↦₆₄ z1409) ∗ ((fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 z1417) ∗
        ((fsp + 1424#64) ↦₆₄ z1424) ∗ ((fsp + 1432#64) ↦₆₄ z1432) ∗ ((fsp + 1440#64) ↦₆₄ z1440) ∗
        ((fsp + 1448#64) ↦₆₄ z1448) ∗ ((fsp + 1456#64) ↦₆₄ z1456) ∗ ((fsp + 1464#64) ↦₆₄ z1464) ∗
        ((fsp + 1472#64) ↦₆₄ z1472) ∗ ((fsp + 1480#64) ↦₆₄ z1480) ∗ ((fsp + 1488#64) ↦₆₄ z1488) ∗
        ((fsp + 1496#64) ↦₆₄ z1496) ∗ ((fsp + 1504#64) ↦₆₄ z1504) ∗ ((fsp + 1512#64) ↦₆₄ z1512) ∗
        (v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗
         memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗
         memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288 ∗
         A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      refine SepWP.mono
        (v9_states_from_pb_copy_uc_to_call_2768 s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 w32
          z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472 z1480 z1488 z1496 z1504 z1512 b1400 _
          hfsp_align hu0_lt hpc hrun hsp hx8 hx9 hx13 hx19 hx20 hx21 hx22 hx23 hx25 hx27 htr) ?_
      rintro s1 P1 _ _ ⟨hP1, hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, _, hx30_1, htr1⟩
      refine ⟨Entails.trans hP1 ?_,
        hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx30_1, htr1⟩
      rw [v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb fsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (v9_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120) ∗
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        (memRegion (fsp + 1888#64) 128 ∗ A.pool ∗ stackAt fsp ct1SentFromPbStack ∗
         memRegion (fsp - 5152#64) 816 ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗
         memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗ memRegion (fsp + 2016#64) 288 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      exact Entails.trans
        (sepConj_mono
          (v9_protoUcAt_pack A (fsp + 1392#64) u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
          (sepConj_mono_left
            (v9_optProtoUcWordsAt_entails_128 (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)))
        (Entails.of_eq (by ac_rfl))
    · rintro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx30_1, htr1⟩
      have hsp1_align : s1.spAligned = true := by
        unfold State.spAligned; rw [hsp1]; exact hfsp_align
      refine v9_sepWPp_call_entails (v9_sub_ok_ct1_sent_from_pb (F := F) hA)
        (x := ⟨fsp + 1888#64, fsp + 1392#64, u⟩)
        (Qpan := statesFromPbOnPanic s0)
        hpc1 hrun1 hsp1_align hx30_1
        (by
          dsimp only [ct1SentFromPbSpec, protoUnchunkedCt1SentSize]
          rw [hsp1]
          exact Entails.pure_right ⟨hx0_1, hx1_1⟩ (Entails.of_eq (by ac_rfl)))
        (fun sf => by dsimp only [ct1SentFromPbSpec]; exact v9_onPanic_frame_entails htr1)
        (fun _ _ => rfl) ?_
      intro s2 hpc2 hrun2 hsp2 hcs2
      obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, _, hx27_2, _, _, hvregs_2⟩ := hcs2
      rw [hsp1] at hsp2; rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2
      rw [hx21_1] at hx21_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
      rw [hx24_1] at hx24_2; rw [hx25_1] at hx25_2; rw [hx27_1] at hx27_2
      dsimp only [ct1SentFromPbSpec, protoUnchunkedCt1SentSize]
      rw [hsp1, sepConj_assoc]
      apply v9_sepWPp_pure_left; intro htr2
      have htr2 : TraceCalleeSaved s2 s0 := ⟨htr2.trans htr1.1, hvregs_2.trans htr1.2⟩
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        (memRegion fsp 1392 ∗ memRegion (fsp + 1392#64) 128 ∗ memRegion (fsp + 1520#64) 368) ∗
        (stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816) ∗
        (ct1SentResultAt A (fsp + 1888#64) (Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u) ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗
         A.pool ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_)
        (v9_tail_2864_to_ret hA hDec s0 s2 fsp out pbA w0 w8 w16 d24 d28 w32 u optDec
          hsp0_align hfsp_eq hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 htr2 hpts)
      rw [← v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb fsp]
      exact Entails.trans
        (sepConj_mono_left (v9_memRegion_1392_1520_entails_1888 fsp))
        (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 800000 in
/-- Variant 9 (`Ct1Acknowledged`) from the switch target `+444` to `s0.x30`. -/
theorem states_from_pb_ct1Acknowledged_444
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (hDec : DecoderFromPbOkExt b A ext)
    (s0 s : State) (fsp out pbA : BitVec 64)
    (st : V1State.Chunked.Ct1Acknowledged)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 444#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64) (hx19 : s.readReg64 .x19 = out)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (optProtoInnerStateAt A pbA (some (.ct1Acknowledged st)) ∗
        A.pool ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Acknowledged st) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  rcases st with ⟨optUc, optDec⟩
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1AcknowledgedAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.weaken_pre
    (sepConj_mono_right
      (sepConj_mono (v9_optProtoUcAt_unpack A (pbA + 8#64) optUc)
        (sepConj_mono_left
          (v9_optProtoPolyDecoderAt_unpack A (pbA + 136#64) (optDec.map pbToProtoPolyDecoder))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply v9_sepWPp_exists_left; intro w0; apply v9_sepWPp_exists_left; intro w8
  apply v9_sepWPp_exists_left; intro w16; apply v9_sepWPp_exists_left; intro d24
  apply v9_sepWPp_exists_left; intro d28; apply v9_sepWPp_exists_left; intro w32
  apply v9_sepWPp_exists_left; intro u0; apply v9_sepWPp_exists_left; intro u8
  apply v9_sepWPp_exists_left; intro u16; apply v9_sepWPp_exists_left; intro u24
  apply v9_sepWPp_exists_left; intro u32; apply v9_sepWPp_exists_left; intro u40
  apply v9_sepWPp_exists_left; intro u48; apply v9_sepWPp_exists_left; intro u56
  apply v9_sepWPp_exists_left; intro u64; apply v9_sepWPp_exists_left; intro u72
  apply v9_sepWPp_exists_left; intro u80; apply v9_sepWPp_exists_left; intro u88
  apply v9_sepWPp_exists_left; intro u96; apply v9_sepWPp_exists_left; intro u104
  apply v9_sepWPp_exists_left; intro u112; apply v9_sepWPp_exists_left; intro u120
  cases optDec with
  | none =>
    dsimp only [Option.map, v9_optProtoPolyDecoderHeap]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜w0 = noneCap⌝ ∗
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
       v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
       ((pbA ↦₆₄ 0x8000000000000009#64) ∗
        v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
        A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl)) ?_
    apply v9_sepWPp_pure_left; rintro rfl
    refine v9_sepWPp_seq_clean
      (v9_states_from_pb_step_444_to_2768_none s0 s fsp out pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
        w8 w16 d24 d28 w32 _ hpc hrun hsp hx19 hx27 htr) ?_
    rintro s1 hpc1 hrun1 ⟨hsp1, _, hx8_1, hx9_1, hx13_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, _, htr1⟩
    rw [hx13] at hx13_1; rw [hx25] at hx25_1
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
          (Entails.of_eq (by dsimp only [Option.map, v9_optProtoPolyDecoderHeap]; ac_rfl))))
      (v9_tail_2768_to_ret hA hDec s0 s1 fsp out pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
        noneCap w8 w16 d24 d28 w32 optUc none
        hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx8_1 hx9_1 hx13_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
        (by intro d hd; cases hd))
  | some d =>
    dsimp only [Option.map]
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
         A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
      (sepConj_mono_left
        (v9_optProtoPolyDecoderHeap_some_cap_lt A (pbToProtoPolyDecoder d) w0 w8 w16 d24 d28 w32))) ?_
    rw [sepConj_assoc]
    apply v9_sepWPp_pure_left; rintro ⟨hw0_lt, hd24⟩
    change d24 = d.ptsNeeded at hd24
    subst hd24
    cases hpts : d.ptsNeeded == 576#32
    · -- Early error path (`+444 -> +488 -> +5368 -> +7084`)
      have hd24_ne : d.ptsNeeded ≠ 576#32 := by
        intro heq; rw [heq] at hpts; revert hpts; decide
      rw [v9_states_from_pb_ct1Acknowledged_ptsNeeded_ne optUc d hpts]
      apply SepWPp.of_sepWP_ret
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
         A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      refine EncoderFromPb.seq_clean
        (v9_states_from_pb_step_444_to_488_err s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d.ptsNeeded d28 w32 _ hw0_lt hd24_ne hpc hrun hsp hx19 hx27 htr) ?_
      rintro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1, _, _, htr1⟩
      cases optUc with
      | none =>
        dsimp only [v9_optProtoUcHeap]
        refine SepWP.weaken_pre
          (Entails.trans (Entails.of_eq (show _ =
            ⌜u0 = noneCap⌝ ∗
            (((pbA ↦₆₄ 0x8000000000000009#64) ∗
              v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
              v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              memRegion (pbA + 176#64) 48) ∗
             (v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              A.pool ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
              statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
          (sepConj_mono_right
            (sepConj_mono_left
              (v9_pbA_entails_224 pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
                w0 w8 w16 d.ptsNeeded d28 w32)))) ?_
        apply SepWP.pure_elim; rintro rfl
        refine EncoderFromPb.seq_clean
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (v9_states_from_pb_drop_proto_uc_none_488 s0 s1 fsp out w8 w0 w16
              (v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
               memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
               memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
              hpc1 hrun1 hsp1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 htr1)) ?_
        rintro s2 hpc2 hrun2 ⟨hpres2, hx22_2⟩
        exact v9_tail_5368_to_ret hA s0 s2 fsp out pbA w0 w8 w16 d.ptsNeeded d28 w32 2#64
          (pbToProtoPolyDecoder d) .msgDecode hsp0_align hfsp_eq hpc2 hrun2 hpres2 hx22_2 rfl
      | some u =>
        refine SepWP.weaken_pre
          (Entails.trans (Entails.of_eq (show _ =
            v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
            (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
             stackAt fsp encoderFromPbStack ∗
             ((pbA ↦₆₄ 0x8000000000000009#64) ∗
              v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
              A.pool ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
          (sepConj_mono_left
            (v9_optProtoUcHeap_some_cap_lt A u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120))) ?_
        rw [sepConj_assoc]
        apply SepWP.pure_elim; intro hu0_lt
        refine SepWP.weaken_pre
          (Entails.trans (Entails.of_eq (show _ =
            (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
             v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120) ∗
            stackAt fsp encoderFromPbStack ∗
            (A.pool ∗
             (pbA ↦₆₄ 0x8000000000000009#64) ∗
             v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
          (sepConj_mono
            (v9_protoUcAt_pack A (pbA + 8#64) u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
            (sepConj_mono_left
              (Entails.trans (v9_stackAt_encoderFromPbStack_to_allocHook fsp)
                (v9_stackAt_allocHook_to_drop32 fsp))))) ?_
        refine EncoderFromPb.seq_clean
          (P_mid := v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
            memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
            memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (SepWP.strengthen_entails_const ?_
              (v9_states_from_pb_drop_proto_uc_some_488 hA s0 s1 fsp out (pbA + 8#64) u0 w8 w0 w16 u
                (memRegion (fsp - 5152#64) 1024 ∗
                 (pbA ↦₆₄ 0x8000000000000009#64) ∗
                 v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
                 v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
                 memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
                hfsp_align hu0_lt hpc1 hrun1 hsp1 hx0_1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 htr1))) ?_
        · refine Entails.trans (Entails.of_eq (show _ =
            ((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
             v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             memRegion (pbA + 176#64) 48) ∗
            (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
            (v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             A.pool ∗ memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono
              (v9_pbA_128_entails_224 pbA w0 w8 w16 d.ptsNeeded d28 w32)
              (sepConj_mono_left
                (Entails.trans (v9_stackAt_drop32_to_allocHook fsp)
                  (v9_stackAt_allocHook_to_encoderFromPbStack fsp))))
            (Entails.of_eq (by ac_rfl))
        · rintro s2 hpc2 hrun2 ⟨hpres2, hx22_2⟩
          exact v9_tail_5368_to_ret hA s0 s2 fsp out pbA w0 w8 w16 d.ptsNeeded d28 w32 2#64
            (pbToProtoPolyDecoder d) .msgDecode hsp0_align hfsp_eq hpc2 hrun2 hpres2 hx22_2 rfl
    · -- Normal path (`+444 -> +2768`) with `d.ptsNeeded == 576#32 = true`
      have hd24_eq : d.ptsNeeded = 576#32 := beq_iff_eq.mp hpts
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
         A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by rw [hd24_eq]; ac_rfl)) ?_
      refine v9_sepWPp_seq_clean
        (v9_states_from_pb_step_444_to_2768_some s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d28 w32 _ hw0_lt hpc hrun hsp hx19 hx27 htr) ?_
      rintro s1 hpc1 hrun1 ⟨hsp1, _, hx8_1, hx9_1, _, hx13_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, _, htr1⟩
      rw [hx13] at hx13_1; rw [hx25] at hx25_1
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [hd24_eq]; ac_rfl))
        (v9_tail_2768_to_ret hA hDec s0 s1 fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d.ptsNeeded d28 w32 optUc (some d)
          hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx8_1 hx9_1 hx13_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
          (by intro d' hd'; cases hd'; exact hpts))

/-- Top-level `subroutine_ok` for Variant 9 (`some (.ct1Acknowledged st)`). -/
theorem states_from_pb_ct1Acknowledged_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (hDec : DecoderFromPbOkExt b A ext)
    (st : V1State.Chunked.Ct1Acknowledged) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.ct1Acknowledged st) }) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesFromPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align, _⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A pbA (some (.ct1Acknowledged st)) ∗
       statesFromPbJumpTableAt b ∗
       A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  refine v9_sepWPp_to_variantSpec s0 s0 out pbA { innerState := some (.ct1Acknowledged st) } _ R ?_
  have hpro := states_from_pb_prologue (b := b) (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A pbA (some (.ct1Acknowledged st)) ∗
     statesFromPbJumpTableAt b ∗
     A.pool)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine v9_sepWPp_seq_clean hpro ?_
  rintro s1 hpc1 hrun1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  dsimp only [optProtoInnerStateAt, protoInnerStateAt]
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      ((pbA ↦₆₄ 0x8000000000000009#64) ∗ statesFromPbJumpTableAt b ∗
       (protoChunkedCt1AcknowledgedAt A (pbA + 8#64) st ∗
        memRegion (pbA + 176#64) 48 ∗
        A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
      (sepConj_mono_left (cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64))) ?_
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (pbA ↦₆₄ 0x8000000000000009#64) ∗ statesFromPbJumpTableAt b ∗
    (protoChunkedCt1AcknowledgedAt A (pbA + 8#64) st ∗
     memRegion (pbA + 176#64) 48 ∗
     A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 2304 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
  refine v9_sepWPp_seq_clean
    (states_from_pb_dispatch_tagged s0 s1 out pbA 0x8000000000000009#64 444#64 _
      TaggedVariantDispatch.ct1Acknowledged hb_align hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1) ?_
  rintro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, _, hx25_2, _, hx13_2, _, htr2⟩
  have hx13_2' : s2.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64 := by rw [hx13_2]; bv_omega
  have hx25_2' : s2.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 := by rw [hx25_2]; bv_omega
  refine SepWPp.weaken_pre
    (by dsimp only [optProtoInnerStateAt, protoInnerStateAt]; exact Entails.of_eq (by ac_rfl))
    (v9_sepWPp_frame_right (J := statesFromPbJumpTableAt b)
      (states_from_pb_ct1Acknowledged_444 hA hDec s0 s2 (s0.sp - 2400#64) out pbA st
        hsp0_align rfl hpc2 hrun2 hsp2 hx13_2' hx19_2 hx25_2' hx27_2 htr2))

end CryptoVerification.SpqrV1.States.FromPb.Ext4K
