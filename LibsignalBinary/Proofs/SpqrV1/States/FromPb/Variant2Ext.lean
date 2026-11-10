/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2eExt
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2` -/

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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

open CryptoVerification.SpqrV1.Alloc

namespace Ext4K

theorem v1_keysSampled_4016_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (henc : EncoderFromPbOkExt b A ext)
    (uc : V1State.Unchunked.HeaderSent) (auth : ProtoAuthenticator)
    (optEnc : Option PolynomialEncoder) (hpts : optEncoderPtsBound optEnc)
    (hauth : uc.auth = some auth)
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63)
    (s0 s : State) (out pbA pa1 pa2 w200 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (R : SepProp)
    (hu24 : u24 = BitVec.ofNat 64 uc.ek.length)
    (hu48 : u48 = BitVec.ofNat 64 uc.dk.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.rootKey.length)
    (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length)
    (hu104 : u104 = uc.epoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4016#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = pa1) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        vecU8Payload A u8 u16 uc.ek ∗
        vecU8Payload A u32 u40 uc.dk ∗
        vecU8Payload A u72 pa1 auth.rootKey ∗
        vecU8Payload A u96 pa2 auth.macKey ∗
        statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysSampled { uc := some uc, sendingHdr := optEnc }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hm176 : memRegion (s0.sp - 2400#64) 64 ∗
      ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
      memRegion (s0.sp - 2400#64 + 72#64) 104 ⊢
      memRegion (s0.sp - 2400#64) 176 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  cases optEnc with
  | none =>
    rw [v1_from_pb_sendingHdr_none uc auth hauth hdk hek hdk_lt hek_lt]
    dsimp only [Option.map, v1_optProtoPolyEncoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine SepWPp.pure_elim fun hw0 => ?_
    subst hw0
    apply SepWPp.of_sepWP_ret
    have hnone := v1_sendingHdr_none_4016_5860 s0 s (s0.sp - 2400#64) out pa1 u8 u32 u72
      (((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
       ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗
       ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
       ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗
       ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
       ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
       memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
       ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
       ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ memRegion pbA 112 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗ vecU8Payload A u8 u16 uc.ek ∗
       vecU8Payload A u32 u40 uc.dk ∗ vecU8Payload A u72 pa1 auth.rootKey ∗
       vecU8Payload A u96 pa2 auth.macKey ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 hx26 hx28 htr
    have hw_1496 : v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) noneCap w8 w16 w24 w32 w40 w48 =
        ((s0.sp - 2400#64 + 1496#64) ↦₆₄ noneCap) ∗
        ((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
        ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗
        ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
        ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗
        ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
        ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48) := rfl
    refine SepWP.seq (SepWP.weaken_pre (by rw [hw_1496]; exact Entails.of_eq (by ac_rfl)) hnone) ?_
    intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx0_1, hx19_1, hx21_1, hx22_1, hx28_1, htr1⟩
    have hm24 : ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ⊢ memRegion (s0.sp - 2400#64 + 192#64) 24 :=
      collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
        collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
    have hm1496 := v1_optProtoPolyEncoderWordsAt_entails_56 (s0.sp - 2400#64 + 1496#64) noneCap w8 w16 w24 w32 w40 w48
    have hm2064 : memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) noneCap w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ⊢ memRegion (s0.sp - 2400#64 + 240#64) 2064 :=
      Entails.trans (sepConj_mono_right (sepConj_mono_left hm1496))
        (collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _)
    have hm112 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48
    have hmpb : memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ⊢ memRegion pbA optProtoInnerStateSize :=
      Entails.trans (sepConj_mono_right (sepConj_mono_left hm112))
        (collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _)
    have hP1' : P1 ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u72 pa1 ∗
        vecCapPtrDealloc A u96 pa2 ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        A.pool ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) := by
      refine Entails.trans hP1 ?_
      rw [hw_1496] at hm2064
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗ memRegion (s0.sp - 2400#64 + 72#64) 104) ∗
        (((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8) ∗
        (memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
         (((s0.sp - 2400#64 + 1496#64) ↦₆₄ noneCap) ∗ ((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
          ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗ ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
          ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗ ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
          ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48)) ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 752) ∗
        (memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 168#64) 56) ∗
        vecU8Payload A u72 pa1 auth.rootKey ∗
        vecU8Payload A u96 pa2 auth.macKey ∗
        vecU8Payload A u8 u16 uc.ek ∗
        vecU8Payload A u32 u40 uc.dk ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
         ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
      exact Entails.trans
        (sepConj_mono hm176 (sepConj_mono hm24 (sepConj_mono hm2064 (sepConj_mono hmpb
          (sepConj_mono (vecU8Payload_entails_dealloc A u72 pa1 auth.rootKey)
            (sepConj_mono (vecU8Payload_entails_dealloc A u96 pa2 auth.macKey)
              (sepConj_mono (vecU8Payload_entails_dealloc A u8 u16 uc.ek)
                (sepConj_mono_left (vecU8Payload_entails_dealloc A u32 u40 uc.dk)))))))))
        (Entails.of_eq (by ac_rfl))
    have hcl := v1_cleanup_sendingHdr_none_5860_sfa (A := A) (F := F) (.of_4k hA) s0 s1 out pa1 pa2 u8 u16 u32 u40 u72 u96
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx21_1 hx22_1 hx28_1 htr1
    refine SepWP.weaken_pre hP1' (SepWP.mono hcl fun sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some pbEnc =>
    rw [v1_from_pb_sendingHdr_some uc auth pbEnc hauth hdk hek hdk_lt hek_lt]
    dsimp only [Option.map]
    have hex_w0 := v1_optProtoPolyEncoderHeap_extract_w0 A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48
    dsimp only at hex_w0
    have hsplit1256 : memRegion (s0.sp - 2400#64 + 240#64) 1256 ⊢
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
        memRegion (s0.sp - 2400#64 + 896#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 952#64) 544 :=
      split_top <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _
    have hsplit752 : memRegion (s0.sp - 2400#64 + 1552#64) 752 ⊢
        memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
        memRegion (s0.sp - 2400#64 + 1888#64) polyEncoderSize ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 :=
      split_top <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
         memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
         ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
         ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
         ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
         v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA 112 ∗
         v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 168#64) 56 ∗ vecU8Payload A u8 u16 uc.ek ∗
         vecU8Payload A u32 u40 uc.dk ∗ vecU8Payload A u72 pa1 auth.rootKey ∗
         vecU8Payload A u96 pa2 auth.macKey ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl))
        (Entails.trans (sepConj_mono hex_w0 (sepConj_mono hsplit1256 (sepConj_mono_left hsplit752)))
          (Entails.of_eq (by ac_rfl)))) ?_
    refine SepWPp.pure_elim fun hw0 => ?_
    have h4016 := v1_sendingHdr_some_copy_4016_4096 (A := A) s0 s (s0.sp - 2400#64) out pbA pa1 w200 u8 u32 u72
      (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
       memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
       memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
       ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
       memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗ memRegion (s0.sp - 2400#64 + 1888#64) polyEncoderSize ∗
       memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ memRegion pbA 112 ∗ memRegion (pbA + 168#64) 56 ∗
       vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
       vecU8Payload A u72 pa1 auth.rootKey ∗ vecU8Payload A u96 pa2 auth.macKey ∗
       statesFromPbJumpTableAt b ∗ A.pool)
      hfsp_align hw0 hpc hrun hsp hx19 hx20 hx21 hx22 hx25 hx26 hx27 hx28 htr
    refine sepWPp_seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) h4016) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx28_1, htr1⟩
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (v1_encoder_call_4096 henc s0 s1 (s0.readReg64 .x30) (s0.sp - 2400#64) out pbA u8 u32 u72
        (pbToProtoPolyEncoder pbEnc) R
        (((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
         memRegion (s0.sp - 2400#64 + 1496#64) 56 ∗
         memRegion (pbA + 112#64) 56 ∗
         memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
         memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
         memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
         ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
         memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗ memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA 112 ∗ memRegion (pbA + 168#64) 56 ∗
         vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
         vecU8Payload A u72 pa1 auth.rootKey ∗ vecU8Payload A u96 pa2 auth.macKey ∗
         statesFromPbJumpTableAt b) _
        hfsp_align hpts hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx28_1 htr1
        fun s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx25_2, hx28_2, htr2⟩ => ?_)
    have hm1648 : memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
        memRegion (s0.sp - 2400#64 + 896#64) protoPolynomialEncoderSize ∗
        memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
        memRegion (s0.sp - 2400#64 + 1496#64) 56 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 336 ⊢
        memRegion (s0.sp - 2400#64 + 240#64) 1648 :=
      collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
        collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
    have hmpb : memRegion pbA 112 ∗ memRegion (pbA + 112#64) 56 ∗ memRegion (pbA + 168#64) 56 ⊢
        memRegion pbA optProtoInnerStateSize :=
      collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
    have hP2' :
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (s0.sp - 2400#64 + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
        memRegion (s0.sp - 2400#64 + 896#64) protoPolynomialEncoderSize ∗
        A.pool ∗
        (((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
         memRegion (s0.sp - 2400#64 + 1496#64) 56 ∗
         memRegion (pbA + 112#64) 56 ∗
         memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
         memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
         memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
         ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
         memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗ memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA 112 ∗ memRegion (pbA + 168#64) 56 ∗
         vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
         vecU8Payload A u72 pa1 auth.rootKey ∗ vecU8Payload A u96 pa2 auth.macKey ∗
         statesFromPbJumpTableAt b) ⊢
        resultPolyEncoderFromPbAt A (s0.sp - 2400#64 + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
        vecU8Payload A u72 pa1 auth.rootKey ∗ vecU8Payload A u96 pa2 auth.macKey ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool := by
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
         memRegion (s0.sp - 2400#64 + 896#64) protoPolynomialEncoderSize ∗
         memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
         memRegion (s0.sp - 2400#64 + 1496#64) 56 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 336) ∗
        (memRegion pbA 112 ∗ memRegion (pbA + 112#64) 56 ∗ memRegion (pbA + 168#64) 56) ∗
        (resultPolyEncoderFromPbAt A (s0.sp - 2400#64 + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
         memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
         ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
         ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
         ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
         vecU8Payload A u72 pa1 auth.rootKey ∗ vecU8Payload A u96 pa2 auth.macKey ∗
         statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hm1648 (sepConj_mono_left hmpb)) (Entails.of_eq (by ac_rfl))
    refine SepWP.weaken_pre hP2' ?_
    cases hres : fromPbResult (pbToProtoPolyEncoder pbEnc) with
    | error err =>
      have herr4100 := v1_encoder_err_4100_4116 (A := A) s0 s2 (s0.sp - 2400#64) out u8 u32 u72 err
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
         memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
         ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
         ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
         ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
         memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 uc.ek ∗
         vecU8Payload A u32 u40 uc.dk ∗ vecU8Payload A u72 pa1 auth.rootKey ∗
         vecU8Payload A u96 pa2 auth.macKey ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTableAt b ∗ A.pool)
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx25_2 hx28_2 htr2
      refine SepWP.seq herr4100 ?_
      intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx22_3, _, hx26_3, hx28_3, htr3⟩
      have hm2064 : memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
          memRegion (s0.sp - 2400#64 + 1888#64) 400 ∗
          memRegion (s0.sp - 2400#64 + 2288#64) 16 ⊢
          memRegion (s0.sp - 2400#64 + 240#64) 2064 :=
        collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
      have hP3' : P3 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 176 ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
          memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
          memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u72 pa1 ∗ vecCapPtrDealloc A u96 pa2 ∗
          vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗
          A.pool ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) := by
        refine Entails.trans hP3 ?_
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗ memRegion (s0.sp - 2400#64 + 72#64) 104) ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
          (memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗ memRegion (s0.sp - 2400#64 + 1888#64) 400 ∗
           memRegion (s0.sp - 2400#64 + 2288#64) 16) ∗
          vecU8Payload A u72 pa1 auth.rootKey ∗ vecU8Payload A u96 pa2 auth.macKey ∗
          vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
           ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
           memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
           ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           A.pool ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono hm176 (sepConj_mono (Drop.pointsTo64_entails_memRegion _ _) (sepConj_mono hm2064
            (sepConj_mono (vecU8Payload_entails_dealloc A u72 pa1 auth.rootKey)
              (sepConj_mono (vecU8Payload_entails_dealloc A u96 pa2 auth.macKey)
                (sepConj_mono (vecU8Payload_entails_dealloc A u8 u16 uc.ek)
                  (sepConj_mono_left (vecU8Payload_entails_dealloc A u32 u40 uc.dk))))))))
          (Entails.of_eq (by ac_rfl))
      have hcl := v1_cleanup_enc_err_4116_sfa (A := A) (F := F) (.of_4k hA) s0 s3 out pa1 pa2 u8 u16 u32 u40 u72 u96
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx26_3 hx28_3 htr3
      refine SepWP.weaken_pre hP3' (SepWP.mono hcl fun sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | ok enc =>
      dsimp only [resultPolyEncoderFromPbAt]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v1_polyEncoderAt_relocate A (s0.sp - 2400#64 + 1888#64) (out + 8#64) enc)) ?_
      wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine ProofLib.SepWP.exists_left fun tag =>
        ProofLib.SepWP.exists_left fun bs =>
        ProofLib.SepWP.exists_left fun hi32 =>
        ProofLib.SepWP.exists_left fun P_heap => ?_
      apply SepWP.pure_elim; rintro ⟨htag, hreloc⟩
      have ha2280 : (s0.sp - 2400#64 + 1888#64) + 392#64 = s0.sp - 2400#64 + 2280#64 := by bv_omega
      wp_conv_pre => rw [v1_bs384_eq_encCells bs.val bs.property (s0.sp - 2400#64 + 1888#64), ha2280]
      have hok4100 := v1_encoder_ok_4100_6568 s0 s2 (s0.sp - 2400#64) out tag u8 u32 u72
        (v1_encCellsAt (s0.sp - 2400#64 + 1888#64) bs.val ∗
         ((s0.sp - 2400#64 + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
         P_heap ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
         memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
         ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
         ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
         ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
         memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 uc.ek ∗
         vecU8Payload A u32 u40 uc.dk ∗ vecU8Payload A u72 pa1 auth.rootKey ∗
         vecU8Payload A u96 pa2 auth.macKey ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTableAt b ∗ A.pool)
        hfsp_align htag hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx23_2 hx25_2 hx28_2 htr2
      refine SepWP.seq hok4100 ?_
      intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx15_3, hx19_3, hx21_3, hx22_3, hx23_3, hx25_3, hx26_3, hx28_3, htr3⟩
      have hu24_1152 : u24 = 1152#64 := by rw [hu24]; exact beq_iff_eq.mp hek
      subst hu104
      have h6568 := v1_keysSampled_6568_ret (A := A) (F := F) hA s0 s3 out tag pa1 pa2
        u8 u16 u24 u32 u40 u48 u72 u96 uc.epoch bs.val bs.property hi32 enc P_heap hreloc
        uc.ek uc.dk auth.rootKey auth.macKey hu24 hu48 hu72 hu96 hu24_1152
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
        hsp0_align hpc3 hrun3 hsp3 hx15_3 hx19_3 hx21_3 hx22_3 hx23_3 hx25_3 hx26_3 hx28_3 htr3
      refine SepWP.weaken_pre (Entails.trans hP3 (Entails.of_eq (by ac_rfl)))
        (SepWP.mono h6568 fun sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 800000 in
/-- Canonical Variant 1 (`InnerState.keysSampled`, `+1104`) post-dispatch `SepWPp` theorem. -/
theorem states_from_pb_keysSampled_1104
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (henc : EncoderFromPbOkExt b A ext)
    (s : V1State.Chunked.KeysSampled) (hpts : optEncoderPtsBound s.sendingHdr)
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1104#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.keysSampled s)) ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.keysSampled s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  cases s with | mk optUc optEnc =>
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysSampledAt] at hpts ⊢
  have ha112 : (pbA + 8#64) + 104#64 = pbA + 112#64 := by bv_omega
  rw [ha112]
  have hunpack :
      optProtoUnchunkedHeaderSentAt A (pbA + 8#64) optUc ∗
        optProtoPolynomialEncoderAt A (pbA + 112#64) (optEnc.map pbToProtoPolyEncoder) ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
      ∃∗ u104 : BitVec 64,
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64,
      ∃∗ w48 : BitVec 64,
        v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 := by
    refine Entails.trans
      (sepConj_mono (v1_optProtoUnchunkedHeaderSentAt_unpack A (pbA + 8#64) optUc)
        (v1_optProtoPolyEncoderAt_unpack A (pbA + 112#64) (optEnc.map pbToProtoPolyEncoder))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16; apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w32; apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro u8; apply Entails.sepExists_elim; intro u16
    apply Entails.sepExists_elim; intro u24; apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u40; apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u56; apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u72; apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u88; apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u104
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
      (Entails.sepExists_right u40 (Entails.sepExists_right u48
      (Entails.sepExists_right u56 (Entails.sepExists_right u64
      (Entails.sepExists_right u72 (Entails.sepExists_right u80
      (Entails.sepExists_right u88 (Entails.sepExists_right u96
      (Entails.sepExists_right u104 (Entails.sepExists_right w0
      (Entails.sepExists_right w8 (Entails.sepExists_right w16
      (Entails.sepExists_right w24 (Entails.sepExists_right w32
      (Entails.sepExists_right w40 (Entails.sepExists_right w48 ?_)))))))))))))))))))
    rw [← v1_uc_and_enc_words_eq_pb128]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      (optProtoUnchunkedHeaderSentAt A (pbA + 8#64) optUc ∗
       optProtoPolynomialEncoderAt A (pbA + 112#64) (optEnc.map pbToProtoPolyEncoder)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000001#64) ∗
       memRegion (pbA + 168#64) 56 ∗
       statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl))
      (sepConj_mono_left hunpack)) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun u8 => SepWPp.exists_elim fun u16 =>
    SepWPp.exists_elim fun u24 => SepWPp.exists_elim fun u32 =>
    SepWPp.exists_elim fun u40 => SepWPp.exists_elim fun u48 =>
    SepWPp.exists_elim fun u56 => SepWPp.exists_elim fun u64 =>
    SepWPp.exists_elim fun u72 => SepWPp.exists_elim fun u80 =>
    SepWPp.exists_elim fun u88 => SepWPp.exists_elim fun u96 =>
    SepWPp.exists_elim fun u104 => SepWPp.exists_elim fun w0 =>
    SepWPp.exists_elim fun w8 => SepWPp.exists_elim fun w16 =>
    SepWPp.exists_elim fun w24 => SepWPp.exists_elim fun w32 =>
    SepWPp.exists_elim fun w40 => SepWPp.exists_elim fun w48 => ?_
  cases optUc with
  | none =>
    rw [v1_from_pb_uc_none optEnc]
    dsimp only [v1_optProtoUcHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine SepWPp.pure_elim fun hu8 => ?_
    subst hu8
    apply SepWPp.of_sepWP_ret
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (v1_keysSampled_uc_none_sfa (.of_4k hA) s0 s1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  | some uc =>
    refine SepWPp.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (v1_optProtoUcHeap_some_extract A uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104)))) ?_
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine SepWPp.pure_elim fun ⟨hu8, hu24, hu32, hu48, hu104, hek_lt, hdk_lt⟩ => ?_
    have hcopy := v1_copy_pb_to_stack_1104 s0 s1 out pbA
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000001#64) ∗ memRegion (pbA + 168#64) 56 ∗
       vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
       v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96 ∗
       v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbJumpTableAt b ∗ A.pool)
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    have hcmn : (u8 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu8)
    simp only [hcmn, Bool.false_eq_true, ↓reduceIte] at hcopy
    refine sepWPp_seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hcopy) ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx27_2, htr2⟩
    by_cases hvalid : (u48 == 2400#64) = true ∧ (u24 == 1152#64) = true ∧ uc.auth.isSome = true
    · rcases hvalid with ⟨hdk, hek, hauth_some⟩
      cases hauth : uc.auth with
      | none => rw [hauth] at hauth_some; cases hauth_some
      | some auth =>
        have hdk_pb : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true := by rw [← hu48]; exact hdk
        have hek_pb : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true := by rw [← hu24]; exact hek
        have hpb112 := v1_pb128_entails_112_and_enc pbA
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
        have h1392 := v1_memRegion_1392_split_frame (s0.sp - 2400#64)
        have hauth_ex := v1_optProtoAuthHeap_some_extract A auth u56 u64 u72 u80 u88 u96
        refine SepWPp.weaken_pre
          (Entails.trans (Entails.of_eq (show _ =
            memRegion (s0.sp - 2400#64) 1392 ∗
            ((pbA ↦₆₄ 0x8000000000000001#64) ∗
             v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
               w0 w8 w16 w24 w32 w40 w48) ∗
            v1_optProtoAuthHeap A (some auth) u56 u64 u72 u80 u88 u96 ∗
            (v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
               u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
               w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             memRegion (pbA + 168#64) 56 ∗
             vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
             v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder)
               w0 w8 w16 w24 w32 w40 w48 ∗
             statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl))
            (sepConj_mono h1392 (sepConj_mono hpb112 (sepConj_mono_left hauth_ex)))) ?_
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
        refine SepWPp.exists_elim fun w232 => SepWPp.exists_elim fun w224 =>
          SepWPp.exists_elim fun w216 => SepWPp.exists_elim fun w200 =>
          SepWPp.exists_elim fun w192 => SepWPp.exists_elim fun w184 =>
          SepWPp.exists_elim fun w176 => SepWPp.exists_elim fun w64 =>
          SepWPp.pure_elim fun ⟨hu56, hu72, hu96, hr_lt63⟩ => ?_
        have hval := v1_validate_ok_1196_1292 s0 s2 out pbA
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w64 w176 w192 w216 w224 w232
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 64 ∗
           memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
           ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
           ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
           memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA 112 ∗
           v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 168#64) 56 ∗
           v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
           vecU8Payload A u56 u64 auth.rootKey ∗ vecU8Payload A u80 u88 auth.macKey ∗
           statesFromPbJumpTableAt b ∗ A.pool)
          hdk hek hu56 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx27_2 htr2
        refine sepWPp_seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hval) ?_
        intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, hx21_3, _, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx9_3, htr3⟩
        rw [hu72] at hx20_3
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (v1_auth_from_pb_step1_1292_8756_sfa (.of_4k hA) s0 s3 (s0.readReg64 .x30) (s0.sp - 2400#64) out pbA
            u8 u56 u64 u80 u88 u96 auth
            (((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
             ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
             ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
             ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
             ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
             memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
             ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
             ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
             memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
             memRegion (s0.sp - 2400#64) 64 ∗
             memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             memRegion pbA 112 ∗
             v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (pbA + 168#64) 56 ∗
             v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
             vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
             vecU8Payload A u80 u88 auth.macKey ∗ statesFromPbJumpTableAt b)
            R _ hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx25_3 hx27_3 hx28_3
            hx9_3 hu96 htr3 fun pa1 s4 hpc4 hrun4
              ⟨hsp4, hx19_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx9_4, htr4⟩ => ?_)
        rw [hu96] at hx9_4
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (v1_auth_from_pb_step2_8756_9804_sfa (.of_4k hA) s0 s4 (s0.readReg64 .x30) (s0.sp - 2400#64) out pbA pa1
            u8 u56 u64 u80 u88 w184 auth
            (((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
             vecCapPtrDealloc A u56 u64 ∗
             vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
             ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
             ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
             ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
             ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
             memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
             ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
             ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
             memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
             memRegion (s0.sp - 2400#64) 64 ∗
             memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             memRegion pbA 112 ∗
             v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (pbA + 168#64) 56 ∗
             v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
             vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
             statesFromPbJumpTableAt b)
            R _ hfsp_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4
            hx9_4 htr4 fun pa2 s5 hpc5 hrun5
              ⟨hsp5, hx19_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, htr5⟩ => ?_)
        have hstep3 := v1_auth_from_pb_step3_9804_4016_sfa (.of_4k hA) s0 s5 out pbA pa1
          u8 u32 u56 u64 u80 u88 auth
          (((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
           vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
           ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
           vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
           ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
           ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
           ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
           memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
           ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
           memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
           memRegion (s0.sp - 2400#64) 64 ∗
           memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA 112 ∗
           v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 168#64) 56 ∗
           v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
           statesFromPbJumpTableAt b)
          hr_lt63 hsp0_align hpc5 hrun5 hsp5 hx19_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 htr5
        refine sepWPp_seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep3) ?_
        intro s6 hpc6 hrun6 ⟨hsp6, hx19_6, hx20_6, hx21_6, hx22_6, hx25_6, hx26_6, hx27_6, hx28_6, htr6⟩
        rw [← hu72] at hx22_6 ⊢
        rw [← hu96]
        exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (v1_keysSampled_4016_ret hA henc uc auth optEnc hpts hauth hdk_pb hek_pb hdk_lt hek_lt
            s0 s6 out pbA pa1 pa2 w200 u8 u16 u24 u32 u40 u48 u72 u96 u104
            w0 w8 w16 w24 w32 w40 w48 R hu24 hu48 hu72 hu96 hu104
            hsp0_align hpc6 hrun6 hsp6 hx19_6 hx20_6 hx21_6 hx22_6 hx25_6 hx26_6 hx27_6 hx28_6 htr6)
    · have herr : (u48 == 2400#64) = false ∨ (u24 == 1152#64) = false ∨ uc.auth = none := by
        rcases Classical.em ((u48 == 2400#64) = true) with h1 | h1
        · rcases Classical.em ((u24 == 1152#64) = true) with h2 | h2
          · right; right
            cases h3 : uc.auth with
            | none => rfl
            | some _ => exfalso; exact hvalid ⟨h1, h2, by simp [h3]⟩
          · right; left; exact Bool.eq_false_iff.mpr h2
        · left; exact Bool.eq_false_iff.mpr h1
      have herr_pb : (BitVec.ofNat 64 uc.dk.length == 2400#64) = false ∨
          (BitVec.ofNat 64 uc.ek.length == 1152#64) = false ∨ uc.auth = none := by
        rw [← hu48, ← hu24]; exact herr
      rw [v1_from_pb_uc_err uc optEnc herr_pb hdk_lt hek_lt]
      apply SepWPp.of_sepWP_ret
      have hpb := v1_pb128_entails_full_224 pbA
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
      have hpre :
          memRegion (s0.sp - 2400#64) 1392 ∗
          v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
            w0 w8 w16 w24 w32 w40 w48 ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           (pbA ↦₆₄ 0x8000000000000001#64) ∗ memRegion (pbA + 168#64) 56 ∗
           vecU8Payload A u8 u16 uc.ek ∗ vecU8Payload A u32 u40 uc.dk ∗
           v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96 ∗
           v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder)
             w0 w8 w16 w24 w32 w40 w48 ∗
           statesFromPbJumpTableAt b ∗ A.pool) ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 1392 ∗
          v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗
          v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96 ∗
          A.pool ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) := by
        refine Entails.trans (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 0x8000000000000001#64) ∗
           v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
             w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 168#64) 56) ∗
          vecU8Payload A u8 u16 uc.ek ∗
          vecU8Payload A u32 u40 uc.dk ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 1392 ∗
           v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
             u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
             w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (optEnc.map pbToProtoPolyEncoder)
             w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96 ∗
           A.pool ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono hpb (sepConj_mono (vecU8Payload_entails_dealloc A u8 u16 uc.ek)
            (sepConj_mono_left (vecU8Payload_entails_dealloc A u32 u40 uc.dk))))
          (Entails.of_eq (by ac_rfl))
      have herr1196 := v1_validate_err_1196_sfa (A := A) (F := F) (.of_4k hA) s0 s2 out pbA
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        uc.auth (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
        herr hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2
      refine SepWP.weaken_pre hpre
        (SepWP.mono herr1196 fun sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
