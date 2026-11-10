/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2Placed
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2bPlacedBudget
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 1 (`KeysSampled`, `+1104`)

Total-correctness relocatable Block-`333` theorems and `subroutine_ok` contracts for
`InnerState.keysSampled` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudget

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_333 blkPl_333 extract_withLsCodeLoaded
   lsProg_333 lsmpl sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder ProtoAuthenticator States V1State pbToProtoPolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize
   optProtoUnchunkedHeaderSentAt protoChunkedKeysSampledAt protoInnerStateAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304 optEncoderPtsBound
   resultChunkedStatesAt sp_sub_2400_align statesFromPbJumpTablePlacedAt statesFromPbSavedCells
   statesFromPbStack v1StatePtsBound v1_bv_add_add_lit v1_bv_sub_sub_lit v1_from_pb_uc_err
   v1_from_pb_uc_none v1_memRegion_1392_split_frame v1_optProtoAuthHeap
   v1_optProtoAuthHeap_some_extract v1_optProtoPolyEncoderAt_unpack v1_optProtoPolyEncoderHeap
   v1_optProtoPolyEncoderWordsAt v1_optProtoUcHeap v1_optProtoUcHeap_some_extract
   v1_optProtoUnchunkedHeaderSentAt_unpack v1_pb128At v1_pb128_entails_112_and_enc
   v1_pb128_entails_full_224 v1_ucWordsAt v1_uc_and_enc_words_eq_pb128)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   fitsEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudgetAux
  (KeysSampledFromPbAllocEnv KeysSampledFromPbEnv KeysSampledTailFits
   fitsEnv_alloc_of_keysSampledEnv fitsEnv_alloc_of_statesFromPbEnv
   fitsEvents_auth_of_keysSampledAllocEnv keysSampledEnv_of_tail
   keysSampledEnv_sub_statesFromPbEnv keysSampledTailFits_of_keysSampledAllocEnv
   keysSampledValidAuth? keysSampledValidAuth?_eq_none_of_err keysSampledValidAuth?_eq_some
   v1_keysSampled_4016_ret_placed_sepWP)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget seq_clean_evs_lscl seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (encoder_from_pb_ok_of_alloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2bPlacedBudget
  (v1_auth_from_pb_step1_1292_8756_placed_sepWP v1_copy_pb_to_stack_1104_placed_budget
   v1_keysSampled_uc_none_rest_placed v1_validate_err_1196_placed
   v1_validate_ok_1196_1292_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlacedBudgetAux
  (v1_auth_from_pb_step2_8756_9804_placed v1_auth_from_pb_step3_9804_4016_placed)

export Variant2PlacedBudgetAux
  (KeysSampledFromPbAllocEnv KeysSampledFromPbEnv fitsEnv_alloc_of_keysSampledEnv
   fitsEnv_alloc_of_statesFromPbEnv keysSampledEnv_sub_statesFromPbEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## Validated `KeysSampled` Composition (`+1292 -> +8756 -> +9804 -> +4016 -> s0.x30`) -/

/-- Validated `s.uc = some uc`, `uc.auth = some auth` composition from `+1292` to `s0.x30`:
    clones `auth.rootKey` (`+1292 -> +8756`) and `auth.macKey` (`+8756 -> +9804`), deallocates
    the protobuf `auth` buffers (`+9804 -> +4016`), and runs `v1_keysSampled_4016_ret_placed_sepWP`
    to `s0.x30` under `KeysSampledFromPbAllocEnv`. -/
theorem v1_keysSampled_1292_ret_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (uc : V1State.Unchunked.HeaderSent) (auth : ProtoAuthenticator)
    (optEnc : Option PolynomialEncoder)
    (hpts : optEncoderPtsBound optEnc)
    (hfits : FitsEnv M lim st (KeysSampledFromPbAllocEnv { uc := some uc, sendingHdr := optEnc }))
    (hauth : uc.auth = some auth)
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (s0 s3 : State) (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w184 w200 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hu24 : u24 = BitVec.ofNat 64 uc.ek.length)
    (hu48 : u48 = BitVec.ofNat 64 uc.dk.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.rootKey.length)
    (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length)
    (hu104 : u104 = uc.epoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 1292#64)
    (hrun3 : s3.status = .Running) (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx21_3 : s3.readReg64 .x21 = u8)
    (hx23_3 : s3.readReg64 .x23 = u80) (hx24_3 : s3.readReg64 .x24 = u88)
    (hx25_3 : s3.readReg64 .x25 = u56) (hx27_3 : s3.readReg64 .x27 = pbA)
    (hx28_3 : s3.readReg64 .x28 = u64) (hx9_3 : s3.readReg64 .x9 = u96)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
        A.pool lim st s3 ∗
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
          v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
            w0 w8 w16 w24 w32 w40 w48 ∗
          vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
          vecU8Payload A.repAlloc u56 u64 auth.rootKey ∗
          vecU8Payload A.repAlloc u80 u88 auth.macKey ∗
          statesFromPbJumpTablePlacedAt))
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          KeysSampledFromPbEnv { uc := some uc, sendingHdr := optEnc } evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysSampled { uc := some uc, sendingHdr := optEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hval_auth : keysSampledValidAuth? uc = some auth :=
    keysSampledValidAuth?_eq_some hdk hek hauth
  have hfits_auth : FitsEvents M lim st (authFromPbEvents auth) :=
    fitsEvents_auth_of_keysSampledAllocEnv hval_auth hfits
  have ⟨hfits_rk, hfits_mk⟩ :=
    (fitsEvents_append M lim (authKeyCloneEvents auth.rootKey)
      (authKeyCloneEvents auth.macKey) st).mp hfits_auth
  let Frame1 : SepProp :=
    ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
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
    v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
      w0 w8 w16 w24 w32 w40 w48 ∗
    vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
    vecU8Payload A.repAlloc u80 u88 auth.macKey ∗ statesFromPbJumpTablePlacedAt
  have hstep1 := v1_auth_from_pb_step1_1292_8756_placed_sepWP hA st s0 s3
    (s0.sp - 2400#64) out pbA u8 u56 u64 u80 u88 u96 auth Frame1
    hfits_rk hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx25_3 hx27_3 hx28_3
    hx9_3 htr3
  refine sepWP_seq_lscl hcl3
    (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by dsimp only [Frame1]; sep_ac_rfl)) hstep1)
      fun s4 _P4 hpc4 hrun4 ⟨pa1, hP4,
        hsp4, hx19_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx9_4, htr4⟩
        hcl4 => ?_)
  refine SepWP.weaken_pre hP4 ?_
  rw [hu96] at hx9_4
  let st1 := M.stepEvents (authKeyCloneEvents auth.rootKey) st
  let Frame2 : SepProp :=
    ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
    vecCapPtrDealloc A.repAlloc u56 u64 ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
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
    v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
      w0 w8 w16 w24 w32 w40 w48 ∗
    vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
    statesFromPbJumpTablePlacedAt
  have hstep2 := v1_auth_from_pb_step2_8756_9804_placed hA st1 s0 s4
    (s0.sp - 2400#64) out pbA pa1 u8 u56 u64 u80 u88 w184 auth Frame2
    hfits_mk hfsp_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4
    hx27_4 hx28_4 hx9_4 htr4
  refine sepWP_seq_lscl hcl4
    (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by dsimp only [Frame1, Frame2, st1]; sep_ac_rfl)) hstep2)
      fun s5 _P5 hpc5 hrun5 ⟨pa2, hP5,
        hsp5, hx19_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, htr5⟩
        hcl5 => ?_)
  refine SepWP.weaken_pre hP5 ?_
  let st2 := M.stepEvents (authFromPbEvents auth) st
  have hst2_eq : M.stepEvents (authKeyCloneEvents auth.macKey) st1 = st2 := by
    dsimp only [st1, st2, authFromPbEvents]
    rw [M.stepEvents_append]
  rw [hst2_eq]
  have hstep3 := v1_auth_from_pb_step3_9804_4016_placed hA st2 s0 s5 out pbA pa1
    u8 u32 u56 u64 u80 u88 auth
    (((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
     ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
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
     v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
       w0 w8 w16 w24 w32 w40 w48 ∗
     vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
     statesFromPbJumpTablePlacedAt)
    hr_lt63 hsp0_align hpc5 hrun5 hsp5 hx19_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 htr5
  refine seq_clean_evs_lscl hcl5
    (SepWP.weaken_pre (Entails.of_eq (by dsimp only [Frame2]; sep_ac_rfl)) hstep3) ?_
  intro evs_af s6 hevs_af hpc6 hrun6 hcl6
    ⟨hsp6, hx19_6, hx20_6, hx21_6, hx22_6, hx25_6, hx26_6, hx27_6, hx28_6, htr6⟩
  rw [← hu72] at hx22_6 ⊢
  rw [← hu96]
  have hfits_tail : KeysSampledTailFits M lim (M.stepEvents evs_af st2) optEnc :=
    keysSampledTailFits_of_keysSampledAllocEnv hval_auth hfits hevs_af
  have h4016 := v1_keysSampled_4016_ret_placed_sepWP (F := F) hA henc (M.stepEvents evs_af st2)
    uc auth optEnc hpts hfits_tail hauth hdk hek hdk_lt hek_lt
    s0 s6 hcl6 out pbA pa1 pa2 w200 u8 u16 u24 u32 u40 u48 u72 u96 u104
    w0 w8 w16 w24 w32 w40 w48 hu24 hu48 hu72 hu96 hu104
    hsp0_align hpc6 hrun6 hsp6 hx19_6 hx20_6 hx21_6 hx22_6 hx25_6 hx26_6 hx27_6 hx28_6 htr6
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono h4016 fun sf Pf _ _ ⟨evs_tail, htail, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
  have hst_all :
      M.stepEvents evs_tail (M.stepEvents evs_af st2) =
        M.stepEvents (authFromPbEvents auth ++ evs_af ++ evs_tail) st := by
    dsimp only [st2]
    rw [M.stepEvents_append, M.stepEvents_append]
  rw [hst_all] at hPf
  exact ⟨authFromPbEvents auth ++ evs_af ++ evs_tail,
    keysSampledEnv_of_tail hval_auth hevs_af htail, hPf, hsp_f, hcs_f, htr_f⟩

/-! ## Full Variant 1 (`KeysSampled`, `+1104`) Composition (`SepWP` & `SepWPp`) -/

/-- Total-correctness `SepWP` for Variant 1 (`InnerState.keysSampled`) from `+1104` to `s0.x30`
    under `RustCliAllocBudget M` and `FitsEnv M lim st (KeysSampledFromPbAllocEnv s)`. -/
theorem states_from_pb_keysSampled_1104_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s : V1State.Chunked.KeysSampled)
    (hpts : v1StatePtsBound { innerState := some (.keysSampled s) })
    (hfits : FitsEnv M lim st (KeysSampledFromPbAllocEnv s))
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.keysSampled s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          KeysSampledFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysSampled s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  cases s with | mk optUc optEnc =>
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysSampledAt] at hpts ⊢
  have ha112 : (pbA + 8#64) + 104#64 = pbA + 112#64 := by bv_omega
  rw [ha112]
  have hunpack :
      optProtoUnchunkedHeaderSentAt A.repAlloc (pbA + 8#64) optUc ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 112#64) (optEnc.map pbToProtoPolyEncoder) ⊢
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
        v1_optProtoUcHeap A.repAlloc optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 := by
    refine Entails.trans
      (sepConj_mono (v1_optProtoUnchunkedHeaderSentAt_unpack A.repAlloc (pbA + 8#64) optUc)
        (v1_optProtoPolyEncoderAt_unpack A.repAlloc (pbA + 112#64)
          (optEnc.map pbToProtoPolyEncoder))) ?_
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
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      (optProtoUnchunkedHeaderSentAt A.repAlloc (pbA + 8#64) optUc ∗
       optProtoPolynomialEncoderAt A.repAlloc (pbA + 112#64) (optEnc.map pbToProtoPolyEncoder)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000001#64) ∗
       memRegion (pbA + 168#64) 56 ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl))
      (sepConj_mono_left hunpack)) ?_
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u8 => SepWP.exists_elim fun u16 =>
    SepWP.exists_elim fun u24 => SepWP.exists_elim fun u32 =>
    SepWP.exists_elim fun u40 => SepWP.exists_elim fun u48 =>
    SepWP.exists_elim fun u56 => SepWP.exists_elim fun u64 =>
    SepWP.exists_elim fun u72 => SepWP.exists_elim fun u80 =>
    SepWP.exists_elim fun u88 => SepWP.exists_elim fun u96 =>
    SepWP.exists_elim fun u104 => SepWP.exists_elim fun w0 =>
    SepWP.exists_elim fun w8 => SepWP.exists_elim fun w16 =>
    SepWP.exists_elim fun w24 => SepWP.exists_elim fun w32 =>
    SepWP.exists_elim fun w40 => SepWP.exists_elim fun w48 => ?_
  cases optUc with
  | none =>
    rw [v1_from_pb_uc_none optEnc]
    dsimp only [v1_optProtoUcHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine SepWP.pure_elim fun hu8 => ?_
    subst hu8
    have huc_none := v1_keysSampled_uc_none_rest_placed (F := F) hA st s0 s1 hcl1 out pbA
      u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
      (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
      statesFromPbJumpTablePlacedAt hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono huc_none fun sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
    exact ⟨⟨evs, hfree, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hsp_f, hcs_f, htr_f⟩
  | some uc =>
    refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (v1_optProtoUcHeap_some_extract A.repAlloc uc
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104)))) ?_
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine SepWP.pure_elim fun ⟨hu8, hu24, hu32, hu48, hu104, hek_lt, hdk_lt⟩ => ?_
    have hcopy := v1_copy_pb_to_stack_1104_placed_budget A lim st (ext := ext) s0 s1 out pbA
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000001#64) ∗ memRegion (pbA + 168#64) 56 ∗
       vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
       v1_optProtoAuthHeap A.repAlloc uc.auth u56 u64 u72 u80 u88 u96 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbJumpTablePlacedAt)
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    have hcmn : (u8 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu8)
    simp only [hcmn, Bool.false_eq_true, ↓reduceIte] at hcopy
    refine seq_clean_lscl_st hcl1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hcopy) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, hx19_2, hx20_2, hx27_2, htr2⟩
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
        have hauth_ex := v1_optProtoAuthHeap_some_extract A.repAlloc auth u56 u64 u72 u80 u88 u96
        refine SepWP.weaken_pre
          (Entails.trans (Entails.of_eq (show _ =
            memRegion (s0.sp - 2400#64) 1392 ∗
            ((pbA ↦₆₄ 0x8000000000000001#64) ∗
             v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
               w0 w8 w16 w24 w32 w40 w48) ∗
            v1_optProtoAuthHeap A.repAlloc (some auth) u56 u64 u72 u80 u88 u96 ∗
            (v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
               u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
               w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             memRegion (pbA + 168#64) 56 ∗
             vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
             v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
               w0 w8 w16 w24 w32 w40 w48 ∗
             statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl))
            (sepConj_mono h1392 (sepConj_mono hpb112 (sepConj_mono_left hauth_ex)))) ?_
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
        refine SepWP.exists_elim fun w232 => SepWP.exists_elim fun w224 =>
          SepWP.exists_elim fun w216 => SepWP.exists_elim fun w200 =>
          SepWP.exists_elim fun w192 => SepWP.exists_elim fun w184 =>
          SepWP.exists_elim fun w176 => SepWP.exists_elim fun w64 =>
          SepWP.pure_elim fun ⟨hu56, hu72, hu96, hr_lt63⟩ => ?_
        have hval := v1_validate_ok_1196_1292_placed_budget A lim st (ext := ext) s0 s2 out pbA
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
           v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
             w0 w8 w16 w24 w32 w40 w48 ∗
           vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
           vecU8Payload A.repAlloc u56 u64 auth.rootKey ∗
           vecU8Payload A.repAlloc u80 u88 auth.macKey ∗
           statesFromPbJumpTablePlacedAt)
          hdk hek hu56 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx27_2 htr2
        refine seq_clean_lscl_st hcl2 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hval) ?_
        intro s3 hpc3 hrun3 hcl3
          ⟨_hvm3, hsp3, hx19_3, hx20_3, hx21_3, _, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx9_3, htr3⟩
        rw [hu72] at hx20_3
        have h1292 := v1_keysSampled_1292_ret_placed_sepWP (F := F) hA henc st
          uc auth optEnc hpts hfits hauth hdk_pb hek_pb hdk_lt hek_lt hr_lt63
          s0 s3 hcl3 out pbA
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w184 w200
          w0 w8 w16 w24 w32 w40 w48 hu24 hu48 hu72 hu96 hu104
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx25_3 hx27_3 hx28_3 hx9_3 htr3
        exact SepWP.mono h1292 fun sf Pf _ _ ⟨evs, henv, hPf, hsp_f, hcs_f, htr_f⟩ =>
          ⟨⟨evs, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩
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
      have herr_val :
          ((BitVec.ofNat 64 uc.dk.length != 2400#64) ||
           (BitVec.ofNat 64 uc.ek.length != 1152#64)) = true ∨
          uc.auth = none := by
        rcases herr_pb with h1 | h2 | h3
        · exact Or.inl (by simp [bne, h1])
        · exact Or.inl (by simp [bne, h2])
        · exact Or.inr h3
      have hval_none : keysSampledValidAuth? uc = none :=
        keysSampledValidAuth?_eq_none_of_err herr_val
      rw [v1_from_pb_uc_err uc optEnc herr_pb hdk_lt hek_lt]
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
          A.pool lim st s2 ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           (pbA ↦₆₄ 0x8000000000000001#64) ∗ memRegion (pbA + 168#64) 56 ∗
           vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
           v1_optProtoAuthHeap A.repAlloc uc.auth u56 u64 u72 u80 u88 u96 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
             w0 w8 w16 w24 w32 w40 w48 ∗
           statesFromPbJumpTablePlacedAt) ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 1392 ∗
          v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
          v1_optProtoAuthHeap A.repAlloc uc.auth u56 u64 u72 u80 u88 u96 ∗
          A.pool lim st s2 ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
        refine Entails.trans (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 0x8000000000000001#64) ∗
           v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
             w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 168#64) 56) ∗
          vecU8Payload A.repAlloc u8 u16 uc.ek ∗
          vecU8Payload A.repAlloc u32 u40 uc.dk ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 1392 ∗
           v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
             u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
             w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
             w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           v1_optProtoAuthHeap A.repAlloc uc.auth u56 u64 u72 u80 u88 u96 ∗
           A.pool lim st s2 ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono hpb (sepConj_mono (vecU8Payload_entails_dealloc A.repAlloc u8 u16 uc.ek)
            (sepConj_mono_left (vecU8Payload_entails_dealloc A.repAlloc u32 u40 uc.dk))))
          (Entails.of_eq (by sep_ac_rfl))
      have herr1196 := v1_validate_err_1196_placed (F := F) hA st s0 s2 hcl2 out pbA
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        uc.auth (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        herr hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2
      refine SepWP.weaken_pre hpre
        (SepWP.mono herr1196 fun sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
      refine ⟨⟨evs, ?_, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hsp_f, hcs_f, htr_f⟩
      dsimp only [KeysSampledFromPbEnv]
      rw [hval_none]
      exact hfree

theorem states_from_pb_keysSampled_1104_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s : V1State.Chunked.KeysSampled)
    (hpts : v1StatePtsBound { innerState := some (.keysSampled s) })
    (hfits : FitsEnv M lim st (KeysSampledFromPbAllocEnv s))
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64) (onPanic : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.keysSampled s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          KeysSampledFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysSampled s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      onPanic :=
  SepWPp.of_sepWP_ret
    (states_from_pb_keysSampled_1104_placed_sepWP hA henc st s hpts hfits
      s0 s1 hcl1 out pbA hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1)

/-! ## `withLsCodeLoaded` Tagged-Variant Dispatch Combiner & `subroutine_ok` Theorems -/

/-- Lift a tagged-variant `SepWP` step at `+off` (requiring `LibsignalCodeLoaded lsmpl s1.mem`
    for cross-block calls) to `subroutine_ok` for
    `withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpecOfEnv ...)`. -/
theorem sfpProof_tagged_ok_of_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {inner : V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    {Env : List AllocEvent → Prop}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A.repAlloc pbA (some inner) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hstep : ∀ (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64),
      v1StatePtsBound { innerState := some inner } →
      FitsEnv M lim st Env →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s0.sp &&& 15#64 == 0#64) = true →
      s1.pc = lsmpl.base 333 + off →
      s1.status = .Running →
      s1.sp = s0.sp - 2400#64 →
      s1.readReg64 .x19 = out →
      s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
      s1.readReg64 .x27 = pbA →
      TraceCalleeSaved s1 s0 →
      SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim st s1)
        (fun sf Pf =>
          (∃ evs : List AllocEvent, Env evs ∧
            (Pf ⊢
              resultChunkedStatesAt A.repAlloc (F := F) out
                (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some inner }) ∗
              memRegion pbA optProtoInnerStateSize ∗
              statesFromPbJumpTablePlacedAt ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [DefsBudget.statesFromPbVariantPlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hpts, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  refine DefsBudget.sepWPp_of_states_exit_cl_placed st s0 s0 out pbA
    { innerState := some inner } Env _ R ?_
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWP_seq_lscl hcl0
    (SepWP.mono hpro fun s1 P1 hpc1 hrun1 ⟨hP1, hsp1, _, hx8_1, hx0_1, htr1, _⟩ hcl1 => ?_)
  have hP1' : P1 ⊢
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail pbA) ∗
      A.pool lim st s1 := by
    refine Entails.trans hP1 ?_
    rw [hinner pbA]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hP1' ?_
  have hdisp := states_from_pb_dispatch_tagged_placed_budget A lim st (ext := ext)
    s0 s1 out pbA tag off
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     Tail pbA)
    htag hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine sepWP_seq_lscl hcl1
    (SepWP.mono hdisp fun s2 P2 hpc2 hrun2
      ⟨hP2, hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2, _⟩ hcl2 => ?_)
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hpre_join : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s2 := by
    refine Entails.trans hP2 ?_
    rw [hinner pbA]
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ tag) ∗ Tail pbA) ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by sep_ac_rfl))
  exact SepWP.weaken_pre hpre_join
    (hstep st s0 s2 out pbA hpts hfits hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2' hx27_2 htr2)

/-- Envelope-parametric `subroutine_ok` for Variant 1 (`InnerState.keysSampled`) with
    `withLsCodeLoaded` under any `Env` with `KeysSampledFromPbEnv s ⊆ Env` and
    `FitsEnv Env → FitsEnv (KeysSampledFromPbAllocEnv s)`. -/
theorem states_from_pb_keysSampled_placed_ok_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.KeysSampled)
    (halloc_fit : ∀ st : M.σ, FitsEnv M lim st Env →
      FitsEnv M lim st (KeysSampledFromPbAllocEnv s))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → KeysSampledFromPbEnv s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.keysSampled s) } Env)) := by
  refine sfpProof_tagged_ok_of_step_cl_placed TaggedVariantDispatch.keysSampled
    (Tail := fun pbA => protoChunkedKeysSampledAt A.repAlloc (pbA + 8#64) s ∗ memRegion (pbA + 168#64) 56)
    (fun _ => rfl) ?_
  intro st s0 s1 out pbA hpts hfits hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1
  have h1104 := states_from_pb_keysSampled_1104_placed_sepWP (F := F) hA henc st s hpts
    (halloc_fit st hfits) s0 s1 hcl1 out pbA hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1
  exact SepWP.mono h1104 fun sf Pf _ _ ⟨⟨evs, hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩ =>
    ⟨⟨evs, hsub st hfits hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩

/-- `subroutine_ok` for Variant 1 (`InnerState.keysSampled`) under its tight envelope
    `KeysSampledFromPbEnv s`. -/
theorem states_from_pb_keysSampled_placed_ok_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.KeysSampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.keysSampled s) } (KeysSampledFromPbEnv s))) :=
  states_from_pb_keysSampled_placed_ok_of_env hA henc s
    (fun _ h => fitsEnv_alloc_of_keysSampledEnv h)
    (fun _ _ _ h => h)

/-- `subroutine_ok` for Variant 1 (`InnerState.keysSampled`) under the uniform
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`), parameterized by `hA` and `henc`. -/
theorem states_from_pb_keysSampled_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.KeysSampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.keysSampled s) })) :=
  states_from_pb_keysSampled_placed_ok_of_env hA henc s
    (fun _ h => fitsEnv_alloc_of_statesFromPbEnv s h)
    (fun _ _ hfits hevs => keysSampledEnv_sub_statesFromPbEnv s hfits hevs)

/-- `subroutine_ok` for Variant 1 (`InnerState.keysSampled`) under the uniform
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`), discharged from `FromPbAllocHooksBudget`
    alone via `encoder_from_pb_ok_of_alloc_placed`. -/
theorem states_from_pb_keysSampled_ok_ext_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s : V1State.Chunked.KeysSampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.keysSampled s) })) :=
  states_from_pb_keysSampled_ok_ext_placed hA (encoder_from_pb_ok_of_alloc_placed hA) s

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudget
