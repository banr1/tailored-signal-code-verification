/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 10 (`Ct2Sampled`, `+1632`)

Total-correctness relocatable Block-`333` theorems and `subroutine_ok` contracts for
`InnerState.ct2Sampled` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudget

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_333 extract_withLsCodeLoaded
   lsProg_333 lsmpl sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoderPB ProtoAuthenticator States V1State pbToProtoPolyEncoder spqrAuthApi
   spqrPolyApi)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoAuthenticatorAt optProtoInnerStateAt optProtoInnerStateSize
   optProtoUnchunkedCt2SentAt protoChunkedCt2SampledAt protoInnerStateAt
   protoUnchunkedCt2SentAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (optProtoPolynomialEncoderAt polyEncoderAt polyEncoderSize protoPolynomialEncoderAt
   protoPolynomialEncoderSize resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack fromPbResult hiBytes7 loByte loBytes7)
open CryptoVerification.SpqrV1.ProtoRepr
  (authenticatorPBAt authenticatorPBAt_eq_exists_pinned authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.States.FromPb
  (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304 optEncoderPtsBound
   resultChunkedStatesAt sp_sub_2400_align spqrErrorByte statesFromPbJumpTablePlacedAt
   statesFromPbSavedCells statesFromPbStack v1StatePtsBound v10_bs384_eq_encCells
   v10_encCellsAt v10_fsp_240_merge_1648 v10_fsp_240_split_5728
   v10_fsp_5808_err_entails_2064 v10_fsp_split_1632 v10_fsp_unsplit_1632
   v10_pbA_some_some_entails_224 v10_pointsTo32_pair_eq_pointsTo64
   v10_pointsTo64_eq_loByte_hiBytes7 v10_polyEncoderAt_relocate
   v10_protoPolynomialEncoderAt_relocate v10_resultPolyEncoder_err_entails_tag_392
   v10_states_from_pb_ct2Sampled_sending_none
   v10_states_from_pb_ct2Sampled_sending_some_err
   v10_states_from_pb_ct2Sampled_sending_some_ok
   v10_vecU8Payload_entails_vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authFromPbEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10PlacedBudget
  (v10_ct2Sent_5808_to_5820_err_placed_budget v10_ct2Sent_5808_to_7904_ok_placed_budget
   v10_ct2Sent_copy_to_encoder_call_5728_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget
  (v10_states_from_pb_err_2084_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudgetAux
  (Ct2SampledFromPbAllocEnv Ct2SampledFromPbEnv ct2SampledEnv_sub_statesFromPbEnv
   encoderFromPbEnv_append_freeOnly fitsEnv_alloc_of_ct2SampledEnv
   fitsEnv_alloc_of_statesFromPbEnv fitsEnv_enc_of_ct2SampledAllocEnv
   fitsEvents_auth_of_ct2SampledAllocEnv
   v10_ct2Sent_1632_to_5728_placed_sepWP
   v10_ct2Sent_sending_none_some_placed_sepWP)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget.toPlacedBudget encoder_from_pb_ok_of_alloc_placed)

export Variant10dPlacedBudgetAux
  (Ct2SampledFromPbAllocEnv Ct2SampledFromPbEnv ct2SampledEnv_sub_statesFromPbEnv
   fitsEnv_alloc_of_ct2SampledEnv fitsEnv_alloc_of_statesFromPbEnv
   v10_ct2Sent_expose_pre_uc_none_2304_placed v10_ct2Sent_err_1632_uc_none_2304_placed
   v10_ct2Sent_expose_pre_auth_none_2304_placed v10_ct2Sent_err_1632_auth_none_2304_placed
   v10_ct2Sent_1632_to_5728_placed v10_ct2Sent_1632_to_5728_placed_sepWP
   v10_ct2Sent_sending_none_some_placed v10_ct2Sent_sending_none_some_placed_sepWP)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## `+1632 -> s0.x30` when `sendingCt2 = some encPb` and `uc = some { auth := some auth, epoch := ep }` -/

set_option maxHeartbeats 800000 in
/-- Total-correctness (`SepWP`) branch `+1632 -> s0.x30` when `sendingCt2 = some encPb` and
    `uc = some { auth := some auth, epoch := ep }`, under
    `FitsEnv M lim st (Ct2SampledFromPbAllocEnv ...)`. -/
theorem v10_ct2Sent_sending_some_some_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s0 s1 : State) (out pbA ep : BitVec 64)
    (encPb : PolynomialEncoderPB) (auth : ProtoAuthenticator)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hpts : ∀ bs ∈ encPb.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st
      (Ct2SampledFromPbAllocEnv
        { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some encPb }))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x800000000000000a#64) ∗
        protoPolynomialEncoderAt A.repAlloc (pbA + 8#64) (pbToProtoPolyEncoder encPb) ∗
        authenticatorPBAt A.repAlloc (pbA + 64#64) auth ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
        memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          Ct2SampledFromPbEnv
            { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some encPb } evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct2Sampled
                    { sendingCt2 := some encPb,
                      uc := some { auth := some auth, epoch := ep } }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfits_auth : FitsEvents M lim st (authFromPbEvents auth) :=
    fitsEvents_auth_of_ct2SampledAllocEnv hfits
  rw [authenticatorPBAt_eq_exists_pinned A.repAlloc (pbA + 64#64) auth]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (v10_fsp_split_1632 (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left
          (v10_protoPolynomialEncoderAt_relocate A.repAlloc pbA ((s0.sp - 2400#64) + 1392#64)
            (pbToProtoPolyEncoder encPb)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun ga => SepWP.exists_elim fun cap_pts =>
    SepWP.exists_elim fun ptr_pts => SepWP.exists_elim fun cap_polys =>
    SepWP.exists_elim fun ptr_polys => SepWP.exists_elim fun w56 =>
    SepWP.exists_elim fun P_enc_heap => SepWP.exists_elim fun v232 =>
    SepWP.exists_elim fun v228 => SepWP.exists_elim fun v224 =>
    SepWP.exists_elim fun v200 => SepWP.exists_elim fun v184 =>
    SepWP.exists_elim fun v152 => ?_
  have hp16 := v10_pointsTo64_eq_loByte_hiBytes7 (pbA + 16#64) ptr_pts
  have ha17 : (pbA + 16#64) + 1#64 = pbA + 17#64 := by bv_omega
  rw [ha17] at hp16
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜cap_pts.toNat < 2 ^ 63 ∧
      ((((s0.sp - 2400#64) + 1392#64) ↦₆₄ cap_pts) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 8#64) ↦₆₄ ptr_pts) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 24#64) ↦₆₄ cap_polys) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 32#64) ↦₆₄ ptr_polys) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
       ((((s0.sp - 2400#64) + 1392#64) + 48#64) ↦₆₄ w56) ∗ P_enc_heap ⊢
        protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyEncoder encPb))⌝ ∗
    (((pbA + 16#64) ↦₆₄ ptr_pts) ∗
     (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
      authenticatorPBPinnedAt A.repAlloc ga (pbA + 64#64) auth ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
      (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗ A.pool lim st s1 ∗
      (memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
       ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
       ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
       ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTablePlacedAt))) by sep_ac_rfl)) ?_
  refine SepWP.pure_elim fun ⟨hcap_pts_lt, hreloc_pb⟩ => ?_
  rw [hp16]
  have h5728 := v10_ct2Sent_1632_to_5728_placed_sepWP hA st s0 s1 out pbA cap_pts ep
    v152 v184 v200 v232 (loByte ptr_pts) v224 ga auth
    (((pbA + 17#64) ↦ₛ hiBytes7 ptr_pts) ∗ memRegion (s0.sp - 2400#64) 152 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗ (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
     ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
     ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
     ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
     ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗
     statesFromPbJumpTablePlacedAt)
    hfits_auth hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine sepWP_seq_lscl hcl1
    (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h5728)
      fun s2 P2 hpc2 hrun2
        ⟨evs_af, pa1, pa2, hevs_af, hl1_lt, hP2,
         hsp2, hx19_2, hx21_2, hx22_2, _, hx26_2, hx27_2, htr2⟩ hcl2 => ?_)
  let st_af := M.stepEvents (authFromPbEvents auth ++ evs_af) st
  have hfits_enc : FitsEnv M lim st_af (EncoderFromPbAllocEnv (pbToProtoPolyEncoder encPb)) :=
    fitsEnv_enc_of_ct2SampledAllocEnv hfits hevs_af
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.trans (Entails.of_eq (show _ =
      (((pbA + 16#64) ↦₈ loByte ptr_pts) ∗ ((pbA + 17#64) ↦ₛ hiBytes7 ptr_pts)) ∗
      memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
       memRegion (pbA + 64#64) 56 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       A.pool lim st_af s2 ∗
       memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
       ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
       ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
       ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTablePlacedAt) by dsimp only [st_af]; sep_ac_rfl))
    (sepConj_mono (Entails.of_eq hp16.symm)
      (sepConj_mono_left (v10_fsp_240_split_5728 (s0.sp - 2400#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u1440 => SepWP.exists_elim fun u1432 =>
    SepWP.exists_elim fun u1424 => SepWP.exists_elim fun u1417 =>
    SepWP.exists_elim fun u1409 => SepWP.exists_elim fun u1401 =>
    SepWP.exists_elim fun b1400 => SepWP.exists_elim fun u1392 => ?_
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hcopy := v10_ct2Sent_copy_to_encoder_call_5728_placed_budget A lim st_af (ext := ext) s2
    (s0.sp - 2400#64) out pbA pa1 (BitVec.ofNat 64 auth.rootKey.length)
    (BitVec.ofNat 64 auth.macKey.length)
    cap_pts ptr_pts (BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length)
    cap_polys ptr_polys (BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) w56
    u1392 u1401 u1409 u1417 u1424 u1432 u1440 b1400
    (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440 ∗
     memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
     memRegion (pbA + 64#64) 56 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
     memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x800000000000000a#64) ∗
     P_enc_heap ∗ memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTablePlacedAt)
    hfsp_align hl1_lt hcap_pts_lt hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx26_2 hx27_2
  refine sepWP_seq_lscl hcl2
    (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hcopy)
      fun s3 P3 hpc3 hrun3
        ⟨hP3, _hvm3, hsp3, hx0_3, hx1_3, hx19_3, hx21_3, _, hx26_3, _, _, hx30_3, htr3⟩
        hcl3 => ?_)
  have htr3_0 : TraceCalleeSaved s3 s0 := htr3.trans htr2
  have hpb224 := v10_pbA_some_some_entails_224 pbA cap_pts ptr_pts
    (BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) cap_polys ptr_polys
    (BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) w56
  have hf1400 : ((s0.sp - 2400#64) + 1392#64) + 8#64 = (s0.sp - 2400#64) + 1400#64 := by bv_omega
  have hf1408 : ((s0.sp - 2400#64) + 1392#64) + 16#64 = (s0.sp - 2400#64) + 1408#64 := by bv_omega
  have hf1416 : ((s0.sp - 2400#64) + 1392#64) + 24#64 = (s0.sp - 2400#64) + 1416#64 := by bv_omega
  have hf1424 : ((s0.sp - 2400#64) + 1392#64) + 32#64 = (s0.sp - 2400#64) + 1424#64 := by bv_omega
  have hf1432 : ((s0.sp - 2400#64) + 1392#64) + 40#64 = (s0.sp - 2400#64) + 1432#64 := by bv_omega
  have hf1440 : ((s0.sp - 2400#64) + 1392#64) + 48#64 = (s0.sp - 2400#64) + 1440#64 := by bv_omega
  rw [hf1400, hf1408, hf1416, hf1424, hf1432, hf1440] at hreloc_pb
  refine SepWP.weaken_pre (Entails.trans hP3 (Entails.trans (Entails.of_eq (show _ =
      ((((s0.sp - 2400#64) + 1392#64) ↦₆₄ cap_pts) ∗
       (((s0.sp - 2400#64) + 1400#64) ↦₆₄ ptr_pts) ∗
       (((s0.sp - 2400#64) + 1408#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
       (((s0.sp - 2400#64) + 1416#64) ↦₆₄ cap_polys) ∗
       (((s0.sp - 2400#64) + 1424#64) ↦₆₄ ptr_polys) ∗
       (((s0.sp - 2400#64) + 1432#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
       (((s0.sp - 2400#64) + 1440#64) ↦₆₄ w56) ∗ P_enc_heap) ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ cap_pts) ∗
       ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).pts.length) ∗
       ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
       ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyEncoder encPb).polys.length) ∗
       ((pbA + 56#64) ↦₆₄ w56) ∗ memRegion (pbA + 64#64) 56 ∗ memRegion (pbA + 120#64) 104) ∗
      (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ A.pool lim st_af s3 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
        (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
        memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt)) by sep_ac_rfl))
    (Entails.trans (sepConj_mono hreloc_pb (sepConj_mono_left hpb224))
      (Entails.of_eq (show _ =
        (memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
         protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyEncoder encPb) ∗
         A.pool lim st_af s3 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
        (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
         (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        by dsimp only [polyEncoderSize]; sep_ac_rfl))))) ?_
  have hcall := Variant10PlacedBudget.v10_ct2Sent_call_encoder_374_to_5808_placed hEnc st_af s0 s3
    (s0.sp - 2400#64)
    (pbToProtoPolyEncoder encPb)
    (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1448#64) 440 ∗
     memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
     memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hcl3 hpts hfits_enc hfsp_align hpc3 hrun3 hsp3 hx0_3 hx1_3 hx30_3 htr3_0
  refine SepWP.seq hcall ?_
  intro s4 P4 hpc4 hrun4
    ⟨evs_enc, hevs_enc, hP4, hsp4, _hcs34, hx19_4_eq, hx21_4_eq, hx26_4_eq, htr4⟩
  have hx19_4 : s4.readReg64 .x19 = out := hx19_4_eq.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = pa1 := hx21_4_eq.trans hx21_3
  have hx26_4 : s4.readReg64 .x26 = BitVec.ofNat 64 auth.macKey.length := hx26_4_eq.trans hx26_3
  let st_enc := M.stepEvents evs_enc st_af
  have hm1648 := v10_fsp_240_merge_1648 (s0.sp - 2400#64)
  refine SepWP.weaken_pre (Entails.trans hP4 (Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1448#64) 440) ∗
      resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
        (fromPbResult (pbToProtoPolyEncoder encPb)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       A.pool lim st_enc s4 ∗
       memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      by dsimp only [protoPolynomialEncoderSize, st_enc]; sep_ac_rfl))
    (sepConj_mono_left hm1648))) ?_
  cases hres : fromPbResult (pbToProtoPolyEncoder encPb) with
  | error err =>
    rw [v10_states_from_pb_ct2Sampled_sending_some_err F encPb auth ep err hres]
    refine SepWP.weaken_pre (Entails.trans
      (sepConj_mono_right (sepConj_mono_left
        (v10_resultPolyEncoder_err_entails_tag_392 A.repAlloc (s0.sp - 2400#64) err)))
      (Entails.of_eq (show _ =
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
        (memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
         (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ∗
        A.pool lim st_enc s4 by sep_ac_rfl))) ?_
    have h5820 := v10_ct2Sent_5808_to_5820_err_placed_budget A lim st_enc (ext := ext)
      s0 s4 out pa1 (BitVec.ofNat 64 auth.macKey.length)
      (memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx26_4 htr4
    refine SepWP.seq h5820 ?_
    intro s5 P5 hpc5 hrun5 ⟨hP5, _hvm5, hsp5, hx19_5, hx21_5, hx26_5, htr5⟩
    have hf2064 := v10_fsp_5808_err_entails_2064 (s0.sp - 2400#64)
    have hd1 := v10_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc
      (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
    have hd2 := v10_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc
      (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
    refine SepWP.weaken_pre (Entails.trans hP5 (Entails.trans (Entails.of_eq (show _ =
        (memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ A.pool lim st_enc s5 ∗
         memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
         memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
         (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
      (Entails.trans (sepConj_mono hf2064 (sepConj_mono hd1 (sepConj_mono_left hd2)))
        (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          vecCapPtrDealloc A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 ∗
          vecCapPtrDealloc A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 ∗
          A.pool lim st_enc s5 ∗
          (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
           memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
           (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
           (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
           memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
           statesFromPbJumpTablePlacedAt) by sep_ac_rfl))))) ?_
    have h2084 := Variant10aPlacedBudget.v10_states_from_pb_err_5820_placed hA st_enc s0 s5 out
      (BitVec.ofNat 64 auth.rootKey.length) pa1 (BitVec.ofNat 64 auth.macKey.length) pa2
      (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt)
      hsp0_align hpc5 hrun5 hsp5 hx19_5 hx21_5 hx26_5 htr5
    refine SepWP.seq h2084 ?_
    intro s6 P6 hpc6 hrun6 ⟨evs_err, hevs_err, hP6, hsp6, hx19_6, hx21_6, htr6⟩
    let st_err := M.stepEvents evs_err st_enc
    have hfsp := v10_fsp_unsplit_1632 (s0.sp - 2400#64)
      ep pa2 (BitVec.ofNat 64 auth.rootKey.length) ga.macKey.ptr
      ((loByte ptr_pts).zeroExtend 32) v228
    refine SepWP.weaken_pre (Entails.trans hP6 (Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
         memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
         (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         memRegion ((s0.sp - 2400#64) + 240#64) 2064) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ A.pool lim st_err s6 ∗
         (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))
        by dsimp only [st_err]; sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (show _ =
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          A.pool lim st_err s6 ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl))))) ?_
    have hx21_byte : (s6.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx21_6]; rfl
    have herr := v10_states_from_pb_err_2084_placed_budget A lim st_err (F := F) (ext := ext)
      s0 s6 out .stateDecode
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc6 hrun6 hsp6 hx19_6 hx21_byte htr6
    refine SepWP.mono herr ?_
    intro sf Pf _ _ ⟨hPf, _hvmf, hsp_f, hcs_f, htr_f⟩
    have hst_all :
        st_err = M.stepEvents (authFromPbEvents auth ++ evs_af ++ (evs_enc ++ evs_err)) st := by
      simp only [st_err, st_enc, st_af, M.stepEvents_append]
    have henv : Ct2SampledFromPbEnv
        { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some encPb }
        (authFromPbEvents auth ++ evs_af ++ (evs_enc ++ evs_err)) :=
      ⟨evs_af, evs_enc ++ evs_err, hevs_af,
       encoderFromPbEnv_append_freeOnly hevs_enc hevs_err, rfl⟩
    exact ⟨authFromPbEvents auth ++ evs_af ++ (evs_enc ++ evs_err), henv,
      Entails.trans hPf (Entails.of_eq (by rw [hst_all]; sep_ac_rfl)),
      hsp_f, hcs_f, htr_f⟩
  | ok enc =>
    rw [v10_states_from_pb_ct2Sampled_sending_some_ok F encPb auth ep enc hres]
    dsimp only [resultPolyEncoderFromPbAt]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left
        (v10_polyEncoderAt_relocate A.repAlloc ((s0.sp - 2400#64) + 1888#64) (out + 8#64) enc))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun tag => SepWP.exists_elim fun bs =>
      SepWP.exists_elim fun hi32 => SepWP.exists_elim fun P_heap => ?_
    have hm224 := v10_pointsTo32_pair_eq_pointsTo64 ((s0.sp - 2400#64) + 224#64)
      ((loByte ptr_pts).zeroExtend 32) v228
    have ha228 : ((s0.sp - 2400#64) + 224#64) + 4#64 = (s0.sp - 2400#64) + 228#64 := by bv_omega
    have ha2280 : ((s0.sp - 2400#64) + 1888#64) + 392#64 = (s0.sp - 2400#64) + 2280#64 := by bv_omega
    rw [ha228] at hm224
    rw [v10_bs384_eq_encCells bs.val bs.property ((s0.sp - 2400#64) + 1888#64), ha2280]
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      ⌜(tag = 0#64 ∨ tag = 1#64) ∧
        (((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs.val) ∗
         (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
          polyEncoderAt A.repAlloc (out + 8#64) enc)⌝ ∗
      ((((s0.sp - 2400#64) + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228)) ∗
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗
       ((memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
        v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
        (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ P_heap ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ∗
        A.pool lim st_enc s4)) by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left (Entails.of_eq hm224)))) ?_
    refine SepWP.pure_elim fun ⟨htag, hreloc_out⟩ => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗
      ((memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ (v228 ++ (loByte ptr_pts).zeroExtend 32)) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) ∗
      A.pool lim st_enc s4 by sep_ac_rfl)) ?_
    have h7904 := v10_ct2Sent_5808_to_7904_ok_placed_budget A lim st_enc (ext := ext)
      s0 s4 (s0.sp - 2400#64) tag htag
      ((memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ (v228 ++ (loByte ptr_pts).zeroExtend 32)) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))
      hfsp_align hpc4 hrun4 hsp4 htr4
    refine SepWP.seq h7904 ?_
    intro s5 P5 hpc5 hrun5 ⟨hP5, _hvm5, hsp5, hx15_5, hx19_5, hx21_5, hx26_5, htr5⟩
    refine SepWP.weaken_pre (Entails.trans hP5 (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ (v228 ++ (loByte ptr_pts).zeroExtend 32)) ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
      (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗
      v10_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
      (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      statesFromPbSavedCells s0 ∗ P_heap ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ∗
      A.pool lim st_enc s5 by sep_ac_rfl))) ?_
    have hret := Variant10cPlacedBudget.v10_ct2Sent_7904_to_ret_placed (F := F) hA.toPlacedBudget st_enc s0 s5
      (s0.sp - 2400#64) out tag ep
      pa1 (BitVec.ofNat 64 auth.rootKey.length) pa2 (BitVec.ofNat 64 auth.macKey.length)
      (v228 ++ (loByte ptr_pts).zeroExtend 32) ga.macKey.ptr
      bs.val bs.property hi32 enc P_heap hreloc_out auth.rootKey auth.macKey rfl rfl
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align rfl hpc5 hrun5 hsp5 hx15_5 (hx19_5.trans hx19_4) (hx21_5.trans hx21_4)
      (hx26_5.trans hx26_4) htr5
    refine SepWP.mono hret ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, _hvmf⟩
    have hst_all :
        st_enc = M.stepEvents (authFromPbEvents auth ++ evs_af ++ evs_enc) st := by
      simp only [st_enc, st_af, M.stepEvents_append]
    have henv : Ct2SampledFromPbEnv
        { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some encPb }
        (authFromPbEvents auth ++ evs_af ++ evs_enc) :=
      ⟨evs_af, evs_enc, hevs_af, hevs_enc, rfl⟩
    exact ⟨authFromPbEvents auth ++ evs_af ++ evs_enc, henv,
      Entails.trans hPf (Entails.of_eq (by rw [hst_all]; sep_ac_rfl)),
      hsp_f, hcs_f, htr_f⟩

theorem v10_ct2Sent_sending_some_some_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s0 s1 : State) (out pbA ep : BitVec 64)
    (encPb : PolynomialEncoderPB) (auth : ProtoAuthenticator)
    (onPanic : State → SepProp → Prop)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hpts : ∀ bs ∈ encPb.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st
      (Ct2SampledFromPbAllocEnv
        { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some encPb }))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x800000000000000a#64) ∗
        protoPolynomialEncoderAt A.repAlloc (pbA + 8#64) (pbToProtoPolyEncoder encPb) ∗
        authenticatorPBAt A.repAlloc (pbA + 64#64) auth ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
        memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          Ct2SampledFromPbEnv
            { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some encPb } evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct2Sampled
                    { sendingCt2 := some encPb,
                      uc := some { auth := some auth, epoch := ep } }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      onPanic :=
  SepWPp.of_sepWP_ret
    (v10_ct2Sent_sending_some_some_placed_sepWP hA hEnc st s0 s1 out pbA ep encPb auth
      hcl1 hpts hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)

/-! ## Full Variant 10 (`Ct2Sampled`, `+1632`) Composition (`SepWP` & `SepWPp`) -/

/-- Total-correctness `SepWP` for Variant 10 (`InnerState.ct2Sampled`) from `+1632` to `s0.x30`
    under `RustCliAllocBudget M` and `FitsEnv M lim st (Ct2SampledFromPbAllocEnv s)`. -/
theorem states_from_pb_ct2Sampled_1632_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s : V1State.Chunked.Ct2Sampled)
    (hpts : v1StatePtsBound { innerState := some (.ct2Sampled s) })
    (hfits : FitsEnv M lim st (Ct2SampledFromPbAllocEnv s))
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.ct2Sampled s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct2SampledFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct2Sampled s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  dsimp only [v1StatePtsBound] at hpts
  dsimp only [optProtoInnerStateAt, protoInnerStateAt]
  cases s with | mk uc sendingCt2 =>
  cases uc with
  | none =>
    have herr := Variant10dPlacedBudgetAux.v10_ct2Sent_err_1632_uc_none_2304_placed (F := F) hA st
      s0 s1 out pbA sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    exact SepWP.mono herr fun sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩ =>
      ⟨⟨evs, hfree, hPf⟩, hsp_f, hcs_f, htr_f⟩
  | some uc =>
    cases uc with | mk ep auth =>
    cases auth with
    | none =>
      have herr := Variant10dPlacedBudgetAux.v10_ct2Sent_err_1632_auth_none_2304_placed (F := F) hA
        st s0 s1 out pbA ep sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      exact SepWP.mono herr fun sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩ =>
        ⟨⟨evs, hfree, hPf⟩, hsp_f, hcs_f, htr_f⟩
    | some auth =>
      dsimp only [protoChunkedCt2SampledAt, optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt,
        optProtoAuthenticatorAt]
      have ha64 : (pbA + 8#64) + 56#64 = pbA + 64#64 := by bv_omega
      have ha112 : (pbA + 64#64) + 48#64 = pbA + 112#64 := by bv_omega
      rw [ha64, ha112]
      cases sendingCt2 with
      | none =>
        dsimp only [Option.map, optProtoPolynomialEncoderAt]
        have ha16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
        rw [ha16]
        simp only [sepConj_assoc, v10_states_from_pb_ct2Sampled_sending_none]
        have hfits_auth : FitsEvents M lim st (authFromPbEvents auth) :=
          fitsEvents_auth_of_ct2SampledAllocEnv hfits
        have hnone := v10_ct2Sent_sending_none_some_placed_sepWP (F := F) hA st s0 s1 out pbA ep
          auth hfits_auth hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
        exact SepWP.mono hnone fun sf Pf _ _ ⟨evs, henv, hPf, hsp_f, hcs_f, htr_f⟩ =>
          ⟨⟨evs, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩
      | some encPb =>
        dsimp only [Option.map, optProtoPolynomialEncoderAt]
        simp only [sepConj_assoc]
        dsimp only [optEncoderPtsBound] at hpts
        have hsome := v10_ct2Sent_sending_some_some_placed_sepWP (F := F) hA hEnc st s0 s1 out
          pbA ep encPb auth hcl1 hpts hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
        exact SepWP.mono hsome fun sf Pf _ _ ⟨evs, henv, hPf, hsp_f, hcs_f, htr_f⟩ =>
          ⟨⟨evs, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩

theorem states_from_pb_ct2Sampled_1632_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s : V1State.Chunked.Ct2Sampled)
    (hpts : v1StatePtsBound { innerState := some (.ct2Sampled s) })
    (hfits : FitsEnv M lim st (Ct2SampledFromPbAllocEnv s))
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64) (onPanic : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.ct2Sampled s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct2SampledFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct2Sampled s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      onPanic :=
  SepWPp.of_sepWP_ret
    (states_from_pb_ct2Sampled_1632_placed_sepWP hA hEnc st s hpts hfits
      s0 s1 hcl1 out pbA hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)

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

/-- Envelope-parametric `subroutine_ok` for Variant 10 (`InnerState.ct2Sampled`) with
    `withLsCodeLoaded` under any `Env` with `Ct2SampledFromPbEnv s ⊆ Env` and
    `FitsEnv Env → FitsEnv (Ct2SampledFromPbAllocEnv s)`. -/
theorem states_from_pb_ct2Sampled_placed_ok_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct2Sampled)
    (halloc_fit : ∀ st : M.σ, FitsEnv M lim st Env →
      FitsEnv M lim st (Ct2SampledFromPbAllocEnv s))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → Ct2SampledFromPbEnv s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct2Sampled s) } Env)) := by
  refine sfpProof_tagged_ok_of_step_cl_placed TaggedVariantDispatch.ct2Sampled
    (Tail := fun pbA =>
      protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) s ∗ memRegion (pbA + 120#64) 104)
    (fun _ => rfl) ?_
  intro st s0 s1 out pbA hpts hfits hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 _hx23_1 hx27_1 htr1
  have h1632 := states_from_pb_ct2Sampled_1632_placed_sepWP (F := F) hA henc st s hpts
    (halloc_fit st hfits) s0 s1 hcl1 out pbA hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  exact SepWP.mono h1632 fun sf Pf _ _ ⟨⟨evs, hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩ =>
    ⟨⟨evs, hsub st hfits hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩

/-- `subroutine_ok` for Variant 10 (`InnerState.ct2Sampled`) under its tight envelope
    `Ct2SampledFromPbEnv s`. -/
theorem states_from_pb_ct2Sampled_placed_ok_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct2Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ct2Sampled s) } (Ct2SampledFromPbEnv s))) :=
  states_from_pb_ct2Sampled_placed_ok_of_env hA henc s
    (fun _ h => fitsEnv_alloc_of_ct2SampledEnv h)
    (fun _ _ _ h => h)

/-- `subroutine_ok` for Variant 10 (`InnerState.ct2Sampled`) under the uniform
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`), parameterized by `hA` and `henc`. -/
theorem states_from_pb_ct2Sampled_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.Ct2Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.ct2Sampled s) })) :=
  states_from_pb_ct2Sampled_placed_ok_of_env hA henc s
    (fun _ h => fitsEnv_alloc_of_statesFromPbEnv s h)
    (fun _ _ hfits hevs => ct2SampledEnv_sub_statesFromPbEnv s hfits hevs)

/-- `subroutine_ok` for Variant 10 (`InnerState.ct2Sampled`) under the uniform
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`), discharged from `FromPbAllocHooksBudget`
    alone via `encoder_from_pb_ok_of_alloc_placed`. -/
theorem states_from_pb_ct2Sampled_ok_ext_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s : V1State.Chunked.Ct2Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.ct2Sampled s) })) :=
  states_from_pb_ct2Sampled_ok_ext_placed hA (encoder_from_pb_ok_of_alloc_placed hA) s

abbrev states_from_pb_variant9_placed := @states_from_pb_ct2Sampled_ok_ext_placed

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudget
