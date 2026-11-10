/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6f
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`)

Total-correctness (`SepWP`) relocatable body proof (`+1464 -> ret`) and `subroutine_ok` contracts
for Variant 6 (`InnerState.headerReceived`) of `<spqr::v1::chunked::states::States>::from_pb` under
`HeaderReceivedFromPbEnv` and `StatesFromPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsProg_333 lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoAuthenticator States V1State pbToProtoPolyDecoder
   spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize
   optProtoUnchunkedHeaderReceivedAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialDecoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304
   resultChunkedStatesAt statesFromPbJumpTablePlacedAt statesFromPbOnPanic
   statesFromPbSavedCells statesFromPbStack
   v6hr_dec_none_unpack v6hr_dec_some_unpack
   v6hr_from_pb_auth_none_dec_none v6hr_from_pb_auth_none_dec_some
   v6hr_from_pb_hdr_eq64_dec_none v6hr_from_pb_hdr_ne64_dec_none
   v6hr_from_pb_hdr_ne64_dec_some v6hr_from_pb_ptsNeeded_ne
   v6hr_from_pb_uc_none_dec_none v6hr_from_pb_uc_none_dec_some
   v6hr_headersAt v6hr_lowStackAt v6hr_memRegion_2304_entails_lowStackAt
   v6hr_ofNat_len_beq_64_false v6hr_optProtoInnerStateAt_headerReceived
   v6hr_sepWP_pure_left v6hr_uc_auth_none_unpack' v6hr_uc_auth_some_unpack'
   v6hr_uc_none_unpack v6hr_vecU8Payload_entails_vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Unchunked (vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlacedBudget
  (V6hrAuthCloneEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
  resultChunkedStatesAt statesFromPbSavedCells vecU8Payload

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudgetAux
  (HeaderReceivedFromPbAllocEnv
   HeaderReceivedFromPbEnv
   v6hrAuthCloneEnv_append_freeOnly
   fitsEnv_alloc_of_headerReceivedEnv
   fitsEvents_authClone_of_allocEnv_dec_none
   fitsEvents_authClone_of_allocEnv_dec_some
   fitsEnv_decAlloc_of_allocEnv_dec_some
   headerReceivedFromPbEnv_sub_statesFromPbEnv
   fitsEnv_alloc_of_statesFromPbEnv
   v6hr_sepWP_bind_lscl
   v6hr_lowStack_load_headers_1464_none_to_3760_placed_budget
   v6hr_lowStack_load_headers_1464_some_eq_to_3760_placed_budget
   v6hr_lowStack_load_headers_1464_some_ne_to_1520_placed_budget
   v6hr_lowStack_err_3760_uc_none_to_10316_placed_budget
   v6hr_lowStack_err_3760_auth_none_to_10316_of_placedHooks
   v6hr_lowStack_err_3760_auth_none_to_10316_placed
   v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316_of_placedHooks
   v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316_placed
   v6hr_lowStack_err_1520_uc_none_to_10324_placed_budget
   v6hr_lowStack_err_1520_auth_none_to_10324_of_placedHooks
   v6hr_lowStack_err_1520_auth_none_to_10324_placed
   v6hr_lowStack_err_1520_auth_some_to_10324_of_placedHooks
   v6hr_lowStack_err_1520_auth_some_to_10324_placed)

private theorem v6hr_reassoc_exit_post {Pf R_out P_pool P_pb P_jt P_st : SepProp}
    (hPf : Pf ⊢ R_out ∗ (P_pool ∗ (P_pb ∗ P_jt)) ∗ P_st) :
    Pf ⊢ R_out ∗ P_pb ∗ P_jt ∗ P_pool ∗ P_st :=
  Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-! ## 1. Post-Dispatch Body Theorem (`+1464 -> ret`) -/

set_option maxHeartbeats 1600000 in
/-- Total-correctness (`SepWP`, no panic/OOM) relocatable body proof for Variant 6
    (`InnerState.headerReceived`, `+1464 -> ret`, Block `333`) under `RustCliAllocBudget M`. -/
theorem states_from_pb_headerReceived_1464_of_placedHooks_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s : V1State.Chunked.HeaderReceived)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (hfits : FitsEnv M lim st (HeaderReceivedFromPbAllocEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (_hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.headerReceived s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          HeaderReceivedFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerReceived s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  rw [v6hr_optProtoInnerStateAt_headerReceived A.repAlloc pbA s]
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        memRegion (s0.sp - 2400#64) 2304 ∗
        (optProtoPolynomialDecoderAt A.repAlloc (pbA + 88#64) (s.receivingEk.map pbToProtoPolyDecoder) ∗
         optProtoUnchunkedHeaderReceivedAt A.repAlloc (pbA + 8#64) s.uc ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
         memRegion (pbA + 128#64) 96 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl))
      (sepConj_mono_left (v6hr_memRegion_2304_entails_lowStackAt s0.sp))) ?_
  simp only [sepExists_sepConj_left]
  refine ProofLib.SepWP.exists_left fun v80 => ProofLib.SepWP.exists_left fun v128 =>
    ProofLib.SepWP.exists_left fun v136 => ProofLib.SepWP.exists_left fun v144 =>
    ProofLib.SepWP.exists_left fun d184 => ProofLib.SepWP.exists_left fun v192 =>
    ProofLib.SepWP.exists_left fun d200 => ProofLib.SepWP.exists_left fun v208 =>
    ProofLib.SepWP.exists_left fun v216 => ProofLib.SepWP.exists_left fun v224 =>
    ProofLib.SepWP.exists_left fun v232 => ?_
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      optProtoPolynomialDecoderAt A.repAlloc (pbA + 88#64) (s.receivingEk.map pbToProtoPolyDecoder) ∗
      (optProtoUnchunkedHeaderReceivedAt A.repAlloc (pbA + 8#64) s.uc ∗
       v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
       memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗ memRegion (pbA + 128#64) 96 ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
  rcases s with ⟨uc, receivingEk⟩
  dsimp only
  cases receivingEk with
  | none =>
    dsimp only [Option.map]
    refine SepWP.weaken_pre (sepConj_mono_left (v6hr_dec_none_unpack A.repAlloc pbA)) ?_
    simp only [sepExists_sepConj_left]
    refine ProofLib.SepWP.exists_left fun w96 => ProofLib.SepWP.exists_left fun w104 =>
      ProofLib.SepWP.exists_left fun d112 => ProofLib.SepWP.exists_left fun d116 =>
      ProofLib.SepWP.exists_left fun w120 => ?_
    refine SepWP.weaken_pre
      (Entails.of_eq (show _ =
        optProtoUnchunkedHeaderReceivedAt A.repAlloc (pbA + 8#64) uc ∗
        (((pbA + 88#64) ↦₆₄ noneCap) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
         ((pbA + 104#64) ↦₆₄ w104) ∗ ((pbA + 112#64) ↦₃₂ d112) ∗
         ((pbA + 116#64) ↦₃₂ d116) ∗ ((pbA + 120#64) ↦₆₄ w120) ∗
         v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗ memRegion (pbA + 128#64) 96 ∗
         statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
    cases uc with
    | none =>
      rw [v6hr_from_pb_uc_none_dec_none F]
      refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_none_unpack A.repAlloc pbA)) ?_
      simp only [sepExists_sepConj_left]
      refine ProofLib.SepWP.exists_left fun w16 => ProofLib.SepWP.exists_left fun w24 =>
        ProofLib.SepWP.exists_left fun w32 => ProofLib.SepWP.exists_left fun w40 =>
        ProofLib.SepWP.exists_left fun w48 => ProofLib.SepWP.exists_left fun w56 =>
        ProofLib.SepWP.exists_left fun w64 => ProofLib.SepWP.exists_left fun w72 =>
        ProofLib.SepWP.exists_left fun w80 => ?_
      refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
        (SepWP.seq
          (v6hr_lowStack_load_headers_1464_none_to_3760_placed_budget A lim st s0 s1 out pbA
            noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 d112 d116 w120
            v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
            (memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             statesFromPbJumpTablePlacedAt)
            hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
      intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
      refine SepWP.weaken_pre hP2
        (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (SepWP.seq
            (v6hr_lowStack_err_3760_uc_none_to_10316_placed_budget A lim st s0 s2 out
              w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
              (memRegion pbA optProtoInnerStateSize ∗ memRegion (s0.sp - 2160#64) 2064 ∗
               stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
              hsp0_align hpc2 hrun2 hregs2) ?_))
      intro s3 P3 hpc3 hrun3 ⟨hP3, _, hpres3, _⟩
      refine SepWP.weaken_pre hP3
        (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono
            (Variant6fPlacedBudgetAux.v6hr_exit_err_10316_none_placed_budget A lim st (F := F)
              s0 s3 out w96 0#64
              v80 v128 v136 v144 d184 v192 d200 v208 v216 w120 w96
              (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
              hsp0_align hpc3 hrun3 rfl hpres3) ?_))
      intro sf Pf _ _ ⟨hPf, _, hsp_f, hcs_f, htr_f⟩
      exact ⟨⟨[], rfl, v6hr_reassoc_exit_post hPf⟩, hsp_f, hcs_f, htr_f⟩
    | some ucVal =>
      rcases ucVal with ⟨epoch, authOpt, hdr⟩
      cases authOpt with
      | none =>
        rw [v6hr_from_pb_auth_none_dec_none F hdr epoch]
        refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_none_unpack' A.repAlloc pbA hdr epoch)) ?_
        simp only [sepExists_sepConj_left]
        refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
          ProofLib.SepWP.exists_left fun w40 => ProofLib.SepWP.exists_left fun w48 =>
          ProofLib.SepWP.exists_left fun w56 => ProofLib.SepWP.exists_left fun w64 =>
          ProofLib.SepWP.exists_left fun w72 => ?_
        refine v6hr_sepWP_pure_left fun ⟨_, hc0⟩ => ?_
        refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
          (SepWP.seq
            (v6hr_lowStack_load_headers_1464_none_to_3760_placed_budget A lim st s0 s1 out pbA
              c0 p0 (BitVec.ofNat 64 hdr.length) noneCap w40 w48 w56 w64 w72 epoch w96 w104 d112 d116 w120
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
              (vecCapPtrDealloc A.repAlloc c0 p0 ∗ memRegion (s0.sp - 2160#64) 2064 ∗
               stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
              hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
        intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
        refine SepWP.weaken_pre hP2
          (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_err_3760_auth_none_to_10316_of_placedHooks hA st s0 s2 out
                c0 p0 (BitVec.ofNat 64 hdr.length) w40 w48 w56 w64 w72 epoch noneCap w96 w104 d112 d116 w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                (memRegion pbA optProtoInnerStateSize ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                hsp0_align hc0 hpc2 hrun2 hregs2) ?_))
        intro s3 P3 hpc3 hrun3 ⟨evs1, hevs1, hP3, hx25_3, hpres3, _⟩
        refine SepWP.weaken_pre hP3
          (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (SepWP.mono
              (Variant6fPlacedBudgetAux.v6hr_exit_err_10316_none_placed_budget A lim
                (M.stepEvents evs1 st) (F := F) s0 s3 out w96 (s3.readReg64 .x25)
                (BitVec.ofNat 64 hdr.length) v128 v136 (if (c0 == 0#64) = true then v144 else p0)
                d184 v192 d200 v208 v216 w120 w96
                (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                hsp0_align hpc3 hrun3 hx25_3 hpres3) ?_))
        intro sf Pf _ _ ⟨hPf, _, hsp_f, hcs_f, htr_f⟩
        exact ⟨⟨evs1, hevs1, v6hr_reassoc_exit_post hPf⟩, hsp_f, hcs_f, htr_f⟩
      | some authPb =>
        refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_some_unpack' A.repAlloc pbA hdr authPb epoch)) ?_
        simp only [sepExists_sepConj_left]
        refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
          ProofLib.SepWP.exists_left fun c1 => ProofLib.SepWP.exists_left fun p1 =>
          ProofLib.SepWP.exists_left fun c2 => ProofLib.SepWP.exists_left fun p2 => ?_
        refine v6hr_sepWP_pure_left fun ⟨⟨hc0_le, hc0⟩, ⟨_, hc1⟩⟩ => ?_
        by_cases hlen : hdr.length = 64
        · rw [v6hr_from_pb_hdr_eq64_dec_none F hdr authPb epoch hlen]
          have hfits_auth : FitsEvents M lim st
              (authKeyCloneEvents authPb.rootKey ++ authKeyCloneEvents authPb.macKey) :=
            fitsEvents_authClone_of_allocEnv_dec_none hfits hlen
          have hlen_bv : BitVec.ofNat 64 hdr.length = 64#64 := by rw [hlen]
          rw [hlen_bv]
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_none_to_3760_placed_budget A lim st s0 s1 out pbA
                c0 p0 64#64 c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch w96 w104 d112 d116 w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecU8Payload A.repAlloc c0 p0 hdr ∗ vecU8Payload A.repAlloc c1 p1 authPb.rootKey ∗
                 vecU8Payload A.repAlloc c2 p2 authPb.macKey ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                 stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
                 memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.seq
                (Variant6fPlacedBudget.v6hr_step_3760_to_9936_of_placedHooks_sepWP hA st s0 s2
                  out c0 p0 c1 p1 c2 p2 epoch noneCap w96 w104 w120 d112 d116
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  authPb.rootKey authPb.macKey
                  (vecU8Payload A.repAlloc c0 p0 hdr ∗ memRegion pbA optProtoInnerStateSize ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                   memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                  hfits_auth hsp0_align hc0 hc1 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨evs1, p1_new, p2_new, d184', hevs1, hP3, hsp3, _, _, hx19_3, _,
            hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.mono
                (Variant6fPlacedBudget.v6hr_step_9936_dec_none_to_exit_of_placedHooks (F := F) hA
                  (M.stepEvents evs1 st) s0 s3
                  out c0 p0 p1_new p2_new epoch p2 w120 w96 d184' d116
                  authPb.rootKey authPb.macKey hdr
                  (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hpc3 hrun3 hsp3 hx19_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3) ?_))
          intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
          refine ⟨⟨evs1 ++ evs2, ?_, ?_⟩, hsp_f, hcs_f, htr_f⟩
          · simp only [HeaderReceivedFromPbEnv, hlen, ↓reduceIte]
            exact v6hrAuthCloneEnv_append_freeOnly hevs1 hevs2
          · rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            exact v6hr_reassoc_exit_post hPf
        · rw [v6hr_from_pb_hdr_ne64_dec_none F hdr authPb epoch hlen]
          have hw24 := v6hr_ofNat_len_beq_64_false hlen hc0_le hc0
          refine SepWP.weaken_pre
            (sepConj_mono_left
              (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c0 p0 hdr)
                (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c1 p1 authPb.rootKey)
                  (sepConj_mono_left (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c2 p2 authPb.macKey))))) ?_
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_none_to_3760_placed_budget A lim st s0 s1 out pbA
                c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch w96 w104 d112 d116 w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecCapPtrDealloc A.repAlloc c0 p0 ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
                 vecCapPtrDealloc A.repAlloc c2 p2 ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                 stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
                 memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.seq
                (v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316_of_placedHooks hA st s0 s2 out
                  c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                  c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch noneCap w96 w104 d112 d116 w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  (memRegion pbA optProtoInnerStateSize ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                   statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hc0 hc1 hw24 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨evs1, hevs1, hP3, hx25_3, hpres3, _⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.mono
                (Variant6fPlacedBudgetAux.v6hr_exit_err_10316_none_placed_budget A lim
                  (M.stepEvents evs1 st) (F := F) s0 s3 out w96 (s3.readReg64 .x25)
                  (BitVec.ofNat 64 hdr.length) v128 v136 (if (c0 == 0#64) = true then v144 else p0)
                  d184 v192 d200 v208 v216 w120 w96
                  (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hpc3 hrun3 hx25_3 hpres3) ?_))
          intro sf Pf _ _ ⟨hPf, _, hsp_f, hcs_f, htr_f⟩
          refine ⟨⟨evs1, ?_, v6hr_reassoc_exit_post hPf⟩, hsp_f, hcs_f, htr_f⟩
          simp only [HeaderReceivedFromPbEnv, hlen, ↓reduceIte]
          exact hevs1
  | some decPb =>
    dsimp only [Option.map]
    refine SepWP.weaken_pre
      (sepConj_mono_left (v6hr_dec_some_unpack A.repAlloc pbA (pbToProtoPolyDecoder decPb))) ?_
    simp only [sepExists_sepConj_left]
    refine ProofLib.SepWP.exists_left fun ptsCap => ProofLib.SepWP.exists_left fun ptsPtr =>
      ProofLib.SepWP.exists_left fun w120 => ?_
    refine v6hr_sepWP_pure_left fun ⟨hpts_le, hpts_cap_lt, hpts_ne, hw120⟩ => ?_
    have hw88 : ptsCap.toNat < 2 ^ 63 := by omega
    refine SepWP.weaken_pre
      (Entails.of_eq (show _ =
        optProtoUnchunkedHeaderReceivedAt A.repAlloc (pbA + 8#64) uc ∗
        (((pbA + 88#64) ↦₆₄ ptsCap) ∗ ((pbA + 96#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length) ∗
         ((pbA + 112#64) ↦₃₂ (pbToProtoPolyDecoder decPb).ptsNeeded) ∗
         ((pbA + 116#64) ↦₃₂ (pbToProtoPolyDecoder decPb).polys) ∗
         ((pbA + 120#64) ↦₆₄ w120) ∗
         (if ptsCap = 0#64 then emp
          else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
              ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
         v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗ memRegion (pbA + 128#64) 96 ∗
         statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
    by_cases heq_pts : decPb.ptsNeeded = 576#32
    · have heq_pts' : (pbToProtoPolyDecoder decPb).ptsNeeded = 576#32 := heq_pts
      rw [heq_pts']
      cases uc with
      | none =>
        rw [v6hr_from_pb_uc_none_dec_some F decPb heq_pts]
        refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_none_unpack A.repAlloc pbA)) ?_
        simp only [sepExists_sepConj_left]
        refine ProofLib.SepWP.exists_left fun w16 => ProofLib.SepWP.exists_left fun w24 =>
          ProofLib.SepWP.exists_left fun w32 => ProofLib.SepWP.exists_left fun w40 =>
          ProofLib.SepWP.exists_left fun w48 => ProofLib.SepWP.exists_left fun w56 =>
          ProofLib.SepWP.exists_left fun w64 => ProofLib.SepWP.exists_left fun w72 =>
          ProofLib.SepWP.exists_left fun w80 => ?_
        refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
          (SepWP.seq
            (v6hr_lowStack_load_headers_1464_some_eq_to_3760_placed_budget A lim st s0 s1 out pbA
              noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 ptsCap ptsPtr
              (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
              (pbToProtoPolyDecoder decPb).polys w120
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
              ((if ptsCap = 0#64 then emp
                else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                  arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                    ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
               memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               statesFromPbJumpTablePlacedAt)
              hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
        intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
        refine SepWP.weaken_pre hP2
          (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_err_3760_uc_none_to_10316_placed_budget A lim st s0 s2 out
                w16 w24 w32 w40 w48 w56 w64 w72 w80 ptsCap ptsPtr
                (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                576#32 (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                (memRegion pbA optProtoInnerStateSize ∗
                 (if ptsCap = 0#64 then emp
                  else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTablePlacedAt)
                hsp0_align hpc2 hrun2 hregs2) ?_))
        intro s3 P3 hpc3 hrun3 ⟨hP3, _, hpres3, hx23_3⟩
        refine SepWP.weaken_pre hP3
          (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (SepWP.mono
              (Variant6fPlacedBudgetAux.v6hr_exit_err_10316_some_of_placedHooks (F := F) hA st
                s0 s3 out ptsPtr ptsCap 0#64
                (pbToProtoPolyDecoder decPb).pts
                v80 v128 v136 v144 d184 v192 d200 v208 v216 w120 ptsPtr
                (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 rfl hpres3 hx23_3) ?_))
        intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨⟨evs2, hevs2, v6hr_reassoc_exit_post hPf⟩, hsp_f, hcs_f, htr_f⟩
      | some ucVal =>
        rcases ucVal with ⟨epoch, authOpt, hdr⟩
        cases authOpt with
        | none =>
          rw [v6hr_from_pb_auth_none_dec_some F hdr epoch decPb heq_pts]
          refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_none_unpack' A.repAlloc pbA hdr epoch)) ?_
          simp only [sepExists_sepConj_left]
          refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
            ProofLib.SepWP.exists_left fun w40 => ProofLib.SepWP.exists_left fun w48 =>
            ProofLib.SepWP.exists_left fun w56 => ProofLib.SepWP.exists_left fun w64 =>
            ProofLib.SepWP.exists_left fun w72 => ?_
          refine v6hr_sepWP_pure_left fun ⟨_, hc0⟩ => ?_
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_some_eq_to_3760_placed_budget A lim st s0 s1 out pbA
                c0 p0 (BitVec.ofNat 64 hdr.length) noneCap w40 w48 w56 w64 w72 epoch
                ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecCapPtrDealloc A.repAlloc c0 p0 ∗
                 (if ptsCap = 0#64 then emp
                  else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTablePlacedAt)
                hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.seq
                (v6hr_lowStack_err_3760_auth_none_to_10316_of_placedHooks hA st s0 s2 out
                  c0 p0 (BitVec.ofNat 64 hdr.length) w40 w48 w56 w64 w72 epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  576#32 (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  (memRegion pbA optProtoInnerStateSize ∗
                   (if ptsCap = 0#64 then emp
                    else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                   memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hc0 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨evs1, hevs1, hP3, hx25_3, hpres3, hx23_3⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.mono
                (Variant6fPlacedBudgetAux.v6hr_exit_err_10316_some_of_placedHooks (F := F) hA
                  (M.stepEvents evs1 st) s0 s3 out ptsPtr ptsCap (s3.readReg64 .x25)
                  (pbToProtoPolyDecoder decPb).pts
                  (BitVec.ofNat 64 hdr.length) v128 v136 (if (c0 == 0#64) = true then v144 else p0)
                  d184 v192 d200 v208 v216 w120 ptsPtr
                  (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hx25_3 hpres3 hx23_3) ?_))
          intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
          refine ⟨⟨evs1 ++ evs2, hevs1.append hevs2, ?_⟩, hsp_f, hcs_f, htr_f⟩
          rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          exact v6hr_reassoc_exit_post hPf
        | some authPb =>
          refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_some_unpack' A.repAlloc pbA hdr authPb epoch)) ?_
          simp only [sepExists_sepConj_left]
          refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
            ProofLib.SepWP.exists_left fun c1 => ProofLib.SepWP.exists_left fun p1 =>
            ProofLib.SepWP.exists_left fun c2 => ProofLib.SepWP.exists_left fun p2 => ?_
          refine v6hr_sepWP_pure_left fun ⟨⟨hc0_le, hc0⟩, ⟨_, hc1⟩⟩ => ?_
          by_cases hlen : hdr.length = 64
          · have hfits_auth : FitsEvents M lim st
                (authKeyCloneEvents authPb.rootKey ++ authKeyCloneEvents authPb.macKey) :=
              fitsEvents_authClone_of_allocEnv_dec_some hfits heq_pts hlen
            have hlen_bv : BitVec.ofNat 64 hdr.length = 64#64 := by rw [hlen]
            rw [hlen_bv]
            refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
              (v6hr_sepWP_bind_lscl hcl1
                (v6hr_lowStack_load_headers_1464_some_eq_to_3760_placed_budget A lim st s0 s1 out pbA
                  c0 p0 64#64 c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                  c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                  (vecU8Payload A.repAlloc c0 p0 hdr ∗ vecU8Payload A.repAlloc c1 p1 authPb.rootKey ∗
                   vecU8Payload A.repAlloc c2 p2 authPb.macKey ∗
                   (if ptsCap = 0#64 then emp
                    else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                   statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                   statesFromPbJumpTablePlacedAt)
                  hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
            intro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, _, hregs2⟩
            refine SepWP.weaken_pre hP2
              (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                (v6hr_sepWP_bind_lscl hcl2
                  (Variant6fPlacedBudget.v6hr_step_3760_to_9936_of_placedHooks_sepWP hA st s0 s2
                    out c0 p0 c1 p1 c2 p2 epoch ptsCap ptsPtr
                    (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length) w120
                    576#32 (pbToProtoPolyDecoder decPb).polys
                    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                    authPb.rootKey authPb.macKey
                    (vecU8Payload A.repAlloc c0 p0 hdr ∗
                     (if ptsCap = 0#64 then emp
                      else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                        memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                          ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                     memRegion pbA optProtoInnerStateSize ∗ memRegion (s0.sp - 2160#64) 2064 ∗
                     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                    hfits_auth hsp0_align hc0 hc1 hpc2 hrun2 hregs2) ?_))
            intro s3 P3 hpc3 hrun3 hcl3 ⟨evs1, p1_new, p2_new, d184', hevs1, hP3, hsp3, hx11_3,
              hx12_3, hx19_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
            have hfits_dec : FitsEnv M lim (M.stepEvents evs1 st)
                (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)) :=
              fitsEnv_decAlloc_of_allocEnv_dec_some hfits heq_pts hlen hevs1
            rw [← heq_pts'] at hx11_3
            refine SepWP.weaken_pre hP3
              (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                (SepWP.mono
                  (Variant6fPlacedBudget.v6hr_step_9936_dec_some_to_exit_of_placedHooks_sepWP
                    (F := F) hA hdec (M.stepEvents evs1 st) s0 s3 hcl3
                    out c0 p0 p1_new p2_new epoch p2 ptsCap ptsPtr w120 d184'
                    authPb hdr decPb
                    (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                    hfits_dec hsp0_align hlen heq_pts hpts_le hpts_cap_lt hpts_ne hw120
                    hpc3 hrun3 hsp3 hx11_3 hx12_3 hx19_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3) ?_))
            intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
            have hcond : decPb.ptsNeeded = 576#32 ∧ hdr.length = 64 := ⟨heq_pts, hlen⟩
            refine ⟨⟨evs1 ++ evs2, ?_, ?_⟩, hsp_f, hcs_f, htr_f⟩
            · simp only [HeaderReceivedFromPbEnv, hcond, ↓reduceIte]
              exact ⟨evs1, evs2, rfl, hevs1, hevs2⟩
            · rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              exact v6hr_reassoc_exit_post hPf
          · rw [v6hr_from_pb_hdr_ne64_dec_some F hdr authPb epoch decPb heq_pts hlen]
            have hw24 := v6hr_ofNat_len_beq_64_false hlen hc0_le hc0
            refine SepWP.weaken_pre
              (sepConj_mono_left
                (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c0 p0 hdr)
                  (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c1 p1 authPb.rootKey)
                    (sepConj_mono_left (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c2 p2 authPb.macKey))))) ?_
            refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
              (SepWP.seq
                (v6hr_lowStack_load_headers_1464_some_eq_to_3760_placed_budget A lim st s0 s1 out pbA
                  c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                  c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                  (vecCapPtrDealloc A.repAlloc c0 p0 ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
                   vecCapPtrDealloc A.repAlloc c2 p2 ∗
                   (if ptsCap = 0#64 then emp
                    else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                   statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                   statesFromPbJumpTablePlacedAt)
                  hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
            intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
            refine SepWP.weaken_pre hP2
              (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                (SepWP.seq
                  (v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316_of_placedHooks hA st s0 s2 out
                    c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                    c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                    ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                    576#32 (pbToProtoPolyDecoder decPb).polys w120
                    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                    (memRegion pbA optProtoInnerStateSize ∗
                     (if ptsCap = 0#64 then emp
                      else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                        memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                          ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                     memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                     memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                    hsp0_align hc0 hc1 hw24 hpc2 hrun2 hregs2) ?_))
            intro s3 P3 hpc3 hrun3 ⟨evs1, hevs1, hP3, hx25_3, hpres3, hx23_3⟩
            refine SepWP.weaken_pre hP3
              (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                (SepWP.mono
                  (Variant6fPlacedBudgetAux.v6hr_exit_err_10316_some_of_placedHooks (F := F) hA
                    (M.stepEvents evs1 st) s0 s3 out ptsPtr ptsCap (s3.readReg64 .x25)
                    (pbToProtoPolyDecoder decPb).pts
                    (BitVec.ofNat 64 hdr.length) v128 v136 (if (c0 == 0#64) = true then v144 else p0)
                    d184 v192 d200 v208 v216 w120 ptsPtr
                    (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                    hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hx25_3 hpres3 hx23_3) ?_))
            intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
            have hcond : ¬ (decPb.ptsNeeded = 576#32 ∧ hdr.length = 64) := fun h => hlen h.2
            refine ⟨⟨evs1 ++ evs2, ?_, ?_⟩, hsp_f, hcs_f, htr_f⟩
            · simp only [HeaderReceivedFromPbEnv, hcond, ↓reduceIte]
              exact hevs1.append hevs2
            · rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              exact v6hr_reassoc_exit_post hPf
    · rw [v6hr_from_pb_ptsNeeded_ne F uc decPb heq_pts]
      have hd112 : ((pbToProtoPolyDecoder decPb).ptsNeeded == 576#32) = false :=
        beq_false_of_ne heq_pts
      cases uc with
      | none =>
        refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_none_unpack A.repAlloc pbA)) ?_
        simp only [sepExists_sepConj_left]
        refine ProofLib.SepWP.exists_left fun w16 => ProofLib.SepWP.exists_left fun w24 =>
          ProofLib.SepWP.exists_left fun w32 => ProofLib.SepWP.exists_left fun w40 =>
          ProofLib.SepWP.exists_left fun w48 => ProofLib.SepWP.exists_left fun w56 =>
          ProofLib.SepWP.exists_left fun w64 => ProofLib.SepWP.exists_left fun w72 =>
          ProofLib.SepWP.exists_left fun w80 => ?_
        refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
          (SepWP.seq
            (v6hr_lowStack_load_headers_1464_some_ne_to_1520_placed_budget A lim st s0 s1 out pbA
              noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 ptsCap ptsPtr
              (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
              (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
              v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
              ((if ptsCap = 0#64 then emp
                else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                  arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                    ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
               memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               statesFromPbJumpTablePlacedAt)
              hsp0_align hw88 hd112 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
        intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
        refine SepWP.weaken_pre hP2
          (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_err_1520_uc_none_to_10324_placed_budget A lim st s0 s2 out
                w16 w24 w32 w40 w48 w56 w64 w72 w80 ptsCap ptsPtr
                (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                (memRegion pbA optProtoInnerStateSize ∗
                 (if ptsCap = 0#64 then emp
                  else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTablePlacedAt)
                hsp0_align hpc2 hrun2 hregs2) ?_))
        intro s3 P3 hpc3 hrun3 ⟨hP3, _, hpres3, hx23_3⟩
        refine SepWP.weaken_pre hP3
          (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (SepWP.mono
              (Variant6fPlacedBudgetAux.v6hr_exit_err_10324_of_placedHooks (F := F) hA st
                s0 s3 out ptsPtr ptsCap
                (pbToProtoPolyDecoder decPb).pts
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 ptsPtr
                (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hpres3 hx23_3) ?_))
        intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨⟨evs2, hevs2, v6hr_reassoc_exit_post hPf⟩, hsp_f, hcs_f, htr_f⟩
      | some ucVal =>
        rcases ucVal with ⟨epoch, authOpt, hdr⟩
        cases authOpt with
        | none =>
          refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_none_unpack' A.repAlloc pbA hdr epoch)) ?_
          simp only [sepExists_sepConj_left]
          refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
            ProofLib.SepWP.exists_left fun w40 => ProofLib.SepWP.exists_left fun w48 =>
            ProofLib.SepWP.exists_left fun w56 => ProofLib.SepWP.exists_left fun w64 =>
            ProofLib.SepWP.exists_left fun w72 => ?_
          refine v6hr_sepWP_pure_left fun ⟨_, hc0⟩ => ?_
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_some_ne_to_1520_placed_budget A lim st s0 s1 out pbA
                c0 p0 (BitVec.ofNat 64 hdr.length) noneCap w40 w48 w56 w64 w72 epoch
                ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecCapPtrDealloc A.repAlloc c0 p0 ∗
                 (if ptsCap = 0#64 then emp
                  else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTablePlacedAt)
                hsp0_align hw88 hd112 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.seq
                (v6hr_lowStack_err_1520_auth_none_to_10324_of_placedHooks hA st s0 s2 out
                  c0 p0 (BitVec.ofNat 64 hdr.length) w40 w48 w56 w64 w72 epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  (memRegion pbA optProtoInnerStateSize ∗
                   (if ptsCap = 0#64 then emp
                    else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                   memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hc0 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨evs1, hevs1, hP3, hpres3, hx23_3⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.mono
                (Variant6fPlacedBudgetAux.v6hr_exit_err_10324_of_placedHooks (F := F) hA
                  (M.stepEvents evs1 st) s0 s3 out ptsPtr ptsCap
                  (pbToProtoPolyDecoder decPb).pts
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 ptsPtr
                  (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hpres3 hx23_3) ?_))
          intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
          refine ⟨⟨evs1 ++ evs2, hevs1.append hevs2, ?_⟩, hsp_f, hcs_f, htr_f⟩
          rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          exact v6hr_reassoc_exit_post hPf
        | some authPb =>
          refine SepWP.weaken_pre (sepConj_mono_left (v6hr_uc_auth_some_unpack' A.repAlloc pbA hdr authPb epoch)) ?_
          simp only [sepExists_sepConj_left]
          refine ProofLib.SepWP.exists_left fun c0 => ProofLib.SepWP.exists_left fun p0 =>
            ProofLib.SepWP.exists_left fun c1 => ProofLib.SepWP.exists_left fun p1 =>
            ProofLib.SepWP.exists_left fun c2 => ProofLib.SepWP.exists_left fun p2 => ?_
          refine v6hr_sepWP_pure_left fun ⟨⟨_, hc0⟩, ⟨_, hc1⟩⟩ => ?_
          refine SepWP.weaken_pre
            (sepConj_mono_left
              (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c0 p0 hdr)
                (sepConj_mono (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c1 p1 authPb.rootKey)
                  (sepConj_mono_left (v6hr_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc c2 p2 authPb.macKey))))) ?_
          refine SepWP.weaken_pre (Entails.of_eq (by unfold v6hr_headersAt; sep_ac_rfl))
            (SepWP.seq
              (v6hr_lowStack_load_headers_1464_some_ne_to_1520_placed_budget A lim st s0 s1 out pbA
                c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
                (vecCapPtrDealloc A.repAlloc c0 p0 ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
                 vecCapPtrDealloc A.repAlloc c2 p2 ∗
                 (if ptsCap = 0#64 then emp
                  else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                    arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                      ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                 memRegion (s0.sp - 2160#64) 2064 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                 statesFromPbJumpTablePlacedAt)
                hsp0_align hw88 hd112 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_)
          intro s2 P2 hpc2 hrun2 ⟨hP2, _, hregs2⟩
          refine SepWP.weaken_pre hP2
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.seq
                (v6hr_lowStack_err_1520_auth_some_to_10324_of_placedHooks hA st s0 s2 out
                  c0 p0 (BitVec.ofNat 64 hdr.length) c1 p1 (BitVec.ofNat 64 authPb.rootKey.length)
                  c2 p2 (BitVec.ofNat 64 authPb.macKey.length) epoch
                  ptsCap ptsPtr (BitVec.ofNat 64 (pbToProtoPolyDecoder decPb).pts.length)
                  (pbToProtoPolyDecoder decPb).ptsNeeded (pbToProtoPolyDecoder decPb).polys w120
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224
                  (memRegion pbA optProtoInnerStateSize ∗
                   (if ptsCap = 0#64 then emp
                    else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
                      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (pbToProtoPolyDecoder decPb).pts ∗
                      memRegion (ptsPtr + BitVec.ofNat 64 ((pbToProtoPolyDecoder decPb).pts.length * 24))
                        ((ptsCap.toNat - (pbToProtoPolyDecoder decPb).pts.length) * 24)) ∗
                   memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
                   memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hc0 hc1 hpc2 hrun2 hregs2) ?_))
          intro s3 P3 hpc3 hrun3 ⟨evs1, hevs1, hP3, hpres3, hx23_3⟩
          refine SepWP.weaken_pre hP3
            (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (SepWP.mono
                (Variant6fPlacedBudgetAux.v6hr_exit_err_10324_of_placedHooks (F := F) hA
                  (M.stepEvents evs1 st) s0 s3 out ptsPtr ptsCap
                  (pbToProtoPolyDecoder decPb).pts
                  v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 ptsPtr
                  (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
                  hsp0_align hpts_le hpts_cap_lt hpc3 hrun3 hpres3 hx23_3) ?_))
          intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
          have hcond : ¬ (decPb.ptsNeeded = 576#32 ∧ hdr.length = 64) := fun h => heq_pts h.1
          refine ⟨⟨evs1 ++ evs2, ?_, ?_⟩, hsp_f, hcs_f, htr_f⟩
          · simp only [HeaderReceivedFromPbEnv, hcond, ↓reduceIte]
            exact hevs1.append hevs2
          · rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            exact v6hr_reassoc_exit_post hPf

theorem states_from_pb_headerReceived_1464_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s : V1State.Chunked.HeaderReceived)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (hfits : FitsEnv M lim st (HeaderReceivedFromPbAllocEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
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
        optProtoInnerStateAt A.repAlloc pbA (some (.headerReceived s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          HeaderReceivedFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerReceived s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  states_from_pb_headerReceived_1464_of_placedHooks_sepWP (F := F) hA.toPlacedBudget hdec
    st s s0 s1 hcl1 out pbA hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

theorem states_from_pb_headerReceived_1464_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s : V1State.Chunked.HeaderReceived)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (hfits : FitsEnv M lim st (HeaderReceivedFromPbAllocEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
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
        optProtoInnerStateAt A.repAlloc pbA (some (.headerReceived s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          HeaderReceivedFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerReceived s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      Qp :=
  SepWPp.of_sepWP_ret
    (states_from_pb_headerReceived_1464_of_placedHooks_sepWP (F := F) hA hdec
      st s s0 s1 hcl1 out pbA hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1)

theorem states_from_pb_headerReceived_1464_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s : V1State.Chunked.HeaderReceived)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64) (R : SepProp)
    (hfits : FitsEnv M lim st (HeaderReceivedFromPbAllocEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
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
        optProtoInnerStateAt A.repAlloc pbA (some (.headerReceived s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          HeaderReceivedFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerReceived s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  states_from_pb_headerReceived_1464_of_placedHooks (F := F) hA.toPlacedBudget hdec
    st s s0 s1 hcl1 out pbA hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

/-! ## 2. Complete `subroutine_ok` Theorems for Variant 6 (`HeaderReceived`) -/

/-- Envelope-parametric `subroutine_ok` for Variant 6 (`InnerState.headerReceived`) on `lsProg_333`
    with `withLsCodeLoaded` under any `Env` containing `HeaderReceivedFromPbEnv s` when `FitsEnv Env`. -/
theorem states_from_pb_headerReceived_ok_ext_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderReceived)
    (halloc_fit : ∀ st : M.σ, FitsEnv M lim st Env →
      FitsEnv M lim st (HeaderReceivedFromPbAllocEnv s))
    (hsub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → HeaderReceivedFromPbEnv s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.headerReceived s) } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  dsimp only [DefsBudget.statesFromPbVariantPlacedSpecOfEnv] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hx0, _hpts, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.headerReceived s)) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  refine DefsBudget.sepWPp_of_states_exit_cl_placed st s0 s0 out pbA
    { innerState := some (.headerReceived s) } Env _ R ?_
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some (.headerReceived s)) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine v6hr_sepWP_bind_lscl hcl0 hpro ?_
  intro s1 P1 hpc1 hrun1 hcl1 ⟨hP1, hsp1, _, hx8_1, hx0_1, htr1, _⟩
  let Tail : SepProp :=
    optProtoUnchunkedHeaderReceivedAt A.repAlloc (pbA + 8#64) s.uc ∗
    optProtoPolynomialDecoderAt A.repAlloc (pbA + 88#64) (s.receivingEk.map pbToProtoPolyDecoder) ∗
    memRegion (pbA + 128#64) 96
  have hinner : optProtoInnerStateAt A.repAlloc pbA (some (.headerReceived s)) =
      (pbA ↦₆₄ 0x8000000000000006#64) ∗ Tail := by
    rw [v6hr_optProtoInnerStateAt_headerReceived A.repAlloc pbA s]
  have hP1' : P1 ⊢
      (pbA ↦₆₄ 0x8000000000000006#64) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail) ∗
      A.pool lim st s1 := by
    refine Entails.trans hP1 ?_
    rw [hinner]
    exact Entails.of_eq (by sep_ac_rfl)
  have hdisp := Variant1bPlacedBudgetAux.states_from_pb_dispatch_tagged_placed_budget A lim st
    (ext := ext) s0 s1 out pbA 0x8000000000000006#64 1464#64
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     Tail)
    TaggedVariantDispatch.headerReceived hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine SepWP.weaken_pre hP1' (v6hr_sepWP_bind_lscl hcl1 hdisp ?_)
  intro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2, _⟩
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hpre_join : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some (.headerReceived s)) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s2 := by
    refine Entails.trans hP2 ?_
    rw [hinner]
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ 0x8000000000000006#64) ∗ Tail) ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by sep_ac_rfl))
  have hbody := states_from_pb_headerReceived_1464_of_placedHooks_sepWP (F := F) hA hdec
    st s s0 s2 hcl2 out pbA (halloc_fit st hfits)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2' hx27_2 htr2
  refine SepWP.weaken_pre hpre_join (SepWP.mono hbody ?_)
  intro sf Pf _ _ ⟨⟨evs, hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩
  exact ⟨⟨evs, hsub st hfits hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩

/-- `subroutine_ok` for Variant 6 (`InnerState.headerReceived`) under its tight envelope
    `HeaderReceivedFromPbEnv s`. -/
theorem states_from_pb_headerReceived_ok_ext_placed_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.headerReceived s) } (HeaderReceivedFromPbEnv s))) :=
  states_from_pb_headerReceived_ok_ext_placed_of_env hA hdec s
    (fun _ h => fitsEnv_alloc_of_headerReceivedEnv h)
    (fun _ _ _ h => h)

/-- `subroutine_ok` for Variant 6 (`InnerState.headerReceived`) under the uniform
    `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`). -/
theorem states_from_pb_headerReceived_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.headerReceived s) })) :=
  states_from_pb_headerReceived_ok_ext_placed_of_env hA hdec s
    (fun _ h => fitsEnv_alloc_of_statesFromPbEnv s h)
    (fun _ _ hfits hevs => headerReceivedFromPbEnv_sub_statesFromPbEnv s hfits hevs)

theorem states_from_pb_headerReceived_ok_ext_placed_tight_fromPbHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.headerReceived s) } (HeaderReceivedFromPbEnv s))) :=
  states_from_pb_headerReceived_ok_ext_placed_tight hA.toPlacedBudget hdec s

theorem states_from_pb_headerReceived_ok_ext_placed_fromPbHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.headerReceived s) })) :=
  states_from_pb_headerReceived_ok_ext_placed hA.toPlacedBudget hdec s

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudget
