/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Mid-Stage Continuations (`+1984` and `+10836`) for `Variant8PlacedBudget`

Proves the budget-threaded Variant 8 (`InnerState.ekReceivedCt1Sampled`, Block `333`) continuations
from `+10836` (`+10836 -> s0.x30`) and `+1984` (`+1984 -> s0.x30`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap

open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsProg_333 lsmpl)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder ProtoAuthenticator pbToProtoPolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved optEncoderPtsBound resultChunkedStatesAt spqrErrorByte statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderHeap_extract_w0 v1_optProtoPolyEncoderWordsAt v8_5vecs_entails_dealloc v8_bs384_eq_encCells v8_bv_add_add_lit v8_encCellsAt v8_fsp_1576_split_728 v8_fsp_240_split_56 v8_fsp_296_to_1520_collapse v8_fsp_896_split_1984 v8_fsp_collapse_2304 v8_fsp_collapse_240_to_1888 v8_pb_uc_enc_entails_224 v8_polyEncoderAt_relocate v8_resultPolyEncoder_err_entails_tag_392 v8_states_from_pb_ok_eq v8_states_from_pb_sendingCt1_err_any_eq v8_states_from_pb_sendingCt1_none_eq v8_tag2_392_entails_400 v8_ucWordsAt v8_ucWordsAt_896_eq vecU8Payload_extract_len_lt63)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudgetAux (v8_check_sendingCt1_10836_none_placed_budget)

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux2

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget encoder_from_pb_ok_of_alloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudget
  (v8_drop_uc_and_sendingCt1_2100_placed v8_drop_uc_auth_none_10544_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudgetAux
  (v8_err_4240_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlacedBudget
  (v8_copy_pb_to_stack_1764_placed_budget v8_ekReceivedCt1Sampled_uc_none_placed
   v8_step_1872_to_2100_len_err_x26_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudget
  (v8_check_auth_1972_none_placed_budget v8_check_auth_1972_some_placed_budget
   v8_check_sendingCt1_10836_none_placed_budget v8_cleanup_5vecs_11120_placed
   v8_clone_macKey_10680_to_10740_placed v8_clone_rootKey_1984_to_10680_placed
   v8_dealloc_old_auth_10740_to_10836_placed v8_step_1872_to_1972_len_ok_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlacedBudget
  (v8_check_enc_res_10904_err_placed_budget v8_check_enc_res_10904_ok_placed_budget
   v8_cleanup_5vecs_10916_placed v8_copy_enc_10836_to_10900_placed_budget)

open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux
  (EkReceivedCt1SampledFromPbAllocEnv EkReceivedCt1SampledFromPbEnv
   EkReceivedCt1SampledTailEnv EkReceivedCt1SampledTailFits
   ekReceivedCt1SampledFromPbEnv_of_tailEnv ekReceivedCt1SampledUcLenOk
   encoderFromPbEnv_append_freeOnly fitsEvents_auth_of_ekReceivedCt1SampledAllocEnv
   seq_clean_lscl_st tailFits_of_ekReceivedCt1SampledAllocEnv
   v8_call_encoder_from_pb_10900_to_10904_placed v8_stage_11264_to_ret_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. Budget-Threaded Tail from `+10836` (`+10836 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
theorem v8_ekReceivedCt1Sampled_from_10836_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hE : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator)
    (sendingCt1 : Option PolynomialEncoder) (hpts : optEncoderPtsBound sendingCt1)
    (hfits : EkReceivedCt1SampledTailFits M lim st sendingCt1)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 pa1 l1 pa2 l2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hlen : ekReceivedCt1SampledUcLenOk u = true)
    (hes : u.es.length = 2080) (hek : u.ek.length = 1152) (hct1 : u.ct1.length = 960)
    (hauth : u.auth = some auth)
    (hl1 : l1 = BitVec.ofNat 64 auth.rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 auth.macKey.length)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 10836#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64) (hx9 : s.readReg64 .x9 = u64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u64)
    (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
        memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
        vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
          u80 u88 u96 u104 u112 u120 u.epoch ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EkReceivedCt1SampledTailEnv sendingCt1 evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
    u80 u88 u96 u104 u112 u120 u.epoch w0 w8 w16 w24 w32 w40 w48
  cases sendingCt1 with
  | none =>
    dsimp only [EkReceivedCt1SampledTailEnv]
    rw [v8_states_from_pb_sendingCt1_none_eq u auth hlen hauth]
    simp only [Option.map_none, v1_optProtoPolyEncoderHeap]
    rw [show stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
        memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        ⌜w0 = noneCap⌝ ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
        vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
          u80 u88 u96 u104 u112 u120 u.epoch ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s =
      ⌜w0 = noneCap⌝ ∗
      ((vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
        vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1) ∗
       ((pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
          u80 u88 u96 u104 u112 u120 u.epoch ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32) ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       A.pool lim st s ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
       memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl]
    apply ProofLib.SepWP.pure_elim; intro hw0
    refine SepWP.weaken_pre
      (sepConj_mono
        (v8_5vecs_entails_dealloc A.repAlloc l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64
          auth.rootKey auth.macKey u.es u.ek u.ct1)
        (sepConj_mono_left hpb_col)) ?_
    subst hw0
    have hw_eq :
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 =
        (((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 8#64) ↦₆₄ w8) ∗
         (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗
         (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗
         (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) := rfl
    have hstep1 := v8_check_sendingCt1_10836_none_placed_budget A lim st (ext := ext)
      s0 s out u64 l1 l2 u8
      (((((s0.sp - 2400#64) + 1520#64 + 8#64) ↦₆₄ w8) ∗
        (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗
        (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗
        (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗
        (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
        (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
       (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
       vecCapPtrDealloc A.repAlloc l1 pa1 ∗ vecCapPtrDealloc A.repAlloc l2 pa2 ∗
       vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
       vecCapPtrDealloc A.repAlloc u56 u64 ∗
       (memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
        memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))
      hsp0_align hpc hrun hsp hx9 hx19 hx21 hx22 hx26 hx28 htr
    refine SepWP.weaken_pre (by rw [hw_eq]; exact Entails.of_eq (by sep_ac_rfl)) (SepWP.seq hstep1 ?_)
    intro s2 P2 hpc2 hrun2 ⟨hP2, _hvm2, hsp2, hx9_2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩
    have hstep2 := Variant8cPlacedBudget.v8_cleanup_5vecs_11120_placed hA st s0 s2 out l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64
      (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx21_2 hx22_2 hx26_2 hx28_2 htr2
    refine SepWP.weaken_pre (Entails.trans hP2 (by rw [hw_eq]; exact Entails.of_eq (by sep_ac_rfl)))
      (SepWP.seq hstep2 ?_)
    intro s3 P3 hpc3 hrun3 ⟨evs, hfree, hP3, hsp3, hx19_3, hx20_3, htr3⟩
    have hcol1 := v8_fsp_collapse_240_to_1888 (s0.sp - 2400#64) noneCap w8 w16 w24 w32 w40 w48
    have hcol2 := v8_fsp_collapse_2304 (s0.sp - 2400#64) u56 u.epoch u16 pa2 pa1 u40 u32
    have hP3' : P3 ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim (M.stepEvents evs st) s3 ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
      refine Entails.trans hP3 ?_
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 ∗
          memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗
        (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
          memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
          memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗ A.pool lim (M.stepEvents evs st) s3 ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hcol1) ?_
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
          memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
          memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗ A.pool lim (M.stepEvents evs st) s3 ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hcol2) (Entails.of_eq (by sep_ac_rfl))
    have hx20_byte : (s3.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx20_3]; rfl
    refine SepWP.weaken_pre hP3'
      (SepWP.mono (v8_err_4240_placed_budget A lim (M.stepEvents evs st) (F := F) s0 s3 out
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_byte htr3) ?_)
    intro sf Pf _ _ ⟨hPf, _hvm_f, hsp_f, hcs_f, htr_f⟩
    exact ⟨evs, hfree, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some pbEnc =>
    dsimp only [EkReceivedCt1SampledTailFits, EkReceivedCt1SampledTailEnv, optEncoderPtsBound]
      at hfits hpts ⊢
    simp only [Option.map_some]
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
         memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
         memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
         v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
         vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
         vecU8Payload A.repAlloc u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
         v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
           u80 u88 u96 u104 u112 u120 u.epoch ∗
         v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
        by sep_ac_rfl))
        (sepConj_mono
          (v1_optProtoPolyEncoderHeap_extract_w0 A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
            w0 w8 w16 w24 w32 w40 w48)
          (sepConj_mono_left (v8_fsp_240_split_56 (s0.sp - 2400#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro z288
    apply ProofLib.SepWP.exists_left; intro z280
    apply ProofLib.SepWP.exists_left; intro z272
    apply ProofLib.SepWP.exists_left; intro z264
    apply ProofLib.SepWP.exists_left; intro z256
    apply ProofLib.SepWP.exists_left; intro z248
    apply ProofLib.SepWP.exists_left; intro z240
    apply ProofLib.SepWP.pure_elim; intro hw0_lt
    have hw_fsp :
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 =
        (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗
         (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗
         (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) := by
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      have h1528 : (s0.sp - 2400#64 + 1520#64) + 8#64 = s0.sp - 2400#64 + 1528#64 := by bv_omega
      rw [h1528]
    have hw_pbA :
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 =
        ((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
        ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗
        ((pbA + 184#64) ↦₆₄ w48) := by
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      simp only [v8_bv_add_add_lit, BitVec.ofNat_eq_ofNat]
    let Rest_copy : SepProp :=
      (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗
      (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗
      (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗
      (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
      (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48) ∗
      ((pbA + 136#64) ↦₆₄ w0) ∗
      v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
        w0 w8 w16 w24 w32 w40 w48 ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
      memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
      memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
      memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗
      memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
      vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
      vecU8Payload A.repAlloc u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
      v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
        u80 u88 u96 u104 u112 u120 u.epoch ∗
      memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt
    have hcopy := v8_copy_enc_10836_to_10900_placed_budget A lim st (ext := ext)
      s0 s out pbA u64 l1 u8 l2 w0 w8 w16 w24 w32 w40 w48
      z240 z248 z256 z264 z272 z280 z288 Rest_copy
      hw0_lt hsp0_align hpc hrun hsp hx19 hx21 hx22 hx23 hx26 hx27 hx28 htr
    refine SepWP.weaken_pre (by dsimp only [Rest_copy]; rw [hw_fsp, hw_pbA]; exact Entails.of_eq (by sep_ac_rfl))
      (seq_clean_lscl_st hcl
        (SepWP.mono hcopy fun sm Pm _ _ ⟨hPm, _hvm_m, hregs_m⟩ => ⟨hPm, hregs_m⟩) ?_)
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx23_2, hx26_2, hx27_2, hx28_2, htr2⟩
    let Frame_call : SepProp :=
      memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
      memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
      memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
      memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
      v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
      vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
      vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
      memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt
    have hP2_col :
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
          ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗
          ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) ∗
          Rest_copy ∗ A.pool lim st s2 ⊢
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
            w0 w8 w16 w24 w32 w40 w48 ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st s2 ∗ Frame_call := by
      dsimp only [Rest_copy, Frame_call]
      refine Entails.trans (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x8000000000000008#64) ∗
          v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
            u80 u88 u96 u104 u112 u120 u.epoch ∗
          (((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
            ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗
            ((pbA + 184#64) ↦₆₄ w48)) ∗
          memRegion (pbA + 192#64) 32) ∗
        ((((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
          ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗
            (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗
            (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗
            (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
            (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48))) ∗
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
            w0 w8 w16 w24 w32 w40 w48 ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st s2 ∗
          memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
          memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
          memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
          vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
          vecU8Payload A.repAlloc u56 u64 u.ct1 ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
      rw [← hw_pbA, ← hw_fsp]
      exact Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (by sep_ac_rfl))
    have hcall := v8_call_encoder_from_pb_10900_to_10904_placed hE st s0 s2 hcl2
      (s0.sp - 2400#64) out u64 l1 u8 pbA l2 pbEnc w0 w8 w16 w24 w32 w40 w48 Frame_call
      hfits hpts hsp0_align rfl hpc2 hrun2 hsp2
      hx0_2 hx1_2 hx19_2 hx21_2 hx22_2 hx23_2 hx26_2 hx27_2 hx28_2 htr2
    refine SepWP.weaken_pre hP2_col (SepWP.seq hcall ?_)
    intro s3 P3 hpc3 hrun3
      ⟨evs_enc, henc_env, hP3, hsp3, hx19_3, hx21_3, hx22_3, hx23_3, hx26_3, hx27_3, hx28_3, htr3⟩
    refine SepWP.weaken_pre hP3 ?_
    dsimp only [Frame_call]
    have hcol_1648 :
        memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion ((s0.sp - 2400#64) + 1576#64) 312 ⊢
        memRegion ((s0.sp - 2400#64) + 240#64) 1648 :=
      v8_fsp_collapse_240_to_1888 (s0.sp - 2400#64) w0 w8 w16 w24 w32 w40 w48
    cases henc : fromPbResult (pbToProtoPolyEncoder pbEnc) with
    | error err =>
      rw [v8_states_from_pb_sendingCt1_err_any_eq u auth pbEnc err hlen hauth henc]
      have herr_tag := v8_resultPolyEncoder_err_entails_tag_392 A.repAlloc (s0.sp - 2400#64) err
      let Rest_err : SepProp :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
        vecCapPtrDealloc A.repAlloc l1 pa1 ∗ vecCapPtrDealloc A.repAlloc l2 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        (memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
         memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      have hpre_err :
          resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            A.pool lim (M.stepEvents evs_enc st) s3 ∗
            (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
             memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
             memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
             (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
             memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
             memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
             v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
             vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
             vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
             memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ⊢
          (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest_err ∗
            A.pool lim (M.stepEvents evs_enc st) s3 := by
        dsimp only [Rest_err]
        refine Entails.trans (Entails.of_eq (show _ =
          resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
          (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
            v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗
          (vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
            vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
            vecU8Payload A.repAlloc u56 u64 u.ct1) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim (M.stepEvents evs_enc st) s3 ∗
            memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
            memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
            memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
            memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono herr_tag
            (sepConj_mono hcol_1648
              (sepConj_mono_left
                (v8_5vecs_entails_dealloc A.repAlloc l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64
                  auth.rootKey auth.macKey u.es u.ek u.ct1))))
          (Entails.of_eq (by sep_ac_rfl))
      refine SepWP.weaken_pre hpre_err
        (SepWP.seq
          (v8_check_enc_res_10904_err_placed_budget A lim (M.stepEvents evs_enc st) s0 s3 Rest_err
            hsp0_align hpc3 hrun3 hsp3 htr3) ?_)
      intro s4 P4 hpc4 hrun4 ⟨hP4, _hvm4, hsp4, hx19_4, hx21_4, hx22_4, hx26_4, hx28_4, htr4⟩
      rw [hx19_3] at hx19_4; rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4
      rw [hx26_3] at hx26_4; rw [hx28_3] at hx28_4
      have hclean := Variant8dPlacedBudget.v8_cleanup_5vecs_10916_placed hA (M.stepEvents evs_enc st)
        s0 s4 out l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64
        ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
         memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
         memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx22_4 hx26_4 hx28_4 htr4
      refine SepWP.weaken_pre (Entails.trans hP4 (by dsimp only [Rest_err]; exact Entails.of_eq (by sep_ac_rfl)))
        (SepWP.seq hclean ?_)
      intro s5 P5 hpc5 hrun5 ⟨evs_free, hfree, hP5, hsp5, hx19_5, hx20_5, htr5⟩
      have hcol2 := v8_fsp_collapse_2304 (s0.sp - 2400#64) u56 u.epoch u16 pa2 pa1 u40 u32
      have hP5' : P5 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs_free (M.stepEvents evs_enc st)) s5 ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
        refine Entails.trans hP5 ?_
        refine Entails.trans (Entails.of_eq (show _ =
          ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392) ∗
          (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
            memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
            memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
            memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            A.pool lim (M.stepEvents evs_free (M.stepEvents evs_enc st)) s5 ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (v8_tag2_392_entails_400 (s0.sp - 2400#64))) ?_
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
            memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
            memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
            memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
            memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            A.pool lim (M.stepEvents evs_free (M.stepEvents evs_enc st)) s5 ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hcol2) (Entails.of_eq (by sep_ac_rfl))
      have hx20_byte : (s5.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
        rw [hx20_5]; rfl
      refine SepWP.weaken_pre hP5'
        (SepWP.mono
          (v8_err_4240_placed_budget A lim (M.stepEvents evs_free (M.stepEvents evs_enc st))
            (F := F) s0 s5 out (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
            hsp0_align hpc5 hrun5 hsp5 hx19_5 hx20_byte htr5) ?_)
      intro sf Pf _ _ ⟨hPf, _hvm_f, hsp_f, hcs_f, htr_f⟩
      rw [← M.stepEvents_append evs_enc evs_free st] at hPf
      exact ⟨evs_enc ++ evs_free, encoderFromPbEnv_append_freeOnly henc_env hfree,
        Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | ok enc =>
      rw [v8_states_from_pb_ok_eq u auth pbEnc enc hlen hauth henc]
      dsimp only [resultPolyEncoderFromPbAt]
      have hrel := v8_polyEncoderAt_relocate A.repAlloc ((s0.sp - 2400#64) + 1888#64) (out + 8#64) enc
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) enc ∗
          (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
            v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
            memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
            memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
            memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
            vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
            vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs_enc st) s3) by sep_ac_rfl))
          (sepConj_mono hrel (sepConj_mono_left hcol_1648))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro tag
      apply ProofLib.SepWP.exists_left; intro bs
      apply ProofLib.SepWP.exists_left; intro hi32
      apply ProofLib.SepWP.exists_left; intro P_heap
      apply ProofLib.SepWP.pure_elim; rintro ⟨htag, hreloc⟩
      have hbs_cells := v8_bs384_eq_encCells bs.val bs.property ((s0.sp - 2400#64) + 1888#64)
      have ha2280 : ((s0.sp - 2400#64) + 1888#64) + 392#64 = (s0.sp - 2400#64) + 2280#64 := by bv_omega
      rw [hbs_cells, ha2280]
      let Rest_ok : SepProp :=
        v8_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
        (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ∗
        memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
        memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc l1 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc l2 pa2 auth.macKey ∗
        vecU8Payload A.repAlloc u8 u16 u.es ∗ vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt
      refine SepWP.weaken_pre (by dsimp only [Rest_ok]; exact Entails.of_eq (by sep_ac_rfl))
        (SepWP.seq
          (v8_check_enc_res_10904_ok_placed_budget A lim (M.stepEvents evs_enc st)
            s0 s3 tag htag Rest_ok hsp0_align hpc3 hrun3 hsp3 htr3) ?_)
      intro s4 P4 hpc4 hrun4 ⟨hP4, _hvm4, hsp4, hx15_4, hx19_4, hx21_4, hx22_4, hx23_4, hx26_4, hx28_4, htr4⟩
      rw [hx19_3] at hx19_4; rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4
      rw [hx23_3] at hx23_4; rw [hx26_3] at hx26_4; rw [hx28_3] at hx28_4
      have hstage := v8_stage_11264_to_ret_placed (F := F) hA (M.stepEvents evs_enc st)
        s0 s4 (s0.sp - 2400#64) out tag u.epoch pa1 l1 pa2 l2 u8 u16 u32 u40 u56 u64
        bs.val bs.property hi32 enc P_heap hreloc
        auth.rootKey auth.macKey u.es u.ek u.ct1 hl1 hl2 hes hek hct1
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align rfl hpc4 hrun4 hsp4 hx15_4 hx19_4 hx21_4 hx22_4 hx23_4 hx26_4 hx28_4 htr4
      refine SepWP.weaken_pre (Entails.trans hP4 (by dsimp only [Rest_ok]; exact Entails.of_eq (by sep_ac_rfl)))
        (SepWP.mono hstage ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨evs_enc, henc_env, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-! ## 2. Budget-Threaded Body from `+1984` (`+1984 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
theorem v8_ekReceivedCt1Sampled_from_1984_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hE : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator)
    (sendingCt1 : Option PolynomialEncoder) (hpts : optEncoderPtsBound sendingCt1)
    (hfits : FitsEnv M lim st
      (EkReceivedCt1SampledFromPbAllocEnv { uc := some u, sendingCt1 := sendingCt1 }))
    (u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hlen : ekReceivedCt1SampledUcLenOk u = true)
    (hes : u.es.length = 2080) (hek : u.ek.length = 1152) (hct1 : u.ct1.length = 960)
    (hauth : u.auth = some auth)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1984#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64) (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = u80) (hx26 : s.readReg64 .x26 = u8)
    (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt ((s0.sp - 2400#64) + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
          u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
          u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
        memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc u80 u88 auth.rootKey ∗
        vecU8Payload A.repAlloc u104 u112 auth.macKey ∗
        vecU8Payload A.repAlloc u8 u16 u.es ∗
        vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
          u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
          u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EkReceivedCt1SampledFromPbEnv { uc := some u, sendingCt1 := sendingCt1 } evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfits_auth : FitsEvents M lim st (authFromPbEvents auth) :=
    fitsEvents_auth_of_ekReceivedCt1SampledAllocEnv hlen hauth hfits
  rw [authFromPbEvents, fitsEvents_append] at hfits_auth
  obtain ⟨hfits_r, hfits_m⟩ := hfits_auth
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A.repAlloc u80 u88 auth.rootKey ∗
      memRegion (s0.sp - 2400#64) 896 ∗
      memRegion ((s0.sp - 2400#64) + 1576#64) 728 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       v8_ucWordsAt ((s0.sp - 2400#64) + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
         u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
         u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
       memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecU8Payload A.repAlloc u104 u112 auth.macKey ∗
       vecU8Payload A.repAlloc u8 u16 u.es ∗
       vecU8Payload A.repAlloc u32 u40 u.ek ∗
       vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
       (pbA ↦₆₄ 0x8000000000000008#64) ∗
       v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
         u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
         u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      by sep_ac_rfl))
      (sepConj_mono (vecU8Payload_extract_len_lt63 A.repAlloc u80 u88 auth.rootKey)
        (sepConj_mono (v8_fsp_896_split_1984 (s0.sp - 2400#64))
          (sepConj_mono_left (v8_fsp_1576_split_728 (s0.sp - 2400#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v224
  apply ProofLib.SepWP.exists_left; intro v216
  apply ProofLib.SepWP.exists_left; intro v200
  apply ProofLib.SepWP.exists_left; intro v184
  apply ProofLib.SepWP.exists_left; intro v176
  apply ProofLib.SepWP.exists_left; intro v120
  apply ProofLib.SepWP.exists_left; intro v64
  apply ProofLib.SepWP.pure_elim; intro hr_lt63
  have hl1_lt : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hr_lt63
  let Rest1 : SepProp :=
    ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
    ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
    ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
    ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗
    ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
    ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
    ((s0.sp - 2400#64 + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
    memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
    memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
    memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
    (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
    memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗
    (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
    memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗
    memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
    v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
      w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
    memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
    memRegion out chunkedStatesSize ∗
    vecU8Payload A.repAlloc u104 u112 auth.macKey ∗
    vecU8Payload A.repAlloc u8 u16 u.es ∗
    vecU8Payload A.repAlloc u32 u40 u.ek ∗
    vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
    (pbA ↦₆₄ 0x8000000000000008#64) ∗
    v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
      u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
      u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt
  have hclone1 := Variant8cPlacedBudget.v8_clone_rootKey_1984_to_10680_placed hA st s0 s out pbA u8 u80 u88 u.epoch
    v120 v200 auth.rootKey Rest1 hfits_r hsp0_align hpc hrun hsp hx19 hx23 hx26 hx27 htr
  refine SepWP.weaken_pre (by rw [v8_ucWordsAt_896_eq]; dsimp only [Rest1]; exact Entails.of_eq (by sep_ac_rfl))
    (SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl (SepWP.mono hclone1 ?_))
  intro s2 P2 hpc2 hrun2 ⟨pa1, hP2, hsp2, hx19_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩ hcl2
  let st1 := M.stepEvents (authKeyCloneEvents auth.rootKey) st
  let Rest2 : SepProp :=
    (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
    (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
    (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u.epoch) ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
    vecCapPtrDealloc A.repAlloc u80 u88 ∗
    ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
    ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
    ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
    ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗
    ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
    ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
    memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
    memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
    memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
    memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗
    (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
    memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
    memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
    v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
      w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
    memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
    memRegion out chunkedStatesSize ∗
    vecU8Payload A.repAlloc u8 u16 u.es ∗
    vecU8Payload A.repAlloc u32 u40 u.ek ∗
    vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
    (pbA ↦₆₄ 0x8000000000000008#64) ∗
    v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
      u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
      u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt
  have hclone2 := Variant8cPlacedBudget.v8_clone_macKey_10680_to_10740_placed hA st1 s0 s2 out pbA u8
    (BitVec.ofNat 64 auth.rootKey.length) u80 u88 u104 u112 v184 auth.macKey Rest2
    hfits_m hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 htr2
  refine SepWP.weaken_pre (Entails.trans hP2 (by dsimp only [Rest1, Rest2, st1]; exact Entails.of_eq (by sep_ac_rfl)))
    (SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl2 (SepWP.mono hclone2 ?_))
  intro s3 P3 hpc3 hrun3 ⟨pa2, hP3, hsp3, hx19_3, hx20_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, htr3⟩ hcl3
  let st2 := M.stepEvents (authFromPbEvents auth) st
  have hst2_eq : M.stepEvents (authKeyCloneEvents auth.macKey) st1 = st2 := by
    dsimp only [st1, st2, authFromPbEvents]
    rw [M.stepEvents_append]
  let Rest3 : SepProp :=
    (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
    (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
    (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
    (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
    (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u.epoch) ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
    ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗
    ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗
    ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
    memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
    memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
    memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗
    memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
    memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
    v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
      w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
    memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
    memRegion out chunkedStatesSize ∗
    vecU8Payload A.repAlloc u8 u16 u.es ∗
    vecU8Payload A.repAlloc u32 u40 u.ek ∗
    vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
    (pbA ↦₆₄ 0x8000000000000008#64) ∗
    v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
      u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
      u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt
  have hdealloc := Variant8cPlacedBudget.v8_dealloc_old_auth_10740_to_10836_placed hA st2 s0 s3 out pbA u8 u16 u32 u40
    u56 u64 u80 u88 u104 u112
    (BitVec.ofNat 64 auth.rootKey.length) (BitVec.ofNat 64 auth.macKey.length)
    v64 v176 v216 v224 Rest3
    hl1_lt hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx26_3 hx27_3 hx28_3 htr3
  refine SepWP.weaken_pre
    (Entails.trans hP3 (by rw [hst2_eq]; dsimp only [Rest2, Rest3]; exact Entails.of_eq (by sep_ac_rfl)))
    (SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl3 (SepWP.mono hdealloc ?_))
  intro s4 P4 hpc4 hrun4 ⟨evs_af, hfree_af, hP4, hsp4, hx9_4, hx19_4, hx21_4, hx22_4, hx23_4, hx26_4, hx27_4, hx28_4, htr4⟩ hcl4
  have hst3_eq : M.stepEvents evs_af st2 = M.stepEvents (authFromPbEvents auth ++ evs_af) st := by
    dsimp only [st2]; rw [M.stepEvents_append]
  have hfits_tail : EkReceivedCt1SampledTailFits M lim
      (M.stepEvents (authFromPbEvents auth ++ evs_af) st) sendingCt1 :=
    tailFits_of_ekReceivedCt1SampledAllocEnv hlen hauth hfree_af hfits
  have hcol_1224 := v8_fsp_296_to_1520_collapse (s0.sp - 2400#64) u8 u16 2080#64 u32 u40 1152#64
    u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
    u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch
  rw [v8_ucWordsAt_896_eq] at hcol_1224
  have htail := v8_ekReceivedCt1Sampled_from_10836_placed (F := F) hA hE
    (M.stepEvents (authFromPbEvents auth ++ evs_af) st)
    s0 s4 out pbA u auth sendingCt1 hpts hfits_tail
    u8 u16 u32 u40 u56 u64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
    u104 u112 (BitVec.ofNat 64 auth.macKey.length)
    pa1 (BitVec.ofNat 64 auth.rootKey.length) pa2 (BitVec.ofNat 64 auth.macKey.length)
    w0 w8 w16 w24 w32 w40 w48
    hlen hes hek hct1 hauth rfl rfl hcl4 hsp0_align hpc4 hrun4 hsp4
    hx9_4 hx19_4 hx21_4 hx22_4 hx23_4 hx26_4 hx27_4 hx28_4 htr4
  refine SepWP.weaken_pre (Entails.trans hP4 ?_) (SepWP.mono htail ?_)
  · rw [hst3_eq]
    dsimp only [Rest3]
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗
        (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
         ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
         ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗
         ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
         ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
         ((s0.sp - 2400#64 + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
         ((s0.sp - 2400#64 + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u.epoch)) ∗
        memRegion ((s0.sp - 2400#64) + 1024#64) 496) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       vecU8Payload A.repAlloc u8 u16 u.es ∗
       vecU8Payload A.repAlloc u32 u40 u.ek ∗
       vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
       (pbA ↦₆₄ 0x8000000000000008#64) ∗
       v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
         u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
         u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents (authFromPbEvents auth ++ evs_af) st) s4) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hcol_1224) (Entails.of_eq (by sep_ac_rfl))
  · intro sf Pf _ _ ⟨evs_tail, htail_env, hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨(authFromPbEvents auth ++ evs_af) ++ evs_tail,
      ekReceivedCt1SampledFromPbEnv_of_tailEnv hlen hauth hfree_af htail_env,
      ?_, hsp_f, hcs_f, htr_f⟩
    rwa [M.stepEvents_append]

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux2
