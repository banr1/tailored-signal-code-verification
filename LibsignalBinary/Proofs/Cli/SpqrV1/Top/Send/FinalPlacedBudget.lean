/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudget
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Final
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp


/-!
# Budget-Threaded Relocatable Phase 1 + Contract Assembly & Entry Wrapper (Block `427`)

Threads `RustCliAllocBudget` through Phase 1 execution and provides the top-level
`subroutine_ok` entry wrapper for `spqr::send::<signal_session_ratchet::Coins>`.
-/


@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false


namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SendCall extract_withLsCodeRoLoaded spqrSendResultAt spqrSendStack
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Error MlKem PqRatchetState States V1State spqrAuthApi spqrDecodeState spqrPolyApi spqrV1)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt optProtoInnerStateAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (EncodeBytesGhost)
open CryptoVerification.SpqrV1.Poly.NextChunk (PolyNextChunkGhost)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.States.FromPb (StatesFromPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred none2Cap optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.MessageSerialize (MessageSerializeGhost)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesWord0 memRegion_950_split_phase2 memRegion_cf0_split_phase2
   send_and_draws_of_spqrDecodeState_error send_and_draws_of_spqrDecodeState_inner_none
   send_and_draws_of_statesFromPb_error spqrSendCalleeStack spqrSendSavedRegs
   statesSendArmOffset)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (lsro_spqrSendFullRoPlacedAt spqrCoinsAfterPlaced spqrCoinsAtPlaced
   spqrCoinsAtPlaced_entails_spqrCoinsAfterPlaced_zero
   spqrCoinsAtPlaced_eq_pure_sep_spqrCoinsAfterPlaced_zero
   spqrLogLevelZeroPlacedAt spqrSendDropJumpTablePlacedAt spqrSendEncodeJumpTablePlacedAt
   spqrSendFullRoPlacedAt spqrSendFullRoPlacedAt_restore spqrSendRoPlacedAt
   spqrSendRoPlacedAt_discard statesFromPbJumpTablePlacedAt statesIntoPbJumpTablePlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced SpqrSendPlacedContracts SpqrSendPlacedContractsOfEnv
   spqrSendPlacedEntry spqrSendPlacedProg spqrSendStatesJumpTablePlacedAt)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudgetAux
  (call_lscro_calleeStack_evs_panic call_lscro_calleeStack_panic
   sepWPp_intro_spqrSendFullRoPlacedAt sepWPp_intro_spqrSendFullRoPlacedAt_oom
   spqrSendCoinsEnv_of_decodeStatePlacedEnv
   spqrSendCoinsEnv_of_decodeStatePlacedEnv_append_freeOnly
   spqrSendCoinsEnv_of_statesFromPbEnv_of_encodeRaw_le
   spqr_send_from_156_placed_panic spqr_send_from_224_placed_panic
   spqr_send_from_80_placed_panic spqr_send_phase1_step_placed_panic
   spqr_send_phase1_step_placed_panic_ofEnv spqr_send_phase1_step_placed_panic_ofPrePostEnv
   spqr_send_phase1_step_placed_panic_tight)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudget
  (decodeStatePlacedSpecXOfPrePostEnv
   spqr_send_from_156_placed spqr_send_from_156_placed_ofEnv spqr_send_from_156_placed_tight
   spqr_send_from_224_placed spqr_send_from_224_placed_ofEnv spqr_send_from_224_placed_tight
   spqr_send_from_80_placed spqr_send_from_80_placed_ofEnv spqr_send_from_80_placed_tight)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (DecodeStatePlacedEnv SpqrSendCoinsEnv StatesFromPbEnv
   spqrSendCoinsPlacedSpecOfEnv spqrSendCoinsPlacedSpecT spqrSendCoinsPlacedSpecTOfEnv
   statesFromPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp] do
    Lean.Attribute.erase nm `arm64_norm
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero


/-! ## 1. Re-Exports from `FinalPlacedBudgetAux`, `Phase1TopPlacedBudget`, & `Send` Specs -/

export CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendFullRoPlacedAt lsro_spqrSendFullRoPlacedAt
   spqrSendRoPlacedAt_discard spqrSendFullRoPlacedAt_restore
   spqrCoinsAtPlaced_eq_pure_sep_spqrCoinsAfterPlaced_zero
   spqrCoinsAtPlaced_entails_spqrCoinsAfterPlaced_zero)

export CryptoVerification.SpqrV1.Top.Send
  (send_and_draws_of_spqrDecodeState_error
   send_and_draws_of_spqrDecodeState_inner_none
   send_and_draws_of_statesFromPb_error
   memRegion_950_split_phase2
   memRegion_cf0_split_phase2)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudget
  (spqr_send_from_224_placed_ofEnv spqr_send_from_224_placed spqr_send_from_224_placed_tight
   spqr_send_from_156_placed_ofEnv spqr_send_from_156_placed spqr_send_from_156_placed_tight
   spqr_send_from_80_placed_ofEnv spqr_send_from_80_placed spqr_send_from_80_placed_tight)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudgetAux
  (sepWPp_intro_spqrSendFullRoPlacedAt_oom sepWPp_intro_spqrSendFullRoPlacedAt
   spqrSendCoinsEnv_of_decodeStatePlacedEnv
   spqrSendCoinsEnv_of_decodeStatePlacedEnv_append_freeOnly
   spqrSendCoinsEnv_of_statesFromPbEnv_of_encodeRaw_le
   call_lscro_calleeStack_panic call_lscro_calleeStack_evs_panic
   spqr_send_from_224_placed_panic spqr_send_from_156_placed_panic
   spqr_send_from_80_placed_panic
   spqr_send_phase1_step_placed_panic_ofPrePostEnv
   spqr_send_phase1_step_placed_panic_ofEnv
   spqr_send_phase1_step_placed_panic
   spqr_send_phase1_step_placed_panic_tight)


/-! ## 2. Top-Level Phase 1 + Early-Return Assembly & Entry Wrapper for `spqrSendCoinsPlacedSpecT` -/

/-- Remaining `.rodata` + coins-tape + global-invariant frame carried through Phase 1 (`Rest0` in
    `TopPlaced.lean`), complementing `v1StateJumpTablesPlacedAt`, `statesFromPbJumpTablePlacedAt`,
    and `spqrSendStatesJumpTablePlacedAt` to form `spqrSendFullRoPlacedAt ∗ spqrCoinsAtPlaced`. -/
def spqrSendPhase1Rest0 (ctl cur : BitVec 64) (rest : List (BitVec 8)) : SepProp :=
  spqrCoinsAtPlaced ctl cur rest ∗
  tokenInitPlacedAt ∗
  spqrLogLevelZeroPlacedAt ∗
  spqrSendEncodeJumpTablePlacedAt ∗
  spqrSendDropJumpTablePlacedAt ∗
  statesIntoPbJumpTablePlacedAt ∗
  reduceTablePlacedAt

/-- Spatial postcondition predicate at `s0.readReg64 .x30` for `spqr::send::<Coins>` before
    restoring `spqrSendFullRoPlacedAt` into `tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt`. -/
def spqrSendBudgetPostGoal (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (F : ShaCompress) (K : MlKem)
    (Env : SendCall → List AllocEvent → Prop)
    (x : SendCall) (s0 : State) (st0 : M.σ) : State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    ∃ evs : List AllocEvent,
      Env x evs ∧
      (Pf ⊢
        ⌜(spqrV1 F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
          ¬ (spqrV1 F K).sendPanics x.st.bytes x.rest⌝ ∗
        x.st.at A.repAlloc ∗
        spqrSendResultAt A.repAlloc x.ret ((spqrV1 F K).send x.st.bytes x.rest) ∗
        spqrCoinsAfterPlaced ctl x.cur x.rest ((spqrV1 F K).draws x.st.bytes x.rest) ∗
        A.pool lim (M.stepEvents evs st0) sf ∗
        stackAt s0.sp spqrSendStack ∗
        spqrSendFullRoPlacedAt)

/-- Budget-threaded counterpart of `TopPlaced.SpqrSendActiveContinuationPanic64Placed` for the
    active `States.from_pb = .ok st_states` continuation (`spqrSendPlacedEntry + statesSendArmOffset`
    to `s0.readReg64 .x30`). -/
def SpqrSendBudgetActiveContinuationPlaced (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (F : ShaCompress) (K : MlKem)
    (EnvDecode : DecodeStateGhost → List AllocEvent → Prop)
    (EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop)
    (Env : SendCall → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (x : SendCall) (s0 : State) (st0 : M.σ) (R : SepProp),
    x.st.bytes.length < 2 ^ 32 →
    64 ≤ x.rest.length →
    FitsEnv M lim st0 (Env x) →
    (s0.sp &&& 15#64 == 0#64) = true →
    ∀ (pq : PqRatchetState) (v1 : V1State)
      (st_states : States spqrPolyApi (spqrAuthApi F))
      (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState x.st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = x.ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion x.ret 72 ∗ A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
            spqrSendPhase1Rest0 ctl x.cur x.rest))
          (spqrSendBudgetPostGoal M A lim ctl F K Env x s0 st0)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(spqrV1 F K).sendPanics x.st.bytes x.rest ∧
              s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))

/-- Runs `spqr_send_phase1_step_placed_panic_ofPrePostEnv` on `Rest := spqrSendPhase1Rest0` and
    discharges all three Phase 1 early-return obligations (`decode_state = .error e`,
    `pq.inner = none`, `States.from_pb = .error (.err err)`) into `spqrSendBudgetPostGoal`,
    leaving only the active `States.from_pb = .ok st_states` continuation `hok_next`. -/
theorem spqr_send_phase1_with_early_returns_placed_ofPrePostEnv {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {F : ShaCompress} {K : MlKem}
    (ext : String → Option (State → State))
    {PreEnvDecode PostEnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    {Env : SendCall → List AllocEvent → Prop}
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfPrePostEnv H_inner M A lim PreEnvDecode PostEnvDecode)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F EnvFromPb)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (x : SendCall) (s0 : State) (st0 : M.σ) {Fr : SepProp}
    (hlen : x.st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (PreEnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      PostEnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    (henv_dec_err : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState x.st.bytes = .error e →
      PostEnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      Env x evs_dec)
    (henv_none : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = none →
      PostEnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      Env x (evs_dec ++ evs_drop))
    (henv_err : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      PostEnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      Env x ((evs_dec ++ evs_fpb) ++ evs_drop))
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.ret) (hx1 : s0.readReg64 .x1 = x.st.v)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F)) (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      PostEnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states → sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 → sf.trace = s0.trace →
        sf.readReg64 .x19 = x.ret → sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 → sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗ memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗ (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion x.ret 72 ∗ A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
            spqrSendPhase1Rest0 ctl x.cur x.rest))
          (spqrSendBudgetPostGoal M A lim ctl F K Env x s0 st0)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜(spqrV1 F K).sendPanics x.st.bytes x.rest ∧
              s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗ x.st.at A.repAlloc ∗ memRegion x.ret 72 ∗
        A.pool lim st0 s0 ∗ v1StateJumpTablesPlacedAt ∗ statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendPhase1Rest0 ctl x.cur x.rest)
      (spqrSendBudgetPostGoal M A lim ctl F K Env x s0 st0)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜(spqrV1 F K).sendPanics x.st.bytes x.rest ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine spqr_send_phase1_step_placed_panic_ofPrePostEnv
    (H_inner := H_inner) (F := F) (K := K)
    (φ_panic := (spqrV1 F K).sendPanics x.st.bytes x.rest)
    ext h_inner_eq hA hdecode hfrom_pb hdropChain
    s0 st0 x.ret x.st hlen hfits_decode hfits_from_pb
    (Rest := spqrSendPhase1Rest0 ctl x.cur x.rest) (Fr := Fr)
    (post := spqrSendBudgetPostGoal M A lim ctl F K Env x s0 st0)
    hcrl hsp0_align hpc hrun hx0 hx1
    ?hdec_err ?hnone ?herr hok_next
  case hdec_err =>
    intro e evs_dec hdec hevs_dec sf Pf _ _ hPf hspf hcsf htrf
    have ⟨hsend, hdraws, hnp⟩ := send_and_draws_of_spqrDecodeState_error (F := F) (K := K)
      (rest := x.rest) hdec
    refine ⟨hspf, hcsf, evs_dec, henv_dec_err e evs_dec hdec hevs_dec, ?_⟩
    rw [hsend, hdraws]
    refine Entails.pure_right ⟨Nat.zero_le _, htrf, hnp⟩ (Entails.trans hPf ?_)
    have hsub :
        spqrCoinsAtPlaced ctl x.cur x.rest ∗
          (x.st.at A.repAlloc ∗ spqrSendResultAt A.repAlloc x.ret none ∗
           A.pool lim (M.stepEvents evs_dec st0) sf ∗
           stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) ⊢
        spqrCoinsAfterPlaced ctl x.cur x.rest 0 ∗
          (x.st.at A.repAlloc ∗ spqrSendResultAt A.repAlloc x.ret none ∗
           A.pool lim (M.stepEvents evs_dec st0) sf ∗
           stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) :=
      sepConj_mono_left (spqrCoinsAtPlaced_entails_spqrCoinsAfterPlaced_zero ctl x.cur x.rest)
    refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by sep_ac_rfl)))
    dsimp only [spqrSendPhase1Rest0, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]; sep_ac_rfl
  case hnone =>
    intro pq evs_dec evs_drop hdec hinner hevs_dec hevs_drop sf Pf _ _ hPf hspf hcsf htrf
    have ⟨hsend, hdraws, hnp⟩ := send_and_draws_of_spqrDecodeState_inner_none (F := F) (K := K)
      (rest := x.rest) hdec hinner
    refine ⟨hspf, hcsf, evs_dec ++ evs_drop, henv_none pq evs_dec evs_drop hdec hinner hevs_dec hevs_drop, ?_⟩
    rw [hsend, hdraws, M.stepEvents_append]
    refine Entails.pure_right ⟨Nat.zero_le _, htrf, hnp⟩ (Entails.trans hPf ?_)
    have hsub :
        spqrCoinsAtPlaced ctl x.cur x.rest ∗
          (x.st.at A.repAlloc ∗ spqrSendResultAt A.repAlloc x.ret (some ([], none, [])) ∗
           A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
           stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) ⊢
        spqrCoinsAfterPlaced ctl x.cur x.rest 0 ∗
          (x.st.at A.repAlloc ∗ spqrSendResultAt A.repAlloc x.ret (some ([], none, [])) ∗
           A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
           stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) :=
      sepConj_mono_left (spqrCoinsAtPlaced_entails_spqrCoinsAfterPlaced_zero ctl x.cur x.rest)
    refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by sep_ac_rfl)))
    dsimp only [spqrSendPhase1Rest0, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]; sep_ac_rfl
  case herr =>
    intro pq v1 err evs_dec evs_fpb evs_drop hdec hinner hfrom hevs_dec hevs_fpb hevs_drop
      sf Pf _ _ hPf hspf hcsf htrf
    have ⟨hsend, hdraws, hnp⟩ := send_and_draws_of_statesFromPb_error (F := F) (K := K)
      (rest := x.rest) hdec hinner hfrom
    refine ⟨hspf, hcsf, (evs_dec ++ evs_fpb) ++ evs_drop,
      henv_err pq v1 err evs_dec evs_fpb evs_drop hdec hinner hfrom hevs_dec hevs_fpb hevs_drop, ?_⟩
    rw [hsend, hdraws, M.stepEvents_append, M.stepEvents_append]
    refine Entails.pure_right ⟨Nat.zero_le _, htrf, hnp⟩ (Entails.trans hPf ?_)
    have hsub :
        spqrCoinsAtPlaced ctl x.cur x.rest ∗
          (x.st.at A.repAlloc ∗ spqrSendResultAt A.repAlloc x.ret none ∗
           A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
           stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) ⊢
        spqrCoinsAfterPlaced ctl x.cur x.rest 0 ∗
          (x.st.at A.repAlloc ∗ spqrSendResultAt A.repAlloc x.ret none ∗
           A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
           stackAt s0.sp spqrSendStack ∗ spqrSendFullRoPlacedAt) :=
      sepConj_mono_left (spqrCoinsAtPlaced_entails_spqrCoinsAfterPlaced_zero ctl x.cur x.rest)
    refine Entails.trans (Entails.of_eq ?_) (Entails.trans hsub (Entails.of_eq (by sep_ac_rfl)))
    dsimp only [spqrSendPhase1Rest0, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]; sep_ac_rfl

/-- Top-level `subroutine_ok` wrapper for `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)
    on `spqrSendPlacedProg ext` against `withLsCodeRoLoaded lsmpl (spqrSendCoinsPlacedSpecTOfEnv ...)`,
    factoring out `.rodata` extraction/restoration, all three Phase 1 early returns, and the budget
    `FitsEnv` decomposition into `EnvDecode` and `EnvFromPb`. -/
theorem spqrSendCoins_placed_ok_of_contracts_and_continuation_ofEnv {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {EnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    {EnvIntoPb : StatesIntoPbGhost C.F → List AllocEvent → Prop}
    {EnvMsgSer : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {PreEnvEncBytes PostEnvEncBytes : EncodeBytesGhost → List AllocEvent → Prop}
    {EnvNextChunk : PolyNextChunkGhost → List AllocEvent → Prop}
    {EnvHsEk : HeaderSentSendEkChunkGhost C.F → List AllocEvent → Prop}
    {EnvCt1rEk : Ct1ReceivedSendEkChunkGhost C.F → List AllocEvent → Prop}
    {EnvCt1sCt1 : Ct1SampledSendCt1ChunkGhost C.F → List AllocEvent → Prop}
    {EnvEkrCt1 : EkReceivedCt1SampledSendCt1ChunkGhost C.F → List AllocEvent → Prop}
    {EnvCt2sCt2 : Ct2SampledSendCt2ChunkGhost C.F → List AllocEvent → Prop}
    {Env : SendCall → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrSendPlacedContractsOfEnv M H_inner A lim ctl C K
      EnvDecode EnvFromPb EnvIntoPb EnvMsgSer PreEnvEncBytes PostEnvEncBytes EnvNextChunk
      EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 ext)
    (hfits_decode : ∀ (x : SendCall) (s0 : State) (st0 : M.σ),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length → FitsEnv M lim st0 (Env x) →
      FitsEnv M lim st0
        (EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (x : SendCall) (s0 : State) (st0 : M.σ)
        (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length → FitsEnv M lim st0 (Env x) →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    (henv_dec_err : ∀ (x : SendCall) (s0 : State) (e : Error) (evs_dec : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → spqrDecodeState x.st.bytes = .error e →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      Env x evs_dec)
    (henv_none : ∀ (x : SendCall) (s0 : State) (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → spqrDecodeState x.st.bytes = .ok pq → pq.inner = none →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop → Env x (evs_dec ++ evs_drop))
    (henv_err : ∀ (x : SendCall) (s0 : State) (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .error (.err err) →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop → Env x ((evs_dec ++ evs_fpb) ++ evs_drop))
    (hcont : SpqrSendBudgetActiveContinuationPlaced M A lim ctl C.F K
      EnvDecode EnvFromPb Env ext) :
    subroutine_ok (spqrSendPlacedProg ext) spqrSendPlacedEntry
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K) Env)) := by
  refine subroutine_ok_of_sepWPp_init fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align => ?_
  have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [withLsCodeRoLoaded, spqrSendCoinsPlacedSpecTOfEnv, spqrSendCoinsPlacedSpecOfEnv] at hpre ⊢
  have hpre1 :
      s0.mem ⊨ ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.st.v ∧ FitsEnv M lim st0 (Env x)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
              (x.st.at A.repAlloc ∗ memRegion x.ret 72 ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
                A.pool lim st0 s0 ∗ stackAt s0.sp spqrSendStack ∗ R)))) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    dsimp only [spqrLogLevelZeroPlacedAt]; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1; rcases hpre1 with ⟨⟨hlen, htape64⟩, hpre1⟩
  rw [satisfies_pure_sepConj] at hpre1; rcases hpre1 with ⟨⟨hx0, hx1, hfits0⟩, hpre2⟩
  rw [satisfies_pure_sepConj] at hpre2; rcases hpre2 with ⟨_, hmem0⟩
  have hmem_ro :
      s0.mem ⊨ spqrSendFullRoPlacedAt ∗
        (x.st.at A.repAlloc ∗ memRegion x.ret 72 ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          A.pool lim st0 s0 ∗ stackAt s0.sp spqrSendStack ∗ R) :=
    lsro_spqrSendFullRoPlacedAt hcrl0.2 hmem0
  let P0 : SepProp :=
    stackAt s0.sp spqrSendStack ∗ x.st.at A.repAlloc ∗ memRegion x.ret 72 ∗
    A.pool lim st0 s0 ∗ v1StateJumpTablesPlacedAt ∗ statesFromPbJumpTablePlacedAt ∗
    spqrSendStatesJumpTablePlacedAt ∗ spqrSendPhase1Rest0 ctl x.cur x.rest
  have hP0 : s0.mem ⊨ P0 ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem_ro
    dsimp only [P0, spqrSendPhase1Rest0, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]; sep_ac_rfl
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hstep1 :
      SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0 P0
        (spqrSendBudgetPostGoal M A lim ctl C.F K Env x s0 st0)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜(spqrV1 C.F K).sendPanics x.st.bytes x.rest ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
    spqr_send_phase1_with_early_returns_placed_ofPrePostEnv
      (H_inner := H_inner) (ctl := ctl) (F := C.F) (K := K)
      (PreEnvDecode := EnvDecode) (PostEnvDecode := EnvDecode)
      (EnvFromPb := EnvFromPb) (Env := Env)
      ext hC.h_inner_eq hC.alloc hC.decodeState_ok hC.statesFromPb_ok hC.dropProtoChain_ok
      x s0 st0 (Fr := R) hlen
      (hfits_decode x s0 st0 hlen htape64 hfits0)
      (hfits_from_pb x s0 st0 · · · hlen htape64 hfits0)
      (henv_dec_err x s0 · · hlen)
      (henv_none x s0 · · · hlen)
      (henv_err x s0 · · · · · · hlen)
      hcrl0 hsp0_align hpc hrun hx0 hx1
      (hcont x s0 st0 R hlen htape64 hfits0 hsp0_align)
  refine ⟨P0, hP0, fun R' hm' hL => ?_⟩
  rcases hstep1 R' hm' hL with
    ⟨sf, hsteps, ⟨hpcf, hrunf, Pf, hmemf, hspf, hcsf, evs, hevs, hPf⟩ | hpan | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, Pf, hmemf, fun hmfR => ?_, hspf, hcsf⟩⟩
    have hmemf' : sf.mem ⊨
        spqrSendFullRoPlacedAt ∗
        (⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
           ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
         x.st.at A.repAlloc ∗
         spqrSendResultAt A.repAlloc x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
         spqrCoinsAfterPlaced ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
         A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp spqrSendStack ∗ R) := by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq ?_)) hmfR
      sep_ac_rfl
    have hrestored := spqrSendFullRoPlacedAt_restore hmemf'
    rw [sepConj_assoc, sepConj_comm tokenInitPlacedAt, sepConj_assoc,
        sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    have hrestored' :
        sf.mem ⊨ ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest⌝ ∗
          (x.st.at A.repAlloc ∗
           spqrSendResultAt A.repAlloc x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
           spqrCoinsAfterPlaced ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp spqrSendStack ∗
           R ∗ tokenInitPlacedAt) := by
      refine Satisfies.mono (Entails.of_eq ?_) hrestored
      dsimp only [spqrLogLevelZeroPlacedAt]; sep_ac_rfl
    rw [satisfies_pure_sepConj] at hrestored'
    rcases hrestored' with ⟨⟨hdraws, htrf, hnp⟩, hspatial⟩
    have hgoal :
        sf.mem ⊨ ⌜(spqrV1 C.F K).draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ (spqrV1 C.F K).sendPanics x.st.bytes x.rest ∧ Env x evs⌝ ∗
          (x.st.at A.repAlloc ∗
           spqrSendResultAt A.repAlloc x.ret ((spqrV1 C.F K).send x.st.bytes x.rest) ∗
           spqrCoinsAfterPlaced ctl x.cur x.rest ((spqrV1 C.F K).draws x.st.bytes x.rest) ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp spqrSendStack ∗
           R ∗ tokenInitPlacedAt) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hdraws, htrf, hnp, hevs⟩, hspatial⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Default (`SpqrSendPlacedContracts` / `SpqrSendCoinsEnv`) specialization of
    `spqrSendCoins_placed_ok_of_contracts_and_continuation_ofEnv` discharging `henv_dec_err` and
    `henv_none` automatically via `spqrSendCoinsEnv_of_decodeStatePlacedEnv*`. -/
theorem spqrSendCoins_placed_ok_of_contracts_and_continuation {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hfits_decode : ∀ (x : SendCall) (s0 : State) (st0 : M.σ),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length → FitsEnv M lim st0 (SpqrSendCoinsEnv x) →
      FitsEnv M lim st0
        (DecodeStatePlacedEnv { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (x : SendCall) (s0 : State) (st0 : M.σ)
        (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length → FitsEnv M lim st0 (SpqrSendCoinsEnv x) →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      DecodeStatePlacedEnv { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                           pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    (henv_err : ∀ (x : SendCall) (s0 : State) (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .error (.err err) →
      DecodeStatePlacedEnv { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop → SpqrSendCoinsEnv x ((evs_dec ++ evs_fpb) ++ evs_drop))
    (hcont : SpqrSendBudgetActiveContinuationPlaced M A lim ctl C.F K
      DecodeStatePlacedEnv StatesFromPbEnv SpqrSendCoinsEnv ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecT M A lim ctl (spqrV1 C.F K))) :=
  spqrSendCoins_placed_ok_of_contracts_and_continuation_ofEnv hC
    hfits_decode hfits_from_pb
    (fun x s0 _ _ _ _ hdec_env =>
      spqrSendCoinsEnv_of_decodeStatePlacedEnv x ((s0.sp - 0x1f80#64) + 0x1260#64) hdec_env)
    (fun x s0 _ _ _ _ _ _ hdec_env hdrop =>
      spqrSendCoinsEnv_of_decodeStatePlacedEnv_append_freeOnly x ((s0.sp - 0x1f80#64) + 0x1260#64)
        hdec_env hdrop)
    henv_err hcont

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget
