/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux2
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1DispatchPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1FromPbPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp


/-!
# Budget-Threaded Relocatable Phase 1 Top-Level Composition (Block `427`)

Composes budget-threaded Phase 1 continuations into full Phase 1 execution (`+0 -> s0.lr`
or 11-arm `<States>::send` dispatch) for `spqr::send::<signal_session_ratchet::Coins>`.
-/


@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded VecArg spqrSendResultAt spqrSendStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB Error MlKem PqRatchetState States V1State VersionNegotiationPB spqrAuthApi
   spqrDecodeState spqrPolyApi)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.States.FromPb
  (StatesFromPbGhost resultChunkedStatesAt statesFromPbStackX v1StatePtsBound)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred decodeStateResultAt decodeStateStackX none2Cap
   optProtoPqRatchetInnerAt optVersionNegotiationPBTailAt relocOptVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesWord0 memRegion_190_1f20_split_states_from_pb memRegion_1f20_split_decode_state
   memRegion_b0_1260_split_930_950 memRegion_b0_950_and_cf0_1f20_rejoin
   memRegion_b0_rejoin_190 sepWPp_of_early_return spqrSendCalleeStack spqrSendName
   spqrSendSavedRegs statesSendArmOffset v1StatePtsBound_of_spqrDecodeState)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (finish_sepWP_lscro of_sepWP_lscro statesFromPbJumpTablePlacedAt)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg spqrSendStatesJumpTablePlacedAt)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (DecodeStatePlacedEnv StatesFromPbEnv decodeStatePlacedSpecX decodeStatePlacedSpecXOfEnv
   statesFromPbPlacedSpecX statesFromPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
  (spqr_send_prologue_placed spqr_send_prologue_placed_pool)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
  (spqr_send_decode_state_err_step_placed_pool spqr_send_decode_state_ok_to_156_placed_pool)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1FromPbPlacedBudget
  (spqr_send_inner_none_step_placed spqr_send_inner_some_to_224_placed_pool)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1DispatchPlacedBudget
  (spqr_send_pre_states_from_pb_224_placed_pool spqr_send_states_from_pb_err_step_placed
   spqr_send_states_from_pb_ok_step_placed_pool)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
  (call_lscro_calleeStack_evs)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpec spqrDecodeStatePlacedSpecOfEnv)

open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux
  (decodeStatePlacedSpecXOfEnv_eq_prePost
   decodeStatePlacedSpecXOfEnv_of_spqrDecodeStatePlacedSpec
   decodeStatePlacedSpecXOfPrePostEnv
   decodeStatePlacedSpecXOfPrePostEnv_of_spqrDecodeState
   sepWPp_of_early_return_evs
   spqr_send_bl_decode_state_76_placed
   spqr_send_from_224_placed
   spqr_send_from_224_placed_ofEnv
   spqr_send_from_224_placed_tight
   spqr_send_prologue_to_decode_state_placed
   spqr_send_prologue_to_decode_state_placed_pool
   statesFromPbPlacedSpecX_tight_eq
   statesFromPbPlacedSpecXOfEnv_tight_eq)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux2
  (spqr_send_from_156_placed
   spqr_send_from_156_placed_ofEnv
   spqr_send_from_156_placed_tight
   spqr_send_from_80_placed
   spqr_send_from_80_placed_ofEnv
   spqr_send_from_80_placed_tight)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux
  (decodeStatePlacedSpecXOfEnv_eq_prePost
   decodeStatePlacedSpecXOfEnv_of_spqrDecodeStatePlacedSpec
   decodeStatePlacedSpecXOfPrePostEnv
   decodeStatePlacedSpecXOfPrePostEnv_of_spqrDecodeState
   sepWPp_of_early_return_evs
   spqr_send_bl_decode_state_76_placed
   spqr_send_from_224_placed
   spqr_send_from_224_placed_ofEnv
   spqr_send_from_224_placed_tight
   spqr_send_prologue_to_decode_state_placed
   spqr_send_prologue_to_decode_state_placed_pool
   statesFromPbPlacedSpecX_tight_eq
   statesFromPbPlacedSpecXOfEnv_tight_eq)
export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux2
  (spqr_send_from_156_placed
   spqr_send_from_156_placed_ofEnv
   spqr_send_from_156_placed_tight
   spqr_send_from_80_placed
   spqr_send_from_80_placed_ofEnv
   spqr_send_from_80_placed_tight)

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
attribute [local simp, local arm64_norm, local wp_norm]
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg


/-! ## 1. Full Phase 1 Step (`+0 -> s0.lr` or `spqrSendPlacedEntry + statesSendArmOffset st0`) -/

/-- Two-envelope (`PreEnvDecode` / `PostEnvDecode`) and panic-parametric (`{Pan : Prop}`)
    relocatable full Phase 1 execution of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`):
    executes the prologue, calls `spqr::decode_state` with `FitsEnv M lim st0 (PreEnvDecode ...)`,
    handles all Phase 1 early-return/error paths (`decode_state = .error e`, `pq.inner = none`,
    `States.from_pb = .error (.err err)`, and vacuous `.error (.panic _)`), and on
    `States.from_pb = .ok st_states` relocates `st_states` to `fsp + 0x950#64` and dispatches
    through jump table 1 to `spqrSendPlacedEntry + statesSendArmOffset st_states`. -/
theorem spqr_send_phase1_step_placed_ofPrePostEnv {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Pan : Prop}
    (ext : String → Option (State → State))
    {PreEnvDecode PostEnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
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
    (s0 : State) (st0 : M.σ) (ret : BitVec 64) (st : VecArg)
    (hlen : st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (PreEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                     pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .error e →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_dec st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = none →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                  pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F))
        (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                  pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
            memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
            (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗
        st.at A.repAlloc ∗
        memRegion ret 72 ∗
        A.pool lim st0 s0 ∗
        v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt s0.sp spqrSendStack ∗
    A.pool lim st0 s0 ∗
    (st.at A.repAlloc ∗
     memRegion ret 72 ∗
     v1StateJumpTablesPlacedAt ∗
     statesFromPbJumpTablePlacedAt ∗
     spqrSendStatesJumpTablePlacedAt ∗
     Rest) by sep_ac_rfl)) ?_
  refine of_sepWP_lscro (mid := lsmpl.base 325) hcrl ?_
  have hpro := spqr_send_prologue_to_decode_state_placed_pool
    (A := A) (lim := lim) (ext := ext) s0 st0 ret st.v
    (st.at A.repAlloc ∗
     memRegion ret 72 ∗
     v1StateJumpTablesPlacedAt ∗
     statesFromPbJumpTablePlacedAt ∗
     spqrSendStatesJumpTablePlacedAt ∗
     Rest)
    hsp0_align hpc hrun hx0 hx1
  refine SepWP.mono hpro ?_
  rintro s1 P1 hpc1 hrun1
    ⟨_, _, hP1, hsp1, ⟨_, hvregs1⟩, hx19_1, hx0_1, hx8_1, hx21_1, hx26_1, hx30_1, htr1⟩ hcrl1
  refine SepWPp.weaken_pre hP1 ?_
  rw [memRegion_1f20_split_decode_state (s0.sp - 0x1f80#64)]
  refine call_lscro_calleeStack_evs
    (spec := decodeStatePlacedSpecXOfPrePostEnv H_inner M A lim PreEnvDecode PostEnvDecode)
    (s0.sp - 0x1f80#64) decodeStateStackX (by decide)
    (x := (({ st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } : DecodeStateGhost), st0))
    (Pan := Pan)
    (φ_pre := s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
      s1.readReg64 .x0 = st.v ∧
      st.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st0
        (PreEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (φ_post := fun evs sf =>
      sf.trace = s1.trace ∧
      PostEnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs)
    (T_pre :=
      v1StateJumpTablesPlacedAt ∗
      st.at A.repAlloc ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) 352 ∗
      A.pool lim st0 s1)
    (T_post := fun evs sf =>
      v1StateJumpTablesPlacedAt ∗
      st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64)
        (spqrDecodeState st.bytes) ∗
      A.pool lim (M.stepEvents evs st0) sf)
    (F :=
      memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
      memRegion ret 72 ∗
      statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      Rest)
    hdecode hcrl1 hpc1 hrun1 hsp1 hfsp_align htr1 hx30_1
    (by dsimp only [decodeStatePlacedSpecXOfPrePostEnv]; sep_ac_rfl)
    ⟨hx8_1, hx0_1, hlen, hfits_decode⟩
    (by sep_ac_rfl)
    (fun _ _ => rfl)
    (fun _ => Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim))
    (fun _ => by dsimp only [decodeStatePlacedSpecXOfPrePostEnv]; congr 1; funext evs; sep_ac_rfl)
    ?_
  rintro s2 evs_dec hpc2 hrun2 hsp2 ⟨htr2, hevs_dec⟩ hcrl2
    hx19_2 _ hx21_2 _ _ _ _ hx26_2 _ _ hvregs2
  rw [hx19_1] at hx19_2
  rw [hx21_1] at hx21_2
  rw [hx26_1] at hx26_2
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
    memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
    decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64)
      (spqrDecodeState st.bytes) ∗
    memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
    memRegion ret 72 ∗
    A.pool lim (M.stepEvents evs_dec st0) s2 ∗
    statesFromPbJumpTablePlacedAt ∗
    spqrSendStatesJumpTablePlacedAt ∗
    spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
    (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest) by sep_ac_rfl)) ?_
  exact spqr_send_from_80_placed_ofEnv (F := F) (K := K) ext h_inner_eq hA hfrom_pb hdropChain
    (M.stepEvents evs_dec st0) ret st.bytes hlen
    (fun pq v1 hdec hinner => hfits_from_pb pq v1 evs_dec hdec hinner hevs_dec)
    hcrl2 hsp0_align hpc2 hrun2 hsp2 (htr2.trans htr1)
    hx19_2 hx21_2 hx26_2
    (fun e hdec => hdec_err_post e evs_dec hdec hevs_dec)
    (fun pq evs_drop hdec hinner hevs_drop =>
      hnone_post pq evs_dec evs_drop hdec hinner hevs_dec hevs_drop)
    (fun pq v1 err evs_fpb evs_drop hdec hinner hres hevs_fpb hevs_drop =>
      herr_post pq v1 err evs_dec evs_fpb evs_drop hdec hinner hres hevs_dec hevs_fpb hevs_drop)
    (fun pq v1 st_states evs_fpb hdec hinner hres hevs_fpb =>
      hok_next pq v1 st_states evs_dec evs_fpb hdec hinner hres hevs_dec hevs_fpb)
    (hvregs2.trans hvregs1)

/-- Single-envelope (`EnvDecode` / `EnvFromPb`, matching `SpqrSendPlacedContractsOfEnv`)
    panic-parametric relocatable full Phase 1 execution of `spqr::send::<Coins>`. -/
theorem spqr_send_phase1_step_placed_ofEnv {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Pan : Prop}
    (ext : String → Option (State → State))
    {EnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecXOfEnv H_inner M A lim EnvDecode)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F EnvFromPb)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 : State) (st0 : M.σ) (ret : BitVec 64) (st : VecArg)
    (hlen : st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                     pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .error e →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_dec st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = none →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                  pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F))
        (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      EnvDecode { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                  pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
            memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
            (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗
        st.at A.repAlloc ∗
        memRegion ret 72 ∗
        A.pool lim st0 s0 ∗
        v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_phase1_step_placed_ofPrePostEnv
    (PreEnvDecode := EnvDecode) (PostEnvDecode := EnvDecode) (EnvFromPb := EnvFromPb)
    (F := F) (K := K) ext h_inner_eq hA hdecode hfrom_pb hdropChain
    s0 st0 ret st hlen hfits_decode hfits_from_pb
    hcrl hsp0_align hpc hrun hx0 hx1
    hdec_err_post hnone_post herr_post hok_next

/-- Peer-seam default (`DecodeStatePlacedEnv` + `StatesFromPbEnv`, matching `SpqrSendPlacedContracts`)
    panic-parametric relocatable full Phase 1 execution of `spqr::send::<Coins>`. -/
theorem spqr_send_phase1_step_placed {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Pan : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX H_inner M A lim)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 : State) (st0 : M.σ) (ret : BitVec 64) (st : VecArg)
    (hlen : st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                           pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                           pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .error e →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_dec st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = none →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                        pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F))
        (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      DecodeStatePlacedEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                        pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
            memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
            (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗
        st.at A.repAlloc ∗
        memRegion ret 72 ∗
        A.pool lim st0 s0 ∗
        v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_phase1_step_placed_ofEnv (F := F) (K := K) ext h_inner_eq hA hdecode hfrom_pb hdropChain
    s0 st0 ret st hlen hfits_decode hfits_from_pb
    hcrl hsp0_align hpc hrun hx0 hx1
    hdec_err_post hnone_post herr_post hok_next

/-- Tight (`spqrDecodeStatePlacedSpec` + `States.FromPb.DefsBudget.statesFromPbPlacedSpecX`,
    matching `SpqrSendPlacedContractsTight`) panic-parametric relocatable full Phase 1 execution
    of `spqr::send::<Coins>`. -/
theorem spqr_send_phase1_step_placed_tight {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Pan : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hdecode : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec H_inner A lim)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX
          M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 : State) (st0 : M.σ) (ret : BitVec 64) (st : VecArg)
    (hlen : st.bytes.length < 2 ^ 32)
    (hfits_decode : FitsEnv M lim st0
      (DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = st.v)
    (hdec_err_post : ∀ (e : Error) (evs_dec : List AllocEvent),
      spqrDecodeState st.bytes = .error e →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_dec st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_dec evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = none →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_dec st0)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1 evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb (M.stepEvents evs_dec st0))) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest)) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi F))
        (evs_dec evs_fpb : List AllocEvent),
      spqrDecodeState st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st_states →
      DecodeStateEnv { st := st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1 evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st_states →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st_states →
        sf.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x23 = w0 →
        sf.readReg64 .x24 = (s0.sp - 0x1f80#64) + 0x950#64 →
        sf.readReg64 .x25 = (s0.sp - 0x1f80#64) + 0x550#64 →
        sf.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 →
        sf.readReg64 .x28 = (s0.sp - 0x1f80#64) + 0x1060#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sf
          ((stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
            memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
            (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) pq.versionNegotiation ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x950 - 0xb0) ∗
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st_states ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb (M.stepEvents evs_dec st0)) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           (st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s0
      (stackAt s0.sp spqrSendStack ∗
        st.at A.repAlloc ∗
        memRegion ret 72 ∗
        A.pool lim st0 s0 ∗
        v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_phase1_step_placed_ofEnv
    (EnvDecode := DecodeStateEnv)
    (EnvFromPb := fun x =>
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv x.pb)
    (F := F) (K := K) ext h_inner_eq hA
    (decodeStatePlacedSpecXOfEnv_of_spqrDecodeStatePlacedSpec hdecode)
    hfrom_pb hdropChain s0 st0 ret st hlen hfits_decode hfits_from_pb
    hcrl hsp0_align hpc hrun hx0 hx1
    hdec_err_post hnone_post herr_post hok_next

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudget
