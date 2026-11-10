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
# Budget-Threaded Relocatable Phase 1 Auxiliary Continuations (Part 2, Block `427`)

Proves the budget-threaded `+156` (`pq.inner` split) and `+80` (post-`decode_state`)
continuations for `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux2

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


/-! ## 1. Continuation from `+156`: `pq.inner = none` vs `some (.v1 v1)` -/

/-- Envelope- and panic-parametric relocatable continuation from `+156` after
    `spqr_send_decode_state_ok_to_156_placed_pool`:
    case-splits on `pq.inner`:
    - `none`: executes `spqr_send_inner_none_step_placed` reaching `s0.readReg64 .x30` with
      `spqrSendResultAt A.repAlloc ret (some ([], none, []))` and `FreeOnlyEvs evs_drop`,
    - `some (.v1 v1)`: executes `spqr_send_inner_some_to_224_placed_pool` and continues with
      `spqr_send_from_224_placed_ofEnv`. -/
theorem spqr_send_from_156_placed_ofEnv {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {Pan : Prop}
    (ext : String → Option (State → State))
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F EnvFromPb)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (pq : PqRatchetState)
    (hpts_of_v1 : ∀ v1 : V1State, pq.inner = some (.v1 v1) → v1StatePtsBound v1)
    (hfits_from_pb : ∀ v1 : V1State, pq.inner = some (.v1 v1) →
      FitsEnv M lim st
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                     pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16)
    (hnone_post : ∀ evs_drop : List AllocEvent,
      pq.inner = none →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop st) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (v1 : V1State) (err : Error) (evs_fpb evs_drop : List AllocEvent),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st0 →
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
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  rcases hinner : pq.inner with _ | ⟨⟨v1⟩⟩
  · -- `pq.inner = none`
    have hreord :
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) none ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest =
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) none ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        (statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) := by sep_ac_rfl
    rw [hreord]
    have hnone := spqr_send_inner_none_step_placed (H_inner := H_inner) hA hdropChain
      s0 s st ret w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq.versionNegotiation pq.chain
      (statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hcrl hsp0_align hpc hrun hsp hx19 hx20 hx23 hlen16 hvregs
    refine sepWPp_of_early_return_evs (SepWP.mono hnone ?_)
      (fun evs_drop sf Pf hevs_drop => hnone_post evs_drop hinner hevs_drop sf Pf)
    rintro sf Pf _ _ ⟨evs_drop, hevs_drop, _, hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨evs_drop, hevs_drop, hPf, hsp_f, hcc_f, htr_f.trans htr⟩
  · -- `pq.inner = some (.v1 v1)`
    have hreord :
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) (some (.v1 v1)) ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest =
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) (some (.v1 v1)) ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        A.pool lim st s ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        (memRegion ret 72 ∗
         statesFromPbJumpTablePlacedAt ∗
         spqrSendStatesJumpTablePlacedAt ∗
         Rest) := by sep_ac_rfl
    rw [hreord]
    refine of_sepWP_lscro (mid := spqrSendPlacedEntry + 224#64) hcrl ?_
    have h224 := spqr_send_inner_some_to_224_placed_pool
      (A := A) (lim := lim) (ext := ext) h_inner_eq s0 s st ret
      w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq.versionNegotiation pq.chain v1
      (memRegion ret 72 ∗ statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx20 hx23 hx26 hlen16
    refine SepWP.mono h224 ?_
    intro sm Pm hpc_m hrun_m ⟨_, _, hPm, hsp_m, hx19_m, hx20_m, hx23_m, hx26_m, htr_m, hvregs_m⟩ hcrl_m
    refine SepWPp.weaken_pre hPm (SepWPp.weaken_pre ?_
      (spqr_send_from_224_placed_ofEnv ext hA hfrom_pb hdropChain st ret w0 w1
        pq.versionNegotiation pq.chain v1 (hpts_of_v1 v1 hinner) (hfits_from_pb v1 hinner)
        hcrl_m hsp0_align hpc_m hrun_m hsp_m (htr_m.trans htr)
        hx19_m hx20_m hx23_m hx26_m
        (fun err evs_fpb evs_drop hres hevs_fpb hevs_drop =>
          herr_post v1 err evs_fpb evs_drop hinner hres hevs_fpb hevs_drop)
        (fun st0 evs_fpb hres hevs_fpb =>
          hok_next v1 st0 evs_fpb hinner hres hevs_fpb)
        (hvregs_m.trans hvregs)))
    exact Entails.of_eq (by sep_ac_rfl)

/-- Default (`SeamSpecsPlacedBudget.StatesFromPbEnv`) continuation from `+156`. -/
theorem spqr_send_from_156_placed {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {Pan : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (pq : PqRatchetState)
    (hpts_of_v1 : ∀ v1 : V1State, pq.inner = some (.v1 v1) → v1StatePtsBound v1)
    (hfits_from_pb : ∀ v1 : V1State, pq.inner = some (.v1 v1) →
      FitsEnv M lim st
        (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                           pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                           pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16)
    (hnone_post : ∀ evs_drop : List AllocEvent,
      pq.inner = none →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop st) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (v1 : V1State) (err : Error) (evs_fpb evs_drop : List AllocEvent),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st0 →
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
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_156_placed_ofEnv ext h_inner_eq hA hfrom_pb hdropChain st ret
    w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq hpts_of_v1 hfits_from_pb
    hcrl hsp0_align hpc hrun hsp htr hx19 hx20 hx23 hx26 hlen16
    hnone_post herr_post hok_next hvregs

/-- Tight (`States.FromPb.DefsBudget.statesFromPbPlacedSpecX`) continuation from `+156`. -/
theorem spqr_send_from_156_placed_tight {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {Pan : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX
          M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (pq : PqRatchetState)
    (hpts_of_v1 : ∀ v1 : V1State, pq.inner = some (.v1 v1) → v1StatePtsBound v1)
    (hfits_from_pb : ∀ v1 : V1State, pq.inner = some (.v1 v1) →
      FitsEnv M lim st
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16)
    (hnone_post : ∀ evs_drop : List AllocEvent,
      pq.inner = none →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop st) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (v1 : V1State) (err : Error) (evs_fpb evs_drop : List AllocEvent),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1 evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (v1 : V1State) (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1 evs_fpb →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st0 →
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
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗ Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
        optProtoPqRatchetInnerAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 pq.versionNegotiation).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_156_placed_ofEnv
    (EnvFromPb := fun x =>
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv x.pb)
    ext h_inner_eq hA hfrom_pb hdropChain st ret
    w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq hpts_of_v1 hfits_from_pb
    hcrl hsp0_align hpc hrun hsp htr hx19 hx20 hx23 hx26 hlen16
    hnone_post herr_post hok_next hvregs

/-! ## 2. Continuation from `+80` after `spqr::decode_state` -/

/-- Envelope- and panic-parametric relocatable continuation from `+80` after `spqr::decode_state`:
    case-splits on `spqrDecodeState stBytes`:
    - `.error e`: executes `spqr_send_decode_state_err_step_placed_pool` reaching `s0.readReg64 .x30`
      with `spqrSendResultAt A.repAlloc ret none` and zero extra allocator events,
    - `.ok pq`: executes `spqr_send_decode_state_ok_to_156_placed_pool` and continues with
      `spqr_send_from_156_placed_ofEnv`. -/
theorem spqr_send_from_80_placed_ofEnv {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Pan : Prop}
    (ext : String → Option (State → State))
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F EnvFromPb)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret : BitVec 64) (stBytes : Bytes)
    (hlen : stBytes.length < 2 ^ 32)
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      FitsEnv M lim st
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                     pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hdec_err_post : ∀ e : Error,
      spqrDecodeState stBytes = .error e →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim st sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_drop : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = none →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop st) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error) (evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st0 →
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
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState stBytes) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  rcases hdec : spqrDecodeState stBytes with e | pq
  · -- `spqrDecodeState stBytes = .error e`
    have hreord :
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (.error e) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest =
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (.error e) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        (statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) := by sep_ac_rfl
    rw [hreord]
    have herr := spqr_send_decode_state_err_step_placed_pool
      (H_inner := H_inner) (A := A) (lim := lim) (ext := ext)
      s0 s st ret e (statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx26 hvregs
    refine SepWPp.of_sepWP (SepWP.mono herr ?_)
    rintro sf Pf hpc_f hrun_f ⟨_, _, hPf, hsp_f, hcc_f, htr_f⟩
    exact SepWPp.done hpc_f hrun_f (hdec_err_post e hdec sf Pf hpc_f hrun_f
      (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))) hsp_f hcc_f (htr_f.trans htr))
  · -- `spqrDecodeState stBytes = .ok pq`
    have hreord :
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (.ok pq) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest =
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (.ok pq) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        A.pool lim st s ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        (memRegion ret 72 ∗ statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) := by sep_ac_rfl
    rw [hreord]
    refine of_sepWP_lscro (mid := spqrSendPlacedEntry + 156#64) hcrl ?_
    have h156 := spqr_send_decode_state_ok_to_156_placed_pool (H_inner := H_inner) hA s0 s st ret pq
      (memRegion ret 72 ∗ statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hsp0_align hpc hrun hsp hx19 hx21 hx26
    refine SepWP.mono h156 ?_
    rintro sm Pm hpc_m hrun_m
      ⟨_, w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, hPm,
       hsp_m, hx19_m, hx20_m, hx23_m, hx26_m, htr_m, hvregs_m⟩ hcrl_m
    refine SepWPp.weaken_pre hPm (SepWPp.weaken_pre ?_
      (spqr_send_from_156_placed_ofEnv ext h_inner_eq hA hfrom_pb hdropChain st
        ret w0 w1 w2 w3 w30 w38 w40 w48 bs16 pq
        (fun v1 hinner => v1StatePtsBound_of_spqrDecodeState (F := F) (K := K) hlen hdec hinner)
        (fun v1 hinner => hfits_from_pb pq v1 hdec hinner)
        hcrl_m hsp0_align hpc_m hrun_m hsp_m (htr_m.trans htr)
        hx19_m hx20_m hx23_m hx26_m hl16
        (fun evs_drop hinner hevs_drop => hnone_post pq evs_drop hdec hinner hevs_drop)
        (fun v1 err evs_fpb evs_drop hinner hres hevs_fpb hevs_drop =>
          herr_post pq v1 err evs_fpb evs_drop hdec hinner hres hevs_fpb hevs_drop)
        (fun v1 st0 evs_fpb hinner hres hevs_fpb =>
          hok_next pq v1 st0 evs_fpb hdec hinner hres hevs_fpb w0 w1 hw0)
        (hvregs_m.trans hvregs)))
    exact Entails.of_eq (by sep_ac_rfl)

/-- Default (`SeamSpecsPlacedBudget.StatesFromPbEnv`) continuation from `+80`. -/
theorem spqr_send_from_80_placed {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Pan : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret : BitVec 64) (stBytes : Bytes)
    (hlen : stBytes.length < 2 ^ 32)
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      FitsEnv M lim st
        (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                           pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                           pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hdec_err_post : ∀ e : Error,
      spqrDecodeState stBytes = .error e →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim st sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_drop : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = none →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop st) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error) (evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st0 →
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
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState stBytes) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_80_placed_ofEnv (F := F) (K := K) ext h_inner_eq hA hfrom_pb hdropChain st
    ret stBytes hlen hfits_from_pb hcrl hsp0_align hpc hrun hsp htr hx19 hx21 hx26
    hdec_err_post hnone_post herr_post hok_next hvregs

/-- Tight (`States.FromPb.DefsBudget.statesFromPbPlacedSpecX`) continuation from `+80`. -/
theorem spqr_send_from_80_placed_tight {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {Pan : Prop}
    (ext : String → Option (State → State))
    (h_inner_eq : ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        optProtoInnerStateAt A.repAlloc a st)
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX
          M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret : BitVec 64) (stBytes : Bytes)
    (hlen : stBytes.length < 2 ^ 32)
    (hfits_from_pb : ∀ (pq : PqRatchetState) (v1 : V1State),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      FitsEnv M lim st
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hdec_err_post : ∀ e : Error,
      spqrDecodeState stBytes = .error e →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim st sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hnone_post : ∀ (pq : PqRatchetState) (evs_drop : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = none →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some ([], none, [])) ∗
          A.pool lim (M.stepEvents evs_drop st) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (herr_post : ∀ (pq : PqRatchetState) (v1 : V1State) (err : Error) (evs_fpb evs_drop : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .error (.err err) →
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1 evs_fpb →
      FreeOnlyEvs evs_drop →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs_drop (M.stepEvents evs_fpb st)) sf ∗
          stackAt s0.sp spqrSendStack ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace →
        post sf Pf)
    (hok_next : ∀ (pq : PqRatchetState) (v1 : V1State)
        (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
      spqrDecodeState stBytes = .ok pq →
      pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0 →
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1 evs_fpb →
      ∀ w0 w1 : BitVec 64, w0 ≠ none2Cap →
      ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
        sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
        sf.status = .Running →
        sf.sp = s0.sp - 0x1f80#64 →
        sf.trace = s0.trace →
        sf.readReg64 .x19 = ret →
        sf.readReg64 .x20 = chunkedStatesWord0 st0 →
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
            chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
            memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1f20 - 0xcf0) ∗
            memRegion ret 72 ∗
            A.pool lim (M.stepEvents evs_fpb st) sf ∗
            statesFromPbJumpTablePlacedAt ∗
            spqrSendStatesJumpTablePlacedAt ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0) ∗
           Rest)
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A.repAlloc ((s0.sp - 0x1f80#64) + 0x1260#64) (spqrDecodeState stBytes) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_80_placed_ofEnv
    (EnvFromPb := fun x =>
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv x.pb)
    (F := F) (K := K) ext h_inner_eq hA hfrom_pb hdropChain st
    ret stBytes hlen hfits_from_pb hcrl hsp0_align hpc hrun hsp htr hx19 hx21 hx26
    hdec_err_post hnone_post herr_post hok_next hvregs

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux2
