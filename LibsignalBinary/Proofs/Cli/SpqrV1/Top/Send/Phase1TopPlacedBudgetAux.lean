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
# Budget-Threaded Relocatable Phase 1 Auxiliary Continuations (Part 1, Block `427`)

Proves budget-threaded prologue-to-`decode_state` stepping and the `+224` (`<States>::from_pb`)
continuation for `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux

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


/-! ## 1. Early-Return Bridge, Callee-Spec Bridges, & Prologue (`+0 -> lsmpl.base 325`) -/

omit [LibsignalPlacement] in
/-- Lift a non-panicking early-return `SepWP` emitting an allocator event list `evs` into `SepWPp`. -/
theorem sepWPp_of_early_return_evs {prog : Program} {s0 s : State} {P : SepProp}
    {P_out : List AllocEvent → State → SepProp}
    {φ_evs : List AllocEvent → Prop}
    {post onPanic : State → SepProp → Prop}
    (h : SepWP prog (s0.readReg64 .x30) s P
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          φ_evs evs ∧
          (Pf ⊢ P_out evs sf) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace))
    (hpost : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      φ_evs evs →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      (Pf ⊢ P_out evs sf) →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      sf.trace = s0.trace →
      post sf Pf) :
    SepWPp prog (s0.readReg64 .x30) s P post onPanic := by
  refine SepWPp.of_sepWP (SepWP.mono h ?_)
  rintro sf Pf hpc hrun ⟨evs, hevs, hPf, hsp, hcc, htr⟩
  exact SepWPp.done hpc hrun (hpost evs sf Pf hevs hpc hrun hPf hsp hcc htr)

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable budget specification for `spqr::decode_state`
    (Block `325`) with outer `∃∗ evs : List AllocEvent` matching `call_lscro_calleeStack_evs`. -/
def decodeStatePlacedSpecXOfPrePostEnv (H_inner : V1InnerHeapPred)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop) :
    Spec (DecodeStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outPtr ∧
      s.readReg64 .x0 = x.st.v ∧
      x.st.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗ stackAt s.sp decodeStateStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decodeStateStackX

theorem decodeStatePlacedSpecXOfEnv_eq_prePost (H_inner : V1InnerHeapPred)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : DecodeStateGhost → List AllocEvent → Prop) :
    decodeStatePlacedSpecXOfEnv H_inner M A lim Env =
      decodeStatePlacedSpecXOfPrePostEnv H_inner M A lim Env Env :=
  rfl

/-- Lift `SpecsPlacedBudget.spqrDecodeStatePlacedSpecOfEnv` (inner existential over `A.pool`) to
    `decodeStatePlacedSpecXOfPrePostEnv` (outer existential matching `call_lscro_calleeStack_evs`). -/
theorem decodeStatePlacedSpecXOfPrePostEnv_of_spqrDecodeState
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv H_inner A lim PreEnv PostEnv))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfPrePostEnv H_inner M A lim PreEnv PostEnv)) := by
  refine subroutine_ok_map h (fun ⟨x, st⟩ R s0 hpre => ⟨(x, st), R, hpre, fun sf hpost => ?_⟩)
  dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpecOfEnv,
    decodeStatePlacedSpecXOfPrePostEnv] at hpost ⊢
  rw [sepExists_sepConj_left, sepExists_sepConj_left] at hpost
  rw [sepExists_sepConj_left]
  rw [satisfies_sepExists] at hpost ⊢
  obtain ⟨evs, hevs⟩ := hpost
  exact ⟨evs, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hevs⟩

/-- Lift `SpecsPlacedBudget.spqrDecodeStatePlacedSpec` to `decodeStatePlacedSpecXOfEnv` with
    `DecodeStateEnv` (`SpqrSendPlacedContractsTight.decodeState_ok` compatibility). -/
theorem decodeStatePlacedSpecXOfEnv_of_spqrDecodeStatePlacedSpec
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec H_inner A lim))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv H_inner M A lim DecodeStateEnv)) :=
  decodeStatePlacedSpecXOfPrePostEnv_of_spqrDecodeState h

/-- Definitional bridge between `States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv` and
    `SeamSpecsPlacedBudget.statesFromPbPlacedSpecXOfEnv`. -/
theorem statesFromPbPlacedSpecXOfEnv_tight_eq
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : V1State → List AllocEvent → Prop) :
    LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv
        M A lim F Env =
      statesFromPbPlacedSpecXOfEnv M A lim F (fun x => Env x.pb) :=
  rfl

/-- Definitional bridge between `States.FromPb.DefsBudget.statesFromPbPlacedSpecX` and
    `SeamSpecsPlacedBudget.statesFromPbPlacedSpecXOfEnv` at `States.FromPb.DefsBudget.StatesFromPbEnv`. -/
theorem statesFromPbPlacedSpecX_tight_eq
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX M A lim F =
      statesFromPbPlacedSpecXOfEnv M A lim F
        (fun x => LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv x.pb) :=
  rfl

/-- Relocatable VM-preserving 1-instruction `bl spqr::decode_state` step at `+76`:
    sets `x30 = spqrSendPlacedEntry + 80#64` and branches to `lsmpl.base 325` (`spqr::decode_state`). -/
theorem spqr_send_bl_decode_state_76_placed {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 76#64)
    (hrun : s.status = .Running) :
    SepWP (spqrSendPlacedProg ext)
      (lsmpl.base 325) s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        Pf = P ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x30 = spqrSendPlacedEntry + 80#64 ∧
        sf.trace = s.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_steps
    exact ProofLib.SepWP.done
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        rfl,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩)

/-- Relocatable VM-preserving prologue (`+0 -> lsmpl.base 325`):
    combines `Phase1PlacedBudget.spqr_send_prologue_placed` (`+0 -> +76`) and
    `spqr_send_bl_decode_state_76_placed` (`+76 -> lsmpl.base 325`). -/
theorem spqr_send_prologue_to_decode_state_placed {ext : String → Option (State → State)}
    (s0 : State) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (spqrSendPlacedProg ext)
      (lsmpl.base 325) s0
      (stackAt s0.sp spqrSendStack ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        AllocCallPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        (s1.readReg64 .x29 = s0.sp - 96#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x0 = stV ∧
        s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x30 = spqrSendPlacedEntry + 80#64 ∧
        s1.trace = s0.trace) := by
  refine SepWP.seq (spqr_send_prologue_placed s0 ret stV Rest hsp0_align hpc hrun hx0 hx1) ?_
  intro s1 P1 hpc1 hrun1 ⟨hvm1, hacp1, hP1, hsp1, hx29_1, hx19_1, hx0_1, hx8_1, hx21_1, hx26_1, htr1, hvregs1⟩
  refine SepWP.mono (spqr_send_bl_decode_state_76_placed s1 P1 hpc1 hrun1) ?_
  intro sf Pf _ _ ⟨hvm2, hacp2, hPf, hsp, hx29, hx19, hx0', hx8, hx21, hx26, hx30, htr, hvregs⟩
  subst hPf
  exact ⟨hvm1.trans hvm2, hacp1.trans hacp2, hP1, hsp.trans hsp1,
    ⟨hx29.trans hx29_1, hvregs.trans hvregs1⟩, hx19.trans hx19_1,
    hx0'.trans hx0_1, hx8.trans hx8_1, hx21.trans hx21_1, hx26.trans hx26_1,
    hx30, htr.trans htr1⟩

/-- Pool-threading corollary of `spqr_send_prologue_to_decode_state_placed`, transporting
    `A.pool lim st s0` to `A.pool lim st s1` across `VmPreserved s0 s1`. -/
theorem spqr_send_prologue_to_decode_state_placed_pool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s0 : State) (st : M.σ) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (spqrSendPlacedProg ext)
      (lsmpl.base 325) s0
      (stackAt s0.sp spqrSendStack ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        AllocCallPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim st s1 ∗ Rest) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        (s1.readReg64 .x29 = s0.sp - 96#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x0 = stV ∧
        s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x30 = spqrSendPlacedEntry + 80#64 ∧
        s1.trace = s0.trace) := by
  have hpr := spqr_send_prologue_to_decode_state_placed (ext := ext) s0 ret stV
    (A.pool lim st s0 ∗ Rest) hsp0_align hpc hrun hx0 hx1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hpr ?_)
  intro s1 P1 _ _ ⟨hvm, hacp, hP1, hsp1, hx29, hx19, hx0', hx8, hx21, hx26, hx30, htr⟩
  refine ⟨hvm, hacp, ?_, hsp1, hx29, hx19, hx0', hx8, hx21, hx26, hx30, htr⟩
  rw [A.pool_transport lim st s0 s1 hvm]
  exact Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))

/-! ## 2. Continuation from `+224`: `<States>::from_pb` Call & Dispatch -/

/-- Envelope- and panic-parametric relocatable continuation from `+224` when `pq.inner = some (.v1 v1)`:
    calls `<States>::from_pb` (Block `333`) with `FitsEnv M lim st (EnvFromPb ...)`, handles the
    `.error (.err err)` early return (emitting `FreeOnlyEvs evs_drop`) and vacuous `.error (.panic _)`
    branch, and on `.ok st0` relocates `st0` to `fsp + 0x950#64` and dispatches through jump table 1
    to `spqrSendPlacedEntry + statesSendArmOffset st0`. -/
theorem spqr_send_from_224_placed_ofEnv {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {Pan : Prop}
    (ext : String → Option (State → State))
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F EnvFromPb)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (hpts : v1StatePtsBound v1)
    (hfits : FitsEnv M lim st
      (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (herr_post : ∀ (err : Error) (evs_fpb evs_drop : List AllocEvent),
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
    (hok_next : ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
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
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
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
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        optProtoInnerStateAt A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    A.pool lim st s ∗
    (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
      (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
      optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
      optProtoInnerStateAt A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
      memRegion ret 72 ∗
      statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      Rest) by sep_ac_rfl)) ?_
  refine of_sepWP_lscro (mid := lsmpl.base 333) hcrl ?_
  refine spqr_send_pre_states_from_pb_224_placed_pool (A := A) (lim := lim) (st := st)
    hpc hrun hsp hfsp_align htr hx20 ?_
  intro s1 _ _ hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx19_1 hx20_1 hx21_1 _ hx23_1 _ _ hx26_1 _ _ hx29_1 hx30_1
  refine finish_sepWP_lscro hpc1 hrun1 (fun hcrl1 => ?_) (Entails.refl _)
  rw [hx19] at hx19_1
  rw [hx23] at hx23_1
  rw [hx26] at hx26_1
  rw [memRegion_190_1f20_split_states_from_pb (s0.sp - 0x1f80#64)]
  refine call_lscro_calleeStack_evs
    (spec := statesFromPbPlacedSpecXOfEnv M A lim F EnvFromPb)
    (s0.sp - 0x1f80#64) statesFromPbStackX (by decide)
    (x := (({ out := (s0.sp - 0x1f80#64) + 0x1260#64,
              pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
              pb := v1 } : StatesFromPbGhost), st))
    (Pan := Pan)
    (φ_pre := s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
      s1.readReg64 .x0 = (s0.sp - 0x1f80#64) + 0xb0#64 ∧
      v1StatePtsBound v1 ∧
      FitsEnv M lim st
        (EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                     pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                     pb := v1 }))
    (φ_post := fun evs sf =>
      sf.trace = s1.trace ∧
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64,
                  pb := v1 } evs)
    (T_pre :=
      memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s1)
    (T_post := fun evs sf =>
      resultChunkedStatesAt A.repAlloc (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
        (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf)
    (F :=
      memRegion (s0.sp - 0x1f80#64) 0x30 ∗
      (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
      (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
      optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190) ∗
      memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
      memRegion ret 72 ∗
      spqrSendStatesJumpTablePlacedAt ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      Rest)
    hfrom_pb hcrl1 hpc1 hrun1 hsp1 hfsp_align htr1 hx30_1
    (by dsimp only [statesFromPbPlacedSpecXOfEnv]; rw [hsp1]; sep_ac_rfl)
    ⟨hx8_1, hx0_1, hpts, hfits⟩
    (by dsimp only [chunkedStatesSize]; sep_ac_rfl)
    (fun _ _ => rfl)
    (fun _ => Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim))
    (fun _ => by dsimp only [statesFromPbPlacedSpecXOfEnv]; congr 1; funext evs; sep_ac_rfl)
    ?_
  rintro s2 evs_fpb hpc2 hrun2 hsp2 ⟨htr2, hevs_fpb⟩ hcrl2
    hx19_2 hx20_2 hx21_2 _ hx23_2 _ _ hx26_2 _ _ hvregs2
  have htr2' : s2.trace = s0.trace := htr2.trans htr1
  have hvregs2' : calleeSavedVRegs s2 = calleeSavedVRegs s0 := (hvregs2.trans hx29_1.2).trans hvregs
  rw [hx19_1] at hx19_2
  rw [hx20_1] at hx20_2
  rw [hx21_1] at hx21_2
  rw [hx23_1] at hx23_2
  rw [hx26_1] at hx26_2
  rcases hres : States.from_pb spqrPolyApi (spqrAuthApi F) v1 with (err | _) | st0
  · -- `.error (.err err)` early return
    have hreord :
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
         (resultChunkedStatesAt A.repAlloc (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64) (.error (.err err)) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs_fpb st) s2)) ∗
        (memRegion (s0.sp - 0x1f80#64) 0x30 ∗
         (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
         (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
         optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
         optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190) ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
         memRegion ret 72 ∗
         spqrSendStatesJumpTablePlacedAt ∗
         spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
         Rest) =
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) optProtoInnerStateSize ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190)) ∗
        resultChunkedStatesAt A.repAlloc (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64) (.error (.err err)) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
        memRegion ret 72 ∗
        A.pool lim (M.stepEvents evs_fpb st) s2 ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        (statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest) := by sep_ac_rfl
    rw [hreord, memRegion_b0_rejoin_190 (s0.sp - 0x1f80#64)]
    have herr := spqr_send_states_from_pb_err_step_placed (F := F) hA hdropChain
      s0 s2 (M.stepEvents evs_fpb st) ret w0 w1 vn chain err
      (statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗ Rest)
      hcrl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hvregs2'
    refine sepWPp_of_early_return_evs (SepWP.mono herr ?_)
      (fun evs_drop sf Pf hevs_drop => herr_post err evs_fpb evs_drop hres hevs_fpb hevs_drop sf Pf)
    rintro sf Pf _ _ ⟨evs_drop, hevs_drop, _, hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨evs_drop, hevs_drop, hPf, hsp_f, hcc_f, htr_f.trans htr2'⟩
  · -- Vacuous `.error (.panic _)` case (`resultChunkedStatesAt = ⌜False⌝`)
    dsimp only [resultChunkedStatesAt]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      ⌜False⌝ ∗
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
       memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs_fpb st) s2 ∗
       memRegion (s0.sp - 0x1f80#64) 0x30 ∗
       (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
       (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
       optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
       optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190) ∗
       memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
       memRegion ret 72 ∗ spqrSendStatesJumpTablePlacedAt ∗
       spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) by sep_ac_rfl)) ?_
    exact SepWPp.pure_left False.elim
  · -- `.ok st0` relocation + jump table dispatch
    rw [← hres]
    have hreord :
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
         (resultChunkedStatesAt A.repAlloc (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
            (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs_fpb st) s2)) ∗
        (memRegion (s0.sp - 0x1f80#64) 0x30 ∗
         (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
         (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
         optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
         optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190) ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
         memRegion ret 72 ∗
         spqrSendStatesJumpTablePlacedAt ∗
         spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
         Rest) =
        (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) optProtoInnerStateSize ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1260 - 0x190)) ∗
        resultChunkedStatesAt A.repAlloc (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        spqrSendStatesJumpTablePlacedAt ∗
        (A.pool lim (M.stepEvents evs_fpb st) s2 ∗
         (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
          memRegion ret 72 ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          Rest)) := by sep_ac_rfl
    rw [hreord, memRegion_b0_rejoin_190 (s0.sp - 0x1f80#64),
        memRegion_b0_1260_split_930_950 (s0.sp - 0x1f80#64)]
    have hreord2 :
        (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x930 - 0xb0) ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x930#64) 24 ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x948#64) 8 ∗
         memRegion ((s0.sp - 0x1f80#64) + 0x950#64) 928 ∗
         memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1260 - 0xcf0)) ∗
        resultChunkedStatesAt A.repAlloc (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        spqrSendStatesJumpTablePlacedAt ∗
        (A.pool lim (M.stepEvents evs_fpb st) s2 ∗
         (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
          memRegion ret 72 ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          Rest)) =
        (resultChunkedStatesAt A.repAlloc (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64)
            (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x930#64) 24 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x950#64) 928 ∗
          spqrSendStatesJumpTablePlacedAt) ∗
        (A.pool lim (M.stepEvents evs_fpb st) s2 ∗
         (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x930 - 0xb0) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x948#64) 8 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1260 - 0xcf0) ∗
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
          memRegion ret 72 ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          Rest)) := by sep_ac_rfl
    rw [hreord2]
    refine of_sepWP_lscro (mid := spqrSendPlacedEntry + statesSendArmOffset st0) hcrl2 ?_
    refine spqr_send_states_from_pb_ok_step_placed_pool
      (st := M.stepEvents evs_fpb st) hA hpc2 hrun2 hsp2 hfsp_align htr2' hx21_2 hx26_2 hres ?_
    intro sf _ hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f _ hx23_f hx24_f hx25_f hx26_f hx28_f hx29_f
    rw [hx19_2] at hx19_f
    rw [hx23_2] at hx23_f
    have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 := hx29_f.2.trans hvregs2'
    refine finish_sepWP_lscro hpc_f hrun_f
      (fun hcrl_f => hok_next st0 evs_fpb hres hevs_fpb sf hcrl_f hpc_f hrun_f hsp_f htr_f
        hx19_f hx20_f hx21_f hx23_f hx24_f hx25_f hx26_f hx28_f hvregs_f) ?_
    have hreord3 :
        (chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x930#64) 24 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) 928 ∗
          spqrSendStatesJumpTablePlacedAt) ∗
        (A.pool lim (M.stepEvents evs_fpb st) sf ∗
         (memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x930 - 0xb0) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x948#64) 8 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1260 - 0xcf0) ∗
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
          memRegion ret 72 ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          Rest)) =
        ((memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x930 - 0xb0) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x930#64) 24 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x948#64) 8) ∗
         (memRegion ((s0.sp - 0x1f80#64) + 0xcf0#64) (0x1260 - 0xcf0) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x1260#64) 928 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600))) ∗
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
         memRegion (s0.sp - 0x1f80#64) 0x30 ∗
         (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
         (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
         optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
         optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
         chunkedStatesAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x950#64) st0 ∗
         memRegion ret 72 ∗
         A.pool lim (M.stepEvents evs_fpb st) sf ∗
         statesFromPbJumpTablePlacedAt ∗
         spqrSendStatesJumpTablePlacedAt ∗
         spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
         Rest) := by sep_ac_rfl
    rw [hreord3, memRegion_b0_950_and_cf0_1f20_rejoin (s0.sp - 0x1f80#64)]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Default (`SeamSpecsPlacedBudget.StatesFromPbEnv`) continuation from `+224`. -/
theorem spqr_send_from_224_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {Pan : Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (hpts : v1StatePtsBound v1)
    (hfits : FitsEnv M lim st
      (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64, pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (herr_post : ∀ (err : Error) (evs_fpb evs_drop : List AllocEvent),
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
    (hok_next : ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
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
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
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
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        optProtoInnerStateAt A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_224_placed_ofEnv ext hA hfrom_pb hdropChain st ret w0 w1 vn chain v1
    hpts hfits hcrl hsp0_align hpc hrun hsp htr hx19 hx20 hx23 hx26 herr_post hok_next hvregs

/-- Tight (`States.FromPb.DefsBudget.statesFromPbPlacedSpecX`) continuation from `+224`. -/
theorem spqr_send_from_224_placed_tight {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {Pan : Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX
          M A lim F)))
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    {s0 s : State} (st : M.σ) (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (hpts : v1StatePtsBound v1)
    (hfits : FitsEnv M lim st
      (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv v1))
    {Rest Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (herr_post : ∀ (err : Error) (evs_fpb evs_drop : List AllocEvent),
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
    (hok_next : ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (evs_fpb : List AllocEvent),
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
            optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
            optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
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
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        optProtoInnerStateAt A.repAlloc ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  spqr_send_from_224_placed_ofEnv
    (EnvFromPb := fun x =>
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.StatesFromPbEnv x.pb)
    ext hA hfrom_pb hdropChain st ret w0 w1 vn chain v1 hpts hfits
    hcrl hsp0_align hpc hrun hsp htr hx19 hx20 hx23 hx26 herr_post hok_next hvregs

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1TopPlacedBudgetAux
