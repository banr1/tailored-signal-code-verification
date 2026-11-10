/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlaced
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Top-Level Proof of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Composes budget-threaded Phase 1, Phase 2, and Phase 3–4 into end-to-end `subroutine_ok`
contracts for Block `427` under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.States.FromPb (StatesFromPbGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send hiding AuthMacHdrPinnedPlacedOkX DoReserve2PlacedOkX
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
open LibsignalBinary.Heap
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget (dropChunkedStatesLocal1PlacedSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (DecodeStatePlacedEnv StatesFromPbEnv spqrSendCoinsPlacedSpecTOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
  (AuthMacHdrPinnedPlacedOkX DoReserve2PlacedOkX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

/-- Honest phase-composed allocation envelope for `spqr::send::<signal_session_ratchet::Coins>`
    (`Block 427`), composing `DecodeStatePlacedEnv`, `StatesFromPbEnv`, `StatesSendEnv`, and
    `SendPhase3Env` with zero existential binders. -/
def SpqrSendCoinsExactEnv (F : ShaCompress) (K : MlKem)
    (x : SendCall) (evs : List AllocEvent) : Prop :=
  let decEnv : List AllocEvent → Prop :=
    DecodeStatePlacedEnv { st := x.st, outPtr := 0#64 }
  let fpbEnv (v1 : V1State) : List AllocEvent → Prop :=
    StatesFromPbEnv { out := 0#64, pbA := 0#64, pb := v1 }
  match spqrDecodeState x.st.bytes with
  | .error _ => decEnv evs
  | .ok pq =>
    match pq.inner with
    | none => SeqEnv decEnv FreeOnlyEvs evs
    | some (.v1 v1) =>
      SeqEnv decEnv
        (match States.from_pb spqrPolyApi (spqrAuthApi F) v1 with
         | .error (.panic _) => fpbEnv v1
         | .error (.err _) => SeqEnv (fpbEnv v1) FreeOnlyEvs
         | .ok st_states =>
           SeqEnv (fpbEnv v1)
             (SeqEnv (StatesSendEnv F K st_states x.rest)
               (match st_states.send K x.rest with
                | .ok (sOut, _) => SendPhase3Env pq sOut
                | .error (.err _) => FreeOnlyEvs
                | .error (.panic _) => LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget.HeaderReceived1aEnv)))
        evs

example (F : ShaCompress) (K : MlKem) (x : SendCall) :
    SpqrSendCoinsExactEnv F K x [] := by
  dsimp only [SpqrSendCoinsExactEnv]
  have hnil : DecodeStatePlacedEnv { st := x.st, outPtr := 0#64 } [] :=
    SpqrBoundedEvs.nil 96 (4 * x.st.bytes.length + 4096)
  cases spqrDecodeState x.st.bytes with
  | error _ => exact hnil
  | ok pq =>
    dsimp only
    cases pq.inner with
    | none => dsimp only [SeqEnv]; exact Or.inl hnil
    | some inner =>
      cases inner with
      | v1 _ => dsimp only [SeqEnv]; exact Or.inl hnil

/-- Budget-threaded extra external contracts required on top of `SendCalleeContractsPlaced`
    to close `SpqrSendPlacedContracts` and the active continuation on `spqrSendPlacedProg ext`
    (`Block 427`). -/
structure SpqrSendExtraContractsPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  panic_hook : ext "_RNvNtCskxtBwYRO61I_4core9panicking5panic" = some Rust.panicked
  panicSubOverflow_hook :
    ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" =
      some Rust.panicked
  unwrapFailed_hook : (Rust.withPanics ext) spqrUnwrapFailedSym = some Rust.panicked
  allocZeroed_hook : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym
    (rustAllocZeroedBudgetSpec M A lim)
  mlkemFromSeed_hook : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym
    (withVmPreserved (mlkemFromSeedSpec K))
  mlkemPk1_hook : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym
    (withVmPreserved mlkemPk1Spec)
  mlkemPk2_hook : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym
    (withVmPreserved mlkemPk2Spec)
  mlkemEncaps1_hook : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym
    (withVmPreserved (mlkemEncaps1Spec K))
  fromSeed_pk1_slice : ∀ s : List.Vector (BitVec 8) 64,
    ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList
  fromSeed_pk2_slice : ∀ s : List.Vector (BitVec 8) 64,
    ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList
  macHdrPinned_ok : AuthMacHdrPinnedPlacedOkX C.F M A lim ext
  doReserve2_ok : DoReserve2PlacedOkX M A lim ext
  dropChainEpochSlice_raw_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim))
  dropChunkedStates_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 443)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim C.F))

theorem spqrSend_dropChainEpochSlice_raw_ok_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)) :=
  LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget.drop_chain_epoch_slice_local1_placed_lscl
    (callerProg := spqrSendPlacedProg ext) hA.dealloc

theorem spqrSend_dropChunkedStates_ok_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 443)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)) :=
  LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1PlacedBudget.drop_chunked_states_local1_placed_lscl
    (callerProg := spqrSendPlacedProg ext) hA.dealloc

set_option maxHeartbeats 800000 in
theorem spqrSendBudgetActiveContinuation_placed_ok_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {EnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    {Env : SendCall → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext)
    (hfits_ss : ∀ (x : SendCall) (s0 : State) (st0 : M.σ)
        (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi C.F))
        (evs_dec evs_fpb : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length →
      FitsEnv M lim st0 (Env x) →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st_states →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FitsEnv M lim (M.stepEvents (evs_dec ++ evs_fpb) st0)
        (SeqEnv (StatesSendEnv C.F K st_states x.rest)
          (match st_states.send K x.rest with
           | .ok (sOut, _) => SendPhase3Env pq sOut
           | .error (.err _) => FreeOnlyEvs
           | .error (.panic _) => LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget.HeaderReceived1aEnv)))
    (henv_active : ∀ (x : SendCall) (s0 : State)
        (pq : PqRatchetState) (v1 : V1State)
        (st_states : States spqrPolyApi (spqrAuthApi C.F))
        (evs_dec evs_fpb evs_tail : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .ok st_states →
      EnvDecode { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      EnvFromPb { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                  pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      (match st_states.send K x.rest with
       | .ok (sOut, _) =>
         SeqEnv (StatesSendEnv C.F K st_states x.rest)
           (SendPhase3Env pq sOut) evs_tail
       | .error (.err _) =>
         SeqEnv (StatesSendEnv C.F K st_states x.rest)
           FreeOnlyEvs evs_tail
       | .error (.panic _) => False) →
      Env x (evs_dec ++ evs_fpb ++ evs_tail)) :
    SpqrSendBudgetActiveContinuationPlaced M A lim ctl C.F K
      EnvDecode EnvFromPb Env ext := by
  intro x s0 st0 R hlen hrest_len hfits0 hsp_align pq v1 st_states evs_dec evs_fpb
    hdec hinner hfrom hevs_dec hevs_fpb w0 w1 hw0 sf hcrlf hpcf hrunf hspf htrf
    hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx28 hvregsf
  rw [← M.stepEvents_append evs_dec evs_fpb st0]
  let sp : BitVec 64 := s0.sp - 0x1f80#64
  let bSt : M.σ := M.stepEvents (evs_dec ++ evs_fpb) st0
  have hfsp_align : (sp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp_align (by decide)
  have hfit_tail :=
    hfits_ss x s0 st0 pq v1 st_states evs_dec evs_fpb hlen hrest_len hfits0
      hdec hinner hfrom hevs_dec hevs_fpb
  dsimp only [spqrSendPhase1Rest0]
  let RestPre : SepProp :=
    (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
      ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      CryptoVerification.SpqrV1.Top.DecodeState.optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
      CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
      memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
      memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
      memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
      statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
     (x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
      (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
       spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
       CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
       CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt))
  have hpull_valid :
      (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        CryptoVerification.SpqrV1.Top.DecodeState.optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
         CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt)) ⊢
      ⌜statesPolyEncoderValid st_states⌝ ∗
      ((stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        CryptoVerification.SpqrV1.Top.DecodeState.optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
         CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt))) := by
    have hv0 := chunkedStatesAt_entails_polyEncoderValid A.repAlloc (sp + 0x950#64) st_states
    refine Entails.trans (Entails.of_eq (show _ = chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗ RestPre by
      dsimp only [RestPre]; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hv0) ?_
    exact Entails.of_eq (by dsimp only [RestPre]; sep_ac_rfl)
  refine SepWPp.weaken_pre hpull_valid (ProofLib.SepWPp.pure_elim fun hv => ?_)
  rcases statesSend_ok_or_headerReceived_encaps1_of_le_64 K hlen hrest_len hdec hinner hfrom hv with
    ⟨sOut, rest', hsend0⟩ | ⟨st, rfl, hencaps, hsend_err⟩
  · rw [hsend0] at hfit_tail
    have hfit_ss : FitsEnv M lim bSt (StatesSendEnv C.F K st_states x.rest) := hfit_tail.seq_left
    have hdec_deps := decodeState_spqrDeps_of_spqrDecodeState_ok C.F K hdec
    have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
      unfold pqRatchetStateToPb; simp [hinner]
    have hraw := CryptoVerification.SpqrV1.Top.StateSize.decodeState_spqrDeps_raw_le hdec_deps
    have hraw' :
        CryptoVerification.SpqrV1.Top.StateSize.optRaw CryptoVerification.SpqrV1.Top.StateSize.rawVN pq.versionNegotiation +
          CryptoVerification.SpqrV1.Top.StateSize.optRaw CryptoVerification.SpqrV1.Top.StateSize.rawChain pq.chain +
          CryptoVerification.SpqrV1.Top.StateSize.rawV1State v1 ≤
        201 * x.st.bytes.length := by
      simpa only [pbToPqRatchetState, pqRatchetStateToPb,
        CryptoVerification.SpqrV1.Top.StateSize.rawPqState,
        CryptoVerification.SpqrV1.Top.StateSize.rawPqInner,
        hinner, Option.map, CryptoVerification.SpqrV1.Top.StateSize.optRaw_some] using hraw
    have hchain_raw :
        CryptoVerification.SpqrV1.Top.StateSize.optRaw CryptoVerification.SpqrV1.Top.StateSize.rawChain pq.chain + 296 ≤ 2 ^ 54 := by
      omega
    rcases CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le hfrom with ⟨hst0_raw, _⟩
    have hroot_len : ∀ st, st_states = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63 := by
      intro st hst; subst hst
      have hrk := headerReceived_rootKey_le_rawV1State st
      omega
    have hpq'_len : ∀ chainPb : Option ChainPB,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw CryptoVerification.SpqrV1.Top.StateSize.rawChain chainPb ≤
          CryptoVerification.SpqrV1.Top.StateSize.optRaw CryptoVerification.SpqrV1.Top.StateSize.rawChain pq.chain + 624 →
        CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStatePBEncodedLen
          { versionNegotiation := pq.versionNegotiation
            chain := chainPb
            inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63 :=
      fun chainPb hch_le =>
        pqRatchetStatePBEncodedLen_lt_of_send C.F K hlen hdec_deps hinner_pb hfrom hsend0 hch_le
    let RestTail : SepProp :=
      statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
      x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt
    let FrameArm : SepProp :=
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
      memRegion x.ret 72 ∗
      (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
       memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
       memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
      spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
      spqrSendEncodeJumpTablePlacedAt ∗
      CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ RestTail
    have hpre_arm :
        (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          CryptoVerification.SpqrV1.Top.DecodeState.optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
          CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
          memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
         (x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
          (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
           CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
           CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt)) ⊢
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗
          tokenInitPlacedAt ∗ CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
          memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
          memRegion (sp + 0x590#64) 920 ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
          statesSendPreArmScratch sp) ∗ FrameArm := by
      have hvn := optVN_30_to_proto A.repAlloc sp w0 w1 pq.versionNegotiation
      have hreg := pre_309cc_regions_eq sp
      dsimp only [FrameArm, RestTail]
      refine Entails.trans (Entails.of_eq (show _ =
        (((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          CryptoVerification.SpqrV1.Top.DecodeState.optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation) ∗
        (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗
          tokenInitPlacedAt ∗ CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
          memRegion x.ret 72 ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          spqrSendEncodeJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendStatesJumpTablePlacedAt ∗
          x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hvn) ?_
      rw [hreg]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_arm ?_
    refine step_send_statesSend_placed (ctl := ctl) A lim bSt ext hA
      hEx.allocZeroed_hook hC.coinsFill_ok hEx.mlkemFromSeed_hook hEx.mlkemPk1_hook hEx.mlkemPk2_hook
      hEx.mlkemEncaps1_hook hEx.fromSeed_pk1_slice hEx.fromSeed_pk2_slice
      hEx.macHdrPinned_ok hEx.doReserve2_ok hC.encodeBytes_ok hC.polyNextChunk_ok hC.hkdfToVec_ok hC.authUpdate_ok
      hC.headerSentSendEkChunk_ok hC.ct1ReceivedSendEkChunk_ok hC.ct1SampledSendCt1Chunk_ok
      hC.ct2SampledSendCt2Chunk_ok hC.ekReceivedCt1SampledSendCt1Chunk_ok
      (s0 := sf) (s := sf) sp x.cur x.rest rest' pq.chain st_states sOut hroot_len hsend0 hfit_ss
      hcrlf hpcf hrunf hspf hfsp_align rfl rfl hx20 hx24 hx25 hx26 hx28 rfl rfl rfl ?_
    intro sm evs_ss hevs_ss hcrl_m hpc_m hrun_m hsp_m htr_m hx19_m _ hx22_m hx25_m hx26_m hx28_m hx23_none_m hpstate_m hvregs_m
    rw [htrf] at htr_m
    rw [hx19] at hx19_m
    rw [hx28] at hx28_m
    have hfit_p3 : FitsEnv M lim (M.stepEvents evs_ss bSt) (SendPhase3Env pq sOut) :=
      hfit_tail.seq_right hevs_ss
    let Rest314d8 : SepProp :=
      spqrCoinsAfterPlaced ctl x.cur x.rest (x.rest.length - rest'.length) ∗
      tokenInitPlacedAt ∗ CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ RestTail
    have hP3196_eq :
        (CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
          memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
          memRegion (sp + 0x950#64) 928 ∗
          optEpochSecretRegSlotAt A.repAlloc sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
          CryptoVerification.SpqrV1.Top.MessageSerialize.messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
          statesSendPostArmScratch sp ∗
          spqrCoinsAfterPlaced ctl x.cur x.rest (x.rest.length - rest'.length) ∗
          tokenInitPlacedAt ∗ CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ A.pool lim (M.stepEvents evs_ss bSt) sm ∗
          stackAt sp spqrSendCalleeStack) ∗ FrameArm =
        (CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
          optEpochSecretRegSlotAt A.repAlloc sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
          memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
          memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
          memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
          memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
          memRegion (sp + 0x8#64) 8 ∗ memRegion x.ret 72 ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
          A.pool lim (M.stepEvents evs_ss bSt) sm ∗ stackAt sp spqrSendCalleeStack ∗
          memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
          memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
          memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
          CryptoVerification.SpqrV1.Top.MessageSerialize.messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
          stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          spqrSendEncodeJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest314d8) := by
      have hreg := post_3196_regions_eq sp
      calc
        _ = (memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
              memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
              statesSendPostArmScratch sp ∗
              memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
              memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
              memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
            (CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
              CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
              optEpochSecretRegSlotAt A.repAlloc sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
              memRegion x.ret 72 ∗ chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
              A.pool lim (M.stepEvents evs_ss bSt) sm ∗ stackAt sp spqrSendCalleeStack ∗
              memRegion (sp + 0x950#64) 928 ∗
              CryptoVerification.SpqrV1.Top.MessageSerialize.messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
              spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
              spqrSendEncodeJumpTablePlacedAt ∗
              CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest314d8) := by
          dsimp only [FrameArm, Rest314d8]; sep_ac_rfl
        _ = _ := by rw [hreg]; sep_ac_rfl
    rw [hP3196_eq]
    refine step_send_from_314d8_placed (M.stepEvents evs_ss bSt) hA hEx.panic_hook hEx.panicSubOverflow_hook
      hEx.dropChainEpochSlice_raw_ok hEx.dropChunkedStates_ok hC.chainFromPb_ok hC.chainFromVn_ok
      hC.chainAddEpoch_ok hC.chainSendKey_ok hC.chainIntoPb_ok hC.messageSerialize_ok
      hC.statesIntoPb_ok s0 sm sp x.ret (sm.readReg64 .x21) (sm.readReg64 .x27) (sm.readReg64 .x23)
      pq sOut hfit_p3 Rest314d8 R _ hsp_align rfl hchain_raw hpq'_len hcrl_m
      hpc_m hrun_m hsp_m htr_m hx19_m rfl hx22_m rfl hx25_m hx26_m rfl hx28_m hx23_none_m hpstate_m
      ?hφ ?herr ?hok (hvregs_m.trans hvregsf)
    case hφ =>
      rintro s_pan ⟨hch_pan, htr_p⟩
      exact ⟨sendPanics_of_sendChainPhase_panic hdec hinner hfrom hsend0 hch_pan,
        htr_p ▸ List.prefix_refl s0.trace⟩
    case herr =>
      intro err evs_p3 hch hevs_p3 sf' Pf' _ _ hPf' hsp_f hcs_f htr_f
      have ⟨hsend_eq, hdraws_eq, hnp⟩ :=
        send_and_draws_of_sendChainPhase_error hdec hinner hfrom hsend0 hch
      have hevs_all : Env x (evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3)) :=
        henv_active x s0 pq v1 st_states evs_dec evs_fpb (evs_ss ++ evs_p3)
          hlen hrest_len hdec hinner hfrom hevs_dec hevs_fpb
          (by rw [hsend0]; exact SeqEnv.append hevs_ss hevs_p3)
      refine ⟨hsp_f, hcs_f, evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3), hevs_all, ?_⟩
      have hstep_eq :
          M.stepEvents (evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3)) st0 =
            M.stepEvents evs_p3 (M.stepEvents evs_ss bSt) := by
        rw [M.stepEvents_append, M.stepEvents_append]
      rw [hsend_eq, hdraws_eq, hstep_eq]
      refine Entails.pure_right ⟨Nat.sub_le _ _, htr_f, hnp⟩ (Entails.trans hPf' ?_)
      dsimp only [Rest314d8, RestTail, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]
      have hinto_eq :
          CryptoVerification.Cli.SpqrV1.Top.Send.statesIntoPbJumpTablePlacedAt =
            CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt := rfl
      rw [hinto_eq]
      exact Entails.of_eq (by sep_ac_rfl)
    case hok =>
      intro idx msgKey chainPb salt evs_p3 hch hsalt hevs_p3 sf' Pf' _ _ hPf' hsp_f hcs_f htr_f
      have ⟨hsend_eq, hdraws_eq, hnp⟩ :=
        send_and_draws_of_sendChainPhase_ok hdec hinner hfrom hsend0 hch hsalt
      have hevs_all : Env x (evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3)) :=
        henv_active x s0 pq v1 st_states evs_dec evs_fpb (evs_ss ++ evs_p3)
          hlen hrest_len hdec hinner hfrom hevs_dec hevs_fpb
          (by rw [hsend0]; exact SeqEnv.append hevs_ss hevs_p3)
      refine ⟨hsp_f, hcs_f, evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3), hevs_all, ?_⟩
      have hstep_eq :
          M.stepEvents (evs_dec ++ evs_fpb ++ (evs_ss ++ evs_p3)) st0 =
            M.stepEvents evs_p3 (M.stepEvents evs_ss bSt) := by
        rw [M.stepEvents_append, M.stepEvents_append]
      rw [hsend_eq, hdraws_eq, hstep_eq]
      refine Entails.pure_right ⟨Nat.sub_le _ _, htr_f, hnp⟩ (Entails.trans hPf' ?_)
      dsimp only [Rest314d8, RestTail, spqrSendFullRoPlacedAt, spqrSendRoPlacedAt]
      have hinto_eq :
          CryptoVerification.Cli.SpqrV1.Top.Send.statesIntoPbJumpTablePlacedAt =
            CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt := rfl
      rw [hinto_eq]
      exact Entails.of_eq (by sep_ac_rfl)
  · rw [hsend_err] at hfit_tail
    have hct1_err : ∀ v, st.send_ct1_chunk K x.rest ≠ .ok v := by
      intro ⟨outSt, chunk, ek, tape1⟩ hok
      simp [States.send, StatesResult.ofPanic, hok, Bind.bind, Except.bind] at hsend_err
    have hss_nil : StatesSendEnv C.F K (.headerReceived st) x.rest [] := by
      dsimp only [StatesSendEnv, StatesSendEnvOfEnv]
      cases h : st.send_ct1_chunk K x.rest with
      | ok v => exact False.elim (hct1_err v h)
      | error _ => rfl
    have hfit_hr :
        FitsEnv M lim bSt
          LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget.HeaderReceived1aEnv :=
      hfit_tail.seq_right hss_nil
    have hpan : (spqrV1 C.F K).sendPanics x.st.bytes x.rest :=
      sendPanics_of_statesSend_panic hdec hinner hfrom hsend_err
    let FramePan : SepProp :=
      ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      CryptoVerification.SpqrV1.Top.DecodeState.optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
      CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
      (memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
       memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
       memRegion (sp + 0x590#64) 920 ∗
       (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp)) ∗
      memRegion x.ret 72 ∗ statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0 ∗
      x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
      tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
      CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
      CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt
    have hpre_pan :
        (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          CryptoVerification.SpqrV1.Top.DecodeState.optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
          CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
          memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
         (x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
          (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
           CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
           CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt)) ⊢
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗ statesSendPreArmScratch sp) ∗ FramePan := by
      have hreg := pre_309cc_regions_eq sp
      refine Entails.of_eq ?_
      calc
        _ = (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
              memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
            (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
              chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
              ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
              CryptoVerification.SpqrV1.Top.DecodeState.optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
              CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
              memRegion x.ret 72 ∗ statesFromPbJumpTablePlacedAt ∗
              spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0 ∗
              x.st.at A.repAlloc ∗ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
              tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
              spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
              CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
              CryptoVerification.SpqrV1.GF.UnacceleratedMul.reduceTablePlacedAt) := by sep_ac_rfl
        _ = _ := by dsimp only [FramePan]; rw [hreg]; sep_ac_rfl
    exact SepWPp.weaken_pre hpre_pan
      (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget.step_send_arm_headerReceived_encaps1_none_ofEnv_placed
        (R := R) (Frame := FramePan)
        hA hEx.allocZeroed_hook hC.coinsFill_ok hEx.mlkemEncaps1_hook hEx.unwrapFailed_hook
        sp x.cur x.rest (by omega) st hencaps hfit_hr hpan hcrlf hpcf hrunf hspf hfsp_align
        htrf hx24 hx26 hx28 rfl)

theorem spqrSendBudgetActiveContinuation_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext) :
    SpqrSendBudgetActiveContinuationPlaced M A lim ctl C.F K
      DecodeStatePlacedEnv StatesFromPbEnv (SpqrSendCoinsExactEnv C.F K) ext := by
  refine spqrSendBudgetActiveContinuation_placed_ok_ofEnv hA hC hEx ?_ ?_
  · intro x s0 st0 pq v1 st_states evs_dec evs_fpb _ _ hfits0 hdec hinner hfrom hevs_dec hevs_fpb evs_tail
    have hevs_dec' : DecodeStatePlacedEnv { st := x.st, outPtr := 0#64 } evs_dec := hevs_dec
    have hevs_fpb' : StatesFromPbEnv { out := 0#64, pbA := 0#64, pb := v1 } evs_fpb := hevs_fpb
    cases h : st_states.send K x.rest with
    | ok val =>
      rcases val with ⟨sOut, rest'⟩
      intro htail
      refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
        (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
      simp only [SpqrSendCoinsExactEnv, hdec, hinner, hfrom, h]
      rw [List.append_assoc]
      exact SeqEnv.append hevs_dec' (SeqEnv.append hevs_fpb' htail)
    | error err =>
      cases err with
      | err e =>
        intro htail
        refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
          (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
        simp only [SpqrSendCoinsExactEnv, hdec, hinner, hfrom, h]
        rw [List.append_assoc]
        exact SeqEnv.append hevs_dec' (SeqEnv.append hevs_fpb' htail)
      | panic p =>
        intro htail
        refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
          (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
        simp only [SpqrSendCoinsExactEnv, hdec, hinner, hfrom, h]
        rw [List.append_assoc]
        exact SeqEnv.append hevs_dec' (SeqEnv.append hevs_fpb' htail)
  · intro x s0 pq v1 st_states evs_dec evs_fpb evs_tail _ _ hdec hinner hfrom hevs_dec hevs_fpb htail
    simp only [SpqrSendCoinsExactEnv, hdec, hinner, hfrom]
    rw [List.append_assoc]
    refine SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb ?_)
    cases h : st_states.send K x.rest with
    | ok val =>
      rcases val with ⟨sOut, rest'⟩
      rw [h] at htail
      exact htail
    | error err =>
      cases err with
      | err e =>
        rw [h] at htail
        exact htail
      | panic p =>
        rw [h] at htail
        exact False.elim htail

theorem spqrSendCoins_placed_ok_of_contracts_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {Env : SendCall → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext)
    (hfits_decode : ∀ (x : SendCall) (s0 : State) (st0 : M.σ),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length → FitsEnv M lim st0 (Env x) →
      FitsEnv M lim st0
        (DecodeStatePlacedEnv { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 }))
    (hfits_from_pb : ∀ (x : SendCall) (s0 : State) (st0 : M.σ)
        (pq : PqRatchetState) (v1 : V1State) (evs_dec : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → 64 ≤ x.rest.length → FitsEnv M lim st0 (Env x) →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      DecodeStatePlacedEnv { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FitsEnv M lim (M.stepEvents evs_dec st0)
        (StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                           pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 }))
    (henv_dec_err : ∀ (x : SendCall) (s0 : State) (e : Error) (evs_dec : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → spqrDecodeState x.st.bytes = .error e →
      DecodeStatePlacedEnv { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      Env x evs_dec)
    (henv_none : ∀ (x : SendCall) (s0 : State) (pq : PqRatchetState)
        (evs_dec evs_drop : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 → spqrDecodeState x.st.bytes = .ok pq → pq.inner = none →
      DecodeStatePlacedEnv { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      FreeOnlyEvs evs_drop → Env x (evs_dec ++ evs_drop))
    (henv_err : ∀ (x : SendCall) (s0 : State) (pq : PqRatchetState) (v1 : V1State) (err : Error)
        (evs_dec evs_fpb evs_drop : List AllocEvent),
      x.st.bytes.length < 2 ^ 32 →
      spqrDecodeState x.st.bytes = .ok pq → pq.inner = some (.v1 v1) →
      States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 = .error (.err err) →
      DecodeStatePlacedEnv { st := x.st, outPtr := (s0.sp - 0x1f80#64) + 0x1260#64 } evs_dec →
      StatesFromPbEnv { out := (s0.sp - 0x1f80#64) + 0x1260#64,
                        pbA := (s0.sp - 0x1f80#64) + 0xb0#64, pb := v1 } evs_fpb →
      FreeOnlyEvs evs_drop → Env x ((evs_dec ++ evs_fpb) ++ evs_drop))
    (hcont : SpqrSendBudgetActiveContinuationPlaced M A lim ctl C.F K
      DecodeStatePlacedEnv StatesFromPbEnv Env ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K) Env)) :=
  spqrSendCoins_placed_ok_of_contracts_and_continuation_ofEnv hC
    hfits_decode hfits_from_pb henv_dec_err henv_none henv_err hcont

theorem spqrSendCoins_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K) (SpqrSendCoinsExactEnv C.F K))) := by
  refine spqrSendCoins_placed_ok_of_contracts_ofEnv hA hC hEx ?_ ?_ ?_ ?_ ?_
    (spqrSendBudgetActiveContinuation_placed_ok hA hC hEx)
  · intro x s0 st0 _ _ hfits0 evs hevs
    apply hfits0 evs
    have hevs' : DecodeStatePlacedEnv { st := x.st, outPtr := 0#64 } evs := hevs
    dsimp only [SpqrSendCoinsExactEnv]
    cases spqrDecodeState x.st.bytes with
    | error _ => exact hevs'
    | ok pq =>
      dsimp only
      cases pq.inner with
      | none => dsimp only [SeqEnv]; exact Or.inl hevs'
      | some inner =>
        cases inner with
        | v1 _ => dsimp only [SeqEnv]; exact Or.inl hevs'
  · intro x s0 st0 pq v1 evs_dec _ _ hfits0 hdec hinner hevs_dec evs_fpb hevs_fpb
    have hevs_dec' : DecodeStatePlacedEnv { st := x.st, outPtr := 0#64 } evs_dec := hevs_dec
    have hevs_fpb' : StatesFromPbEnv { out := 0#64, pbA := 0#64, pb := v1 } evs_fpb := hevs_fpb
    refine ((fitsEvents_append M lim evs_dec evs_fpb st0).mp
      (hfits0 (evs_dec ++ evs_fpb) ?_)).2
    simp only [SpqrSendCoinsExactEnv, hdec, hinner]
    cases States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 with
    | error err =>
      cases err with
      | panic _ => exact SeqEnv.append hevs_dec' hevs_fpb'
      | err _ => exact SeqEnv.append hevs_dec' (SeqEnv.inl hevs_fpb')
    | ok _ => exact SeqEnv.append hevs_dec' (SeqEnv.inl hevs_fpb')
  · intro x s0 e evs_dec _ hdec hevs_dec
    simp only [SpqrSendCoinsExactEnv, hdec]
    exact hevs_dec
  · intro x s0 pq evs_dec evs_drop _ hdec hinner hevs_dec hevs_drop
    simp only [SpqrSendCoinsExactEnv, hdec, hinner]
    exact SeqEnv.append hevs_dec hevs_drop
  · intro x s0 pq v1 err evs_dec evs_fpb evs_drop _ hdec hinner hfrom hevs_dec hevs_fpb hevs_drop
    simp only [SpqrSendCoinsExactEnv, hdec, hinner, hfrom]
    rw [List.append_assoc]
    exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb hevs_drop)

theorem spqr_send_placed_ok_blockProgram_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 427 (Rust.withPanics ext))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K) (SpqrSendCoinsExactEnv C.F K))) := by
  have hok := spqrSendCoins_placed_ok_of_contracts hA hC hEx
  rwa [← CryptoVerification.IsLsBlockProg.eq_blockProgram (prog := spqrSendPlacedProg ext)]

theorem spqr_send_placed_ok_blockProgram_ext_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 427 ext)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K) (SpqrSendCoinsExactEnv C.F K))) := by
  have heq : Rust.withPanics ext = ext := by
    funext sym; unfold Rust.withPanics; split
    · next h => exact (hp sym h).symm
    · rfl
  simpa only [heq] using spqr_send_placed_ok_blockProgram_of_contracts hA hC hEx

theorem spqrSendCoins_placed_ok_at_prog_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide)
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext) :
    subroutine_ok callerProg (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K) (SpqrSendCoinsExactEnv C.F K))) :=
  ls_subroutine_ok_of_blockProgram_cro (callerProg := callerProg)
    (spqr_send_placed_ok_blockProgram_of_contracts hA hC hEx) hi

theorem spqrSendCoins_placed_ok_at_prog_ext_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide)
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContracts M H_inner A lim ctl C K ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext) :
    subroutine_ok callerProg (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K) (SpqrSendCoinsExactEnv C.F K))) :=
  ls_subroutine_ok_of_blockProgram_cro (callerProg := callerProg)
    (spqr_send_placed_ok_blockProgram_ext_of_contracts hp hA hC hEx) hi

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget
