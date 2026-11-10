/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import ProofLib.SepLogic.WPp

/-!
# Cap-Free & Guarded-Tight `spqr::send::<Coins>` and `SpqrV1PlacedSeamsOfEnv`

**Checked by Lean.**

Proves cap-free and domain-guarded placed budget contracts for `spqr::send::<Coins>` (Block 427)
and `SpqrV1PlacedSeamsOfEnv` on `cliGhostExterns`:
- Unconditional cap-free contracts at `SpqrSendCoinsTightLinkedEnv` and assembly of
  `SpqrV1PlacedSeamsOfEnv` at `(InitialStateEnv, CliSpqrRecvTightLinkedEnv,
  SpqrSendCoinsTightLinkedEnv)`.
- Leaf-parametric (`hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv`) and implication/`ite`-guarded
  allocation envelopes. When a domain guard is false, the guarded envelope degenerates to
  `fun _ => True`, whose `FitsEnv` precondition is unsatisfiable (`hpt_not_fitsEnv_true`) because
  `AllocEvent.alloc (2 ^ 64)` violates `withinMaxAlloc`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (ls_subroutine_ok_of_blockProgram_cro spqrCoinsAfterPlaced spqrCoinsAtPlaced
   spqrLogLevelZeroPlacedAt spqrSendDropJumpTablePlacedAt spqrSendEncodeJumpTablePlacedAt
   spqrSendFullRoPlacedAt spqrSendRoPlacedAt statesFromPbJumpTablePlacedAt)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB Error MlKem PqRatchetState States StatesResult V1Send V1State
   pbToPqRatchetState pqRatchetStateToPb spqrAuthApi spqrDecodeState spqrHkdfWith spqrPolyApi
   spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SendCall VecArg keys_ls_subroutine_ok_of_block_cro
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SpqrV1.ChainProofs (hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt optVersionNegotiationPBAt)
open CryptoVerification.SpqrV1.States.FromPb
  (StatesFromPbGhost resultChunkedStatesAt statesFromPbStackX v1StatePtsBound)
open CryptoVerification.SpqrV1.States.IntoPb (statesIntoPbJumpTablePlacedAt)
open CryptoVerification.SpqrV1.States.Leaves
  (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap decodeStateResultAt decodeStateStackX
   optProtoInnerStateAt_canonical_eq_drop optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost messageAt messageSerializeStackX)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesAt_entails_polyEncoderValid chunkedStatesWord0
   decodeState_spqrDeps_of_spqrDecodeState_ok headerReceived_rootKey_le_rawV1State
   optEpochSecretRegSlotAt optVN_30_to_proto post_3196_regions_eq
   pqRatchetStatePBEncodedLen_lt_of_send pre_309cc_regions_eq
   sendPanics_of_sendChainPhase_panic sendPanics_of_statesSend_panic
   send_and_draws_of_sendChainPhase_error send_and_draws_of_sendChainPhase_ok
   spqrSendCalleeStack spqrSendSavedRegs stackRestA stackRestB0_950
   stackRestC stackRestCF0_1F20 statesPolyEncoderValid statesSendArmOffset
   statesSendPostArmScratch statesSendPreArmScratch
   statesSend_ok_or_headerReceived_encaps1_of_le_64)
open CryptoVerification.SpqrV1.Top.StateSize
  (decodeState_spqrDeps_raw_le optRaw optRaw_some rawChain rawPqInner rawPqState rawV1State rawVN)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FreeOnlyEvs
   MallocngCostModelIface MallocngCostModelSound RustCliAllocBudget SeqEnv fitsEvents_append
   rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget
  (drop_chain_epoch_slice_local1_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
  (drop_chain_epoch_slice_local1_placed_ok_x drop_proto_spqr_chain_placed_ok_x
   ls_subroutine_ok_of_blockProgram_plain)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX SpqrSendPlacedContractsOfEnv spqrSendPlacedEntry
   spqrSendPlacedProg spqrSendStatesJumpTablePlacedAt)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget
  (SpqrSendBudgetActiveContinuationPlaced
   spqrSendCoins_placed_ok_of_contracts_and_continuation_ofEnv spqrSendPhase1Rest0)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (decodeStatePlacedSpecXOfEnv messageSerializeSpecXOfEnv spqrSendCoinsPlacedSpecOfEnv
   spqrSendCoinsPlacedSpecTOfEnv statesFromPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudget
  (step_send_statesSend_tight_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (StatesSendEnvOfEnv StatesSendTightEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (HeaderReceived1aEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
  (SendPhase3EnvOfEnv step_send_from_314d8_ofEnv_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget (SpqrSendExtraContractsPlaced)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget
  (step_send_arm_headerReceived_encaps1_none_ofEnv_placed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudget mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
  (FineSmallEvs fineSmallEventCost fineSmallRealloc_80 fineSmallTraceCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers (MessageSerializeTightEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
  (cliSpqrSend_chainFromPb_ok cliSpqrSend_chainFromVn_ok cliSpqrSend_chainIntoPb_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
  (cliSpqrSend_decodeState_closed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (CliSpqrRecvTightLinkedEnv DecodeStateBytesEnv SpqrSendCoinsTightBytesEnv
   SpqrSendCoinsTightLinkedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
  (hpo_cliLibcruxHmac_budget_hookSat hpo_cliLibcruxHmac_mallocngHook_budget_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliExternsPlaced_noAllocShimBudget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliAuthMacHdr_placed_ok cliAuthUpdate_placed_ok cliChainAddEpoch_placed_ok
   cliChainSendKey_placed_ok cliEncodeBytesPlacedOkX cliEncodeVarintPlacedOkX
   cliEncodeVarint_placed_ok cliHkdfToVec_placed_ok cliPolyNextChunkPlacedOkX
   cliSpqrSendAllocContractsPlaced cliSpqrSendAllocContractsPlacedExt
   cliSpqrSend_coinsFill_ok_cli cliStatesPlacedSeams spqrSendExtraContractsPlaced_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
  (cliStatesIntoPb_sendCoins_exact_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
  (spqrV1PlacedSeamsOfEnv_mallocngHook_of_sendCoins spqrV1PlacedSeamsOfEnv_of_sendCoins
   spqrV1PlacedSeamsOfEnv_tightLinked_of_sendCoins)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpec spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
  (MessageSerializeEnv messageSerializeEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget
  (messageSerialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)

/-!
## 1. Leaf-Parametric & Guarded `spqr::send::<Coins>` Envelopes and `FitsEnv` Unsatisfiability
-/

/-- Unsatisfiability of `FitsEnv M lim st0 (fun _ => True)`: the single allocation
event `AllocEvent.alloc (2 ^ 64)` belongs to `fun _ => True`, yet violates `withinMaxAlloc`
(`2 ^ 64 < 2 ^ 64`). -/
theorem hpt_not_fitsEnv_true (M : AllocCostModel) (lim : BudgetLimits) (st0 : M.σ) :
    ¬ FitsEnv M lim st0 (fun _ => True) :=
  fun h => absurd (h [AllocEvent.alloc (2 ^ 64)] trivial).1.1 (by decide)

/-- More generally, no `Env` containing `AllocEvent.alloc (2 ^ 64)` can satisfy `FitsEnv`. -/
theorem hpt_not_fitsEnv_of_univ {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {Env : List AllocEvent → Prop} (hUniv : ∀ evs, Env evs) :
    ¬ FitsEnv M lim st0 Env :=
  fun h => absurd (h [AllocEvent.alloc (2 ^ 64)] (hUniv _)).1.1 (by decide)

/-- Tight `<Message>::serialize` bridge: every trace in
`MessageSerializeBudget.MessageSerializeEnv spqrPolyApi x` satisfies
`SpqrSendTightHelpers.MessageSerializeTightEnv` (`FineSmallEvs 2 9135 80`). -/
theorem hpt_messageSerializeEnv_to_tight
    (x : MessageSerializeGhost spqrPolyApi) {evs : List AllocEvent}
    (h : MessageSerializeEnv spqrPolyApi x evs) :
    MessageSerializeTightEnv evs := by
  subst h
  have h40 : FineSmallEvs 1 738 80 (rustAllocEvents 40 1) :=
    FineSmallEvs.rustAlloc (by decide) (by decide) (smallAllocCost_le_738_of_le_44 (by decide))
  have h80 : FineSmallEvs 1 8397 80 (rustReallocEvents 40 80 1) := by
    refine ⟨by decide, ?_, ?_⟩
    · simp only [rustReallocEvents]
      exact Nat.le_refl 8397
    · simp [rustReallocEvents, eventStepReq, eventStepAlign]
  have halloc : MessageSerializeTightEnv (rustAllocEvents 40 1) :=
    h40.mono (by decide) (by decide) (by decide)
  have hboth : MessageSerializeTightEnv (rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1) :=
    (h40.append h80).mono (by decide) (by decide) (by decide)
  unfold messageSerializeEvents
  cases x.msg.payload <;> dsimp only <;>
    first | exact halloc | (split <;> [exact halloc; exact hboth])

/-- Leaf-parametric Block-`427` `SpqrSendBudgetEnv` parameterized by `DecBytesEnv` (`spqr::decode_state`)
and `FromPbValEnv` (`<States>::from_pb`), keeping `StatesSendTightEnv`,
`MessageSerializeEnv spqrPolyApi`, and `StatesIntoPbExactEnv` exact and cap-free.
- At `(DecodeStateBytesEnv, StatesFromPbEnv)`, this is definitionally (`rfl`) equal to
  `SpqrExactEnvDefs.SpqrSendCoinsTightBytesEnv F K` (and on `sc : SendCall` to
  `SpqrExactEnvDefs.SpqrSendCoinsTightLinkedEnv F K sc`).
- At `(fun _ => DecodeStateTightEnv, fun _ => StatesFromPbTightEnv)`, this is definitionally (`rfl`)
  equal to the guarded encrypt slot's `sendEnv`. -/
def hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv (F : ShaCompress) (K : MlKem)
    (DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop)
    (FromPbValEnv : V1State → List AllocEvent → Prop) : SpqrSendBudgetEnv :=
  fun stBs rest evs =>
    let decEnv : List AllocEvent → Prop := DecBytesEnv stBs
    let fpbEnv (v1 : V1State) : List AllocEvent → Prop := FromPbValEnv v1
    match spqrDecodeState stBs with
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
               (SeqEnv (StatesSendTightEnv F K st_states rest)
                 (match st_states.send K rest with
                  | .ok (sOut, _) =>
                    SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv
                      0#64 pq sOut
                  | .error (.err _) => FreeOnlyEvs
                  | .error (.panic _) => HeaderReceived1aEnv)))
          evs

/-- `SendCall`-indexed view of `hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv`. -/
abbrev hpt_SpqrSendCoinsOfDecodeFromPbEnv (F : ShaCompress) (K : MlKem)
    (DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop)
    (FromPbValEnv : V1State → List AllocEvent → Prop)
    (x : SendCall) (evs : List AllocEvent) : Prop :=
  hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv F K DecBytesEnv FromPbValEnv x.st.bytes x.rest evs

/-- Constant-leaf specialization of `hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv` (parameterized by
state-independent `decEnv, fpbEnv : List AllocEvent → Prop`, e.g. `DecodeStateTightEnv` or
`DecodeStateTight128Env` and `StatesFromPbTightEnv`). -/
abbrev hpt_SpqrSendCoinsConstLeavesBytesEnv (F : ShaCompress) (K : MlKem)
    (decEnv fpbEnv : List AllocEvent → Prop) : SpqrSendBudgetEnv :=
  hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv F K (fun _ => decEnv) (fun _ => fpbEnv)

/-- Canonical `SpqrCodecPeakSpec` (`DecodeStateTightEnv`, `StatesFromPbTightEnv`) specialization of
`hpt_SpqrSendCoinsConstLeavesBytesEnv`. -/
abbrev hpt_SpqrSendCoinsCodecTightBytesEnv (F : ShaCompress) (K : MlKem) : SpqrSendBudgetEnv :=
  hpt_SpqrSendCoinsConstLeavesBytesEnv F K DecodeStateTightEnv StatesFromPbTightEnv

/-- Implication-guarded `SpqrSendBudgetEnv` (`Guard stBs → BaseBytesEnv stBs rest evs`: false-guard branch reduces to `True`, whose `FitsEnv` is unsatisfiable by
`hpt_not_fitsEnv_of_univ`). -/
def hpt_SpqrSendGuardedImplBytesEnv
    (Guard : List (BitVec 8) → Prop) (BaseBytesEnv : SpqrSendBudgetEnv) : SpqrSendBudgetEnv :=
  fun stBs rest evs => Guard stBs → BaseBytesEnv stBs rest evs

/-- `if-then-else`-guarded `SpqrSendBudgetEnv` (`if Guard stBs then BaseBytesEnv stBs rest evs else True`). -/
noncomputable def hpt_SpqrSendGuardedIteBytesEnv
    (Guard : List (BitVec 8) → Prop) (BaseBytesEnv : SpqrSendBudgetEnv) : SpqrSendBudgetEnv :=
  fun stBs rest evs =>
    haveI := Classical.propDecidable (Guard stBs)
    if Guard stBs then BaseBytesEnv stBs rest evs else True

theorem hpt_spqrSendCoinsOfDecodeFromPbEnv_eq_tightLinked (F : ShaCompress) (K : MlKem) :
    hpt_SpqrSendCoinsOfDecodeFromPbEnv F K DecodeStateBytesEnv StatesFromPbEnv =
      SpqrSendCoinsTightLinkedEnv F K :=
  rfl

theorem hpt_spqrSendCoinsOfDecodeFromPbBytesEnv_eq_tightBytes (F : ShaCompress) (K : MlKem) :
    hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv F K DecodeStateBytesEnv StatesFromPbEnv =
      SpqrSendCoinsTightBytesEnv F K :=
  rfl

private theorem hpt_seqEnv_mono_left
    {P P' Q : List AllocEvent → Prop} {evs : List AllocEvent}
    (hP : ∀ e, P e → P' e) (h : SeqEnv P Q evs) :
    SeqEnv P' Q evs :=
  h.imp (hP evs) fun ⟨e1, e2, heq, h1, h2⟩ => ⟨e1, e2, heq, hP e1 h1, h2⟩

/-- Pointwise monotonicity of `SpqrSendCoinsTightLinkedEnv F K x` into
`hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv F K DecBytesEnv FromPbValEnv x.st.bytes x.rest` given
decode/from_pb inclusions on `x.st.bytes` (note `hFromPb` receives the decoded `pq` and `v1`
equations `spqrDecodeState x.st.bytes = .ok pq` and `pq.inner = some (.v1 v1)`). -/
theorem hpt_spqrSendCoinsTightLinked_mono_leaves
    {F : ShaCompress} {K : MlKem}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    {x : SendCall} {evs : List AllocEvent}
    (hDec : ∀ e, DecodeStateBytesEnv x.st.bytes e → DecBytesEnv x.st.bytes e)
    (hFromPb : ∀ pq v1 e,
      spqrDecodeState x.st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      StatesFromPbEnv v1 e → FromPbValEnv v1 e)
    (hevs : SpqrSendCoinsTightLinkedEnv F K x evs) :
    hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv F K DecBytesEnv FromPbValEnv x.st.bytes x.rest evs := by
  dsimp only [SpqrSendCoinsTightLinkedEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv] at hevs ⊢
  cases hdec : spqrDecodeState x.st.bytes with
  | error _ =>
    rw [hdec] at hevs
    exact hDec evs hevs
  | ok pq =>
    rw [hdec] at hevs
    dsimp only at hevs ⊢
    cases hinner : pq.inner with
    | none =>
      rw [hinner] at hevs
      exact hpt_seqEnv_mono_left hDec hevs
    | some inner =>
      cases inner with
      | v1 v1 =>
        rw [hinner] at hevs
        dsimp only at hevs ⊢
        rcases hevs with h1 | ⟨e1, e2, rfl, h1, h2⟩
        · exact Or.inl (hDec evs h1)
        · refine SeqEnv.append (hDec e1 h1) ?_
          cases hfpb : States.from_pb spqrPolyApi (spqrAuthApi F) v1 with
          | error err =>
            cases err with
            | panic _ =>
              rw [hfpb] at h2
              exact hFromPb pq v1 e2 hdec hinner h2
            | err _ =>
              rw [hfpb] at h2
              exact hpt_seqEnv_mono_left (hFromPb pq v1 · hdec hinner) h2
          | ok st_states =>
            rw [hfpb] at h2
            exact hpt_seqEnv_mono_left (hFromPb pq v1 · hdec hinner) h2

/-!
## 2. Exact Leaf Bridges on `spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))`
-/

private theorem hpt_hExt_withPanics_id
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym _
  exact congrFun (withPanics_cliGhostExterns mmpl gh W) sym

private theorem hpt_cliGhostExterns_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

/-- Block `352` (`<Message>::serialize`) at the exact cap-free envelope
`MessageSerializeBudget.MessageSerializeEnv spqrPolyApi` on `blockProgram lsmpl 352`. -/
theorem hpt_cliMessageSerialize_exact_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 352
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl
        (messageSerializeSpecXOfEnv spqrPolyApi M A lim (MessageSerializeEnv spqrPolyApi))) := by
  have hc := cliSpqrSendAllocContractsPlacedExt mmpl gh W hA.toCliGhostAllocHooks (fun _ _ => rfl)
  have hraw := messageSerialize_placed_ok_of_hooks spqrPolyApi A lim
    (cliGhostExterns gh (cliExternsPlaced mmpl W))
    hc.handle_error
    (hookSat_of_eq (hpt_hExt_withPanics_id mmpl gh W _ (by decide))
      (cliExternsPlaced_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    hc.alloc hc.realloc
    (cliEncodeVarintPlacedOkX mmpl gh W hA (fun _ _ => rfl))
  have hcro := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hraw
  exact subroutine_ok_mono hcro
    (fun _ _ _ hpre => hpre)
    (fun (x, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded, messageSerializeSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget.messageSerializeSpecX] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
          (⌜MessageSerializeEnv spqrPolyApi x evs⌝ ∗
            ((messageAt spqrPolyApi x.msgA x.msg ∗
                vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
                A.pool lim (M.stepEvents evs stB) sf ∗
                stackAt s0.sp messageSerializeStackX) ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨htr, hevs, hrest⟩
      have hgoal : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ MessageSerializeEnv spqrPolyApi x evs⌝ ∗
          ((messageAt spqrPolyApi x.msgA x.msg ∗
              vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
              A.pool lim (M.stepEvents evs stB) sf ∗
              stackAt s0.sp messageSerializeStackX) ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨htr, hevs⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun _ _ _ _ hp => hp)

/-- Block `352` (`<Message>::serialize`) lifted to `spqrSendPlacedProg` at exact
`MessageSerializeBudget.MessageSerializeEnv spqrPolyApi`. -/
theorem hpt_cliSpqrSend_messageSerialize_exact_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl
        (messageSerializeSpecXOfEnv spqrPolyApi M A lim (MessageSerializeEnv spqrPolyApi))) :=
  ls_subroutine_ok_of_blockProgram_cro
    (hpt_cliMessageSerialize_exact_placed_ok mmpl gh W hA)

/-- Block `325` (`spqr::decode_state`) on `spqrSendPlacedProg` lifted from
`SpqrChunkedMergePlacedInstBudget.cliSpqrSend_decodeState_closed_ok` to
`SeamSpecsPlacedBudget.decodeStatePlacedSpecXOfEnv` for any `DecBytesEnv` containing
`DecodeStateBytesEnv`. -/
theorem hpt_cliSpqrSend_decodeState_xOfEnv_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hDecSub : ∀ bs evs, DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv canonicalV1InnerHeap M A lim
          (fun g => DecBytesEnv g.st.bytes))) := by
  have hok := cliSpqrSend_decodeState_closed_ok mmpl gh W hA
    (ext := cliGhostExterns gh (cliExternsPlaced mmpl W)) (fun _ _ => rfl)
  exact subroutine_ok_mono hok
    (fun (g, stB) R s0 hpre => by
      dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpec, spqrDecodeStatePlacedSpecOfEnv,
        decodeStatePlacedSpecXOfEnv] at hpre ⊢
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.outPtr ∧ s0.readReg64 .x0 = g.st.v ∧
            g.st.bytes.length < 2 ^ 32 ∧ FitsEnv M lim stB (DecBytesEnv g.st.bytes)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗ memRegion g.outPtr 352 ∗
              A.pool lim stB s0 ∗ stackAt s0.sp decodeStateStackX ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'
      rcases hpre' with ⟨⟨hx8, hx0, hlen, hfit⟩, hrest⟩
      have hgoal : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.outPtr ∧ s0.readReg64 .x0 = g.st.v ∧
            g.st.bytes.length < 2 ^ 32 ∧ FitsEnv M lim stB (DecodeStateEnv g)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗ memRegion g.outPtr 352 ∗
              A.pool lim stB s0 ∗ stackAt s0.sp decodeStateStackX ∗ R)) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx8, hx0, hlen, hfit.mono (hDecSub g.st.bytes)⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun (g, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpec, spqrDecodeStatePlacedSpecOfEnv,
        decodeStatePlacedSpecXOfEnv] at hpost ⊢
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ DecodeStateEnv g evs⌝ ∗
          (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗
            decodeStateResultAt canonicalV1InnerHeap A.repAlloc g.outPtr
              (spqrDecodeState g.st.bytes) ∗
            A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp decodeStateStackX ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨⟨htr, hevs⟩, hrest⟩
      have hgoal : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ DecBytesEnv g.st.bytes evs⌝ ∗
          (v1StateJumpTablesPlacedAt ∗ g.st.at A.repAlloc ∗
            decodeStateResultAt canonicalV1InnerHeap A.repAlloc g.outPtr
              (spqrDecodeState g.st.bytes) ∗
            A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp decodeStateStackX ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨htr, hDecSub g.st.bytes evs hevs⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun _ _ _ _ hp => hp)

/-- Block `333` (`<States>::from_pb`) on `spqrSendPlacedProg` lifted from
`(cliStatesPlacedSeams mmpl gh W hA hHmac).statesFromPb_on` to
`SeamSpecsPlacedBudget.statesFromPbPlacedSpecXOfEnv` for any `FromPbValEnv` containing
`FromPb.DefsBudget.StatesFromPbEnv`. -/
theorem hpt_cliSpqrSend_statesFromPb_xOfEnv_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hFromPbSub : ∀ v1 evs, StatesFromPbEnv v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedSpecXOfEnv M A lim W.C.F (fun g => FromPbValEnv g.pb))) := by
  have hok : subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX
          M A lim W.C.F)) :=
    (cliStatesPlacedSeams mmpl gh W hA hHmac).statesFromPb_on
  have hjt_eq :
      CryptoVerification.SpqrV1.States.FromPb.statesFromPbJumpTablePlacedAt =
        statesFromPbJumpTablePlacedAt := rfl
  exact subroutine_ok_mono hok
    (fun (g, stB) R s0 hpre => by
      dsimp only [withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv,
        statesFromPbPlacedSpecXOfEnv] at hpre ⊢
      rw [hjt_eq]
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.out ∧ s0.readReg64 .x0 = g.pbA ∧
            v1StatePtsBound g.pb ∧ FitsEnv M lim stB (FromPbValEnv g.pb)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (memRegion g.out chunkedStatesSize ∗
              optProtoInnerStateAt A.repAlloc g.pbA g.pb.innerState ∗
              statesFromPbJumpTablePlacedAt ∗ A.pool lim stB s0 ∗
              stackAt s0.sp statesFromPbStackX ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'
      rcases hpre' with ⟨⟨hx8, hx0, hpts, hfit⟩, hrest⟩
      have hgoal : s0.mem ⊨
          ⌜s0.readReg64 .x8 = g.out ∧ s0.readReg64 .x0 = g.pbA ∧
            v1StatePtsBound g.pb ∧ FitsEnv M lim stB (StatesFromPbEnv g.pb)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            (memRegion g.out chunkedStatesSize ∗
              optProtoInnerStateAt A.repAlloc g.pbA g.pb.innerState ∗
              statesFromPbJumpTablePlacedAt ∗ A.pool lim stB s0 ∗
              stackAt s0.sp statesFromPbStackX ∗ R)) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx8, hx0, hpts, hfit.mono (hFromPbSub g.pb)⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun (g, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv,
        statesFromPbPlacedSpecXOfEnv] at hpost ⊢
      rw [hjt_eq] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ StatesFromPbEnv g.pb evs⌝ ∗
          (resultChunkedStatesAt A.repAlloc (F := W.C.F) g.out
              (States.from_pb spqrPolyApi (spqrAuthApi W.C.F) g.pb) ∗
            memRegion g.pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs stB) sf ∗
            stackAt s0.sp statesFromPbStackX ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨⟨htr, hevs⟩, hrest⟩
      have hgoal : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ FromPbValEnv g.pb evs⌝ ∗
          (resultChunkedStatesAt A.repAlloc (F := W.C.F) g.out
              (States.from_pb spqrPolyApi (spqrAuthApi W.C.F) g.pb) ∗
            memRegion g.pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs stB) sf ∗
            stackAt s0.sp statesFromPbStackX ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨htr, hFromPbSub g.pb evs hevs⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal)
    (fun _ _ _ _ hp => hp)

private theorem hpt_cliSpqrSend_chainAddEpoch_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 368)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainAddEpoch_placed_ok mmpl gh W hA (hpt_hExt_withPanics_id mmpl gh W)))

private theorem hpt_cliSpqrSend_chainSendKey_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 367)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainSendKey_placed_ok mmpl gh W hA (hpt_hExt_withPanics_id mmpl gh W)))

private theorem hpt_cliSpqrSend_coinsFill_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    CoinsFillPlacedOkX (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  ls_subroutine_ok_of_blockProgram_plain (cliSpqrSend_coinsFill_ok_cli mmpl gh W hA)

private theorem hpt_cliSpqrSend_encodeVarint_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliEncodeVarint_placed_ok mmpl gh W hA (fun _ _ => rfl))

/-- Complete cap-free `SpqrSendPlacedContractsOfEnv` assembly on
`cliGhostExterns gh (cliExternsPlaced mmpl W)` for any `(DecBytesEnv, FromPbValEnv)` containing
`(DecodeStateBytesEnv, FromPb.DefsBudget.StatesFromPbEnv)`. -/
theorem hpt_spqrSendPlacedContractsOfEnv_of_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hDecSub : ∀ bs evs, DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hFromPbSub : ∀ v1 evs, StatesFromPbEnv v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrSendPlacedContractsOfEnv M canonicalV1InnerHeap A lim 0#64 W.C W.Q.K
      (fun g => DecBytesEnv g.st.bytes)
      (fun g => FromPbValEnv g.pb)
      StatesIntoPbExactEnv
      (MessageSerializeEnv spqrPolyApi)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget.PolyNextChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.HeaderSentSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1ReceivedSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.EkReceivedCt1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct2SampledSendCt2ChunkEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hAlloc := cliSpqrSendAllocContractsPlaced mmpl gh W hA.toCliGhostAllocHooks
  have hS := cliStatesPlacedSeams mmpl gh W hA hHmac
  exact
    { h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A.repAlloc
      alloc := hAlloc
      coinsFill_ok := hpt_cliSpqrSend_coinsFill_on mmpl gh W hA.toCliGhostAllocHooks
      decodeState_ok := hpt_cliSpqrSend_decodeState_xOfEnv_on mmpl gh W hDecSub hA.toCliGhostAllocHooks
      statesFromPb_ok := hpt_cliSpqrSend_statesFromPb_xOfEnv_on mmpl gh W hFromPbSub hA hHmac
      statesIntoPb_ok := cliStatesIntoPb_sendCoins_exact_ok mmpl gh W hA.toCliGhostAllocHooks
      chainFromPb_ok := cliSpqrSend_chainFromPb_ok mmpl gh W hA.toCliGhostAllocHooks
      chainFromVn_ok := cliSpqrSend_chainFromVn_ok mmpl gh W hA.toCliGhostAllocHooks
      chainAddEpoch_ok := hpt_cliSpqrSend_chainAddEpoch_on mmpl gh W hA.toCliGhostAllocHooks
      chainSendKey_ok := hpt_cliSpqrSend_chainSendKey_on mmpl gh W hA.toCliGhostAllocHooks
      chainIntoPb_ok := cliSpqrSend_chainIntoPb_ok mmpl gh W hA.toCliGhostAllocHooks
      messageSerialize_ok := hpt_cliSpqrSend_messageSerialize_exact_on mmpl gh W hA
      encodeVarint_ok := hpt_cliSpqrSend_encodeVarint_on mmpl gh W hA
      authMacHdr_ok := cliAuthMacHdr_placed_ok mmpl gh W hA hHmac
      authUpdate_ok := cliAuthUpdate_placed_ok mmpl gh W hA
      hkdfToVec_ok := cliHkdfToVec_placed_ok mmpl gh W hA
      encodeBytes_ok := cliEncodeBytesPlacedOkX mmpl gh W hA.toCliGhostAllocHooks
      polyNextChunk_ok := cliPolyNextChunkPlacedOkX mmpl gh W hA.toCliGhostAllocHooks
      headerSentSendEkChunk_ok := hS.headerSentSendEkChunk_on
      ct1ReceivedSendEkChunk_ok := hS.ct1ReceivedSendEkChunk_on
      ct1SampledSendCt1Chunk_ok := hS.ct1SampledSendCt1Chunk_on
      ekReceivedCt1SampledSendCt1Chunk_ok := hS.ekReceivedCt1SampledSendCt1Chunk_on
      ct2SampledSendCt2Chunk_ok := hS.ct2SampledSendCt2Chunk_on
      dropProtoChain_ok := drop_proto_spqr_chain_placed_ok_x hAlloc
      dropChainEpochSlice_ok := drop_chain_epoch_slice_local1_placed_ok_x hAlloc }

/-! ## 3. Active Phase 2–4 Continuation & Full Block `427` Proof at Cap-Free Envelopes -/

set_option maxHeartbeats 800000 in
/-- Tight cap-free active Phase 2–4 continuation for Block `427` composing
`step_send_statesSend_tight_placed` (`StatesSendTightEnv`) and
`step_send_from_314d8_ofEnv_placed` (`MessageSerializeEnv spqrPolyApi` + `StatesIntoPbExactEnv`). -/
theorem hpt_spqrSendBudgetActiveContinuation_placed_ok_tight [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {EnvDecode : DecodeStateGhost → List AllocEvent → Prop}
    {EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop}
    {Env : SendCall → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContractsOfEnv M H_inner A lim ctl C K
      EnvDecode EnvFromPb StatesIntoPbExactEnv (MessageSerializeEnv spqrPolyApi)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget.PolyNextChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.HeaderSentSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1ReceivedSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.EkReceivedCt1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct2SampledSendCt2ChunkEnv
      ext)
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
        (SeqEnv (StatesSendTightEnv C.F K st_states x.rest)
          (match st_states.send K x.rest with
           | .ok (sOut, _) =>
             SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv 0#64 pq sOut
           | .error (.err _) => FreeOnlyEvs
           | .error (.panic _) => HeaderReceived1aEnv)))
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
         SeqEnv (StatesSendTightEnv C.F K st_states x.rest)
           (SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv 0#64 pq sOut)
           evs_tail
       | .error (.err _) =>
         SeqEnv (StatesSendTightEnv C.F K st_states x.rest)
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
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
      memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
      memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
      memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
      statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
     (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
      (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
       spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
       statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt))
  have hpull_valid :
      (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
        (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt)) ⊢
      ⌜statesPolyEncoderValid st_states⌝ ∗
      ((stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
        ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
        optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
        chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
        memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
        memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
        statesFromPbJumpTablePlacedAt ∗
        spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
       (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
        (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt))) := by
    have hv0 := chunkedStatesAt_entails_polyEncoderValid A.repAlloc (sp + 0x950#64) st_states
    refine Entails.trans (Entails.of_eq (show _ =
        chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗ RestPre by
      dsimp only [RestPre]; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hv0) ?_
    exact Entails.of_eq (by dsimp only [RestPre]; sep_ac_rfl)
  refine SepWPp.weaken_pre hpull_valid (ProofLib.SepWPp.pure_elim fun hv => ?_)
  rcases statesSend_ok_or_headerReceived_encaps1_of_le_64 K hlen hrest_len hdec hinner hfrom hv with
    ⟨sOut, rest', hsend0⟩ | ⟨st, rfl, hencaps, hsend_err⟩
  · rw [hsend0] at hfit_tail
    have hfit_ss : FitsEnv M lim bSt (StatesSendTightEnv C.F K st_states x.rest) :=
      hfit_tail.seq_left
    have hdec_deps := decodeState_spqrDeps_of_spqrDecodeState_ok C.F K hdec
    have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
      unfold pqRatchetStateToPb; simp [hinner]
    have hraw := decodeState_spqrDeps_raw_le hdec_deps
    have hraw' :
        optRaw rawVN pq.versionNegotiation + optRaw rawChain pq.chain + rawV1State v1 ≤
        201 * x.st.bytes.length := by
      simpa only [pbToPqRatchetState, pqRatchetStateToPb, rawPqState, rawPqInner,
        hinner, Option.map, optRaw_some] using hraw
    have hchain_raw : optRaw rawChain pq.chain + 296 ≤ 2 ^ 54 := by
      omega
    rcases CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le hfrom with ⟨hst0_raw, _⟩
    have hroot_len : ∀ st, st_states = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63 := by
      intro st hst; subst hst
      have hrk := headerReceived_rootKey_le_rawV1State st
      omega
    have hpq'_len : ∀ chainPb : Option ChainPB,
        optRaw rawChain chainPb ≤ optRaw rawChain pq.chain + 624 →
        pqRatchetStatePBEncodedLen
          { versionNegotiation := pq.versionNegotiation
            chain := chainPb
            inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63 :=
      fun chainPb hch_le =>
        pqRatchetStatePBEncodedLen_lt_of_send C.F K hlen hdec_deps hinner_pb hfrom hsend0 hch_le
    let RestTail : SepProp :=
      statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
      x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt
    let FrameArm : SepProp :=
      optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
      memRegion x.ret 72 ∗
      (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
       memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
       memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
      spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
      spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ RestTail
    have hpre_arm :
        (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
          optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
          memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
         (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
          (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
           statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt)) ⊢
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
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
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation) ∗
        (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) st_states ∗
          memRegion x.ret 72 ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗
          statesFromPbJumpTablePlacedAt ∗ spqrSendStatesJumpTablePlacedAt ∗
          x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hvn) ?_
      rw [hreg]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_arm ?_
    refine step_send_statesSend_tight_placed (ctl := ctl) A lim bSt ext hA
      hEx.allocZeroed_hook hC.coinsFill_ok hEx.mlkemFromSeed_hook hEx.mlkemPk1_hook hEx.mlkemPk2_hook
      hEx.mlkemEncaps1_hook hEx.fromSeed_pk1_slice hEx.fromSeed_pk2_slice
      hEx.macHdrPinned_ok hEx.doReserve2_ok hC.encodeBytes_ok hC.polyNextChunk_ok
      hC.hkdfToVec_ok hC.authUpdate_ok
      hC.headerSentSendEkChunk_ok hC.ct1ReceivedSendEkChunk_ok hC.ct1SampledSendCt1Chunk_ok
      hC.ct2SampledSendCt2Chunk_ok hC.ekReceivedCt1SampledSendCt1Chunk_ok
      (s0 := sf) (s := sf) sp x.cur x.rest rest' pq.chain st_states sOut hroot_len hsend0 hfit_ss
      hcrlf hpcf hrunf hspf hfsp_align rfl rfl hx20 hx24 hx25 hx26 hx28 rfl rfl rfl ?_
    intro sm evs_ss hevs_ss hcrl_m hpc_m hrun_m hsp_m htr_m hx19_m _ hx22_m hx25_m hx26_m
      hx28_m hx23_none_m hpstate_m hvregs_m
    rw [htrf] at htr_m
    rw [hx19] at hx19_m
    rw [hx28] at hx28_m
    have hfit_p3 : FitsEnv M lim (M.stepEvents evs_ss bSt)
        (SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv sp pq sOut) :=
      hfit_tail.seq_right hevs_ss
    let Rest314d8 : SepProp :=
      spqrCoinsAfterPlaced ctl x.cur x.rest (x.rest.length - rest'.length) ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ RestTail
    have hP3196_eq :
        (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
          memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
          memRegion (sp + 0x950#64) 928 ∗
          optEpochSecretRegSlotAt A.repAlloc sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
          statesSendPostArmScratch sp ∗
          spqrCoinsAfterPlaced ctl x.cur x.rest (x.rest.length - rest'.length) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ A.pool lim (M.stepEvents evs_ss bSt) sm ∗
          stackAt sp spqrSendCalleeStack) ∗ FrameArm =
        (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
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
          messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
          stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest314d8) := by
      have hreg := post_3196_regions_eq sp
      calc
        _ = (memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
              memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
              statesSendPostArmScratch sp ∗
              memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
              memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
              memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp) ∗
            (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
              optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
              optEpochSecretRegSlotAt A.repAlloc sp (sm.readReg64 .x21) (sm.readReg64 .x27) sOut.key ∗
              memRegion x.ret 72 ∗ chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
              A.pool lim (M.stepEvents evs_ss bSt) sm ∗ stackAt sp spqrSendCalleeStack ∗
              memRegion (sp + 0x950#64) 928 ∗
              messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
              spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
              spqrSendEncodeJumpTablePlacedAt ∗ statesIntoPbJumpTablePlacedAt ∗ Rest314d8) := by
          dsimp only [FrameArm, Rest314d8]; sep_ac_rfl
        _ = _ := by rw [hreg]; sep_ac_rfl
    rw [hP3196_eq]
    refine step_send_from_314d8_ofEnv_placed (M.stepEvents evs_ss bSt) hA
      hEx.panic_hook hEx.panicSubOverflow_hook
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
            statesIntoPbJumpTablePlacedAt := rfl
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
            statesIntoPbJumpTablePlacedAt := rfl
      rw [hinto_eq]
      exact Entails.of_eq (by sep_ac_rfl)
  · rw [hsend_err] at hfit_tail
    have hct1_err : ∀ v, st.send_ct1_chunk K x.rest ≠ .ok v := by
      intro ⟨outSt, chunk, ek, tape1⟩ hok
      simp [States.send, StatesResult.ofPanic, hok, Bind.bind, Except.bind] at hsend_err
    have hss_nil : StatesSendTightEnv C.F K (.headerReceived st) x.rest [] := by
      dsimp only [StatesSendTightEnv, StatesSendEnvOfEnv]
      cases h : st.send_ct1_chunk K x.rest with
      | ok v => exact False.elim (hct1_err v h)
      | error _ => rfl
    have hfit_hr : FitsEnv M lim bSt HeaderReceived1aEnv :=
      hfit_tail.seq_right hss_nil
    have hpan : (spqrV1 C.F K).sendPanics x.st.bytes x.rest :=
      sendPanics_of_statesSend_panic hdec hinner hfrom hsend_err
    let FramePan : SepProp :=
      ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
      (memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
       memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
       memRegion (sp + 0x590#64) 920 ∗
       (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp)) ∗
      memRegion x.ret 72 ∗ statesFromPbJumpTablePlacedAt ∗
      spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0 ∗
      x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
      tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
      statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt
    have hpre_pan :
        (stackAt sp spqrSendCalleeStack ∗ memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
          optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
          memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
          memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) ∗
          memRegion x.ret 72 ∗ A.pool lim bSt sf ∗
          statesFromPbJumpTablePlacedAt ∗
          spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0) ∗
         (x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
          (spqrCoinsAtPlaced ctl x.cur x.rest ∗ tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
           statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt)) ⊢
        (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗ spqrCoinsAtPlaced ctl x.cur x.rest ∗
          chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
          statesSendPreArmScratch sp) ∗ FramePan := by
      have hreg := pre_309cc_regions_eq sp
      refine Entails.of_eq ?_
      calc
        _ = (memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
              memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
            (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt sf ∗
              spqrCoinsAtPlaced ctl x.cur x.rest ∗
              chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
              ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
              optVersionNegotiationPBTailAt A.repAlloc w0 w1 (sp + 0x40#64) pq.versionNegotiation ∗
              optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
              memRegion x.ret 72 ∗ statesFromPbJumpTablePlacedAt ∗
              spqrSendStatesJumpTablePlacedAt ∗ spqrSendSavedRegs sp s0 ∗
              x.st.at A.repAlloc ∗ v1StateJumpTablesPlacedAt ∗
              tokenInitPlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
              spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
              statesIntoPbJumpTablePlacedAt ∗ reduceTablePlacedAt) := by sep_ac_rfl
        _ = _ := by dsimp only [FramePan]; rw [hreg]; sep_ac_rfl
    exact SepWPp.weaken_pre hpre_pan
      (step_send_arm_headerReceived_encaps1_none_ofEnv_placed
        (R := R) (Frame := FramePan)
        hA hEx.allocZeroed_hook hC.coinsFill_ok hEx.mlkemEncaps1_hook hEx.unwrapFailed_hook
        sp x.cur x.rest (by omega) st hencaps hfit_hr hpan hcrlf hpcf hrunf hspf hfsp_align
        htrf hx24 hx26 hx28 rfl)

/-- Full Block `427` `subroutine_ok` on `spqrSendPlacedProg ext` at
`hpt_SpqrSendCoinsOfDecodeFromPbEnv C.F K DecBytesEnv FromPbValEnv`. -/
theorem hpt_spqrSendCoins_placed_ok_of_contracts_tight [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hC : SpqrSendPlacedContractsOfEnv M H_inner A lim ctl C K
      (fun g => DecBytesEnv g.st.bytes)
      (fun g => FromPbValEnv g.pb)
      StatesIntoPbExactEnv (MessageSerializeEnv spqrPolyApi)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      (fun x => LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.EncodeBytesEnv x.msg.length)
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget.PolyNextChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.HeaderSentSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1ReceivedSendEkChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.EkReceivedCt1SampledSendCt1ChunkEnv
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget.Ct2SampledSendCt2ChunkEnv
      ext)
    (hEx : SpqrSendExtraContractsPlaced M A lim ctl C K ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl (spqrV1 C.F K)
          (hpt_SpqrSendCoinsOfDecodeFromPbEnv C.F K DecBytesEnv FromPbValEnv))) := by
  refine spqrSendCoins_placed_ok_of_contracts_and_continuation_ofEnv hC ?_ ?_ ?_ ?_ ?_
    (hpt_spqrSendBudgetActiveContinuation_placed_ok_tight hA hC hEx ?_ ?_)
  · intro x _ st0 _ _ hfits0 evs hevs
    apply hfits0 evs
    dsimp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv]
    cases spqrDecodeState x.st.bytes with
    | error _ => exact hevs
    | ok pq =>
      dsimp only
      cases pq.inner with
      | none => exact Or.inl hevs
      | some inner =>
        cases inner with
        | v1 _ => exact Or.inl hevs
  · intro x _ st0 pq v1 evs_dec _ _ hfits0 hdec hinner hevs_dec evs_fpb hevs_fpb
    refine ((fitsEvents_append M lim evs_dec evs_fpb st0).mp
      (hfits0 (evs_dec ++ evs_fpb) ?_)).2
    simp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv,
      hdec, hinner]
    cases States.from_pb spqrPolyApi (spqrAuthApi C.F) v1 with
    | error err =>
      cases err with
      | panic _ => exact SeqEnv.append hevs_dec hevs_fpb
      | err _ => exact SeqEnv.append hevs_dec (SeqEnv.inl hevs_fpb)
    | ok _ => exact SeqEnv.append hevs_dec (SeqEnv.inl hevs_fpb)
  · intro x _ _ evs_dec _ hdec hevs_dec
    simp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv, hdec]
    exact hevs_dec
  · intro x _ pq evs_dec evs_drop _ hdec hinner hevs_dec hevs_drop
    simp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv,
      hdec, hinner]
    exact SeqEnv.append hevs_dec hevs_drop
  · intro x _ pq v1 _ evs_dec evs_fpb evs_drop _ hdec hinner hfrom hevs_dec hevs_fpb hevs_drop
    simp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv,
      hdec, hinner, hfrom]
    rw [List.append_assoc]
    exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb hevs_drop)
  · intro x _ st0 pq v1 st_states evs_dec evs_fpb _ _ hfits0 hdec hinner hfrom
      hevs_dec hevs_fpb evs_tail
    cases h : st_states.send K x.rest with
    | ok val =>
      rcases val with ⟨sOut, _⟩
      intro htail
      refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
        (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
      simp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv,
        hdec, hinner, hfrom, h]
      rw [List.append_assoc]
      exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb htail)
    | error err =>
      cases err with
      | err _ =>
        intro htail
        refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
          (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
        simp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv,
          hdec, hinner, hfrom, h]
        rw [List.append_assoc]
        exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb htail)
      | panic _ =>
        intro htail
        refine ((fitsEvents_append M lim (evs_dec ++ evs_fpb) evs_tail st0).mp
          (hfits0 ((evs_dec ++ evs_fpb) ++ evs_tail) ?_)).2
        simp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv,
          hdec, hinner, hfrom, h]
        rw [List.append_assoc]
        exact SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb htail)
  · intro x _ pq v1 st_states evs_dec evs_fpb evs_tail _ _ hdec hinner hfrom
      hevs_dec hevs_fpb htail
    simp only [hpt_SpqrSendCoinsOfDecodeFromPbEnv, hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv,
      hdec, hinner, hfrom]
    rw [List.append_assoc]
    refine SeqEnv.append hevs_dec (SeqEnv.append hevs_fpb ?_)
    cases h : st_states.send K x.rest with
    | ok val =>
      rcases val with ⟨sOut, _⟩
      rw [h] at htail
      exact htail
    | error err =>
      cases err with
      | err _ =>
        rw [h] at htail
        exact htail
      | panic _ =>
        rw [h] at htail
        exact False.elim htail

/-- CLI Block `427` (`(blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W))`)
producer at `SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv` for any leaf-parametric
`(DecBytesEnv, FromPbValEnv)` containing `(DecodeStateBytesEnv, StatesFromPbEnv)`. -/
theorem hpt_cliSpqrSendCoins_placed_ok_of_decode_fromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hDecSub : ∀ bs evs, DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hFromPbSub : ∀ v1 evs, StatesFromPbEnv v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (hpt_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv))) := by
  have hraw := hpt_spqrSendCoins_placed_ok_of_contracts_tight
    (cliSpqrSendAllocContractsPlaced mmpl gh W hA.toCliGhostAllocHooks)
    (hpt_spqrSendPlacedContractsOfEnv_of_cli mmpl gh W hDecSub hFromPbSub hA hHmac)
    (spqrSendExtraContractsPlaced_of_cli mmpl gh W hA hHmac)
  have hblk_wp : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 427
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (hpt_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv))) := by
    rwa [← IsLsBlockProg.eq_blockProgram
      (prog := spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))]
  have hwp_eq :
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
        cliGhostExterns gh (cliExternsPlaced mmpl W) := by
    funext sym; unfold Rust.withPanics; split
    · next hp => exact (hpt_cliGhostExterns_isPanic mmpl gh W sym hp).symm
    · rfl
  have hblk_ext : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 427
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (hpt_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv))) := by
    simpa only [hwp_eq] using hblk_wp
  have hok : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (hpt_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv))) :=
    ls_subroutine_ok_of_blockProgram_cro
      (callerProg := (blkPC_427).rebase (blkPl_427).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hblk_ext (by decide)
  have heq_cro (m : Memory) :
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m =
        LibsignalCodeRoLoaded lsmpl m :=
    propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have hmod : pqxdhSpqrModel ⟨W.C, W.Q⟩ = spqrV1 W.C.F W.Q.K := rfl
  rw [hmod]
  have hcoinsAt : spqrCoinsAtPlaced = cliTapeAt := rfl
  have hcoinsAfter : spqrCoinsAfterPlaced = cliTapeAfter := rfl
  exact subroutine_ok_mono hok
    (fun (sc, stB) _ s hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded, spqrSendCoinsPlacedSpecTOfEnv, spqrSendCoinsPlacedSpecOfEnv]
        at hpre ⊢
      rw [heq_cro s.mem] at hpre
      rw [hcoinsAt]
      exact hpre)
    (fun (sc, stB) _ s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded, spqrSendCoinsPlacedSpecTOfEnv, spqrSendCoinsPlacedSpecOfEnv]
        at hpost ⊢
      rw [hcoinsAfter] at hpost
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hd, htr, hnp, hevs⟩ => ⟨hevs, hd, htr, hnp⟩)
    (fun _ _ _ _ hpanic => hpanic)

/-! ## 4. Unconditional `SpqrSendCoinsTightLinkedEnv` & `SpqrV1PlacedSeamsOfEnv` Producers -/

/-- Unconditional Block `427` (`spqr::send::<Coins>`) producer at
`SpqrExactEnvDefs.SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K`. -/
theorem hpt_cliSpqrSendCoins_placed_ok_tightLinked [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K))) :=
  hpt_cliSpqrSendCoins_placed_ok_of_decode_fromPb mmpl gh W
    (fun _ _ h => h) (fun _ _ h => h) hA hHmac

/-- `hHmac`-discharged Block `427` producer at `SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K` on
`(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)`. -/
theorem hpt_cliSpqrSendCoins_placed_ok_tightLinked_fine [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K))) :=
  hpt_cliSpqrSendCoins_placed_ok_tightLinked mmpl gh W hGSpqr
    (hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart lim gh W hPl_mng)

/-- `(M, I)`-generic `hHmac`-discharged Block `427` producer at
`SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K` on `mallocngHookRustCliAllocBudget`. -/
theorem hpt_cliSpqrSendCoins_placed_ok_tightLinked_mallocngHook [LibsignalPlacement]
    {M : AllocCostModel} {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks M
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim gh) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv M
          (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K))) :=
  hpt_cliSpqrSendCoins_placed_ok_tightLinked mmpl gh W hGSpqr
    (hpo_cliLibcruxHmac_mallocngHook_budget_hookSat hS γ mmpl tp brkStart lim gh W hPl_mng)

/-- Complete `SpqrV1PlacedSeamsOfEnv` assembly at `(InitialStateEnv W.C.F, CliSpqrRecvTightLinkedEnv W,
SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)` for arbitrary `(M, A, lim)` given `hA` and `hHmac`. -/
theorem hpt_spqrV1PlacedSeams_tightLinked_of_hmac [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F)
      (CliSpqrRecvTightLinkedEnv W)
      (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K) :=
  spqrV1PlacedSeamsOfEnv_of_sendCoins mmpl gh W hA hHmac
    (fun _ _ h => h) (fun _ _ _ h => h)
    (hpt_cliSpqrSendCoins_placed_ok_tightLinked mmpl gh W hA hHmac)

/-- Complete `hHmac`-discharged `SpqrV1PlacedSeamsOfEnv` assembly at
`(InitialStateEnv W.C.F, CliSpqrRecvTightLinkedEnv W, SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)` on
`(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)` from ONLY
`VerifiedLibraries.mallocngLib.Placeable mmpl` and `CliGhostSpqrAllocHooks` ...`). -/
theorem hpt_spqrV1PlacedSeams_tightLinked [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh) :
    SpqrV1PlacedSeamsOfEnv fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim mmpl gh W
      (InitialStateEnv W.C.F)
      (CliSpqrRecvTightLinkedEnv W)
      (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K) :=
  spqrV1PlacedSeamsOfEnv_tightLinked_of_sendCoins γ mmpl tp brkStart lim gh W hPl_mng hGSpqr
    (hpt_cliSpqrSendCoins_placed_ok_tightLinked_fine γ mmpl tp brkStart lim gh W hPl_mng hGSpqr)

/-- `(M, I)`-generic `hHmac`-discharged `SpqrV1PlacedSeamsOfEnv` assembly at
`(InitialStateEnv W.C.F, CliSpqrRecvTightLinkedEnv W, SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)` on
`mallocngHookRustCliAllocBudget`. -/
theorem hpt_spqrV1PlacedSeams_tightLinked_mallocngHook [LibsignalPlacement]
    {M : AllocCostModel} {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks M
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim gh) :
    SpqrV1PlacedSeamsOfEnv M
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim mmpl gh W
      (InitialStateEnv W.C.F)
      (CliSpqrRecvTightLinkedEnv W)
      (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K) :=
  spqrV1PlacedSeamsOfEnv_mallocngHook_of_sendCoins hS γ mmpl tp brkStart lim gh W hPl_mng hGSpqr
    (hpt_cliSpqrSendCoins_placed_ok_tightLinked_mallocngHook hS γ mmpl tp brkStart lim gh W
      hPl_mng hGSpqr)

/-! ## 5. Guarded-Tight Block `427` & `SpqrV1PlacedSeamsOfEnv` Producers -/

/-- Lifts `hpt_cliSpqrSendCoins_placed_ok_tightLinked` to any `SendEnv` under a predicate `Guard`:
- `hTrue`: under `Guard sc`, `SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K sc ⊆ SendEnv sc`;
- `hFalse`: under `¬ Guard sc`, `SendEnv sc` is universal (`∀ evs, SendEnv sc evs`), making
  `FitsEnv M lim stB (SendEnv sc)` unsatisfiable via `hpt_not_fitsEnv_of_univ`. -/
theorem hpt_cliSpqrSendCoins_placed_ok_guarded [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Guard : SendCall → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hTrue : ∀ sc evs, Guard sc → SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K sc evs → SendEnv sc evs)
    (hFalse : ∀ sc evs, ¬ Guard sc → SendEnv sc evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) := by
  have hok := hpt_cliSpqrSendCoins_placed_ok_tightLinked mmpl gh W hA hHmac
  exact subroutine_ok_mono hok
    (fun (sc, stB) _ _ hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec]
        at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, h2, hfit⟩ => by
        by_cases hG : Guard sc
        · exact ⟨h1, h2, hfit.mono (hTrue sc · hG)⟩
        · exact False.elim (hpt_not_fitsEnv_of_univ (fun evs => hFalse sc evs hG) hfit))
    (fun (sc, stB) _ _ _ hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec]
        at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hevs, hd, htr, hnp⟩ => by
        by_cases hG : Guard sc
        · exact ⟨hTrue sc evs hG hevs, hd, htr, hnp⟩
        · exact ⟨hFalse sc evs hG, hd, htr, hnp⟩)
    (fun _ _ _ _ hp => hp)

/-- `hHmac`-discharged guarded Block `427` producer on
`(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)`. -/
theorem hpt_cliSpqrSendCoins_placed_ok_guarded_fine [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    {Guard : SendCall → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hTrue : ∀ sc evs, Guard sc → SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K sc evs → SendEnv sc evs)
    (hFalse : ∀ sc evs, ¬ Guard sc → SendEnv sc evs)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) :=
  hpt_cliSpqrSendCoins_placed_ok_guarded mmpl gh W hTrue hFalse hGSpqr
    (hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart lim gh W hPl_mng)

/-- Leaf-parametric implication-guarded Block `427` producer on `(DecBytesEnv, FromPbValEnv)`
(`hpt_SpqrSendGuardedImplBytesEnv Guard (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv)`):
requires ONLY guarded decode/from_pb inclusions under `Guard sc.st.bytes`. -/
theorem hpt_cliSpqrSendCoins_placed_ok_guarded_leaves_imp [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Guard : List (BitVec 8) → Prop}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hDecGuard : ∀ bs evs, Guard bs → DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hFromPbGuard : ∀ bs pq v1 evs, Guard bs →
      spqrDecodeState bs = .ok pq → pq.inner = some (.v1 v1) →
      StatesFromPbEnv v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (fun sc => hpt_SpqrSendGuardedImplBytesEnv Guard
            (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv)
            sc.st.bytes sc.rest))) :=
  hpt_cliSpqrSendCoins_placed_ok_guarded (Guard := fun sc => Guard sc.st.bytes) mmpl gh W
    (fun sc _ hG hevs _ =>
      hpt_spqrSendCoinsTightLinked_mono_leaves
        (hDecGuard sc.st.bytes · hG)
        (hFromPbGuard sc.st.bytes · · · hG)
        hevs)
    (fun _ _ hnG hG => absurd hG hnG)
    hA hHmac

/-- Leaf-parametric `if-then-else`-guarded Block `427` producer on `(DecBytesEnv, FromPbValEnv)`. -/
theorem hpt_cliSpqrSendCoins_placed_ok_guarded_leaves_ite [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Guard : List (BitVec 8) → Prop}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hDecGuard : ∀ bs evs, Guard bs → DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hFromPbGuard : ∀ bs pq v1 evs, Guard bs →
      spqrDecodeState bs = .ok pq → pq.inner = some (.v1 v1) →
      StatesFromPbEnv v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (fun sc => hpt_SpqrSendGuardedIteBytesEnv Guard
            (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv)
            sc.st.bytes sc.rest))) :=
  hpt_cliSpqrSendCoins_placed_ok_guarded (Guard := fun sc => Guard sc.st.bytes) mmpl gh W
    (fun sc evs hG hevs => by
      simp only [hpt_SpqrSendGuardedIteBytesEnv, hG, ↓reduceIte]
      exact hpt_spqrSendCoinsTightLinked_mono_leaves
        (hDecGuard sc.st.bytes · hG)
        (hFromPbGuard sc.st.bytes · · · hG)
        hevs)
    (fun sc _ hnG => by
      simp only [hpt_SpqrSendGuardedIteBytesEnv, hnG, ↓reduceIte])
    hA hHmac

/-- Guarded `SpqrV1PlacedSeamsOfEnv` assembly on `(fineCostModel, fineHookRustCliAllocBudget)` for
any `Guard : SendCall → Prop` and `SendEnv : SendCall → List AllocEvent → Prop`. -/
theorem hpt_spqrV1PlacedSeams_guarded [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    {Guard : SendCall → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hTrue : ∀ sc evs, Guard sc → SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K sc evs → SendEnv sc evs)
    (hFalse : ∀ sc evs, ¬ Guard sc → SendEnv sc evs)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh) :
    SpqrV1PlacedSeamsOfEnv fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim mmpl gh W
      (InitialStateEnv W.C.F)
      (CliSpqrRecvTightLinkedEnv W)
      SendEnv :=
  spqrV1PlacedSeamsOfEnv_tightLinked_of_sendCoins γ mmpl tp brkStart lim gh W hPl_mng hGSpqr
    (hpt_cliSpqrSendCoins_placed_ok_guarded_fine γ mmpl tp brkStart lim gh W hTrue hFalse
      hPl_mng hGSpqr)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst
