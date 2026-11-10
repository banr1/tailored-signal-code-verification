/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.FinalPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedTightBudgetR
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Exact `States::from_pb` to `StatesFromPbTightEnv` CLI Bridges

**Checked by Lean.**

Lifts the exact 12-arm `<States>::from_pb` (Block 333) allocation contract
`e2b_StatesFromPbExactEnv` onto the CLI `CliGhostSpqrAllocHooks` hook table and both SPQR top-level
entry points (`spqr::recv` on Block 329 and `spqr::send::<Coins>` on Block 427), bridging exact
per-variant traces into `StatesFromPbTightEnv` under `gu2b_FromPbStateGuard`, `TopStateTight`, and
`SpqrStateTight640`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsmpl)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (ls_subroutine_ok_of_blockProgram_cro spqrCoinsAfterPlaced spqrCoinsAtPlaced
   statesFromPbJumpTablePlacedAt)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1State spqrAuthApi spqrDecodeState spqrHkdfWith
   spqrPolyApi spqrV1 spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SendCall VecArg sessionMemmoveSpec spqrRecvStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (lsRngFillSym trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Alloc (spqrMemmoveSym)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.States.FromPb
  (resultChunkedStatesAt statesFromPbStackX v1StatePtsBound)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs MallocngCostModelIface
   MallocngCostModelSound RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (SpqrSendPlacedContractsOfEnv spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (StatesSendTightEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (HeaderReceived1aEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget (SendPhase3EnvOfEnv)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudget mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07C09aTightLinkedEnv SpqrRecvC07TightLinkedEnv SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
  (spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07TightLinked
   spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07c09aTightLinked
   spqr_recv_placed_ok_blockProgram_ext_of_contracts_tightLinked)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidV1PtsAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (SpqrStateTight640 TopStateTight)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (DecodeStateBytesEnv StatesRecvExactPairEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
  (hpo_cliLibcruxHmac_budget_hookSat hpo_cliLibcruxHmac_mallocngHook_budget_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliExternsPlaced_sessionMemmove_allocVm_sat cliRecvCt2PlacedAllocExt cliSpqrSendAllocContractsPlaced
   cliStatesPlacedSeams cliStatesPlacedSeamsExt spqrSendExtraContractsPlaced_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst
  (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv hpt_SpqrSendCoinsOfDecodeFromPbEnv
   hpt_SpqrSendGuardedImplBytesEnv hpt_SpqrSendGuardedIteBytesEnv hpt_not_fitsEnv_of_univ
   hpt_spqrSendCoins_placed_ok_of_contracts_tight hpt_spqrSendPlacedContractsOfEnv_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeamsOfEnv spqrRecvPlacedInnerSpecXOfEnv spqrRecvPlacedInnerSpecXTOfEnv
   spqrSendCoinsPlacedSpecTOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
  (cliSpqrInitialState_placed_ok_ofEnv cliSpqrRecvPlacedContracts_exact trTrapExternsPlaced_isPanic)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedTightBudgetR
  (e2b_StatesFromPbExactEnv e2b_StatesFromPbGuardedTightEnv e2b_StatesFromPbImpTightEnv
   e2b_StatesFromPbTightDom e2b_statesFromPbExactEnv_sub_tight e2b_statesFromPbTightDom_of_bokTight
   e2b_statesFromPbTightDom_of_spqrStateTight640 e2b_statesFromPbTightDom_of_topStateTight
   e2b_states_from_pb_ok_x_placed_exact e2b_states_from_pb_ok_x_placed_guardedTight
   e2b_states_from_pb_ok_x_placed_impTight)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget (StatesRecvExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (RecvCt2PlacedAlloc)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
  (Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv StatesFromPbPlacedOkXOfEnv
   StatesPlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget (MessageSerializeEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
  (spqrRecvPlacedRawSpecXOfEnv spqrRecvPlacedSpecXOfEnv spqrRecvPlacedSpecXTOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContractsOfEnv decodeStatePlacedSpecXOfEnv statesFromPbPlacedSpecXOfEnv
   statesIntoPbPlacedSpecXOfEnv statesRecvPlacedSpecOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)

/-!
## 1. Domain & Tight-Inclusion Bridges (`e2b_StatesFromPbExactEnv` → `StatesFromPbTightEnv`)
-/

/-- Per-state input guard for `<States>::from_pb` (`Block 333`), definitionally equal (`rfl`) to
`ElfHole3W2IntAux.w2i_FromPbStateGuard F pb` while residing in `@[default_target]`. -/
def gu2b_FromPbStateGuard (F : ShaCompress) (pb : V1State) : Prop :=
  (∃ st : States spqrPolyApi (spqrAuthApi F), BOkTight st ∧ pb = st.into_pb) ∧
    rawV1State pb ≤ 46880 ∧ ValidV1PtsAt 640 pb

/-- Canonical implication-guarded `Block 333` (`<States>::from_pb`) envelope, definitionally equal
(`rfl`) to `ElfHole3W2IntAux.w2i_StatesFromPbGuardedEnv F`. -/
def gu2b_StatesFromPbGuardedEnv (F : ShaCompress)
    (pb : V1State) (evs : List AllocEvent) : Prop :=
  gu2b_FromPbStateGuard F pb → StatesFromPbTightEnv evs

/-- `gu2b_FromPbStateGuard F pb` (`= w2i_FromPbStateGuard F pb`) implies
`e2b_StatesFromPbTightDom pb` via `e2b_statesFromPbTightDom_of_bokTight`. -/
theorem gu2b_tightDom_of_fromPbStateGuard {F : ShaCompress} {pb : V1State}
    (hG : gu2b_FromPbStateGuard F pb) :
    e2b_StatesFromPbTightDom pb := by
  rcases hG with ⟨⟨st, hbok, rfl⟩, _, hpts⟩
  exact e2b_statesFromPbTightDom_of_bokTight hbok hpts

/-- Tight inclusion from `e2b_StatesFromPbExactEnv F pb` into `StatesFromPbTightEnv` (`≤ 56` ops,
`≤ 359,623` B, `maxReq ≤ 2,560`) under `gu2b_FromPbStateGuard F pb` (exact `hFromPb_sub` premise of
`ElfHole3W2IntAux` at `FromPbEnv := e2b_StatesFromPbExactEnv W.C.F`). -/
theorem gu2b_exactEnv_sub_tight_of_fromPbStateGuard {F : ShaCompress} (pb : V1State)
    (evs : List AllocEvent)
    (hG : gu2b_FromPbStateGuard F pb)
    (hEnv : e2b_StatesFromPbExactEnv F pb evs) :
    StatesFromPbTightEnv evs :=
  e2b_statesFromPbExactEnv_sub_tight (gu2b_tightDom_of_fromPbStateGuard hG) hEnv

/-- On-domain projection of `e2b_StatesFromPbGuardedTightEnv` into `StatesFromPbTightEnv`. -/
theorem gu2b_guardedTightEnv_sub_tight_of_dom {pb : V1State} {evs : List AllocEvent}
    (hDom : e2b_StatesFromPbTightDom pb)
    (hEnv : e2b_StatesFromPbGuardedTightEnv pb evs) :
    StatesFromPbTightEnv evs := by
  rcases hEnv with ⟨_, hTight⟩ | ⟨hnDom, _⟩
  · exact hTight
  · exact absurd hDom hnDom

/-- Tight inclusion from `e2b_StatesFromPbGuardedTightEnv` into `StatesFromPbTightEnv` under
`gu2b_FromPbStateGuard F pb`. -/
theorem gu2b_guardedTightEnv_sub_tight_of_fromPbStateGuard {F : ShaCompress} (pb : V1State)
    (evs : List AllocEvent)
    (hG : gu2b_FromPbStateGuard F pb)
    (hEnv : e2b_StatesFromPbGuardedTightEnv pb evs) :
    StatesFromPbTightEnv evs :=
  gu2b_guardedTightEnv_sub_tight_of_dom (gu2b_tightDom_of_fromPbStateGuard hG) hEnv

/-- Unconditional inclusion of `e2b_StatesFromPbExactEnv F` into `gu2b_StatesFromPbGuardedEnv F`
(`= w2i_StatesFromPbGuardedEnv F`). -/
theorem gu2b_exactEnv_sub_fromPbGuardedEnv {F : ShaCompress} (pb : V1State)
    (evs : List AllocEvent)
    (hEnv : e2b_StatesFromPbExactEnv F pb evs) :
    gu2b_StatesFromPbGuardedEnv F pb evs :=
  fun hG => gu2b_exactEnv_sub_tight_of_fromPbStateGuard pb evs hG hEnv

/-- Unconditional inclusion of `e2b_StatesFromPbGuardedTightEnv` into
`gu2b_StatesFromPbGuardedEnv F` (`= w2i_StatesFromPbGuardedEnv F`). -/
theorem gu2b_guardedTightEnv_sub_fromPbGuardedEnv {F : ShaCompress} (pb : V1State)
    (evs : List AllocEvent)
    (hEnv : e2b_StatesFromPbGuardedTightEnv pb evs) :
    gu2b_StatesFromPbGuardedEnv F pb evs :=
  fun hG => gu2b_guardedTightEnv_sub_tight_of_fromPbStateGuard pb evs hG hEnv

/-- Unconditional inclusion of `e2b_StatesFromPbImpTightEnv` into `gu2b_StatesFromPbGuardedEnv F`
(`= w2i_StatesFromPbGuardedEnv F`). -/
theorem gu2b_impTightEnv_sub_fromPbGuardedEnv {F : ShaCompress} (pb : V1State)
    (evs : List AllocEvent)
    (hEnv : e2b_StatesFromPbImpTightEnv pb evs) :
    gu2b_StatesFromPbGuardedEnv F pb evs :=
  fun hG => hEnv (gu2b_tightDom_of_fromPbStateGuard hG)

/-- Decoded `V1` state tight inclusion under `TopStateTight F K bs`: bridges
`e2b_StatesFromPbExactEnv F pb` directly to `StatesFromPbTightEnv`. -/
theorem gu2b_exactEnv_sub_tight_of_topStateTight {F : ShaCompress} {K : MlKem}
    {bs : Bytes} {pq : PqRatchetState} {pb : V1State} {evs : List AllocEvent}
    (hTop : TopStateTight F K bs)
    (hdec : spqrDecodeState bs = .ok pq)
    (hpb : pq.inner = some (.v1 pb))
    (hEnv : e2b_StatesFromPbExactEnv F pb evs) :
    StatesFromPbTightEnv evs :=
  e2b_statesFromPbExactEnv_sub_tight (e2b_statesFromPbTightDom_of_topStateTight hTop hdec hpb) hEnv

/-- Decoded `V1` state tight inclusion under `SpqrStateTight640 F K bs`: bridges
`e2b_StatesFromPbExactEnv F pb` directly to `StatesFromPbTightEnv` (the `bs = []` disjunct decodes
to `pq.inner = none` and is vacuous). -/
theorem gu2b_exactEnv_sub_tight_of_spqrStateTight640 {F : ShaCompress} {K : MlKem}
    {bs : Bytes} {pq : PqRatchetState} {pb : V1State} {evs : List AllocEvent}
    (hSt : SpqrStateTight640 F K bs)
    (hdec : spqrDecodeState bs = .ok pq)
    (hpb : pq.inner = some (.v1 pb))
    (hEnv : e2b_StatesFromPbExactEnv F pb evs) :
    StatesFromPbTightEnv evs :=
  e2b_statesFromPbExactEnv_sub_tight (e2b_statesFromPbTightDom_of_spqrStateTight640 hSt hdec hpb) hEnv

/-!
## 2. CLI `FromPbAllocHooksBudget` & `StatesFromPbPlacedOkXOfEnv` / `StatesPlacedSeamsOfEnv`
-/

private theorem gu2b_hookSat_allocMemcpyVm_of_framelessAcp {hooks : String → Option (State → State)}
    {name : String}
    (h : HookSat hooks name
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec) :
    HookSat hooks name LibsignalBinary.Heap.allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec.pre
        (dst, src, bs) s0 ∗ R := by
    dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hsat (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

private theorem gu2b_hExt_withPanics
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym hne
  have h1 : Rust.withPanics ext sym =
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
    simp only [Rust.withPanics, hExt sym hne]
  exact h1.trans (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)

private theorem gu2b_trTrap_hExt (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
  fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne]

/-- Extracts `FromPbAllocHooksBudget M A lim ext` from `RecvCt2PlacedAlloc M A lim ext`. -/
theorem gu2b_fromPbAllocHooksBudget_of_recvCt2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext) :
    FromPbAllocHooksBudget M A lim ext where
  panic_ok := hA.handleError
  shim := hA.shim
  alloc := hA.alloc
  dealloc := hA.dealloc
  memcpy := gu2b_hookSat_allocMemcpyVm_of_framelessAcp hA.memcpy

/-- Builds `FromPbAllocHooksBudget M A lim ext` from `CliGhostSpqrAllocHooks M A lim gh` for any
`ext` agreeing with `cliGhostExterns gh (cliExternsPlaced mmpl W)` outside
`libsignal_session_rng_fill`. -/
theorem gu2b_fromPbAllocHooksBudget_cliExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    FromPbAllocHooksBudget M A lim ext :=
  gu2b_fromPbAllocHooksBudget_of_recvCt2 (cliRecvCt2PlacedAllocExt mmpl gh W hA hExt)

/-- Relocatable `Block 333` (`<States>::from_pb`) `StatesFromPbPlacedOkXOfEnv` producer at
`e2b_StatesFromPbExactEnv W.C.F`. -/
theorem gu2b_statesFromPb_placed_okX_exact_cliExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesFromPbPlacedOkXOfEnv M A lim W.C.F ext (e2b_StatesFromPbExactEnv W.C.F) :=
  e2b_states_from_pb_ok_x_placed_exact
    (gu2b_fromPbAllocHooksBudget_cliExt mmpl gh W hA hExt)
    (hookSat_of_eq (gu2b_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W))

/-- Relocatable `Block 333` `StatesFromPbPlacedOkXOfEnv` producer at domain-split
`e2b_StatesFromPbGuardedTightEnv`. -/
theorem gu2b_statesFromPb_placed_okX_guardedTight_cliExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesFromPbPlacedOkXOfEnv M A lim W.C.F ext e2b_StatesFromPbGuardedTightEnv :=
  e2b_states_from_pb_ok_x_placed_guardedTight
    (gu2b_fromPbAllocHooksBudget_cliExt mmpl gh W hA hExt)
    (hookSat_of_eq (gu2b_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W))

/-- Relocatable `Block 333` `StatesFromPbPlacedOkXOfEnv` producer at implication-guarded
`e2b_StatesFromPbImpTightEnv`. -/
theorem gu2b_statesFromPb_placed_okX_impTight_cliExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesFromPbPlacedOkXOfEnv M A lim W.C.F ext e2b_StatesFromPbImpTightEnv :=
  e2b_states_from_pb_ok_x_placed_impTight
    (gu2b_fromPbAllocHooksBudget_cliExt mmpl gh W hA hExt)
    (hookSat_of_eq (gu2b_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W))

/-- Envelope-monotonic lift of `StatesFromPbPlacedOkXOfEnv` along any pointwise inclusion
`∀ pb evs, Env₁ pb evs → Env₂ pb evs`. -/
theorem gu2b_statesFromPbPlacedOkXOfEnv_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env₁ Env₂ : V1State → List AllocEvent → Prop}
    (hSub : ∀ pb evs, Env₁ pb evs → Env₂ pb evs)
    (hok : StatesFromPbPlacedOkXOfEnv M A lim F ext Env₁) :
    StatesFromPbPlacedOkXOfEnv M A lim F ext Env₂ :=
  subroutine_ok_mono hok
    (fun (g, stB) _ _ hpre => by
      dsimp only [withLsCodeRoLoaded, statesFromPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv]
        at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
      exact Entails.pure_mono fun ⟨h1, h2, h3, hfit⟩ => ⟨h1, h2, h3, hfit.mono (hSub g.pb)⟩)
    (fun (g, stB) _ _ _ hpost => by
      dsimp only [withLsCodeRoLoaded, statesFromPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv]
        at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, hevs⟩ => ⟨h1, hSub g.pb evs hevs⟩)
    (fun _ _ _ _ hp => hp)

/-- Relocatable `Block 333` `StatesFromPbPlacedOkXOfEnv` producer for any `FromPbEnv'` containing
`e2b_StatesFromPbExactEnv W.C.F`. -/
theorem gu2b_statesFromPb_placed_okX_ofEnv_cliExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {FromPbEnv' : V1State → List AllocEvent → Prop}
    (hSub : ∀ pb evs, e2b_StatesFromPbExactEnv W.C.F pb evs → FromPbEnv' pb evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesFromPbPlacedOkXOfEnv M A lim W.C.F ext FromPbEnv' :=
  gu2b_statesFromPbPlacedOkXOfEnv_mono hSub
    (gu2b_statesFromPb_placed_okX_exact_cliExt mmpl gh W hA hExt)

/-- Exact-`from_pb` upgrade of `SpqrSendCoinsPlacedInstBudget.cliStatesPlacedSeamsExt`, replacing
coarse `StatesFromPbEnv` (`128` ops) with `e2b_StatesFromPbExactEnv W.C.F`. -/
theorem gu2b_cliStatesPlacedSeamsExt_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesPlacedSeamsOfEnv M A lim W.C.F W.Q.K
      (e2b_StatesFromPbExactEnv W.C.F) (StatesRecvExactEnv W.Q.K)
      HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
      Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
      ext :=
  { cliStatesPlacedSeamsExt mmpl gh W hA hHmac hExt with
    statesFromPb_ok := gu2b_statesFromPb_placed_okX_exact_cliExt mmpl gh W hA hExt }

/-- Exact-`from_pb` upgrade of `SpqrSendCoinsPlacedInstBudget.cliStatesPlacedSeams` on
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem gu2b_cliStatesPlacedSeams_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    StatesPlacedSeamsOfEnv M A lim W.C.F W.Q.K
      (e2b_StatesFromPbExactEnv W.C.F) (StatesRecvExactEnv W.Q.K)
      HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
      Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  gu2b_cliStatesPlacedSeamsExt_exactFromPb mmpl gh W hA hHmac (fun _ _ => rfl)

/-! ## 3. `Block 329` (`spqr::recv` / `trTrapExternsPlaced`) Bridges & `hFromPb` Discharger -/

/-- `Block 333` (`<States>::from_pb`) lifted onto `spqrRecvPlacedProg (trTrapExternsPlaced ...)` at
`e2b_StatesFromPbExactEnv W.C.F`. -/
theorem gu2b_cliSpqrRecv_statesFromPb_exact_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedSpecXOfEnv M A lim W.C.F (e2b_StatesFromPbExactEnv W.C.F))) :=
  LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg :=
      spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (i := 329)
    (gu2b_statesFromPb_placed_okX_exact_cliExt mmpl gh W hA (gu2b_trTrap_hExt mmpl gh W))

/-- `Block 333` (`<States>::from_pb`) lifted onto `spqrRecvPlacedProg (trTrapExternsPlaced ...)` at
`e2b_StatesFromPbGuardedTightEnv`. -/
theorem gu2b_cliSpqrRecv_statesFromPb_guardedTight_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedSpecXOfEnv M A lim W.C.F e2b_StatesFromPbGuardedTightEnv)) :=
  LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg :=
      spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (i := 329)
    (gu2b_statesFromPb_placed_okX_guardedTight_cliExt mmpl gh W hA (gu2b_trTrap_hExt mmpl gh W))

/-- `Block 333` (`<States>::from_pb`) lifted onto `spqrRecvPlacedProg (trTrapExternsPlaced ...)` at
`e2b_StatesFromPbImpTightEnv`. -/
theorem gu2b_cliSpqrRecv_statesFromPb_impTight_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedSpecXOfEnv M A lim W.C.F e2b_StatesFromPbImpTightEnv)) :=
  LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg :=
      spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (i := 329)
    (gu2b_statesFromPb_placed_okX_impTight_cliExt mmpl gh W hA (gu2b_trTrap_hExt mmpl gh W))

/-- `Block 333` (`<States>::from_pb`) lifted onto `spqrRecvPlacedProg (trTrapExternsPlaced ...)` for
any `FromPbEnv'` containing `e2b_StatesFromPbExactEnv W.C.F`. -/
theorem gu2b_cliSpqrRecv_statesFromPb_ofEnv_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {FromPbEnv' : V1State → List AllocEvent → Prop}
    (hSub : ∀ pb evs, e2b_StatesFromPbExactEnv W.C.F pb evs → FromPbEnv' pb evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedSpecXOfEnv M A lim W.C.F FromPbEnv')) :=
  LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg :=
      spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (i := 329)
    (gu2b_statesFromPb_placed_okX_ofEnv_cliExt mmpl gh W hSub hA (gu2b_trTrap_hExt mmpl gh W))

/-- Proves `Block 333` on `spqrRecvPlacedProg (trTrapExternsPlaced ...)` at
`gu2b_StatesFromPbGuardedEnv W.C.F` from `CliGhostSpqrAllocHooks` alone. -/
theorem gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedSpecXOfEnv M A lim W.C.F (gu2b_StatesFromPbGuardedEnv W.C.F))) :=
  gu2b_cliSpqrRecv_statesFromPb_ofEnv_ok mmpl gh W gu2b_exactEnv_sub_fromPbGuardedEnv hA

/-- Closed `SpqrRecvPlacedContractsOfEnv` on `trTrapExternsPlaced` with
`e2b_StatesFromPbExactEnv W.C.F` in place of coarse `StatesFromPbEnv` (`128` ops). -/
theorem gu2b_cliSpqrRecvPlacedContracts_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrRecvPlacedContractsOfEnv canonicalV1InnerHeap A lim W.C.F W.Q.K
      (fun g => DecodeStateBytesEnv g.st.bytes)
      (fun g => DecodeStateBytesEnv g.st.bytes)
      (InitInnerEnv W.C.F)
      (e2b_StatesFromPbExactEnv W.C.F)
      (fun g => StatesRecvExactPairEnv W.Q.K g.self g.msg)
      StatesIntoPbExactEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
  { cliSpqrRecvPlacedContracts_exact mmpl gh W hA hHmac with
    statesFromPb_ok := gu2b_cliSpqrRecv_statesFromPb_exact_ok mmpl gh W hA }

/-- Envelope-monotonic generalization of `gu2b_cliSpqrRecvPlacedContracts_exactFromPb` taking
`hFromPb : ∀ v1 evs, e2b_StatesFromPbExactEnv W.C.F v1 evs → StatesFromPbEnv' v1 evs` instead of
the unprovable `StatesFromPbEnv` inclusion in `SpqrV1PlacedSeamsBudgetInst.cliSpqrRecvPlacedContracts_ofEnv`. -/
theorem gu2b_cliSpqrRecvPlacedContracts_ofEnv_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecodeStateEnv' : List (BitVec 8) → List AllocEvent → Prop}
    {StatesFromPbEnv' : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi W.C.F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hDec : ∀ bs evs, DecodeStateBytesEnv bs evs → DecodeStateEnv' bs evs)
    (hFromPb : ∀ v1 evs, e2b_StatesFromPbExactEnv W.C.F v1 evs → StatesFromPbEnv' v1 evs)
    (hIntoPb : ∀ g evs, StatesIntoPbExactEnv g evs → StatesIntoPbEnv' g evs)
    (hRecv : ∀ st msg evs, StatesRecvExactPairEnv W.Q.K st msg evs → StatesRecvEnv' st msg evs) :
    SpqrRecvPlacedContractsOfEnv canonicalV1InnerHeap A lim W.C.F W.Q.K
      (fun g => DecodeStateEnv' g.st.bytes)
      (fun g => DecodeStateEnv' g.st.bytes)
      (InitInnerEnv W.C.F)
      StatesFromPbEnv'
      (fun g => StatesRecvEnv' g.self g.msg)
      StatesIntoPbEnv'
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
  have hBase := gu2b_cliSpqrRecvPlacedContracts_exactFromPb mmpl gh W hA hHmac
  exact
    { hBase with
      decodeState_ok := subroutine_ok_mono hBase.decodeState_ok
        (fun (g, stB) _ _ hpre => by
          dsimp only [withLsCodeRoLoaded, decodeStatePlacedSpecXOfEnv,
            LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget.spqrDecodeStatePlacedSpecOfEnv]
            at hpre ⊢
          refine Satisfies.mono ?_ hpre
          refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
          exact Entails.pure_mono fun ⟨h1, h2, h3, hfit⟩ =>
            ⟨h1, h2, h3, hfit.mono (hDec g.st.bytes)⟩)
        (fun (g, stB) _ _ _ hpost => by
          dsimp only [withLsCodeRoLoaded, decodeStatePlacedSpecXOfEnv,
            LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget.spqrDecodeStatePlacedSpecOfEnv]
            at hpost ⊢
          refine Satisfies.mono ?_ hpost
          refine sepConj_mono_left (sepConj_mono_left (Entails.sepExists_mono fun evs => ?_))
          refine sepConj_mono_left ?_
          exact Entails.pure_mono fun ⟨h1, hevs⟩ => ⟨h1, hDec g.st.bytes evs hevs⟩)
        (fun _ _ _ _ hp => hp)
      statesFromPb_ok := gu2b_cliSpqrRecv_statesFromPb_ofEnv_ok mmpl gh W hFromPb hA
      statesRecv_ok := subroutine_ok_mono hBase.statesRecv_ok
        (fun (g, stB) _ _ hpre => by
          dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
            LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
            at hpre ⊢
          refine Satisfies.mono ?_ hpre
          refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
          exact Entails.pure_mono fun ⟨h1, h2, h3, h4, hfit, hlr⟩ =>
            ⟨h1, h2, h3, h4, hfit.mono (hRecv g.self g.msg), hlr⟩)
        (fun (g, stB) _ _ _ hpost => by
          dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
            LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
            at hpost ⊢
          refine Satisfies.mono ?_ hpost
          refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
          refine sepConj_mono_left ?_
          exact Entails.pure_mono fun ⟨h1, hevs⟩ => ⟨h1, hRecv g.self g.msg evs hevs⟩)
        (fun _ _ _ _ hp => hp)
      statesIntoPb_ok := subroutine_ok_mono hBase.statesIntoPb_ok
        (fun (g, stB) _ _ hpre => by
          dsimp only [withLsCodeRoLoaded, statesIntoPbPlacedSpecXOfEnv,
            LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv]
            at hpre ⊢
          refine Satisfies.mono ?_ hpre
          refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
          exact Entails.pure_mono fun ⟨h1, h2, hfit⟩ => ⟨h1, h2, hfit.mono (hIntoPb g)⟩)
        (fun (g, stB) _ _ _ hpost => by
          dsimp only [withLsCodeRoLoaded, statesIntoPbPlacedSpecXOfEnv,
            LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv]
            at hpost ⊢
          refine Satisfies.mono ?_ hpost
          refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
          refine sepConj_mono_left ?_
          exact Entails.pure_mono fun ⟨h1, hevs⟩ => ⟨h1, hIntoPb g evs hevs⟩)
        (fun _ _ _ _ hp => hp) }

private theorem gu2b_bridge_spqrRecvSpecXT_to_innerSpecXT [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : VecArg → VecArg → List AllocEvent → Prop}
    (hSub : ∀ st msg evs, Env₁ st msg evs → Env₂ st msg evs)
    (hok : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv W.C.F W.Q.K) Env₁)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) Env₂)) := by
  have heq_cro (m : Memory) :
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m =
        LibsignalCodeRoLoaded lsmpl m :=
    propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  exact subroutine_ok_mono hok
    (fun ((st, msg, ret), stB) Fr s hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv, withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecXOfEnv, lsLogOff] at hpre ⊢
      rw [heq_cro s.mem] at hpre
      have hpre' : s.mem ⊨
          ⌜FitsEnv M lim stB (Env₂ st msg)⌝ ∗
          (⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
            (⌜st.bytes.length < 2 ^ 32 ∧ msg.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
              CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
              st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
              (CryptoVerification.lsLogFilterAddr ↦₆₄ 0#64) ∗
              A.pool lim stB s ∗ stackAt s.sp spqrRecvStack ∗
              ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ Fr)) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpre'
      rcases hpre' with ⟨hfit, ⟨hx0, hx1, hx8⟩, hrest⟩
      have hgoal : s.mem ⊨
          ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret ∧
            FitsEnv M lim stB (Env₁ st msg)⌝ ∗
          (⌜st.bytes.length < 2 ^ 32 ∧ msg.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
            CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
            st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
            (CryptoVerification.lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim stB s ∗ stackAt s.sp spqrRecvStack ∗
            ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ Fr) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx1, hx8, hfit.mono (hSub st msg)⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hgoal)
    (fun ((st, msg, ret), stB) Fr s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv, withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecXOfEnv, lsLogOff] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨
          ⌜sf.trace = s0.trace ∧ Env₁ st msg evs ∧
            ¬ (spqrV1Recv W.C.F W.Q.K).recvPanics st.bytes msg.bytes⌝ ∗
          (CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
            st.at A.repAlloc ∗ msg.at A.repAlloc ∗
            CryptoVerification.LibsignalSpqrV1.recvResultExactKeyAt A.repAlloc ret
              ((spqrV1Recv W.C.F W.Q.K).recv st.bytes msg.bytes) ∗
            (CryptoVerification.lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp spqrRecvStack ∗ Fr) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨⟨htr, hevs, hnp⟩, hrest⟩
      have hgoal : sf.mem ⊨ ⌜Env₂ st msg evs⌝ ∗
          (⌜sf.trace = s0.trace ∧ ¬ (spqrV1Recv W.C.F W.Q.K).recvPanics st.bytes msg.bytes⌝ ∗
            (CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
              st.at A.repAlloc ∗ msg.at A.repAlloc ∗
              CryptoVerification.LibsignalSpqrV1.recvResultExactKeyAt A.repAlloc ret
                ((spqrV1Recv W.C.F W.Q.K).recv st.bytes msg.bytes) ∗
              (CryptoVerification.lsLogFilterAddr ↦₆₄ 0#64) ∗
              A.pool lim (M.stepEvents evs stB) sf ∗ stackAt s0.sp spqrRecvStack ∗ Fr)) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨hSub st msg evs hevs, ⟨htr, hnp⟩, hrest⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hgoal)
    (fun _ _ _ _ hpanic => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv, withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecXOfEnv] at hpanic ⊢
      exact hpanic)

/-- Exact-`from_pb` companion to `SpqrExactEnvDefs.CliSpqrRecvTightLinkedEnv`: replaces coarse
`StatesFromPbEnv` (`128` ops) with the exact 12-arm `e2b_StatesFromPbExactEnv W.C.F`. -/
def gu2b_CliSpqrRecvExactFromPbLinkedEnv (W : CliHooks) (st _msg : VecArg)
    (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    SpqrRecvTightLinkedEnv W.C.F W.Q.K
      DecodeStateBytesEnv (e2b_StatesFromPbExactEnv W.C.F) StatesIntoPbExactEnv
      (StatesRecvExactPairEnv W.Q.K)
      st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- Closed linked `Block 329` (`spqr::recv`) witness (raw `spqrRecvPlacedSpecXTOfEnv` form) at
`gu2b_CliSpqrRecvExactFromPbLinkedEnv W`. -/
theorem gu2b_cliSpqrRecv_placed_ok_exactFromPb_raw [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv W.C.F W.Q.K)
        (gu2b_CliSpqrRecvExactFromPbLinkedEnv W)) :=
  spqr_recv_placed_ok_blockProgram_ext_of_contracts_tightLinked
    (trTrapExternsPlaced_isPanic mmpl gh W)
    (gu2b_cliSpqrRecvPlacedContracts_exactFromPb mmpl gh W hA hHmac)

/-- Closed linked `Block 329` (`spqr::recv`) seam (`spqrRecvPlacedInnerSpecXTOfEnv` form) at
`gu2b_CliSpqrRecvExactFromPbLinkedEnv W`. -/
theorem gu2b_cliSpqrRecv_placed_ok_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (gu2b_CliSpqrRecvExactFromPbLinkedEnv W))) :=
  gu2b_bridge_spqrRecvSpecXT_to_innerSpecXT (fun _ _ _ h => h)
    (gu2b_cliSpqrRecv_placed_ok_exactFromPb_raw mmpl gh W hA hHmac)

/-- Envelope-monotonic lift of `gu2b_cliSpqrRecv_placed_ok_exactFromPb` to any `RecvEnv` containing
`gu2b_CliSpqrRecvExactFromPbLinkedEnv W`. -/
theorem gu2b_cliSpqrRecv_placed_ok_ofEnv_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    (hSub : ∀ st msg evs, gu2b_CliSpqrRecvExactFromPbLinkedEnv W st msg evs → RecvEnv st msg evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) :=
  gu2b_bridge_spqrRecvSpecXT_to_innerSpecXT hSub
    (gu2b_cliSpqrRecv_placed_ok_exactFromPb_raw mmpl gh W hA hHmac)

/-- Exact-`from_pb` upgrade of `SpqrV1PlacedSeamsBudgetInst.cliSpqrRecv_placed_ok_c07TightLinked`:
takes `e2b_StatesFromPbExactEnv W.C.F v1 evs → StatesFromPbTightEnv evs` instead of the false
coarse `StatesFromPbEnv` inclusion. -/
theorem gu2b_cliSpqrRecv_placed_ok_c07TightLinked_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi W.C.F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hDec : ∀ bs evs, DecodeStateBytesEnv bs evs → DecodeStateTightEnv evs)
    (hFromPb : ∀ v1 evs, e2b_StatesFromPbExactEnv W.C.F v1 evs → StatesFromPbTightEnv evs)
    (hIntoPb : ∀ g evs, StatesIntoPbExactEnv (F := W.C.F) g evs → StatesIntoPbTightEnv evs)
    (hRecv : ∀ st msg evs,
      StatesRecvExactPairEnv (F := W.C.F) W.Q.K st msg evs → StatesRecvEnv' st msg evs) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st _msg evs =>
            ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
              SpqrRecvC07TightLinkedEnv W.C.F W.Q.K StatesRecvEnv'
                st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs))) :=
  gu2b_bridge_spqrRecvSpecXT_to_innerSpecXT (fun _ _ _ h => h)
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07TightLinked
      (trTrapExternsPlaced_isPanic mmpl gh W)
      (gu2b_cliSpqrRecvPlacedContracts_ofEnv_exactFromPb mmpl gh W hA hHmac
        hDec hFromPb hIntoPb hRecv))

/-- Exact-`from_pb` upgrade of `SpqrV1PlacedSeamsBudgetInst.cliSpqrRecv_placed_ok_c07c09aTightLinked`:
takes `e2b_StatesFromPbExactEnv W.C.F v1 evs → StatesFromPbTightEnv evs` instead of the false
coarse `StatesFromPbEnv` inclusion. -/
theorem gu2b_cliSpqrRecv_placed_ok_c07c09aTightLinked_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hDec : ∀ bs evs, DecodeStateBytesEnv bs evs → DecodeStateTightEnv evs)
    (hFromPb : ∀ v1 evs, e2b_StatesFromPbExactEnv W.C.F v1 evs → StatesFromPbTightEnv evs)
    (hIntoPb : ∀ g evs, StatesIntoPbExactEnv (F := W.C.F) g evs → StatesIntoPbTightEnv evs)
    (hRecv : ∀ st msg evs, StatesRecvExactPairEnv (F := W.C.F) W.Q.K st msg evs →
      StatesRecvProtoEnv (F := W.C.F) st msg evs) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st _msg evs =>
            ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
              SpqrRecvC07C09aTightLinkedEnv W.C.F W.Q.K
                st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs))) :=
  gu2b_bridge_spqrRecvSpecXT_to_innerSpecXT (fun _ _ _ h => h)
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07c09aTightLinked
      (trTrapExternsPlaced_isPanic mmpl gh W)
      (gu2b_cliSpqrRecvPlacedContracts_ofEnv_exactFromPb mmpl gh W hA hHmac
        hDec hFromPb hIntoPb hRecv))

/-! ## 4. `Block 427` (`spqr::send::<Coins>`) Exact-`from_pb` & Guarded-Tight Bridges -/

/-- `Block 333` (`<States>::from_pb`) on `spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))`
lifted from `e2b_StatesFromPbExactEnv W.C.F` to any `FromPbValEnv`. -/
theorem gu2b_cliSpqrSend_statesFromPb_xOfEnv_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hFromPbSub : ∀ v1 evs, e2b_StatesFromPbExactEnv W.C.F v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.statesFromPbPlacedSpecXOfEnv M A lim W.C.F
          (fun g => FromPbValEnv g.pb))) := by
  have hok : subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv
          M A lim W.C.F FromPbValEnv)) :=
    ls_subroutine_ok_of_blockProgram_cro
      (gu2b_statesFromPb_placed_okX_ofEnv_cliExt mmpl gh W hFromPbSub hA (fun _ _ => rfl))
  have hjt_eq :
      CryptoVerification.SpqrV1.States.FromPb.statesFromPbJumpTablePlacedAt =
        statesFromPbJumpTablePlacedAt := rfl
  exact subroutine_ok_mono hok
    (fun (g, stB) R s0 hpre => by
      dsimp only [withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.statesFromPbPlacedSpecXOfEnv] at hpre ⊢
      rw [hjt_eq]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre)
    (fun (g, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.statesFromPbPlacedSpecXOfEnv] at hpost ⊢
      rw [hjt_eq] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      exact ⟨evs, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost⟩)
    (fun _ _ _ _ hp => hp)

/-- Exact-`from_pb` upgrade of `SpqrSendCoinsTightCliInst.hpt_spqrSendPlacedContractsOfEnv_of_cli`:
takes `∀ v1 evs, e2b_StatesFromPbExactEnv W.C.F v1 evs → FromPbValEnv v1 evs` instead of coarse
`StatesFromPbEnv`. -/
theorem gu2b_spqrSendPlacedContractsOfEnv_of_cli_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hDecSub : ∀ bs evs, DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hFromPbSub : ∀ v1 evs, e2b_StatesFromPbExactEnv W.C.F v1 evs → FromPbValEnv v1 evs)
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
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  { hpt_spqrSendPlacedContractsOfEnv_of_cli mmpl gh W hDecSub (fun _ _ h => h) hA hHmac with
    statesFromPb_ok := gu2b_cliSpqrSend_statesFromPb_xOfEnv_on mmpl gh W hFromPbSub hA }

private theorem gu2b_cliGhostExterns_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

/-- Exact-`from_pb` upgrade of `SpqrSendCoinsTightCliInst.hpt_cliSpqrSendCoins_placed_ok_of_decode_fromPb`:
CLI `Block 427` producer for any `(DecBytesEnv, FromPbValEnv)` containing
`(DecodeStateBytesEnv, e2b_StatesFromPbExactEnv W.C.F)`. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_of_decode_fromPb_exact [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hDecSub : ∀ bs evs, DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hFromPbSub : ∀ v1 evs, e2b_StatesFromPbExactEnv W.C.F v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (hpt_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv))) := by
  have hraw := hpt_spqrSendCoins_placed_ok_of_contracts_tight
    (cliSpqrSendAllocContractsPlaced mmpl gh W hA.toCliGhostAllocHooks)
    (gu2b_spqrSendPlacedContractsOfEnv_of_cli_exactFromPb mmpl gh W hDecSub hFromPbSub hA hHmac)
    (spqrSendExtraContractsPlaced_of_cli mmpl gh W hA hHmac)
  have hblk_wp : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 427
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (hpt_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv))) := by
    rwa [← IsLsBlockProg.eq_blockProgram
      (prog := spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))]
  have hwp_eq :
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
        cliGhostExterns gh (cliExternsPlaced mmpl W) := by
    funext sym; unfold Rust.withPanics; split
    · next hp => exact (gu2b_cliGhostExterns_isPanic mmpl gh W sym hp).symm
    · rfl
  have hblk_ext : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 427
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
          (hpt_SpqrSendCoinsOfDecodeFromPbEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv))) := by
    simpa only [hwp_eq] using hblk_wp
  have hok : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (spqrV1 W.C.F W.Q.K)
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
        spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded, LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecOfEnv] at hpre ⊢
      rw [heq_cro s.mem] at hpre
      rw [hcoinsAt]
      exact hpre)
    (fun (sc, stB) _ s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded, LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecOfEnv] at hpost ⊢
      rw [hcoinsAfter] at hpost
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hd, htr, hnp, hevs⟩ => ⟨hevs, hd, htr, hnp⟩)
    (fun _ _ _ _ hpanic => hpanic)

/-- Exact-`from_pb` cap-free `SendCall`-indexed `Block 427` envelope: replaces coarse
`StatesFromPbEnv` in `SpqrExactEnvDefs.SpqrSendCoinsTightLinkedEnv` with
`e2b_StatesFromPbExactEnv F`. -/
abbrev gu2b_SpqrSendCoinsExactFromPbLinkedEnv (F : ShaCompress) (K : MlKem) :
    SendCall → List AllocEvent → Prop :=
  hpt_SpqrSendCoinsOfDecodeFromPbEnv F K DecodeStateBytesEnv (e2b_StatesFromPbExactEnv F)

/-- Byte-slice-indexed `SpqrSendBudgetEnv` form of `gu2b_SpqrSendCoinsExactFromPbLinkedEnv`. -/
abbrev gu2b_SpqrSendCoinsExactFromPbBytesEnv (F : ShaCompress) (K : MlKem) : SpqrSendBudgetEnv :=
  hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv F K DecodeStateBytesEnv (e2b_StatesFromPbExactEnv F)

/-- Unconditional `Block 427` (`spqr::send::<Coins>`) producer at
`gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K`. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K))) :=
  gu2b_cliSpqrSendCoins_placed_ok_of_decode_fromPb_exact mmpl gh W
    (fun _ _ h => h) (fun _ _ h => h) hA hHmac

/-- `hHmac`-discharged `Block 427` producer at `gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K`
on `(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)`. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_exactFromPb_fine [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K))) :=
  gu2b_cliSpqrSendCoins_placed_ok_exactFromPb mmpl gh W hGSpqr
    (hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart lim gh W hPl_mng)

/-- `(M, I)`-generic `hHmac`-discharged `Block 427` producer at
`gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K` on `mallocngHookRustCliAllocBudget`. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_exactFromPb_mallocngHook [LibsignalPlacement]
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
        (spqrSendCoinsPlacedSpecTOfEnv M
          (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K))) :=
  gu2b_cliSpqrSendCoins_placed_ok_exactFromPb mmpl gh W hGSpqr
    (hpo_cliLibcruxHmac_mallocngHook_budget_hookSat hS γ mmpl tp brkStart lim gh W hPl_mng)

private theorem gu2b_seqEnv_mono_left
    {P P' Q : List AllocEvent → Prop} {evs : List AllocEvent}
    (hP : ∀ e, P e → P' e) (h : SeqEnv P Q evs) :
    SeqEnv P' Q evs :=
  h.imp (hP evs) fun ⟨e1, e2, heq, h1, h2⟩ => ⟨e1, e2, heq, hP e1 h1, h2⟩

/-- Pointwise monotonicity of `gu2b_SpqrSendCoinsExactFromPbLinkedEnv F K x` into
`hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv F K DecBytesEnv FromPbValEnv x.st.bytes x.rest`, routing
the `from_pb` branch through `e2b_StatesFromPbExactEnv F v1` instead of coarse `StatesFromPbEnv`. -/
theorem gu2b_spqrSendCoinsExactFromPb_mono_leaves
    {F : ShaCompress} {K : MlKem}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    {x : SendCall} {evs : List AllocEvent}
    (hDec : ∀ e, DecodeStateBytesEnv x.st.bytes e → DecBytesEnv x.st.bytes e)
    (hFromPb : ∀ pq v1 e,
      spqrDecodeState x.st.bytes = .ok pq →
      pq.inner = some (.v1 v1) →
      e2b_StatesFromPbExactEnv F v1 e → FromPbValEnv v1 e)
    (hevs : gu2b_SpqrSendCoinsExactFromPbLinkedEnv F K x evs) :
    hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv F K DecBytesEnv FromPbValEnv x.st.bytes x.rest evs := by
  dsimp only [gu2b_SpqrSendCoinsExactFromPbLinkedEnv, hpt_SpqrSendCoinsOfDecodeFromPbEnv,
    hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv] at hevs ⊢
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
      exact gu2b_seqEnv_mono_left hDec hevs
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
              exact gu2b_seqEnv_mono_left (hFromPb pq v1 · hdec hinner) h2
          | ok st_states =>
            rw [hfpb] at h2
            exact gu2b_seqEnv_mono_left (hFromPb pq v1 · hdec hinner) h2

/-- Generic guarded `Block 427` producer routed through `gu2b_SpqrSendCoinsExactFromPbLinkedEnv`
(false-guard `FitsEnv` unsatisfiability via `hpt_not_fitsEnv_of_univ`). -/
theorem gu2b_cliSpqrSendCoins_placed_ok_guarded_exactFromPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Guard : SendCall → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hTrue : ∀ sc evs, Guard sc →
      gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K sc evs → SendEnv sc evs)
    (hFalse : ∀ sc evs, ¬ Guard sc → SendEnv sc evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) := by
  have hok := gu2b_cliSpqrSendCoins_placed_ok_exactFromPb mmpl gh W hA hHmac
  exact subroutine_ok_mono hok
    (fun (sc, stB) _ _ hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrSendCoinsPlacedSpecTOfEnv,
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
        spqrSendCoinsPlacedSpecTOfEnv,
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

/-- `hHmac`-discharged guarded `Block 427` producer routed through
`gu2b_SpqrSendCoinsExactFromPbLinkedEnv` on `(fineCostModel, fineHookRustCliAllocBudget)`. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_guarded_exactFromPb_fine [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    {Guard : SendCall → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hTrue : ∀ sc evs, Guard sc →
      gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K sc evs → SendEnv sc evs)
    (hFalse : ∀ sc evs, ¬ Guard sc → SendEnv sc evs)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) :=
  gu2b_cliSpqrSendCoins_placed_ok_guarded_exactFromPb mmpl gh W hTrue hFalse hGSpqr
    (hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart lim gh W hPl_mng)

/-- Exact-`from_pb` upgrade of `SpqrSendCoinsTightCliInst.hpt_cliSpqrSendCoins_placed_ok_guarded_leaves_imp`:
requires `e2b_StatesFromPbExactEnv W.C.F v1 evs → FromPbValEnv v1 evs` under `Guard bs` (instead of
the unprovable `StatesFromPbEnv v1 evs → FromPbValEnv v1 evs` at `StatesFromPbTightEnv`). -/
theorem gu2b_cliSpqrSendCoins_placed_ok_guarded_leaves_imp_exact [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Guard : List (BitVec 8) → Prop}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hDecGuard : ∀ bs evs, Guard bs → DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hFromPbGuard : ∀ bs pq v1 evs, Guard bs →
      spqrDecodeState bs = .ok pq → pq.inner = some (.v1 v1) →
      e2b_StatesFromPbExactEnv W.C.F v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (fun sc => hpt_SpqrSendGuardedImplBytesEnv Guard
            (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv)
            sc.st.bytes sc.rest))) :=
  gu2b_cliSpqrSendCoins_placed_ok_guarded_exactFromPb (Guard := fun sc => Guard sc.st.bytes)
    mmpl gh W
    (fun sc _ hG hevs _ =>
      gu2b_spqrSendCoinsExactFromPb_mono_leaves
        (hDecGuard sc.st.bytes · hG)
        (hFromPbGuard sc.st.bytes · · · hG)
        hevs)
    (fun _ _ hnG hG => absurd hG hnG)
    hA hHmac

/-- Exact-`from_pb` upgrade of `SpqrSendCoinsTightCliInst.hpt_cliSpqrSendCoins_placed_ok_guarded_leaves_ite`. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_guarded_leaves_ite_exact [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Guard : List (BitVec 8) → Prop}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    {FromPbValEnv : V1State → List AllocEvent → Prop}
    (hDecGuard : ∀ bs evs, Guard bs → DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hFromPbGuard : ∀ bs pq v1 evs, Guard bs →
      spqrDecodeState bs = .ok pq → pq.inner = some (.v1 v1) →
      e2b_StatesFromPbExactEnv W.C.F v1 evs → FromPbValEnv v1 evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (fun sc => hpt_SpqrSendGuardedIteBytesEnv Guard
            (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv FromPbValEnv)
            sc.st.bytes sc.rest))) :=
  gu2b_cliSpqrSendCoins_placed_ok_guarded_exactFromPb (Guard := fun sc => Guard sc.st.bytes)
    mmpl gh W
    (fun sc evs hG hevs => by
      simp only [hpt_SpqrSendGuardedIteBytesEnv, hG, ↓reduceIte]
      exact gu2b_spqrSendCoinsExactFromPb_mono_leaves
        (hDecGuard sc.st.bytes · hG)
        (hFromPbGuard sc.st.bytes · · · hG)
        hevs)
    (fun sc _ hnG => by
      simp only [hpt_SpqrSendGuardedIteBytesEnv, hnG, ↓reduceIte])
    hA hHmac

/-- Concrete `SpqrStateTight640`-guarded `Block 427` producer at `FromPbValEnv := fun _ => StatesFromPbTightEnv`
(implication form) with the `from_pb` tight inclusion discharged. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_spqrStateTight640_imp [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hDecGuard : ∀ bs evs, SpqrStateTight640 W.C.F W.Q.K bs →
      DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (fun sc => hpt_SpqrSendGuardedImplBytesEnv (SpqrStateTight640 W.C.F W.Q.K)
            (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv
              (fun _ => StatesFromPbTightEnv))
            sc.st.bytes sc.rest))) :=
  gu2b_cliSpqrSendCoins_placed_ok_guarded_leaves_imp_exact mmpl gh W hDecGuard
    (fun _ _ _ _ hSt hdec hpb hevs =>
      gu2b_exactEnv_sub_tight_of_spqrStateTight640 hSt hdec hpb hevs)
    hA hHmac

/-- Concrete `SpqrStateTight640`-guarded `Block 427` producer at `FromPbValEnv := fun _ => StatesFromPbTightEnv`
(`if-then-else` form) with `hFromPbGuard` discharged. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_spqrStateTight640_ite [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hDecGuard : ∀ bs evs, SpqrStateTight640 W.C.F W.Q.K bs →
      DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (fun sc => hpt_SpqrSendGuardedIteBytesEnv (SpqrStateTight640 W.C.F W.Q.K)
            (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv
              (fun _ => StatesFromPbTightEnv))
            sc.st.bytes sc.rest))) :=
  gu2b_cliSpqrSendCoins_placed_ok_guarded_leaves_ite_exact mmpl gh W hDecGuard
    (fun _ _ _ _ hSt hdec hpb hevs =>
      gu2b_exactEnv_sub_tight_of_spqrStateTight640 hSt hdec hpb hevs)
    hA hHmac

/-- Concrete `TopStateTight`-guarded `Block 427` producer at `FromPbValEnv := fun _ => StatesFromPbTightEnv`
(implication form) with `hFromPbGuard` discharged. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_topStateTight_imp [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hDecGuard : ∀ bs evs, TopStateTight W.C.F W.Q.K bs →
      DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (fun sc => hpt_SpqrSendGuardedImplBytesEnv (TopStateTight W.C.F W.Q.K)
            (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv
              (fun _ => StatesFromPbTightEnv))
            sc.st.bytes sc.rest))) :=
  gu2b_cliSpqrSendCoins_placed_ok_guarded_leaves_imp_exact mmpl gh W hDecGuard
    (fun _ _ _ _ hTop hdec hpb hevs =>
      gu2b_exactEnv_sub_tight_of_topStateTight hTop hdec hpb hevs)
    hA hHmac

/-- Concrete `TopStateTight`-guarded `Block 427` producer at `FromPbValEnv := fun _ => StatesFromPbTightEnv`
(`if-then-else` form) with `hFromPbGuard` discharged. -/
theorem gu2b_cliSpqrSendCoins_placed_ok_topStateTight_ite [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hDecGuard : ∀ bs evs, TopStateTight W.C.F W.Q.K bs →
      DecodeStateBytesEnv bs evs → DecBytesEnv bs evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩)
          (fun sc => hpt_SpqrSendGuardedIteBytesEnv (TopStateTight W.C.F W.Q.K)
            (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K DecBytesEnv
              (fun _ => StatesFromPbTightEnv))
            sc.st.bytes sc.rest))) :=
  gu2b_cliSpqrSendCoins_placed_ok_guarded_leaves_ite_exact mmpl gh W hDecGuard
    (fun _ _ _ _ hTop hdec hpb hevs =>
      gu2b_exactEnv_sub_tight_of_topStateTight hTop hdec hpb hevs)
    hA hHmac

/-! ## 5. Complete Exact-`from_pb` `SpqrV1PlacedSeamsOfEnv` Bundles -/

/-- Complete `SpqrV1PlacedSeamsOfEnv` assembly at
`(InitialStateEnv W.C.F, gu2b_CliSpqrRecvExactFromPbLinkedEnv W, gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K)`
with both `spqr::recv` and `spqr::send::<Coins>` routed through `e2b_StatesFromPbExactEnv W.C.F`. -/
theorem gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F)
      (gu2b_CliSpqrRecvExactFromPbLinkedEnv W)
      (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K) where
  spqrInitialState := cliSpqrInitialState_placed_ok_ofEnv mmpl gh W (fun _ _ h => h) hA
  spqrRecv := gu2b_cliSpqrRecv_placed_ok_exactFromPb mmpl gh W hA hHmac
  spqrSendCoins := gu2b_cliSpqrSendCoins_placed_ok_exactFromPb mmpl gh W hA hHmac

/-- `hHmac`-discharged exact-`from_pb` `SpqrV1PlacedSeamsOfEnv` bundle on
`(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)`. -/
theorem gu2b_spqrV1PlacedSeams_exactFromPb [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh) :
    SpqrV1PlacedSeamsOfEnv fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim mmpl gh W
      (InitialStateEnv W.C.F)
      (gu2b_CliSpqrRecvExactFromPbLinkedEnv W)
      (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K) :=
  gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac mmpl gh W hGSpqr
    (hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart lim gh W hPl_mng)

/-- `(M, I)`-generic `hHmac`-discharged exact-`from_pb` `SpqrV1PlacedSeamsOfEnv` bundle on
`mallocngHookRustCliAllocBudget`. -/
theorem gu2b_spqrV1PlacedSeams_exactFromPb_mallocngHook [LibsignalPlacement]
    {M : AllocCostModel} {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks M
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim gh) :
    SpqrV1PlacedSeamsOfEnv M
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim mmpl gh W
      (InitialStateEnv W.C.F)
      (gu2b_CliSpqrRecvExactFromPbLinkedEnv W)
      (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K) :=
  gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac mmpl gh W hGSpqr
    (hpo_cliLibcruxHmac_mallocngHook_budget_hookSat hS γ mmpl tp brkStart lim gh W hPl_mng)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
