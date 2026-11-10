/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsInst
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget

/-!
# Budget-Threaded SPQR-V1 Seam Bundle & Linked `spqr::recv` Witness

Assembles closed `SpqrRecvPlacedContractsOfEnv` and linked `spqr::recv` (Block 329) budget
contracts at `CliSpqrRecvTightLinkedEnv` on `Slots.trTrapExternsPlaced`, envelope-monotonic lifts
for `spqr::initial_state` (Block 327), and complete `SpqrV1PlacedSeamsOfEnv` bundles.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst

export LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (DecodeStateBytesEnv StatesRecvExactPairEnv CliSpqrRecvTightLinkedEnv)

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkPC_366 blkPl_366 blkPC_368 blkPl_368
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib
   ls_subroutine_ok_cl_of_block lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Message MlKem Params States V1State spqrAuthApi spqrHkdfWith spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall VecArg spqrRecvStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunGlue (hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliExternsPlaced_rngFill lsRngFillSym trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost canonicalV1InnerHeap optProtoInnerStateAt_canonical_eq_drop)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.SpqrV1.Top.Recv
  (ls_subroutine_ok_cro_of_callInv ls_subroutine_ok_cro_of_cro spqrRecvPlacedProg)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv MallocngCostModelIface MallocngCostModelSound
   RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
  (spqrInitialStatePlacedInnerSpec spqrInitialStatePlacedInnerSpecOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget (CliSpqrSendPeerSeams)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget (SpqrSendCoinsExactEnv)
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
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_framelessMemcpy_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
  (cliDeallocBudget_at_block cliSpqrRecv_chainFromPb_ok_trTrap cliSpqrRecv_chainFrom_ok_trTrap
   cliSpqrRecv_chainIntoPb_ok_trTrap cliSpqrRecv_chainNew_ok_trTrap
   cliSpqrRecv_dropEpochSlice_ok_trTrap)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
  (cliSpqrDecodeState_recv_trTrap_closed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (cliDrop_267_cl cliDrop_270_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (CliSpqrRecvTightLinkedEnv DecodeStateBytesEnv StatesRecvExactPairEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
  (hpo_cliLibcruxHmac_budget_hookSat hpo_cliLibcruxHmac_mallocngHook_budget_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliDrop_266_cl cliDrop_269_cl cliDrop_273_cl cliEncodeToVec_placed_ok
   cliInitInner_callInv_placed_ok cliSpqrInitialState_placed_ok_closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliChainAddEpoch_placed_ok cliChainRecvKey_placed_ok cliMessageDeserialize_placed_ok
   cliSpqrSendCoins_placed_ok_of_peerSeams cliStatesPlacedSeamsExt)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
  (cliStatesIntoPb_recv_trTrap_exact_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv spqrRecvPlacedInnerSpecXOfEnv
   spqrRecvPlacedInnerSpecXTOfEnv spqrSendCoinsPlacedSpecTOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (PqRatchetStateEncodeToVecPlacedOkExt pqRatchetStateEncodeToVecSpecX)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withLsRoLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget (StatesRecvExactEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
  (MessageDeserializePlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
  (spqrRecvPlacedRawSpecXOfEnv spqrRecvPlacedSpecXOfEnv spqrRecvPlacedSpecXTOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContractsOfEnv decodeStatePlacedSpecXOfEnv
   statesFromPbPlacedSpecXOfEnv statesIntoPbPlacedSpecXOfEnv statesRecvPlacedSpecOfEnv)

/-! ## 1. Block-Program Transfer & Panic-Symbol Preservation on `trTrapExternsPlaced` -/

private theorem hExt_withPanics (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym hne
  refine (?_ : Rust.withPanics ext sym =
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym).trans
    (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)
  unfold Rust.withPanics
  rw [hExt sym hne]

private theorem trTrap_hExt (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
  fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne]

private theorem lift_rebase_cl_to_recv [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg calleeProg j (Rust.withPanics ext)]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (spqrRecvPlacedProg ext) entry (withLsCodeLoaded lsmpl spec) := by
  have hcl : subroutine_ok (spqrRecvPlacedProg ext) entry (withLsCl lsmpl spec) :=
    ls_subroutine_ok_cl_of_block (callerProg := spqrRecvPlacedProg ext)
      (i := 329) (j := j) hcallee (by decide) hj hj_unmut
  exact subroutine_ok_mono hcl
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

private theorem lift_blockProgram_cl_to_recv [LibsignalPlacement] {α : Type}
    {j : Nat} {ext : String → Option (State → State)}
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns := by decide)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j (Rust.withPanics ext))
      entry (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (spqrRecvPlacedProg ext) entry (withLsCodeLoaded lsmpl spec) := by
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl j (Rust.withPanics ext))
      j (Rust.withPanics ext) := ⟨rfl, hext_j⟩
  exact lift_rebase_cl_to_recv hcallee hj hj_unmut

theorem trTrapExternsPlaced_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        some Rust.panicked := by
  intro sym hsym
  have hp := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at hp
  have hne : sym ≠ lsRngFillSym := by
    intro heq
    subst heq
    rw [cliExternsPlaced_rngFill mmpl gh W] at hp
    exact absurd hp (by simp)
  have hbeq : (sym == lsRngFillSym) = false := beq_false_of_ne hne
  simp only [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq, Bool.false_eq_true, ↓reduceIte]
  exact hp.symm

/-!
## 2. Exact Leaf Envelopes (`SpqrExactEnvDefs`) & Closed `SpqrRecvPlacedContractsOfEnv` (`Block 329`)
-/

/-- Closed `SpqrRecvPlacedContractsOfEnv` on
    `trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` with no
    envelope inclusion hypotheses beyond `hA : CliGhostSpqrAllocHooks M A lim gh` and `hHmac`. -/
theorem cliSpqrRecvPlacedContracts_exact [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrRecvPlacedContractsOfEnv canonicalV1InnerHeap A lim W.C.F W.Q.K
      (fun g => DecodeStateBytesEnv g.st.bytes)
      (fun g => DecodeStateBytesEnv g.st.bytes)
      (InitInnerEnv W.C.F)
      StatesFromPbEnv
      (fun g => StatesRecvExactPairEnv W.Q.K g.self g.msg)
      StatesIntoPbExactEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) where
  dealloc_ok :=
    cliDeallocBudget_at_block mmpl gh W hA.toCliGhostAllocHooks
      (hExt_withPanics mmpl gh W (trTrap_hExt mmpl gh W))
      (prog := spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (i := 329)
  memcpy_ok :=
    spqr_hook_ok_of_mem
      (prog := spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (i := 329)
      (hookSat_of_eq (hExt_withPanics mmpl gh W (trTrap_hExt mmpl gh W) "memcpy" (by decide))
        (cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hA.toCliGhostAllocHooks))
      (by decide) (by decide) (by decide)
  dropEpochSlice_ok := cliSpqrRecv_dropEpochSlice_ok_trTrap mmpl gh W hA.toCliGhostAllocHooks
  dropOptProtoInnerState_ok :=
    lift_blockProgram_cl_to_recv (j := 267)
      (hcallee := cliDrop_267_cl mmpl gh W hA.toCliGhostAllocHooks (trTrap_hExt mmpl gh W))
  dropOptProtoChain_ok :=
    lift_blockProgram_cl_to_recv (j := 266)
      (hcallee := cliDrop_266_cl mmpl gh W hA.toCliGhostAllocHooks (trTrap_hExt mmpl gh W))
  dropChain_ok :=
    lift_blockProgram_cl_to_recv (j := 269)
      (hcallee := cliDrop_269_cl mmpl gh W hA.toCliGhostAllocHooks (trTrap_hExt mmpl gh W))
  dropPqRatchetState_ok :=
    lift_blockProgram_cl_to_recv (j := 270)
      (hcallee := cliDrop_270_cl mmpl gh W hA.toCliGhostAllocHooks (trTrap_hExt mmpl gh W))
  dropStates_ok :=
    lift_blockProgram_cl_to_recv (j := 273)
      (hcallee := cliDrop_273_cl mmpl gh W hA.toCliGhostAllocHooks (trTrap_hExt mmpl gh W))
  decodeState_ok := cliSpqrDecodeState_recv_trTrap_closed_ok mmpl gh W hA.toCliGhostAllocHooks
  initInner_ok :=
    ls_subroutine_ok_cro_of_callInv
      (callerProg := spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (i := 329) (j := 324)
      (cliInitInner_callInv_placed_ok mmpl gh W hA (trTrap_hExt mmpl gh W))
  chainFrom_ok := cliSpqrRecv_chainFrom_ok_trTrap mmpl gh W hA.toCliGhostAllocHooks
  chainFromPb_ok := cliSpqrRecv_chainFromPb_ok_trTrap mmpl gh W hA.toCliGhostAllocHooks
  chainNew_ok := cliSpqrRecv_chainNew_ok_trTrap mmpl gh W hA.toCliGhostAllocHooks
  chainAddEpoch_ok :=
    ls_subroutine_ok_cro_of_callInv
      (callerProg := spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (i := 329) (j := 368)
      (cliChainAddEpoch_placed_ok mmpl gh W hA.toCliGhostAllocHooks
        (hExt_withPanics mmpl gh W (trTrap_hExt mmpl gh W)))
  chainRecvKey_ok :=
    ls_subroutine_ok_cro_of_callInv
      (callerProg := spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (i := 329) (j := 366)
      (cliChainRecvKey_placed_ok mmpl gh W hA
        (hExt_withPanics mmpl gh W (trTrap_hExt mmpl gh W)))
  chainIntoPb_ok := cliSpqrRecv_chainIntoPb_ok_trTrap mmpl gh W hA.toCliGhostAllocHooks
  messageDeserialize_ok := by
    have h0 := cliMessageDeserialize_placed_ok mmpl gh W hA.toCliGhostAllocHooks
      (trTrap_hExt mmpl gh W)
    dsimp only [MessageDeserializePlacedOkX] at h0
    exact ls_subroutine_ok_cro_of_callInv
      (callerProg := spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (i := 329) (j := 351) h0
  statesFromPb_ok :=
    (cliStatesPlacedSeamsExt mmpl gh W hA hHmac
      (trTrap_hExt mmpl gh W)).statesFromPb_on
  statesRecv_ok := by
    have h0 := (cliStatesPlacedSeamsExt mmpl gh W hA hHmac
      (trTrap_hExt mmpl gh W)).statesRecv_on
      (callerProg := spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (i := 329)
    exact subroutine_ok_mono h0
      (fun (g, stB) _ _ hpre => by
        dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
          LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
          at hpre ⊢
        refine Satisfies.mono ?_ hpre
        refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
        exact Entails.pure_mono fun ⟨h1, h2, h3, h4, hfit, hlr⟩ =>
          ⟨h1, h2, h3, h4, hfit.mono fun evs hevs => ⟨g.outA, g.selfA, g.msgA, hevs⟩, hlr⟩)
      (fun (g, stB) _ _ _ hpost => by
        dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
          LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
          at hpost ⊢
        refine Satisfies.mono ?_ hpost
        refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
        refine sepConj_mono_left ?_
        exact Entails.pure_mono fun ⟨h1, hevs⟩ =>
          ⟨h1, ⟨g.outA, g.selfA, g.msgA, hevs⟩⟩)
      (fun _ _ _ _ hp => hp)
  statesIntoPb_ok := cliStatesIntoPb_recv_trTrap_exact_ok mmpl gh W hA.toCliGhostAllocHooks
  encodeToVec_ok := by
    have h0 := cliEncodeToVec_placed_ok mmpl gh W hA.toCliGhostAllocHooks
      (trTrap_hExt mmpl gh W)
    dsimp only [PqRatchetStateEncodeToVecPlacedOkExt] at h0
    have henc_cro :=
      subroutine_ok_mono h0
        (spec' := withLsCodeRoLoaded lsmpl (pqRatchetStateEncodeToVecSpecX A lim))
        (fun _ _ _ hpre => by
          dsimp only [withLsCodeRoLoaded, withLsRoLoaded, withLsCodeLoaded,
            pqRatchetStateEncodeToVecSpecX] at hpre ⊢
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
          refine ⟨hpre.1.2, ?_⟩
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
          exact ⟨hpre.1.1, hpre.2⟩)
        (fun _ _ _ _ hpost => hpost)
    exact ls_subroutine_ok_cro_of_cro
      (callerProg := spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (i := 329) (j := 426) henc_cro
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A.repAlloc

/-- Envelope-monotonic generalization of `cliSpqrRecvPlacedContracts_exact` to any caller-chosen
    peer envelopes `(DecodeStateEnv', StatesFromPbEnv', StatesIntoPbEnv', StatesRecvEnv')`. -/
theorem cliSpqrRecvPlacedContracts_ofEnv [LibsignalPlacement]
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
    (hFromPb : ∀ v1 evs, StatesFromPbEnv v1 evs → StatesFromPbEnv' v1 evs)
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
  have hBase := cliSpqrRecvPlacedContracts_exact mmpl gh W hA hHmac
  exact { hBase with
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
    statesFromPb_ok := subroutine_ok_mono hBase.statesFromPb_ok
      (fun (g, stB) _ _ hpre => by
        dsimp only [withLsCodeRoLoaded, statesFromPbPlacedSpecXOfEnv,
          LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv]
          at hpre ⊢
        refine Satisfies.mono ?_ hpre
        refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
        exact Entails.pure_mono fun ⟨h1, h2, h3, hfit⟩ =>
          ⟨h1, h2, h3, hfit.mono (hFromPb g.pb)⟩)
      (fun (g, stB) _ _ _ hpost => by
        dsimp only [withLsCodeRoLoaded, statesFromPbPlacedSpecXOfEnv,
          LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv]
          at hpost ⊢
        refine Satisfies.mono ?_ hpost
        refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
        refine sepConj_mono_left ?_
        exact Entails.pure_mono fun ⟨h1, hevs⟩ => ⟨h1, hFromPb g.pb evs hevs⟩)
      (fun _ _ _ _ hp => hp)
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
        exact Entails.pure_mono fun ⟨h1, h2, hfit⟩ =>
          ⟨h1, h2, hfit.mono (hIntoPb g)⟩)
      (fun (g, stB) _ _ _ hpost => by
        dsimp only [withLsCodeRoLoaded, statesIntoPbPlacedSpecXOfEnv,
          LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv]
          at hpost ⊢
        refine Satisfies.mono ?_ hpost
        refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
        refine sepConj_mono_left ?_
        exact Entails.pure_mono fun ⟨h1, hevs⟩ => ⟨h1, hIntoPb g evs hevs⟩)
      (fun _ _ _ _ hp => hp) }

/-! ## 3. Program-Side Linked `Block 329` (`spqr::recv`) Witnesses -/

private theorem bridge_spqrRecvSpecXT_to_innerSpecXT [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
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
      LibsignalCodeRoLoaded lsmpl m =
        CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl m :=
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
              ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ Fr)) :=
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
            ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ Fr) := by
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

/-- (raw `spqrRecvPlacedSpecXTOfEnv` form) Closed linked `Block 329`
    (`spqr::recv`) program witness on `trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`
    with no envelope inclusion side-conditions (`hA` + `hHmac` only). -/
theorem cliSpqrRecv_placed_ok_tightLinked_raw [LibsignalPlacement]
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
        (CliSpqrRecvTightLinkedEnv W)) :=
  spqr_recv_placed_ok_blockProgram_ext_of_contracts_tightLinked
    (trTrapExternsPlaced_isPanic mmpl gh W)
    (cliSpqrRecvPlacedContracts_exact mmpl gh W hA hHmac)

/-- (`SpqrV1PlacedSeamsBudget` inner spec form) Closed linked `Block 329`
    (`spqr::recv`) seam on `trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` at
    `CliSpqrRecvTightLinkedEnv W`. -/
theorem cliSpqrRecv_placed_ok_tightLinked [LibsignalPlacement]
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
          (CliSpqrRecvTightLinkedEnv W))) :=
  bridge_spqrRecvSpecXT_to_innerSpecXT (fun _ _ _ h => h)
    (cliSpqrRecv_placed_ok_tightLinked_raw mmpl gh W hA hHmac)

/-- Lift `cliSpqrRecv_placed_ok_tightLinked` to any `RecvEnv` containing
    `CliSpqrRecvTightLinkedEnv W`. -/
theorem cliSpqrRecv_placed_ok_ofEnv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    (hSub : ∀ st msg evs, CliSpqrRecvTightLinkedEnv W st msg evs → RecvEnv st msg evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) :=
  bridge_spqrRecvSpecXT_to_innerSpecXT hSub
    (cliSpqrRecv_placed_ok_tightLinked_raw mmpl gh W hA hHmac)

/-- (`SpqrRecvC07TightLinkedEnv` specialization) Instantiates
    `spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07TightLinked` on
    `trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem cliSpqrRecv_placed_ok_c07TightLinked [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi W.C.F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hDec : ∀ bs evs, DecodeStateBytesEnv bs evs → DecodeStateTightEnv evs)
    (hFromPb : ∀ v1 evs, StatesFromPbEnv v1 evs → StatesFromPbTightEnv evs)
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
  bridge_spqrRecvSpecXT_to_innerSpecXT (fun _ _ _ h => h)
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07TightLinked
      (trTrapExternsPlaced_isPanic mmpl gh W)
      (cliSpqrRecvPlacedContracts_ofEnv mmpl gh W hA hHmac hDec hFromPb hIntoPb hRecv))

/-- (`SpqrRecvC07C09aTightLinkedEnv` specialization) Instantiates
    `spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07c09aTightLinked` on
    `trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem cliSpqrRecv_placed_ok_c07c09aTightLinked [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hDec : ∀ bs evs, DecodeStateBytesEnv bs evs → DecodeStateTightEnv evs)
    (hFromPb : ∀ v1 evs, StatesFromPbEnv v1 evs → StatesFromPbTightEnv evs)
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
  bridge_spqrRecvSpecXT_to_innerSpecXT (fun _ _ _ h => h)
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07c09aTightLinked
      (trTrapExternsPlaced_isPanic mmpl gh W)
      (cliSpqrRecvPlacedContracts_ofEnv mmpl gh W hA hHmac hDec hFromPb hIntoPb hRecv))

/-!
## 4. `Block 327` (`spqr::initial_state`) Envelope Lifting & Full `SpqrV1PlacedSeamsOfEnv`
-/

/-- Lift `cliSpqrInitialState_placed_ok_closed` to any `InitEnv` containing
    `InitialStateEnv W.C.F`. -/
theorem cliSpqrInitialState_placed_ok_ofEnv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    (hSub : ∀ g evs, InitialStateEnv W.C.F g evs → InitEnv g evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 327
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStatePlacedInnerSpecOfEnv M A lim W.C.F InitEnv)) := by
  have hok := cliSpqrInitialState_placed_ok_closed mmpl gh W hA
  exact subroutine_ok_mono hok
    (fun (g, stB) _ _ hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrInitialStatePlacedInnerSpec, spqrInitialStatePlacedInnerSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget.initialStatePlacedSpec,
        LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget.initialStatePlacedSpecOfEnv]
        at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
      exact Entails.pure_mono fun ⟨h1, h2, h3, h4, hfit⟩ => ⟨h1, h2, h3, h4, hfit.mono (hSub g)⟩)
    (fun (g, stB) _ _ _ hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrInitialStatePlacedInnerSpec, spqrInitialStatePlacedInnerSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget.initialStatePlacedSpec,
        LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget.initialStatePlacedSpecOfEnv]
        at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, hevs⟩ => ⟨h1, hSub g evs hevs⟩)
    (fun _ _ _ _ hp => hp)

/-- Complete `SpqrV1PlacedSeamsBudget.SpqrV1PlacedSeamsOfEnv` assembly at the exact proved
    `Block 327` and `Block 329` witnesses, given a `Block 427` witness. -/
theorem spqrV1PlacedSeamsOfEnv_of_sendCoins [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hInitSub : ∀ g evs, InitialStateEnv W.C.F g evs → InitEnv g evs)
    (hRecvSub : ∀ st msg evs, CliSpqrRecvTightLinkedEnv W st msg evs → RecvEnv st msg evs)
    (hSendCoins : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv))) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv where
  spqrInitialState := cliSpqrInitialState_placed_ok_ofEnv mmpl gh W hInitSub hA
  spqrRecv := cliSpqrRecv_placed_ok_ofEnv mmpl gh W hRecvSub hA hHmac
  spqrSendCoins := hSendCoins

/-- Complete `SpqrV1PlacedSeamsOfEnv` assembly from `CliSpqrSendPeerSeams` at the exact
    `InitialStateEnv`, `CliSpqrRecvTightLinkedEnv`, and `SpqrSendCoinsExactEnv` envelopes. -/
theorem spqrV1PlacedSeamsOfEnv_exact_of_peerSeams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hPeers : CliSpqrSendPeerSeams M A lim W.C (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F)
      (CliSpqrRecvTightLinkedEnv W)
      (SpqrSendCoinsExactEnv W.C.F W.Q.K) :=
  spqrV1PlacedSeamsOfEnv_of_sendCoins mmpl gh W hA hHmac
    (fun _ _ h => h) (fun _ _ _ h => h)
    (cliSpqrSendCoins_placed_ok_of_peerSeams mmpl gh W hA hHmac hPeers)

/-- `hHmac`-discharged `SpqrV1PlacedSeamsOfEnv` corollary on
    `(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)` from
    `VerifiedLibraries.mallocngLib.Placeable mmpl`, `CliGhostSpqrAllocHooks`, and a
    `Block 427` `SendCoinsEnv` witness. -/
theorem spqrV1PlacedSeamsOfEnv_tightLinked_of_sendCoins [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    {SendCoinsEnv : SendCall → List AllocEvent → Prop}
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim gh)
    (hSendCoins : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendCoinsEnv))) :
    SpqrV1PlacedSeamsOfEnv fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim mmpl gh W
      (InitialStateEnv W.C.F) (CliSpqrRecvTightLinkedEnv W) SendCoinsEnv :=
  spqrV1PlacedSeamsOfEnv_of_sendCoins mmpl gh W hGSpqr
    (hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart lim gh W hPl_mng)
    (fun _ _ h => h) (fun _ _ _ h => h) hSendCoins

/-- `(M, I)`-generic `hHmac`-discharged `SpqrV1PlacedSeamsOfEnv` corollary on
    `mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart`. -/
theorem spqrV1PlacedSeamsOfEnv_mallocngHook_of_sendCoins [LibsignalPlacement]
    {M : AllocCostModel} {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    {SendCoinsEnv : SendCall → List AllocEvent → Prop}
    (hPl_mng : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks M
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim gh)
    (hSendCoins : subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M
          (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendCoinsEnv))) :
    SpqrV1PlacedSeamsOfEnv M
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim mmpl gh W
      (InitialStateEnv W.C.F) (CliSpqrRecvTightLinkedEnv W) SendCoinsEnv :=
  spqrV1PlacedSeamsOfEnv_of_sendCoins mmpl gh W hGSpqr
    (hpo_cliLibcruxHmac_mallocngHook_budget_hookSat hS γ mmpl tp brkStart lim gh W hPl_mng)
    (fun _ _ h => h) (fun _ _ _ h => h) hSendCoins

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
