/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `decryptSignal` (`W2`, Block `463`) Linked and State-Guarded Inner Producers

**Checked by Lean.** Refutes the unconditional protobuf-to-tight allocation inclusion
`∀ pb evs, StatesFromPbEnv pb evs → StatesFromPbTightEnv evs` via a constructive counterexample
(`fob2_not_statesFromPbEnv_sub_tight`), discharges fine-budget extern and binary-store-kit
obligations on `cliGhostExterns`, and derives `InnerDecryptFrozenPlacedOk` producers for
`decryptSignal` (block `463`) at `TryDecryptCliLinkedEnv` and under per-state `StateGuard`
hypotheses on `spqr::recv`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFob2W2InnerLinked

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
   ls_hook_ok_ultra_of_mem lsmpl)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (region_ok_restrictPre_true)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.E2E
  (aesDecHookMallocng fmtWriteHook0 formatInnerHook0 pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_46 lsProg_52)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (lsStringCloneSym)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_withLsCodeRoLoaded_of_plain withEnvPre)
open CryptoVerification.LibsignalSpqrV1 (V1State spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall VecArg region_ok)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced cliHookTablePlaced
   libsignalSessionLib lsFmtWriteSym lsFormatInnerSym lsReadFileSym
   lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.KitInst
  (cliGhostExterns_blackBox cliIdentityVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdentityKitSpecPlaced_quiet)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (cliSessionKitSpecPlaced_quiet)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs cliExternsPlaced_row cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (cliDecModelRecOkAt_opened fmtWrite_row_placed formatInner_row_placed libcruxHmac_row_placed
   lsLibcruxHmacSymCli scopeIn scopeKit scopeKit_pqrState_lt scopeKit_recordInScopeP
   trTrapExternsPlaced)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState (V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine
  (fineCostModel fineCostModelSound fineHookRustCliAllocBudget formatInnerHook0_budget_ok)
open LibsignalBinary.Heap.SpecBudget
  (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec fmtWriteBudgetSpec
   formatInnerBudgetEnvSpec libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
  (withStoresDecPlacedSpecVX)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget
  (recordDecryptPlacedSpecTPTight withStoresDecPlacedSpecVTPF)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget
  (cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget
  (recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (aesDecHookMallocng_budget_ok fineLibcruxHmac_budget_hookSat)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliEnvOfPure TryDecryptCliLinkedEnv
   spqrRecvC07C09aBytesEnv_nonempty)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
  (spqrV1PlacedSeamsOfEnv_of_c07c09aLinked tryDecryptCliEnvOf_eq_linked)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (RecordDeserializeCancelEnv sessDeserEvents_mem_recordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdKitOkIE_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessKitOkSE_seqFree_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudget
  (w2IdKitBudgetEnv w2SessKitBudgetEnv w2_inner_full_placed_ok_ofEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced withStoresDecPlacedSpecVTP)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (ofBytesEnv sessDeserialize_cli_dcan_byBytes_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
  (serializeCanonSeqFree_cli_placed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget (SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## Counterexample to Unconditional `StatesFromPbEnv ⊆ StatesFromPbTightEnv` -/

def fob2_statesFromPbEnv_witnessPb : V1State :=
  { innerState := some (.keysUnsampled default) }

/-- Single-allocation trace (`3000` B aligned at `8` B) inside `StatesFromPbEnv`
(`maxReq ≤ 4 * encodeRaw.length + 4096`) and outside `StatesFromPbTightEnv` (`maxReq ≤ 2560`). -/
def fob2_statesFromPbEnv_witnessEvs : List AllocEvent :=
  [AllocEvent.aligned 8 3000]

theorem fob2_statesFromPbEnv_witness_mem :
    StatesFromPbEnv fob2_statesFromPbEnv_witnessPb fob2_statesFromPbEnv_witnessEvs := by
  unfold StatesFromPbEnv fob2_statesFromPbEnv_witnessPb fob2_statesFromPbEnv_witnessEvs
  refine ⟨by decide, fun ev hev => ?_⟩
  rcases List.mem_singleton.mp hev with rfl
  refine ⟨by decide, Nat.le_trans (by decide : 3000 ≤ 4096) (Nat.le_add_left 4096 _), ?_, ?_⟩
  · intro al _ h
    cases h
    decide
  · intro _ _ _ h
    cases h

theorem fob2_statesFromPbEnv_witness_not_tight :
    ¬ StatesFromPbTightEnv fob2_statesFromPbEnv_witnessEvs := by
  intro h
  have hreq := (h.2.2.2 (AllocEvent.aligned 8 3000) List.mem_cons_self).1
  exact absurd hreq (by decide)

/-- Constructive witness `(pb, evs)` satisfying `StatesFromPbEnv pb evs` and
`¬ StatesFromPbTightEnv evs`. -/
theorem fob2_statesFromPbEnv_counterexample :
    ∃ (pb : V1State) (evs : List AllocEvent),
      StatesFromPbEnv pb evs ∧ ¬ StatesFromPbTightEnv evs :=
  ⟨fob2_statesFromPbEnv_witnessPb, fob2_statesFromPbEnv_witnessEvs,
   fob2_statesFromPbEnv_witness_mem, fob2_statesFromPbEnv_witness_not_tight⟩

theorem fob2_not_statesFromPbEnv_sub_tight :
    ¬ (∀ (pb : V1State) (evs : List AllocEvent),
        StatesFromPbEnv pb evs → StatesFromPbTightEnv evs) := fun hAll =>
  fob2_statesFromPbEnv_witness_not_tight
    (hAll fob2_statesFromPbEnv_witnessPb fob2_statesFromPbEnv_witnessEvs
      fob2_statesFromPbEnv_witness_mem)

/-! ## Fine-Budget Extern Hook Dischargers -/

private theorem fob2_cliGhost_row_aux (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide) (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans (cliExternsPlaced_row mmpl W hrow)

private theorem fob2_fmtWriteHook0_budget_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk fmtWriteHook0 (fmtWriteBudgetSpec M A lim) := by
  intro ⟨_, bs, st⟩ R s0 hrun hpre _
  dsimp only [fmtWriteBudgetSpec, fmtWriteBudgetEnvSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hmem⟩
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  dsimp only [fmtWriteBudgetSpec, fmtWriteBudgetEnvSpec]
  have hpool : A.pool lim (M.stepEvents [] st) (fmtWriteHook0 s0) = A.pool lim st s0 :=
    A.pool_transport lim st s0 (fmtWriteHook0 s0) ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  refine Satisfies.mono (sepConj_mono_left
    (Entails.sepExists_right ([] : List AllocEvent) ?_)) hmem
  rw [hpool]
  exact Entails.pure_right ⟨by simp only [fmtWriteHook0, retHook, wp_norm], rfl, rfl⟩
    (sepConj_mono_left (Entails.sepExists_right bs (Entails.refl _)))

theorem fob2_fmtWrite_hookSat {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim FmtWriteEnv) :=
  ⟨fmtWriteHook0, fob2_cliGhost_row_aux mmpl gh W (fmtWrite_row_placed mmpl W),
   fob2_fmtWriteHook0_budget_ok A lim⟩

theorem fob2_formatInner_hookSat {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim FormatInnerEnv) :=
  ⟨formatInnerHook0, fob2_cliGhost_row_aux mmpl gh W (formatInner_row_placed mmpl W),
   formatInnerHook0_budget_ok M A lim⟩

theorem fob2_aesDec_hookOk {mmpl : MultiPlacement}
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    HookOk (aesDecHookMallocng mmpl W.C.D)
      (aesDecBudgetSpec W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  aesDecHookMallocng_budget_ok fineCostModelSound γ tp cliElfImage.brkStart cliBudgetLimits
    hPl_mng W.C.D

theorem fob2_libcruxHmac_hookSat {mmpl : MultiPlacement}
    (gh : CliGhostHooks) (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
  fineLibcruxHmac_budget_hookSat γ tp cliElfImage.brkStart cliBudgetLimits hPl_mng W.C.F
    (fob2_cliGhost_row_aux mmpl gh W (libcruxHmac_row_placed mmpl W))

/-! ## Binary Store-Kit (`decBinarySessKitPlacedBudgetFixed` / `decBinaryIdKitPlacedBudgetFixed`) Producers -/

theorem fob2_decBinarySessKitPlacedFixed_okSE [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd))) :
    SessionOnlyKitPlacedOkSE A lim
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_placed
    (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
    (deserProg := lsProg_46 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 46)
    (serProg := lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
        hReadHook (by decide) (by decide) (by decide)))
    (sessDeserialize_cli_dcan_byBytes_placed_ok mmpl gh W hG (fun _ h => h))
    (serializeCanonSeqFree_cli_placed mmpl gh W hG)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem fob2_decBinaryIdKitPlacedFixed_okIE [LibsignalPlacement]
    {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd))) :
    IdentityStoreKitPlacedOkI A lim
      (decIdKitPlaced A.repAlloc F0 peer B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_placed
    (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
    (vtSym := cliIdentityVtRoSym)
    hDropNz (fun _ hp => hp.2) hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
        hReadHook (by decide) (by decide) (by decide)))
    (cliGhostExterns_blackBox mmpl gh W)
    (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _)

/-! ## `InnerDecryptFrozenPlacedOk` Producers for `decryptSignal` -/

/-- Instantiates `w2_inner_full_placed_ok_ofEnv` at `TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem fob2_w2_inner_full_placed_ok_linked_of_spqr [LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B
      (TryDecryptCliLinkedEnv W.C W.Q.K)
      (w2SessKitBudgetEnv A.repAlloc B
        (ofBytesEnv RecordDeserializeCancelEnv) (ReadFileRuleEnvFixed cliIo.rd))
      (w2IdKitBudgetEnv A.repAlloc B (ReadFileRuleEnvFixed cliIo.rd)) := by
  rw [← tryDecryptCliEnvOf_eq_linked W.C W.Q.K]
  exact w2_inner_full_placed_ok_ofEnv mmpl gh W A lim hDropNz hG hFs hh hReadHook
    (fun _ hr => sessDeserEvents_mem_recordDeserializeCancelEnv hr)
    hAesDec hSpqrLinked
    (fob2_fmtWrite_hookSat mmpl gh W A lim)
    (fob2_formatInner_hookSat mmpl gh W A lim)
    (spqrRecvC07C09aBytesEnv_nonempty W.C.F W.Q.K)
    ⟨[], rfl⟩
    ⟨[], rfl⟩

/-- Binary-store-kit counterpart of `w2_inner_frozen_placed_ok_of_region_ofEnv`. -/
theorem fob2_w2_inner_binaryKitFixed_frozen_placed_ok_of_region [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (_hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv)).withVRegs.restrictPre (fun _ => True))) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) := by
  intro F0 peer hPeer
  have hSess := fob2_decBinarySessKitPlacedFixed_okSE mmpl gh W A lim B F0 peer
    hDropNz hG hh hReadHook
  have hId := fob2_decBinaryIdKitPlacedFixed_okIE mmpl gh W A lim B F0 peer
    hDropNz hh hReadHook
  have hq : (decSessKitPlaced A.repAlloc F0 peer B).Quiet ∧
      (decIdKitPlaced A.repAlloc F0 peer B).Quiet :=
    ⟨cliSessionKitSpecPlaced_quiet, cliIdentityKitSpecPlaced_quiet⟩
  have hraw :=
    cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks
      mmpl gh W
      (A := A) (lim := lim) (ctl := 0#64) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (tdEnv := tdEnv)
      (kit := decSessKitPlaced A.repAlloc F0 peer B)
      (kitEnv := decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (ikit := decIdKitPlaced A.repAlloc F0 peer B)
      (ikitEnv := decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (st0 := StoresGhost.opened.sessions) (ist0 := StoresGhost.opened.identity)
      (Scope := scopeKit) (Q := fun _ => True)
      hh hSess hId hq
      (fun _ hr => scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        cliDecModelRecOkAt_opened
          (A := A.repAlloc) (b := 0#64) (pathOk := cliWrOk)
          (Scope₀ := scopeIn) (F0 := F0) (peer := peer)
          (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
          (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
          (fun _ h => h) hPeer x rec rec' pt haddr hsc hdec)
      hrec
      (fun _ _ ses hsc hcur => ⟨scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
  refine Arm64.subroutine_ok_mono hraw ?_ ?_
  · intro xs R s0 hpre
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Arm64.Spec.restrictPre] at hpre ⊢
    generalize (withStoresDecPlacedSpecVX W.C A lim 0#64 uuidTryParse
      (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv encodeRecord
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B F0 peer)
      (decIdKitPlaced A.repAlloc F0 peer B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B F0 peer)
      StoresGhost.opened.sessions StoresGhost.opened.identity
      scopeKit (fun _ _ => False)).pre xs s0 = Bpre at hpre ⊢
    generalize tokenInitPlacedAt = T at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · intro xs R s0 sf hpost
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      withStoresDecPlacedSpecVTPF, Arm64.Spec.restrictPre] at hpost ⊢
    exact hpost

/-- Envelope-parametric `[LibsignalFullPlacement]` `InnerDecryptFrozenPlacedOk` producer at
`decBinarySessKitPlacedBudgetFixed` and `decBinaryIdKitPlacedBudgetFixed`. -/
theorem fob2_w2_inner_binaryKitFixed_full_placed_ok_ofEnv [LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv a evs) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B tdEnv
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) :=
  fob2_w2_inner_binaryKitFixed_frozen_placed_ok_of_region mmpl gh W A lim
    hDropNz hG hFs hh hReadHook
    (region_ok_restrictPre_true
      (recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv
        mmpl gh W 0#64 hG hAesDec hSpqr
        (fob2_fmtWrite_hookSat mmpl gh W A lim)
        (fob2_formatInner_hookSat mmpl gh W A lim)
        hRecv_ne ⟨[], rfl⟩ ⟨[], rfl⟩ htd))

/-- Specialization of `fob2_w2_inner_binaryKitFixed_full_placed_ok_ofEnv` to
`TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem fob2_w2_inner_binaryKitFixed_placed_ok_linked_of_spqr [LibsignalFullPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {B : RunBudgets}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hFs : CliGhostHooksFs gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadHook : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqrLinked : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv) :
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) B
      (TryDecryptCliLinkedEnv W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) :=
  fob2_w2_inner_binaryKitFixed_full_placed_ok_ofEnv mmpl gh W A lim
    hDropNz hG hFs hh hReadHook hAesDec hSpqrLinked
    (spqrRecvC07C09aBytesEnv_nonempty W.C.F W.Q.K)
    (fun _ _ h => h)

/-- Two-placement `InnerDecryptFrozenPlacedOk` producer on `cliElfBytes` at
`TryDecryptCliLinkedEnv W.C W.Q.K`. -/
theorem fob2_w2_inner_linked_ok_of_spqr
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSpqrLinked : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv
      (fun st msg => SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliRunBudgets
      (TryDecryptCliLinkedEnv W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact fob2_w2_inner_binaryKitFixed_placed_ok_linked_of_spqr mmpl ghFixed W
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    h547 hGSpqr.toCliGhostAllocHooks hFs hHooks.runHooks hsat
    (fob2_aesDec_hookOk hPl_mng W γ tp) hSpqrLinked

/-- State-guarded `InnerDecryptFrozenPlacedOk` producer: lifts `SpqrV1PlacedSeamsOfEnv` at
`StateGuard st.bytes → SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes evs` into
`TryDecryptCliEnvOfPure`. -/
theorem fob2_w2_inner_stateGuarded_ok_of_spqr
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (StateGuard : List (BitVec 8) → Prop)
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSpqrGuarded : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv
      (fun st msg evs =>
        StateGuard st.bytes → SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes evs)
      SendEnv) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliRunBudgets
      (TryDecryptCliEnvOfPure W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv
        (fun stBs msgBs evs => StateGuard stBs → SpqrRecvC07C09aBytesEnv W.C.F W.Q.K stBs msgBs evs)
        FormatInnerEnv)
      (decBinarySessKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  refine fob2_w2_inner_binaryKitFixed_full_placed_ok_ofEnv mmpl ghFixed W
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    h547 hGSpqr.toCliGhostAllocHooks hFs hHooks.runHooks hsat
    (fob2_aesDec_hookOk hPl_mng W γ tp) hSpqrGuarded
    (fun stBs msgBs =>
      let ⟨evs, hevs⟩ := spqrRecvC07C09aBytesEnv_nonempty W.C.F W.Q.K stBs msgBs
      ⟨evs, fun _ => hevs⟩)
    (fun _ _ h => h)

/-- Variant of `fob2_w2_inner_linked_ok_of_spqr` taking `SpqrRecvPlacedContractsOfEnv` at the tight
`C07 + C09a` leaves. -/
theorem fob2_w2_inner_linked_ok_of_recvContracts
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    {H_inner : V1InnerHeapPred}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {PrevRecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hBase : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv PrevRecvEnv SendEnv)
    (hRecvC : @SpqrRecvPlacedContractsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel H_inner
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits W.C.F W.Q.K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv W.C.F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv)
      (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliRunBudgets
      (TryDecryptCliLinkedEnv W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact fob2_w2_inner_linked_ok_of_spqr hLs hblk hext_nodup ghFixed hPl_mng W γ tp
    hGSpqr hFs hsat hHooks h547 (spqrV1PlacedSeamsOfEnv_of_c07c09aLinked hBase hRecvC)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFob2W2InnerLinked
