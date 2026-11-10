/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.StringClonePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Untrusted-Identity Branch

Constructs budget-threaded `SessionOnlyKitPlacedOkSE` and `IdentityStoreKitPlacedOkI` instances for
`cliPollSessKitPlaced` and `cliPollIdKitPlaced`, proves `stageP1_untrusted_mangled_placed_ok` on
Block `623`, and discharges `closure_untrusted_placed_ok` on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  lsLogOff withLsCodeRoLoaded LibsignalCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_plain
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin hiding encodeRecord
open CryptoVerification.E2E.Record hiding Bytes
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp Bytes eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  SessionOnlyKitPlacedOkSE IdentityStoreKitPlacedOkI
  kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI
  kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.Slots
open CryptoVerification.SignalSession.Cli.KitInst hiding cliSessKitOkSE_placed
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (cliIdentityKitSpecPlaced)
open CryptoVerification.SignalSession.Coins.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  StageP1UntrustedPlacedStmt
  cliFiles_eq_of_trace_eq_placed cliSlotTraceFT_of_trace_eq_placed
  dpPollPost_of_decResAt_placed cliPollStageP1_fsAt_placed
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
  (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudget
  (stageP1_untrusted_ok_kit_x_ext_placed)
open LibsignalBinary.Proofs.Common.StringClonePlaced
  (lsRustAllocPlacedSym lsRustNoAllocShimPlacedSym)
open LibsignalBinary.Proofs.Common.StringClonePlacedBudget
  (stringCloneBudget_placed_codeLoaded_ok)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE kitSavePollPlacedSpec
   kitSavePollPlacedSpecE kitSavePollPlacedSpecI kitTrustPollPlacedSpec
   kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
  (SerContractsXPlaced serializeCanonSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdKitOkIE_placed cliIdentityKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessKitOkSE_placed cliSessionKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
  (dpPollPost_of_slotTraceFT_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
  (StageP1UntrustedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (cliExternsPlaced_sessionMemcpy_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
   cliExternsPlaced_sessionMemmove_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
  (serializeCanonX_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (session_memcpy_region_lscro_of_cli)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)

/-! ## 1. `RunHooksPlaced` Converters (`SkeletonPlacedBudget` ↔ `ClosureStagesStmtPlacedBudget`) -/

/-- Convert `SkeletonPlacedBudget.RunHooksPlaced` (`PollStmtPlacedBudget.RunHooksPlaced`) to
`ClosureStagesStmtPlacedBudget.RunHooksPlaced`. -/
theorem runHooks_to_stages [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim ext where
  alloc := hh.alloc
  allocFs := hh.allocFs
  panics := hh.panics
  memcpyRO := hh.memcpyRO
  bcmp := hh.bcmp
  fs := hh.fs
  utf8 := hh.utf8
  memrchr := hh.memrchr
  codecHooks := hh.codecHooks
  allocZeroed := hh.allocZeroed
  stringClone := hh.stringClone
  formatInner := hh.formatInner

/-- Convert `ClosureStagesStmtPlacedBudget.RunHooksPlaced` to
`SkeletonPlacedBudget.RunHooksPlaced` (`PollStmtPlacedBudget.RunHooksPlaced`). -/
theorem runHooks_of_stages [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext where
  alloc := hh.alloc
  allocFs := hh.allocFs
  panics := hh.panics
  memcpyRO := hh.memcpyRO
  bcmp := hh.bcmp
  fs := hh.fs
  utf8 := hh.utf8
  memrchr := hh.memrchr
  codecHooks := hh.codecHooks
  allocZeroed := hh.allocZeroed
  stringClone := hh.stringClone
  formatInner := hh.formatInner

/-! ## 2. Budget-Threaded Trace, `FsAt`, & Exit Postcondition Packagers -/

theorem cliFiles_eq_of_trace_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {s0 sf : State}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext)
    (hst : Steps prog s0 sf)
    (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (hh.fs prog i).files_eq hst (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil

theorem cliSlotTraceFT_of_trace_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {s0 sf : State}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext)
    (hst : Steps prog s0 sf)
    (htr : sf.trace = s0.trace) :
    slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
  ⟨htr ▸ List.prefix_refl s0.trace,
   cliFiles_eq_of_trace_eq_placed hh hst htr,
   congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩

theorem dpPollPost_of_decResAt_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {prog : Program} {i : Nat}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 sf : State) (evs : List AllocEvent)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) Bytes)
    (Leftover : SepProp)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext)
    (hevs : DecPkEnv y.g evs)
    (hsteps : Steps prog s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' e s0.trace sf.trace) :
    decResAt A.repAlloc y.out e ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗
      A.pool lim (M.stepEvents evs y.st) sf ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      stackAt s0.sp stk' ⊢
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf :=
  dpPollPost_of_slotTraceFT_placed A lim DecPkEnv B S stk' y s0 sf evs g' e Leftover hevs
    (cliSlotTraceFT_of_trace_eq_placed hh hsteps htr) hout

theorem cliPollStageP1_fsAt_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) {s0 : State}
    (hf : s0.fs.files = F0) :
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 Scope peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (dpPollProgPlaced ext) s0 :=
  .inr ⟨⟨⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩,
         ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩⟩,
        hh.fs (dpPollProgPlaced ext) 518,
        hf ▸ ⟨rfl, rfl⟩⟩

/-! ## 3. Budget-Threaded `cliPollSessKitPlaced` & `cliPollIdKitPlaced` Envelopes & Kit Instances -/

private theorem saveUpd_own_placed (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (addr : AddrVal) (key : IdentityKey) :
    (IdGhost.saveUpd rd F0 g addr key).own = g.own := by
  unfold IdGhost.saveUpd; cases IdGhost.peer rd F0 g addr <;> rfl

/-- Lift an `IdentityStoreBudgetEnv` from `cliIdentityKitSpecPlaced` (`IdState = IdGhost`) to
`cliIdStoreSpecFullPlaced` (`IdState = IdGhost`). -/
def cliIdStoreFullBudgetEnv [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {t1 t2 t3 t4 : Nat}
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)) :
    IdentityStoreBudgetEnv
      (cliIdStoreSpecFullPlaced A rd F0 pathOk peer t1 t2 t3 t4) where
  trustPollEnv := ikitEnv.trustPollEnv
  savePollEnv := ikitEnv.savePollEnv

/-- Lift `IdentityStoreKitPlacedOkI` from `cliIdentityKitSpecPlaced` (`cliIdStoreAt`, `peers` only)
to `cliIdStoreSpecFullPlaced` (`cliIdStoreAtFull`, framing `⌜CliIdOwnInv …⌝ ∗ dirAt A self g.own`). -/
theorem cliIdKitPlacedOkI_full [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {t1 t2 t3 t4 : Nat}
    {ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)}
    (hBase : IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
      ikitEnv H) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdStoreSpecFullPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4)
      (cliIdStoreFullBudgetEnv ikitEnv) H where
  trustShim := hBase.trustShim
  trustFutDrop := hBase.trustFutDrop
  saveShim := hBase.saveShim
  saveFutDrop := hBase.saveFutDrop
  trustPoll hblk := by
    refine subroutine_ok.of_codeLoaded fun ⟨x, d, self, g, st⟩ R s0 hpc hrun hpre halign _ => ?_
    change IdGhost at g
    dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
      kitTrustPollPlacedSpec, withEnvPre, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
      cliIdentityStoreSpec, cliIdStoreAtFull, cliIdStoreFullBudgetEnv] at hpre
    let R' : SepProp := ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim
        (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
        ikitEnv)).pre (x, d, self, g, st) s0 ∗ R' := by
      dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec, R']
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
    refine (hBase.trustPoll hblk).mono_outcome (x, d, self, g, st) R' s0 hpc hrun hpre' halign
      fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec,
        cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
        cliIdStoreFullBudgetEnv, R'] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      obtain ⟨ans, evs, hm⟩ := hpost
      exact ⟨ans, evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
    · dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withLsRoCl, kitTrustPollPlacedSpecI, withLsLogOff, kitTrustPollPlacedSpecE,
        kitTrustPollPlacedSpec, withEnvPre] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  savePoll hblk := by
    refine subroutine_ok.of_codeLoaded fun ⟨x, self, g, st⟩ R s0 hpc hrun hpre halign _ => ?_
    change IdGhost at g
    dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
      kitSavePollPlacedSpec, withEnvPre, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
      cliIdentityStoreSpec, cliIdStoreAtFull, cliIdStoreFullBudgetEnv] at hpre
    let R' : SepProp := ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ R
    have hpre' : s0.mem ⊨ (withLsRoCl lsmpl (kitSavePollPlacedSpecI M A lim
        (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer t1 t2 t3 t4 cliIdentityVtSym)
        ikitEnv)).pre (x, self, g, st) s0 ∗ R' := by
      dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec, R']
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
    refine (hBase.savePoll hblk).mono_outcome (x, self, g, st) R' s0 hpc hrun hpre' halign
      fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre, cliIdentityKitSpecPlaced, cliIdentityStoreSpec,
        cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdStoreAtFull,
        cliIdStoreFullBudgetEnv, R'] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      obtain ⟨ans, evs, hm⟩ := hpost
      rw [saveUpd_own_placed]
      exact ⟨ans, evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
    · dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withLsRoCl, kitSavePollPlacedSpecI, withLsLogOff, kitSavePollPlacedSpecE,
        kitSavePollPlacedSpec, withEnvPre] at hoom
      exact (not_satisfies_false_sepConj hoom).elim

/-- Canonical `SessionStoreBudgetEnv` for `cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)`
at given `ReadEnv` and `DeserEnv`. -/
abbrev cliPollSessBudgetEnv [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) :
    SessionStoreBudgetEnv
      (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)) :=
  cliSessionKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk scopeKit peer
    (cliKitStk B).sessLoadShim (cliKitStk B).sessLoadPoll
    (cliKitStk B).sessStoreShim (cliKitStk B).sessStorePoll
    DeserEnv cliSessionVtSym cliIdentityVtSym ReadEnv

/-- Canonical `IdentityStoreBudgetEnv` for `cliPollIdKitPlaced A F0 peer (cliKitStk B)` at given
`ReadEnv`. -/
abbrev cliPollIdBudgetEnv [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A F0 peer (cliKitStk B)) :=
  cliIdStoreFullBudgetEnv
    (cliIdentityKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk peer
      (cliKitStk B).idTrustShim (cliKitStk B).idTrustPoll
      (cliKitStk B).idSaveShim (cliKitStk B).idSavePoll
      cliIdentityVtSym ReadEnv)

private theorem cliGhostExterns_blackBox_local (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  CryptoVerification.SignalSession.Cli.KitInst.IdKit.cliGhostExterns_blackBox mmpl g W

private theorem hookSat_sessionMemcpyRegionBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym sessionMemcpyRegionBudgetSpec :=
  ProofLib.HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩

private theorem hookSat_sessionMemcpyBudget_of_codec {H : LibsignalHooks} (stk : Nat)
    (h : HookSat H CryptoVerification.lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym (sessionMemcpyBudgetSpec stk) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      withVmPreserved, framelessMemcpySpec] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec,
      withVmPreserved, framelessMemcpySpec] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Construct `SerContractsXPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W))` directly from
`hh : SkeletonPlacedBudget.RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))` (via `hh.codecHooks`). -/
theorem serContractsX_of_runHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    SerContractsXPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  SerContractsXPlaced.of_hooks
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    hh.codecHooks.realloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    (let ⟨f, hf, hok⟩ := cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack
     ⟨f, (cliGhostExterns_other g (cliExternsPlaced mmpl W)
       (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hf, hok⟩)
    (hookSat_sessionMemcpyBudget_of_codec extHookStack hh.codecHooks.memcpy)

/-- Full `SessionOnlyKitPlacedOkSE` instance for `cliPollSessKitPlaced` extracted directly from
`hh : SkeletonPlacedBudget.RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))`, `hRead`, and `hDeser`. -/
theorem cliPollSess_kitPlacedOkSE [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) :
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_placed
    (readProg := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 518)
    (deserProg := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (deserBlk := 518)
    (serProg := lsProg_52 (cliGhostExterns g (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz
    (fun _ hp => hp.2)
    hh
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
    hDeser
    (serializeCanonX_placed_ok_of_serContractsX (serContractsX_of_runHooks mmpl g W hh))
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Full `IdentityStoreKitPlacedOkI` instance for `cliPollIdKitPlaced` extracted directly from
`hh : SkeletonPlacedBudget.RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))` and `hRead`. -/
theorem cliPollId_kitPlacedOkI [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc F0 peer B ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitPlacedOkI_full
    (cliIdKitOkIE_placed
      (readProg := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 518)
      hDropNz
      (fun _ hp => hp.2)
      hh
      (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
      (cliGhostExterns_blackBox_local mmpl g W)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) (by decide))

/-- Exact untrusted-path Stage-P1 allocation envelope on `(W, B, ReadEnv, DeserEnv)` at `g : DecPkGhost`. -/
def CliDpPollUntrustedEnv [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  StageP1UntrustedEnv
    (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
    (cliPollSessBudgetEnv A g.F g.peer B ReadEnv DeserEnv)
    StoresGhost.opened.sessions
    (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
    (cliPollIdBudgetEnv A g.F g.peer B ReadEnv)
    StoresGhost.opened.identity
    g.peer g.msg.identityKey

/-! ## 4. Mangled-Symbol `StageP1UntrustedMangledPlacedStmt` & Unconditional Discharge -/

private theorem sepWPp_intro_stageP1VtablesPlacedAt [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {target : BitVec 64} {s0 : State}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {P : SepProp} {post onPanic : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hsess : SessionOnlyVtablesPlacedOk kit)
    (hid : IdentityVtablesPlacedOk ikit)
    (hwp : SepWPp prog target s0 (stageP1VtablesPlacedAt kit ikit ∗ P)
      (fun sf P_f => ∃ Drop P_clean, (P_f ⊢ Drop ∗ P_clean) ∧ post sf P_clean)
      onPanic) :
    SepWPp prog target s0 P post onPanic := by
  have hwp' := SepWPp.congr_post_drop_left hwp
  intro R hm hL
  have hm' : s0.mem ⊨ (stageP1VtablesPlacedAt kit ikit ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact satisfies_stageP1VtablesPlacedAt hsess hid hro hm
  exact hwp' R hm' hL

private theorem session2MemcpyBudget_of_allocContracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hA : AllocContractsXCliPlaced A lim ext) :
    subroutine_ok (dpPollProgPlaced ext) (lsρ "memcpy")
      (withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX) := by
  have h := session_memcpy_region_lscro_of_cli (callerProg := dpPollProgPlaced ext) (i := 518)
    (stk := extHookStack) hA
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec,
      session2MemcpyBudgetSpecX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · rcases x with ⟨dst, src, bs⟩
    dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
      session2MemcpyBudgetSpecX] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩

private theorem extHookStack_le_cliPollSess_loadCallStack [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤
      loadCallStack (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed,
    CryptoVerification.RustHeap.allocHookStack]
  omega

/-- Block-`623` counterpart of `ClosureStageDefsPlacedBudget.StageP1UntrustedPlacedStmt`:
discharges `<String as Clone>::clone` at `(lsmpl.base 623)` from `lsRustNoAllocShimPlacedSym`,
`lsRustAllocPlacedSym`, and `"memcpy"`, plus `HookSat ext lsRustDeallocSymCli
(rustCliDeallocBudgetSpec M A lim)` and `SessionOnlyVtablesPlacedOk kit` +
`IdentityVtablesPlacedOk ikit`. -/
def StageP1UntrustedMangledPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st : kit.StoreState} {ist : ikit.IdState} {st_b : M.σ}
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    AllocContractsXCliPlaced A lim ext →
    HookSat ext lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim) →
    HookSat ext lsRustNoAllocShimPlacedSym sessionShimBudgetSpec →
    HookSat ext lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false) →
    HookSat ext "memcpy" sessionMemcpyRegionBudgetSpec →
    SessionOnlyVtablesPlacedOk kit →
    IdentityVtablesPlacedOk ikit →
    SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord ext →
    IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext →
    stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 →
    extHookStack ≤ loadCallStack kit →
    kit.addrOk peer.val →
    ikit.addrOk peer.val →
    (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
    (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false) →
    FitsEnv M lim st_b (StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey) →
    ∀ (s0 : State)
      (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
       sessStorePtr idStorePtr
       preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
       kyberStorePtr kyberStoreVt rngPtr
       v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
      (b_390 : BitVec 8),
      LibsignalCodeRoLoaded lsmpl s0.mem →
      FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
        (dpPollProgPlaced ext) s0 →
      s0.pc = dpPollEntryPlaced →
      s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.sp - 0xcd0#64 = sp →
      s0.readReg64 .x0 = outPtr →
      s0.readReg64 .x1 = coroPtr →
      s0.readReg64 .x2 = ctxPtr →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s0
        (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
           sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
           preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
           kyberStorePtr kyberStoreVt rngPtr ∗
         cells (coroPtr + 0x70#64) 14 ∗
         cells (coroPtr + 0xe0#64) 4 ∗
         memRegion (coroPtr + 0x100#64) 336 ∗
         cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
         cells (coroPtr + 0x2c8#64) 25 ∗
         ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
         ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
         (sp ↦₆₄ v_sp0) ∗
         ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
         ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (sp + 0xd8#64) 348 ∗
         memRegion (sp + 0x370#64) 36 ∗
         memRegion (sp + 0x3e0#64) 368 ∗
         cells (sp + 0xa90#64) 6 ∗
         cells (s0.sp - 0x60#64) 12 ∗
         memRegion outPtr 48 ∗
         lsLogOff ∗
         kit.storeAt sessStorePtr st ∗
         ikit.identityAt idStorePtr ist ∗
         protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
         ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
         A.pool lim st_b s0 ∗
         stackAt sp (stageP1UntrustedCallStack kit ikit))
        (fun sf P_f =>
          (∃ opt : Option (SessionRecord (List (BitVec 8))), ∃ evs : List AllocEvent,
            StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey evs ∧
            kit.loadRel st peer.val (.ok opt) ∧
            ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
            sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
              ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
            (P_f ⊢
              ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
                decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                  preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                  kyberStorePtr kyberStoreVt rngPtr ∗
                decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                  preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                  kyberStorePtr kyberStoreVt rngPtr ∗
                memRegion (coroPtr + 0xe0#64) 368 ∗
                cells (coroPtr + 0x250#64) 6 ∗
                ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
                processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                  spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
                ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
                cells (coroPtr + 0x398#64) 2 ∗
                (sp ↦₆₄ 0#64) ∗
                ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
                ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
                ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
                ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
                ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
                memRegion (sp + 0xd8#64) 348 ∗
                memRegion (sp + 0x370#64) 36 ∗
                memRegion (sp + 0x3e0#64) 368 ∗
                cells (sp + 0xa90#64) 6 ∗
                decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
                apiDecResultAt A.repAlloc outPtr (.error (.untrustedIdentity peer.val)) ∗
                lsLogOff ∗
                kit.storeAt sessStorePtr st ∗
                ikit.identityAt idStorePtr
                  (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
                protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
                ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
                A.pool lim (M.stepEvents evs st_b) sf ∗
                stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
          sf.sp = s0.sp ∧
          ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem)
        (fun _ _ => False)

set_option maxHeartbeats 800000 in
/-- Unconditional proof of `StageP1UntrustedMangledPlacedStmt` from
`StageP1UntrustedOkTrapPlacedBudget.stageP1_untrusted_ok_kit_x_ext_placed`,
`StringClonePlacedBudget.stringCloneBudget_placed_codeLoaded_ok`, and
`satisfies_stageP1VtablesPlacedAt`. -/
theorem stageP1_untrusted_mangled_placed_ok [LibsignalPlacement] :
    StageP1UntrustedMangledPlacedStmt := by
  intro M A lim ext Scope encRecord kit kitEnv ikit ikitEnv st ist st_b
    peer remoteIdKey hAlloc hDealloc hShim hAllocHook hMemcpy hsessVt hidVt hSkit hIkit
    hstack_lt hext_load haddr_ss haddr_id hload_ok htrust_false hfits
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hcrl hfs hpc hrun hsp_align hsp_def hx0 hx1 hx2
  refine sepWPp_intro_stageP1VtablesPlacedAt hcrl.2 hsessVt hidVt ?_
  have hdrop_ss :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 512)
        (withLsCodeRoLoaded lsmpl
          (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
            M A lim)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (drop_session_structure4_placed_ok_at (callerProg := stageP1ProgPlaced ext) (i := 518)
        hDealloc (by decide))
  have hdealloc_sub :
      subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustDeallocSymCli)
        (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem (prog := stageP1ProgPlaced ext) (i := 518) hDealloc (by decide)
  have hmemcpy_sub :
      subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
        (withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX) :=
    session2MemcpyBudget_of_allocContracts hAlloc
  have hclone_sub :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 623)
        (withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (stringCloneBudget_placed_codeLoaded_ok
        (callerProg := stageP1ProgPlaced ext) (i := 518)
        hShim hAllocHook hMemcpy (by decide))
  have hwp := stageP1_untrusted_ok_kit_x_ext_placed
    (M := M) (A := A) (lim := lim) (st0 := st_b) (ext := ext)
    (Scope := Scope) (encRecord := encRecord)
    (kit := kit) (kitEnv := kitEnv) (ikit := ikit) (ikitEnv := ikitEnv)
    (st := st) (ist := ist) (Qp := fun _ _ => False)
    peer remoteIdKey
    hdrop_ss hdealloc_sub hmemcpy_sub hclone_sub
    (hSkit.loadShim (callerProg := stageP1ProgPlaced ext) (callerBlk := 518) (by decide))
    (hSkit.loadPoll (callerProg := stageP1ProgPlaced ext) (callerBlk := 518) (by decide))
    (hSkit.loadFutDrop (callerProg := stageP1ProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustShim (callerProg := stageP1ProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustPoll (callerProg := stageP1ProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustFutDrop (callerProg := stageP1ProgPlaced ext) (callerBlk := 518) (by decide))
    hstack_lt hext_load haddr_ss haddr_id hload_ok htrust_false hfits
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hcrl hfs hpc hrun hsp_align hsp_def hx0 hx1 hx2
  refine SepWPp.mono_run
    (SepWPp.weaken_pre (Entails.of_eq (by dsimp only [stageP1VtablesPlacedAt]; sep_ac_rfl)) hwp)
    fun sf P_f hpost => ?_
  rcases hpost with ⟨⟨opt, evs, hrel_load, hrel_trust, hevs, htr_f, hent⟩, hregs⟩
  refine ⟨stageP1VtablesPlacedAt kit ikit, _, ?_,
    ⟨opt, evs, hevs, hrel_load, hrel_trust, htr_f, Entails.refl _⟩, hregs⟩
  refine Entails.trans hent (Entails.of_eq ?_)
  simp only [sepExists_sepConj_right]
  refine congrArg sepExists (funext fun v_a8 => ?_)
  refine congrArg sepExists (funext fun v_b8 => ?_)
  refine congrArg sepExists (funext fun v_d0 => ?_)
  dsimp only [stageP1VtablesPlacedAt]
  sep_ac_rfl

/-! ## 5. Untrusted-Identity Branch of `dpPollSpecStateBudget` (`closure_untrusted_placed_ok`) -/

set_option maxHeartbeats 800000 in
/-- Statement-parameterized budget-threaded untrusted-identity branch (`trusted =.ok false`) of
`subroutine_ok_of_sepWPp_steps` for Block `518` under `[LibsignalPlacement]`. -/
theorem closure_untrusted_of_stmt_placed_ok [LibsignalPlacement]
    (hUntrusted : StageP1UntrustedMangledPlacedStmt)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hent_stores := storesAt_entails_cliPollStoresKitsAtPlaced (A := A.repAlloc)
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ
    y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer)
    (cliIdOwnInv_opened hdecOk)
    (cliIdInv_opened_peer hfPeer)
    (cliPkInv_opened hdecOk pid)
    (cliSpkInv_opened hdecOk sid)
    (cliKpkInvFull_opened hdecOk kid sid kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗
    cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗
    cells (y.fut + 0x250#64) 6 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
    cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
    (sp ↦₆₄ v_sp0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
    ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
    ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗
    memRegion y.out 48 ∗
    lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    A.pool lim y.st s0 ∗
    stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At y.fut ∗
    closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
      cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    (M := M) (A := A) (lim := lim) (ext := cliGhostExterns g (cliExternsPlaced mmpl W))
    (Scope := scopeKit) (encRecord := encodeRecord)
    (kit := kit) (kitEnv := cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit) (ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := StoresGhost.opened.sessions) (ist := StoresGhost.opened.identity)
    (st_b := y.st)
    y.g.peer y.g.msg.identityKey
    hh.alloc
    hh.codecHooks.dealloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    (cliPollSess_kitPlacedOkSE mmpl g W hDropNz hh hRead hDeser)
    (cliPollId_kitPlacedOkI mmpl g W hDropNz hh hRead)
    hp1_64
    (extHookStack_le_cliPollSess_loadCallStack A.repAlloc B y.g.F y.g.peer)
    rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0
    (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, evs, hevs_p1, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _⟩
    refine ⟨?_, hspf, closureCalleeSaved_toCalleeSavedPreserved hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hloadRec : CryptoVerification.SignalSession.Cli.Slots.loadRec Scope y.g.F y.g.peer.val =
        .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
    have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
    have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0
      0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
    have hres := apiDecResultAt_untrusted_entails_decResAt A.repAlloc y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗
          Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗
            cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗
            cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗
            cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
            coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
              ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
      rw [htrust_id] at hmf2
      dsimp only [Fr_inner] at hmf2
      refine Satisfies.mono ?_ hmf2
      dsimp only [Leftover, cliPollStoresKitsAtPlaced]
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗
          Leftover ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres
          (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hcoro
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280)))))))))))))
        hmf_reord
    dsimp only [sp] at hmf_folded
    rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
    have hpost := dpPollPost_of_decResAt_placed A lim DecPkEnv B S stk' y s0 sf evs
      StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) Leftover
      hh (hevs_sub evs hevs_p1) hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro _ _ hfalse _ _
    exact False.elim hfalse

/-- Closed budget-threaded untrusted-identity branch (`trusted =.ok false`) of
`subroutine_ok_of_sepWPp_steps` for Block `518` under `[LibsignalPlacement]`, discharging Stage P1
directly via `stageP1_untrusted_mangled_placed_ok`. -/
theorem closure_untrusted_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) :=
  closure_untrusted_of_stmt_placed_ok stageP1_untrusted_mangled_placed_ok
    A lim hDropNz mmpl g W X B S Scope hh hRead hDeser hinjK hsub hS stk' hneed hstk63 y
    hfits_p1 hevs_sub R s0 hpc hrun hsp hro0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base

/-- Convenience wrapper around `closure_untrusted_placed_ok` accepting
`ClosureStagesStmtPlacedBudget.RunHooksPlaced`. -/
theorem closure_untrusted_stagesHooks_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) :=
  closure_untrusted_placed_ok A lim hDropNz mmpl g W X B S Scope (runHooks_of_stages hh) hRead hDeser
    hinjK hsub hS stk' hneed hstk63 y hfits_p1 hevs_sub R s0 hpc hrun hsp hro0 hx0 hx1 hx2
    hfiles0 hfPeer hdecOk htrusted hm_base

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
