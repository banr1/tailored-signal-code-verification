/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EntryAndRegIdPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Stage 5 (`[LibsignalPlacement]`): PreKey Metadata, Registration ID, `save_identity`, `promote_state`, and `store_session`

Top-level Stage 5 (`+0x1484 → ret` at `lr`, both `Ok(())` and `Err`) theorems and `Stage5BudgetFits`
allocator-envelope composition on `initProgPlaced W` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5PlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement LibsignalRoLoaded lsmpl lsρ)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost TailVecGhost)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (IdPollGhost SessStorePollGhost StoresGhost cliIdentityVtSym cliSessionVtSym idRegIdFutVtSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs
  (InitOk₀ cliInitiateFrame cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtStage5Placed IdOwnPollGhostPlaced InitTraceFsSound initProgPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerializeEnvX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage5MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced dropSessionStructure_cli_placed_ok promoteState_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EntryAndRegIdPlacedBudget
  (initiate_stage5_placed_ok_impl initiate_stage5_placed_ok_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranchPlacedBudget
  (initIdRegIdPollGhostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlacedBudget
  (initIdSavePollGhost initSessStorePollGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (promoteStateEmptyBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (CliIdRegIdPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs InitStoreCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
  (SetUnackPreKeyMsgEpochEnv setUnackPreKeyMsgEpochEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (idOwnShimSpecPlaced idRegIdPollSpecPlaced idSavePollSpecPlaced idSaveShimSpecPlaced
   sessStorePollSpecPlaced sessStoreShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget (CliStorePollEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (dropSessionStructureLocal2Spec)

/-- Budget-fitness and allocator-event composition hypotheses for Stage 5 (`+0x1484 → ret`). -/
structure Stage5BudgetFits [LibsignalPlacement]
    (M : AllocCostModel) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (RegPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop)
    (StoreEnv : SessStorePollGhost → List AllocEvent → Prop)
    (x : InitGhost) (be : PreKeyBundleFields) (kp : IdentityKeyPair)
    (hdr : SignalPqxdh.HandshakeHdr) (opkId : BitVec 32)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (s0 : State) (st0 st : M.σ) : Prop where
  fitUnackMsg : FitsEnv M lim st SetUnackPreKeyMsgEpochEnv
  fitRegShim : FitsEnv M lim (M.stepEvents setUnackPreKeyMsgEpochEvents st) (BoxAllocEnv 16)
  fitRegPoll : ∀ (futReg : BitVec 64) (evsRegShim : List AllocEvent),
    BoxAllocEnv 16 evsRegShim →
    FitsEnv M lim (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))
      (RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg))
  envErr : StoresGhost.opened.identity.regId cliIo.rd x.F = .error () →
    ∀ (futReg : BitVec 64) (evsRegShim evsRegPoll evsDrop : List AllocEvent),
    BoxAllocEnv 16 evsRegShim →
    RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
    FreeOnlyEvs evsDrop →
    ∃ evs, InitEnv x evs ∧
      M.stepEvents (rustDeallocEvents 1568 1)
        (M.stepEvents evsDrop
          (M.stepEvents (rustDeallocEvents 16 8)
            (M.stepEvents evsRegPoll
              (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))) =
        M.stepEvents evs st0
  fitSaveShim : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
    ∀ (futReg : BitVec 64) (evsRegShim evsRegPoll : List AllocEvent),
    BoxAllocEnv 16 evsRegShim →
    RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
    FitsEnv M lim
      (M.stepEvents (rustDeallocEvents 16 8)
        (M.stepEvents evsRegPoll
          (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))
      (BoxAllocEnv 32)
  fitSavePoll : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
    ∀ (futReg futSave : BitVec 64) (evsRegShim evsRegPoll evsSaveShim : List AllocEvent),
    BoxAllocEnv 16 evsRegShim →
    RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
    BoxAllocEnv 32 evsSaveShim →
    FitsEnv M lim
      (M.stepEvents evsSaveShim
        (M.stepEvents (rustDeallocEvents 16 8)
          (M.stepEvents evsRegPoll
            (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st)))))
      (SaveEnv x.F (initIdSavePollGhost x s0 futSave))
  fitStoreShim : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
    ∀ (futReg futSave : BitVec 64)
      (evsRegShim evsRegPoll evsSaveShim evsSavePoll : List AllocEvent),
    BoxAllocEnv 16 evsRegShim →
    RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
    BoxAllocEnv 32 evsSaveShim →
    SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
    FitsEnv M lim
      (M.stepEvents (rustDeallocEvents 32 8)
        (M.stepEvents evsSavePoll
          (M.stepEvents evsSaveShim
            (M.stepEvents (rustDeallocEvents 16 8)
              (M.stepEvents evsRegPoll
                (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st)))))))
      (BoxAllocEnv 32)
  fitStorePoll : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
    ∀ (futReg futSave futStore : BitVec 64)
      (evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim : List AllocEvent),
    BoxAllocEnv 16 evsRegShim →
    RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
    BoxAllocEnv 32 evsSaveShim →
    SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
    BoxAllocEnv 32 evsStoreShim →
    ∀ (dataPtr : BitVec 64) (padVal w1_kyb : BitVec 32) (kg : TailVecGhost),
    FitsEnv M lim
      (M.stepEvents evsStoreShim
        (M.stepEvents (rustDeallocEvents 32 8)
          (M.stepEvents evsSavePoll
            (M.stepEvents evsSaveShim
              (M.stepEvents (rustDeallocEvents 16 8)
                (M.stepEvents evsRegPoll
                  (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))))))
      (StoreEnv
        (initSessStorePollGhost x be kp hdr dataPtr opkId reg padVal w1_kyb sg ss kg s0 futStore))
  envOk : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
    ∀ (futReg futSave futStore : BitVec 64)
      (evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim evsStorePoll evsDrop :
        List AllocEvent),
    BoxAllocEnv 16 evsRegShim →
    RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
    BoxAllocEnv 32 evsSaveShim →
    SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
    BoxAllocEnv 32 evsStoreShim →
    ∀ (dataPtr : BitVec 64) (padVal w1_kyb : BitVec 32) (kg : TailVecGhost),
    StoreEnv
      (initSessStorePollGhost x be kp hdr dataPtr opkId reg padVal w1_kyb sg ss kg s0 futStore)
      evsStorePoll →
    FreeOnlyEvs evsDrop →
    ∃ evs, InitEnv x evs ∧
      M.stepEvents evsDrop
        (M.stepEvents (rustDeallocEvents 1568 1)
          (M.stepEvents (rustDeallocEvents 32 8)
            (M.stepEvents evsStorePoll
              (M.stepEvents evsStoreShim
                (M.stepEvents (rustDeallocEvents 32 8)
                  (M.stepEvents evsSavePoll
                    (M.stepEvents evsSaveShim
                      (M.stepEvents (rustDeallocEvents 16 8)
                        (M.stepEvents evsRegPoll
                          (M.stepEvents evsRegShim
                            (M.stepEvents setUnackPreKeyMsgEpochEvents st))))))))))) =
        M.stepEvents evs st0

/-- Specialization of `Stage5BudgetFits` to `InitStoreCalleesPlaced`'s CLI store-poll envelopes. -/
abbrev CliStage5BudgetFits [LibsignalPlacement]
    (M : AllocCostModel) (lim : BudgetLimits)
    (eEnvs : ExistingStoreCalleesEnvs)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (x : InitGhost) (be : PreKeyBundleFields) (kp : IdentityKeyPair)
    (hdr : SignalPqxdh.HandshakeHdr) (opkId : BitVec 32)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (s0 : State) (st0 st : M.σ) : Prop :=
  Stage5BudgetFits M lim InitEnv
    (CliIdRegIdPollEnv eEnvs.dirGet cliIo.rd)
    eEnvs.idSavePoll
    (CliStorePollEnv eEnvs.addressText SerializeEnvX eEnvs.dirPut)
    x be kp hdr opkId sg ss s0 st0 st

theorem initiate_stage5_placed_ok_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {RegPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRodataRegIdSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliIdentityVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 603) ∗ P))
    (hRegShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim (stk - cliInitiateFrame)))
    (hRegPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 568)
      (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim RegPollEnv (stk - cliInitiateFrame)))
    (hRodataSaveSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliIdentityVtSym + 40#64) ↦₆₄ᵣ lsmpl.base 600) ∗ P))
    (hSaveShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hSavePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 565)
      (idSavePollSpecPlaced cliIo.rd cliWrOk A lim SaveEnv (stk - cliInitiateFrame)))
    (hPromote : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
      (withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec))
    (hRodataStoreSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P))
    (hStoreShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hStorePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim StoreEnv (stk - cliInitiateFrame)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hDropSS : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hFit : Stage5BudgetFits M lim InitEnv RegPollEnv SaveEnv StoreEnv x be kp hdr opkId sg ss s0
      st0 st)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
      (stage5MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
      Q Qp oom :=
  initiate_stage5_placed_ok_of_hooks hh
    hRodataRegIdSlot hRegShim hRegPoll
    hRodataSaveSlot hSaveShim hSavePoll
    hPromote
    hRodataStoreSlot hStoreShim hStorePoll
    hFutDrop hDropSS
    hFit.fitUnackMsg hFit.fitRegShim hFit.fitRegPoll hFit.envErr
    hFit.fitSaveShim hFit.fitSavePoll hFit.fitStoreShim hFit.fitStorePoll hFit.envOk
    hS hinitOk hcoinsLt hstk hstk64 hs5 hpost

theorem initiate_stage5_placed_ok_of_store [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hFit : CliStage5BudgetFits M lim eEnvs InitEnv x be kp hdr opkId sg ss s0 st0 st)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
      (stage5MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
      Q Qp oom :=
  initiate_stage5_placed_ok_gen hh
    hStore.rodata_idVt_regIdSlot hStore.idRegIdShim hStore.idRegIdPoll
    hStore.rodata_idVt_saveSlot hStore.idSaveShim hStore.idSavePoll
    (promoteState_cli_placed_ok mmpl gh W hh)
    hStore.rodata_sessVt_storeSlot hStore.sessStoreShim hStore.sessStorePoll
    hStore.futDrop (dropSessionStructure_cli_placed_ok mmpl gh W hh)
    hFit hS hinitOk hcoinsLt hstk hstk64 hspk hs5 hpost

/-- Budget-threaded Stage 5 (`+0x1484 → ret` at `lr`, both `Ok(())` and `Err`) on `initProgPlaced W`. -/
theorem initiate_stage5_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : CliStage5BudgetFits M lim eEnvs InitEnv x be kp hdr opkId sg ss s0 st0 st)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
      (stage5MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
      Q Qp oom := by
  letI : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  exact initiate_stage5_placed_ok_impl hh.alloc
    hLocal.setUnackPreKeyMsg hLocal.setUnackKyberId
    hStore.rodata_idVt_regIdSlot hStore.idRegIdShim hStore.idRegIdPoll
    hStore.rodata_idVt_saveSlot hStore.idSaveShim hStore.idSavePoll
    hLocal.promoteState
    hStore.rodata_sessVt_storeSlot hStore.sessStoreShim hStore.sessStorePoll
    hStore.futDrop hLocal.dropSessionStructure
    hFit.fitUnackMsg hFit.fitRegShim hFit.fitRegPoll hFit.envErr
    hFit.fitSaveShim hFit.fitSavePoll hFit.fitStoreShim hFit.fitStorePoll hFit.envOk
    hS hinitOk hcoinsLt hstk hstk64 hs5 hpost

theorem initiate_stage5_placed_ok_with_panic [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : CliStage5BudgetFits M lim eEnvs InitEnv x be kp hdr opkId sg ss s0 st0 st)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (_hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
      (stage5MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
      Q Qp oom :=
  initiate_stage5_placed_ok hh hStore hLocal hFit hS hinitOk hcoinsLt hstk hstk64 hspk hs5 hpost

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5PlacedBudget

end
