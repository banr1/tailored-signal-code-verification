/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage-P1 and Stage-P4 Store-Kit Projections from `CliDecPkPollKitsPlacedOk`

Projects `PreKeyRemoveKitPlacedOk`, `KyberPreKeyMarkKitPlacedOk`, `H7RAStageP4Prev1AtBStmt`, and
`SeqFree` `SessionOnlyKitPlacedOkSE` directly from `CliDecPkPollKitsPlacedOk` without raw `hRead`
or `hDeser` hypotheses.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.Stage4KitsPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles KyberPreKeyStoreSpec PreKeyStoreSpec withLsRoCl
)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget (
  KyberPreKeyMarkKitPlacedOk
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget (
  PreKeyRemoveKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv kitKpkMarkPollSpecE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  PreKeyStoreBudgetEnv futDropBudgetSpec kitPreKeyRemovePollSpecE
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget (
  CliDecPkPollKitsPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520 (
  H7RAStageP4Prev1AtBStmt h7ra_cliStageP4Prev1SeqFreeEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (
  SessKitHooksPlaced cliAddrText_placed_ok_of_sessHooks cliDirPut_placed_ok_of_sessHooks
  cliSessStorePoll_rocl_seqFree_placed_ok cliSessStoreShim_rocl_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget (
  cliPollSess_prev1SeqFreeKitPlacedOk stageP4Prev1_placed_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliPollKpkFullBudgetEnv cliPollPkFullBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessSeqFreeBudgetEnv
  cliSerializeCanonSeqFree_placed_ok
)

/-- At `fds = false`, `futDropBudgetSpec fdsOk false = futDropBudgetSpec (fun _ => True) false`. -/
theorem futDropBudgetSpec_false_eq (fdsOk : FsState → Prop) :
    futDropBudgetSpec fdsOk false = futDropBudgetSpec :=
  rfl

/-- Projects `PreKeyStoreKitPlacedOk` at `cliPollPkFullBudgetEnv` to `PreKeyRemoveKitPlacedOk`
at `cliPollPkBudgetEnv` (`removePollEnv` agrees definitionally). -/
theorem preKeyRemoveKitPlacedOk_of_fullStore [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles} {pid : BitVec 32} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    (h : PreKeyStoreKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) H) :
    PreKeyRemoveKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) H where
  removeShim hblk := h.removeShim hblk
  removePoll hblk := h.removePoll hblk
  removeFutDrop hblk := futDropBudgetSpec_false_eq _ ▸ h.removeFutDrop hblk

/-- Projects `KyberPreKeyStoreKitPlacedOk` at `cliPollKpkFullBudgetEnv` to `KyberPreKeyMarkKitPlacedOk`
at `cliPollKpkBudgetEnv` (`markPollEnv` agrees definitionally). -/
theorem kyberPreKeyMarkKitPlacedOk_of_fullStore [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles} {kid sid : BitVec 32} {kbk : PublicKey} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    (h : KyberPreKeyStoreKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) H) :
    KyberPreKeyMarkKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) H where
  markShim hblk := h.markShim hblk
  markPoll hblk := h.markPoll hblk
  markFutDrop hblk := futDropBudgetSpec_false_eq _ ▸ h.markFutDrop hblk

/-- Discharges `H7RAStageP4Prev1AtBStmt` from `CliDecPkPollKitsPlacedOk` without a raw `hRead` hypothesis. -/
theorem h7ra_stageP4Prev1_seqFree_at_cliRunBudgets_of_kits [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hKits : CliDecPkPollKitsPlacedOk A lim cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    H7RAStageP4Prev1AtBStmt A lim mmpl gh W cliRunBudgets
      (fun B F0 peer pid kpkId spkId kbk =>
        h7ra_cliStageP4Prev1SeqFreeEnvs A.repAlloc B F0 peer pid kpkId spkId kbk
          (ReadFileRuleEnvFixed cliIo.rd)) :=
  fun F0 peer pid kpkId spkId kbk st_b hhStages =>
    stageP4Prev1_placed_of_kits mmpl gh W cliRunBudgets F0 peer pid kpkId spkId kbk h547 hhStages
      (cliPollSess_prev1SeqFreeKitPlacedOk mmpl gh W cliRunBudgets F0 peer h547 hhStages)
      (hKits.idOk F0 peer)
      (preKeyRemoveKitPlacedOk_of_fullStore (hKits.pkOk F0 pid))
      (kyberPreKeyMarkKitPlacedOk_of_fullStore (hKits.kpkOk F0 kpkId spkId kbk))
      st_b

/-- Upgrades `SessionOnlyKitPlacedOkSE` from `cliPollSessBudgetEnv` to
`cliPollSessSeqFreeBudgetEnv` without raw `hRead` or `hDeser` hypotheses. -/
theorem cliPollSess_seqFreeKitPlacedOkSE_of_kits [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSess : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
        A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessSeqFreeBudgetEnv A.repAlloc F0 peer (cliKitStk B) DeserEnv ReadEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hhS := SessKitHooksPlaced.of_runHooks
    { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
      bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
      codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed,
      stringClone := hh.stringClone, formatInner := hh.formatInner }
  have hAddr := cliAddrText_placed_ok_of_sessHooks hhS
  have hPut := cliDirPut_placed_ok_of_sessHooks hhS
  have hSer := cliSerializeCanonSeqFree_placed_ok mmpl gh W hh
  exact
    { loadShim := fun hblk => hSess.loadShim hblk
      loadPoll := fun hblk => hSess.loadPoll hblk
      loadFutDrop := fun hblk => hSess.loadFutDrop hblk
      storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hhS.alloc (Nat.le_refl _) hblk
      storePoll := fun hblk =>
        cliSessStorePoll_rocl_seqFree_placed_ok (serProg := CryptoVerification.E2E.Record.Placed.lsProg_52 H)
          (serBlk := 52) hhS.alloc hAddr hSer hPut (Nat.le_refl _) hblk
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      storeFutDrop := fun hblk => hSess.storeFutDrop hblk }

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.Stage4KitsPlacedBudgetFd
