/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySelfKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberPreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SignedPreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Six-Kit CLI `decrypt_prekey` Poll Seam (`fds = true`)

Defines the plain (`CliDecPkPollKitsPlacedOk`) and `FdsGe3Closed`-threaded
(`CliDecPkPollKitsPlacedOkFds`) six-kit bundles for `decrypt_prekey` poll (`dpPollProgPlaced ext`),
and constructs `CliDecPkPollKitsPlacedOkFds` from `AllocContractsFsPlaced`, `lsmpl.base 547 ≠ 0#64`,
and the `withFdsGe3Closed` poll triples on blocks 565–571, 573, 575, 576, and 578.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession.Cli (cliIdentityVtSym cliSessionVtSym keyName)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (lsProg_565 lsProg_566 lsProg_567 lsProg_568 lsProg_569 lsProg_570 lsProg_571 lsProg_573
   lsProg_575 lsProg_576 lsProg_578)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSelfKitPlaced
   cliPollSessKitPlaced cliPollSpkKitPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentitySelfStoreKitPlacedOkI IdentitySelfStoreKitPlacedOkIFds IdentityStoreKitPlacedOkI
   IdentityStoreKitPlacedOkIFds KyberPreKeyStoreKitPlacedOk KyberPreKeyStoreKitPlacedOkFds
   PreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOkFds SessionOnlyKitPlacedOkSE
   SessionOnlyKitPlacedOkSEFds SignedPreKeyStoreKitPlacedOk SignedPreKeyStoreKitPlacedOkFds)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerializeEnvX)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
  (cliIdKitOkIE_fds_placed_direct_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySelfKitFdsPlacedBudget
  (cliIdKitPlacedOkIFds_full cliIdSelfKitPlacedOkIFds_full_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberPreKeyKitFdsPlacedBudget
  (cliKpkKitPlacedOkFds_full_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyKitFdsPlacedBudget
  (cliPkKitPlacedOkFds_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitFdsPlacedBudget
  (cliSessKitOkSE_fds_placed_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (AddrTextValEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SignedPreKeyKitFdsPlacedBudget
  (cliSpkKitPlacedOkFds_of_poll)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
  (cliPollSelfBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (cliPollIdBudgetEnv cliPollSessBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
  (CliPkDecodeEnv CliSpkDecodeEnv cliPollKpkFullBudgetEnv cliPollPkFullBudgetEnv
   cliPollSpkFullBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (CliIdKeyPairPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (CliIdRegIdPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced idKeyPairPollSpecPlaced idRegIdPollSpecPlaced idSavePollSpecPlaced
   idTrustPollSpecPlaced kpkGetPollSpecPlaced kpkMarkPollSpecPlaced pkGetPollSpecPlaced
   pkRemovePollSpecPlaced sessLoadPollSpecPlaced sessStorePollSpecPlaced spkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget (CliIdSavePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlacedBudget (CliIdTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux (CliKpkMarkPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (CliLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget (CliStorePollEnv)

/-! ## Six-Kit CLI `decrypt_prekey` Poll Seam -/

/-- Plain (`fds = false`) bundle of the 6 CLI store-kit `PlacedOk*` contracts consumed across
Stage P1 and Stage P2 of `decrypt_prekey` poll (`dpPollProgPlaced ext`). -/
structure CliDecPkPollKitsPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : LibsignalHooks) : Prop where
  sessOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord ext
  idOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc F0 peer B ReadEnv) ext
  selfOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentitySelfStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv) ext
  spkOk : ∀ (F0 : FsFiles) (sid : BitVec 32),
    SignedPreKeyStoreKitPlacedOk A lim
      (cliPollSpkKitPlaced A.repAlloc F0 sid (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc F0 sid (cliKitStk B) ReadEnv) ext
  kpkOk : ∀ (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey),
    KyberPreKeyStoreKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) ext
  pkOk : ∀ (F0 : FsFiles) (pid : BitVec 32),
    PreKeyStoreKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) ext

/-- Descriptor-threaded (`fds = true`, `.fdsOk = FdsGe3Closed`) bundle of the six CLI store-kit
`PlacedOk*Fds` contracts for `decrypt_prekey` poll. -/
structure CliDecPkPollKitsPlacedOkFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : LibsignalHooks) : Prop where
  sessFdsEq : ∀ (F0 : FsFiles) (peer : AddrGhost),
    (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B)).fdsOk = FdsGe3Closed
  sessOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyKitPlacedOkSEFds A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord ext
  idFdsEq : ∀ (F0 : FsFiles) (peer : AddrGhost),
    (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B)).fdsOk = FdsGe3Closed
  idOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityStoreKitPlacedOkIFds A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc F0 peer B ReadEnv) ext
  selfFdsEq : ∀ (F0 : FsFiles) (peer : AddrGhost),
    (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)).fdsOk = FdsGe3Closed
  selfOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentitySelfStoreKitPlacedOkIFds A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv) ext
  spkFdsEq : ∀ (F0 : FsFiles) (sid : BitVec 32),
    (cliPollSpkKitPlaced A.repAlloc F0 sid (cliKitStk B)).fdsOk = FdsGe3Closed
  spkOk : ∀ (F0 : FsFiles) (sid : BitVec 32),
    SignedPreKeyStoreKitPlacedOkFds A lim
      (cliPollSpkKitPlaced A.repAlloc F0 sid (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc F0 sid (cliKitStk B) ReadEnv) ext
  kpkFdsEq : ∀ (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey),
    (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B)).fdsOk = FdsGe3Closed
  kpkOk : ∀ (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey),
    KyberPreKeyStoreKitPlacedOkFds A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) ext
  pkFdsEq : ∀ (F0 : FsFiles) (pid : BitVec 32),
    (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B)).fdsOk = FdsGe3Closed
  pkOk : ∀ (F0 : FsFiles) (pid : BitVec 32),
    PreKeyStoreKitPlacedOkFds A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) ext

/-! ## Constructor from `AllocContractsFsPlaced` and the 11 Poll Triples -/

/-- Assemble `CliDecPkPollKitsPlacedOkFds` from `lsmpl.base 547 ≠ 0#64`, `AllocContractsFsPlaced`,
and the `withFdsGe3Closed` poll triples on blocks 569, 570, 566, 565, 567, 568, 571, 576, 578,
573, and 575. -/
theorem cliDecPkPollKitsPlacedOkFds_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : LibsignalHooks}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim ext)
    (h569 : subroutine_ok (lsProg_569 ext) (lsmpl.base 569)
      (withFdsGe3Closed
        (sessLoadPollSpecPlaced cliIo.rd cliWrOk scopeKit A lim
          (CliLoadPollEnv cliIo.rd scopeKit (fun g => AddrTextValEnv DecimalEnv g.val)
            (DirGetEnv PathEnv ReadEnv cliIo.rd) DeserEnv)
          (cliKitStk B).sessLoadPoll)))
    (h570 : subroutine_ok (lsProg_570 ext) (lsmpl.base 570)
      (withFdsGe3Closed
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv (fun g => AddrTextValEnv DecimalEnv g.val) SerializeEnvX DirPutEnv)
          (cliKitStk B).sessStorePoll)))
    (h566 : subroutine_ok (lsProg_566 ext) (lsmpl.base 566)
      (withFdsGe3Closed
        (idTrustPollSpecPlaced cliIo.rd cliWrOk A lim
          (CliIdTrustPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd))
          (cliKitStk B).idTrustPoll)))
    (h565 : subroutine_ok (lsProg_565 ext) (lsmpl.base 565)
      (withFdsGe3Closed
        (idSavePollSpecPlaced cliIo.rd cliWrOk A lim
          (CliIdSavePollEnv cliIo.rd (DirGetEnv PathEnv ReadEnv cliIo.rd) DirPutStrEnv)
          (cliKitStk B).idSavePoll)))
    (h567 : subroutine_ok (lsProg_567 ext) (lsmpl.base 567)
      (withFdsGe3Closed
        (idKeyPairPollSpecPlaced cliIo.rd cliWrOk A lim
          (CliIdKeyPairPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd)
          (cliKitStk B).kpPoll)))
    (h568 : subroutine_ok (lsProg_568 ext) (lsmpl.base 568)
      (withFdsGe3Closed
        (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim
          (CliIdRegIdPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) cliIo.rd)
          (cliKitStk B).regIdPoll)))
    (h571 : subroutine_ok (lsProg_571 ext) (lsmpl.base 571)
      (withFdsGe3Closed
        (spkGetPollSpecPlaced cliIo.rd cliWrOk A lim
          (fun F0 x => CliSpkGetPollEnv DecimalEnv
            (fun dir k => DirGetEnv PathEnv ReadEnv cliIo.rd F0 dir (keyName k))
            CliSpkDecodeEnv cliIo.rd F0 x)
          (cliKitStk B).spkGetPoll)))
    (h576 : subroutine_ok (lsProg_576 ext) (lsmpl.base 576)
      (withFdsGe3Closed
        (kpkGetPollSpecPlaced cliIo.rd cliWrOk A lim
          (fun F0 x => CliKpkGetPollEnv DecimalEnv
            (fun dir k => DirGetEnv PathEnv ReadEnv cliIo.rd F0 dir (keyName k))
            CliSpkDecodeEnv cliIo.rd F0 x)
          (cliKitStk B).kpkGetPoll)))
    (h578 : subroutine_ok (lsProg_578 ext) (lsmpl.base 578)
      (withFdsGe3Closed
        (kpkMarkPollSpecPlaced cliIo.rd cliWrOk A lim
          (CliKpkMarkPollEnv cliIo.rd DecimalEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) DirPutEnv)
          (cliKitStk B).kpkMarkPoll)))
    (h573 : subroutine_ok (lsProg_573 ext) (lsmpl.base 573)
      (withFdsGe3Closed
        (pkGetPollSpecPlaced cliIo.rd cliWrOk A lim
          (fun F0 x => CliPkGetPollEnv DecimalEnv
            (DirGetEnv PathEnv ReadEnv cliIo.rd F0) CliPkDecodeEnv cliIo.rd F0 x)
          (cliKitStk B).pkGetPoll)))
    (h575 : subroutine_ok (lsProg_575 ext) (lsmpl.base 575)
      (withFdsGe3Closed
        (pkRemovePollSpecPlaced cliIo.rd cliWrOk A lim
          (CliPkRemovePollEnv cliIo.rd DecimalEnv (DirGetEnv PathEnv ReadEnv cliIo.rd) DirPutEnv)
          (cliKitStk B).pkRemovePoll))) :
    CliDecPkPollKitsPlacedOkFds A lim B ReadEnv DeserEnv ext where
  sessFdsEq _ _ := rfl
  sessOk F0 peer :=
    cliSessKitOkSE_fds_placed_of_polls
      (F0 := F0) (peer := peer) (vtSym := cliSessionVtSym) (idVtSym := cliIdentityVtSym)
      hDropNz hFs h569 h570 (Nat.le_refl _) (Nat.le_refl _)
  idFdsEq _ _ := rfl
  idOk F0 peer :=
    cliIdKitPlacedOkIFds_full
      (cliIdKitOkIE_fds_placed_direct_of_polls
        (F0 := F0) (peer := peer) (vtSym := cliIdentityVtSym)
        hDropNz hFs h566 h565 (Nat.le_refl _) (Nat.le_refl _))
  selfFdsEq _ _ := rfl
  selfOk F0 peer :=
    cliIdSelfKitPlacedOkIFds_full_of_polls
      (t1 := (cliKitStk B).idTrustShim) (t2 := (cliKitStk B).idTrustPoll)
      (t3 := (cliKitStk B).idSaveShim) (t4 := (cliKitStk B).idSavePoll)
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)
      hDropNz hFs (Nat.le_refl _) (Nat.le_refl _)
      (fun _ _ _ _ _ hm => hm)
      (fun _ _ _ _ _ hm => hm)
      h567 h568
  spkFdsEq _ _ := rfl
  spkOk F0 sid :=
    cliSpkKitPlacedOkFds_of_poll
      (kitEnv := cliPollSpkFullBudgetEnv A.repAlloc F0 sid (cliKitStk B) ReadEnv)
      hDropNz hFs (fun _ _ _ _ _ hm => hm) h571 (Nat.le_refl _)
  kpkFdsEq _ _ _ _ := rfl
  kpkOk F0 kid sid kbk :=
    cliKpkKitPlacedOkFds_full_of_polls
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv)
      hDropNz hFs (Nat.le_refl _) (Nat.le_refl _)
      (fun _ _ _ _ _ hm => hm)
      (fun _ _ _ _ _ _ hm => hm)
      h576 h578
  pkFdsEq _ _ := rfl
  pkOk F0 pid :=
    cliPkKitPlacedOkFds_of_polls
      (kitEnv := cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv)
      hDropNz hFs
      (fun _ _ _ _ _ hm => hm)
      (fun _ _ _ _ _ hm => hm)
      h573 h575 (Nat.le_refl _) (Nat.le_refl _)

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
