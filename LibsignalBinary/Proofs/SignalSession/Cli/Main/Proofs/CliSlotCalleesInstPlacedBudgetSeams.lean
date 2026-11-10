/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded CLI Slot Seams & Store-Kit Witnesses (`[LibsignalPlacement]`)

Allocation-event envelopes, external hook bundles, upstream `SpqrV1` / deserialization /
signature-verification seams, and placed session/identity store-kit witnesses (`Dir::put`) for
`CliSlotCalleesInstPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsBlackBoxU8Sym lsmpl lsρ)
open CryptoVerification.CliRatchet.EncPlaced (lsProg_464)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims pqxdhSpqrModel)
open CryptoVerification.E2E.Record (RecordPqEmpty encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles IdentityVtablesPlacedOk SessionOnlyVtablesPlacedOk withEnvPre withLsCodeRoLoaded
)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel extHookStack finishGrowStackX)
open CryptoVerification.LibsignalTripleRatchet.Encrypt (lsAesEncSym)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsDropOffPlaced_eq lsFormatInnerSym lsReadFileSym
  lsRustAllocZeroedSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliGhostExterns_blackBox cliIdentityVtRoSym cliIdentityVtablesPlacedOk cliSessionVtRoSym
)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (
  savePollNeed saveShimNeed trustPollNeed trustShimNeed
)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (
  cliSessionKitSpecPlaced_vtables dirPutNeedPlaced loadPollNeed loadShimNeed
  storePollNeedX storeShimNeed
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_542 lsProg_543 lsProg_569 lsProg_586 lsProg_589)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (cliDirPutStk initProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer cliEncRecOk_opened scopeIn scopeKit
  scopeKit_pqrState_lt scopeKit_recordInScopeEnc
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (
  FormatInnerEnv aesEncBudgetSpec formatInnerBudgetEnvSpec formatInnerBudgetSpec
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux (
  PublicApiEncHooksPlaced otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget (
  spqrSendCoinsPlacedSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudget (dirPut_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget (dirPutStr_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget (
  cliIdKitOkIE_placed cliIdentityKitDefaultBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (
  cliGrowOneDir_placed_ok cliSessKitOkSE_cli_scopeKit_placed cliSessionKitDefaultBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget (
  spqrInitialStateInnerSpec verifySignatureInnerSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget (
  decIdKitPlaced decSessKitPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  w1IdKitPlaced w1SessKitPlaced withStoresEncPlacedSpecVT_cli
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostSpqrAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  dirPutSpecPlaced dirPutStrSpecPlaced readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Explicit Allocation-Event Envelopes, Hook Bundle, & Upstream Seams -/

/-- Explicit allocation-event envelopes parameterized at the CLI slot-callee boundary
(`0` existential quantifiers). -/
structure CliSlotEnvs where
  readFile : FsFiles → List (BitVec 8) → List AllocEvent → Prop
  sessDeser : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop
  spqrSend : SpqrSendBudgetEnv
  tryDecrypt : TryDecryptEnvArgs → List AllocEvent → Prop
  spqrInitState : Params → List AllocEvent → Prop

/-- Budget-threaded external hook witnesses on `cliGhostExterns g (cliExternsPlaced mmpl W)`
for `encrypt`, `decrypt`, and `initiate` slot callees. -/
structure CliSlotAllocHooks [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) : Prop where
  alloc : CliGhostSpqrAllocHooks M A lim g
  strClone_fsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f
  stringClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
    (stringCloneBudgetSpec M A lim)
  stringCloneEnc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsStringCloneSym
    (stringCloneBudgetSpec M A lim)
  aesEnc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesEncSym
    (aesEncBudgetSpec W.C.E M A lim)
  formatInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
    (formatInnerBudgetSpec M A lim)
  formatInnerEnv : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W))
    CryptoVerification.LibsignalTripleRatchet.Encrypt.lsFormatInnerSym
    (formatInnerBudgetEnvSpec M A lim FormatInnerEnv)
  readFile : ∀ (stk : Nat),
    subroutine_ok (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim stk ReadEnv))

/-- Budget-threaded counterpart of `SpqrV1PlacedSeams` plus the upstream Block-`46`
`SessionRecord::deserialize` (`sessDeserScopeKit`) and Block-`203` `verify_signature` seams. -/
structure SpqrV1PlacedSeamsBudget [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (envs : CliSlotEnvs) : Prop where
  spqrSendCoins :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩)
            (fun sc evs => envs.spqrSend sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜sc.st.bytes.length < 2 ^ 32 ∧ 64 ≤ sc.rest.length⌝ ∗ tokenInitPlacedAt ∗
              (spqrSendCoinsPlacedSpec M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩)
                (fun sc evs => envs.spqrSend sc.st.bytes sc.rest evs)).pre (sc, st) s
          post := fun (sc, st) s0 sf =>
            tokenInitPlacedAt ∗ (spqrSendCoinsPlacedSpec M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩)
              (fun sc evs => envs.spqrSend sc.st.bytes sc.rest evs)).post (sc, st) s0 sf })
  spqrInitialState_initProg :
    subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim envs.spqrInitState W.C.F))
  sessDeserScopeKit :
    subroutine_ok (lsProg_569 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim envs.sessDeser)
  verifySignature : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩)))

/-- Seam over Block `464` (`Cli/PublicApi/MessageEncrypt/WithStoresVTPlaced` budget composition),
matching `withStores_placed_okVT_fs_cli` once all segment, kit, vtable, and Block-`428`
`otrEncrypt` budget contracts are supplied. -/
def WithStoresEncVTPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer)) : Prop :=
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  PublicApiEncHooksPlaced A lim H →
  (∀ F peer, SessionOnlyKitPlacedOkSE A lim (w1SessKitPlaced A.repAlloc B F peer)
    (kitEnv F peer) scopeKit encodeRecord H) →
  (∀ F peer, IdentityStoreKitPlacedOkI A lim (w1IdKitPlaced A.repAlloc B F peer)
    (ikitEnv F peer) H) →
  subroutine_ok (lsProg_464 H)
    (CryptoVerification.libsignalSessionLib.fnAddr lsmpl
      CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
      (otrEncryptPlacedSpecQF (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length)
        tokenInitPlacedAt W.C A lim 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) sendEnv)) →
  subroutine_ok (lsProg_464 H)
    (CryptoVerification.libsignalSessionLib.fnAddr lsmpl
      CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
      (otrEncryptPlacedSpecQ (· = []) W.C A lim 0#64 uuidTryParse
        (pqxdhSpqrModel ⟨W.C, W.Q⟩) (fun _ _ evs => evs = []))) →
  (∀ F peer, SessionOnlyVtablesPlacedOk (w1SessKitPlaced A.repAlloc B F peer)) →
  (∀ F peer, IdentityVtablesPlacedOk (w1IdKitPlaced A.repAlloc B F peer)) →
  ∀ (F : FsFiles) (peer : AddrGhost), FilesOkPeer scopeIn F peer.val →
    let kit := w1SessKitPlaced A.repAlloc B F peer
    let ikit := w1IdKitPlaced A.repAlloc B F peer
    subroutine_ok (lsProg_464 H) (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim kit (kitEnv F peer)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
          ikit (ikitEnv F peer)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          scopeKit W.C 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) sendEnv encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))

/-! ## 2. Placed Store Kits, Vtables, & `Dir::put` / `Dir::put::<&str>` Witnesses -/

theorem skeletonHooks_of_slotHooks [LibsignalPlacement] {M : AllocCostModel}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  RunHooksPlaced.of_hooks mmpl g W hH.alloc hH.strClone_fsT hH.stringClone hH.formatInner

theorem cliGhostExterns_blackBox_eq (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  cliGhostExterns_blackBox mmpl g W

noncomputable abbrev w1SessKitBudgetEnv [LibsignalPlacement]
    (A : CryptoVerification.RustHeap.RustAlloc) (B : RunBudgets)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (peer : AddrGhost) :
    SessionStoreBudgetEnv (w1SessKitPlaced A B F0 peer) :=
  cliSessionKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk scopeKit peer
    loadShimNeed (loadPollNeed B.readFile)
    storeShimNeed storePollNeedX
    DeserEnv cliSessionVtRoSym cliIdentityVtRoSym ReadEnv

noncomputable abbrev w1IdKitBudgetEnv [LibsignalPlacement]
    (A : CryptoVerification.RustHeap.RustAlloc) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (peer : AddrGhost) :
    IdentityStoreBudgetEnv (w1IdKitPlaced A B F0 peer) :=
  cliIdentityKitDefaultBudgetEnv A cliIo.rd F0 cliWrOk peer
    trustShimNeed (trustPollNeed B.readFile)
    saveShimNeed (savePollNeed B.readFile)
    cliIdentityVtRoSym ReadEnv

noncomputable abbrev decSessKitBudgetEnv [LibsignalPlacement]
    (A : CryptoVerification.RustHeap.RustAlloc) (B : RunBudgets)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (peer : AddrGhost) :
    SessionStoreBudgetEnv (decSessKitPlaced A F0 peer B) :=
  w1SessKitBudgetEnv A B DeserEnv ReadEnv F0 peer

noncomputable abbrev decIdKitBudgetEnv [LibsignalPlacement]
    (A : CryptoVerification.RustHeap.RustAlloc) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (peer : AddrGhost) :
    IdentityStoreBudgetEnv (decIdKitPlaced A F0 peer B) :=
  w1IdKitBudgetEnv A B ReadEnv F0 peer

/-- Vtable witness `SessionOnlyVtablesPlacedOk` for `w1SessKitPlaced` / `decSessKitPlaced`. -/
theorem w2SessVt_placed_ok [LibsignalPlacement]
    (A : CryptoVerification.RustHeap.RustAlloc) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64) (F0 : FsFiles) (peer : AddrGhost) :
    SessionOnlyVtablesPlacedOk (decSessKitPlaced A F0 peer B) :=
  cliSessionKitSpecPlaced_vtables (A := A) (rd := cliIo.rd) (F0 := F0)
    (pathOk := cliWrOk) (Scope := scopeKit) (peer := peer)
    (s1 := loadShimNeed) (s2 := loadPollNeed B.readFile)
    (s3 := storeShimNeed) (s4 := storePollNeedX)
    (idVtSym := cliIdentityVtRoSym) hDropNz

/-- Vtable witness `IdentityVtablesPlacedOk` for `w1IdKitPlaced` / `decIdKitPlaced`. -/
theorem w2IdVt_placed_ok [LibsignalPlacement]
    (A : CryptoVerification.RustHeap.RustAlloc) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64) (F0 : FsFiles) (peer : AddrGhost) :
    IdentityVtablesPlacedOk (decIdKitPlaced A F0 peer B) := by
  refine cliIdentityVtablesPlacedOk ?_
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    lsDropOffPlaced_eq hDropNz, lsDropOffPlaced_eq hDropNz, rfl, rfl⟩

/-- `SessionOnlyKitPlacedOkSE` for `w1SessKitPlaced A.repAlloc B F0 peer`. -/
theorem w1SessKitPlaced_okSE [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (envs : CliSlotEnvs) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (F0 : FsFiles) (peer : AddrGhost) :
    SessionOnlyKitPlacedOkSE A lim (w1SessKitPlaced A.repAlloc B F0 peer)
      (w1SessKitBudgetEnv A.repAlloc B envs.sessDeser envs.readFile F0 peer)
      scopeKit encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_scopeKit_placed mmpl g W
    (F0 := F0) (Scope := scopeKit) (peer := peer)
    (readStk := B.readFile)
    (s1 := loadShimNeed) (s2 := loadPollNeed B.readFile)
    (s3 := storeShimNeed) (s4 := storePollNeedX)
    (vtSym := cliSessionVtRoSym) (idVtSym := cliIdentityVtRoSym)
    (readProg := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 589)
    (deserProg := lsProg_569 (cliGhostExterns g (cliExternsPlaced mmpl W))) (deserBlk := 569)
    hDropNz hH.alloc.toCliGhostAllocHooks hH.alloc.allocZeroed_fsT hH.strClone_fsT
    (hH.readFile B.readFile) hSpqr.sessDeserScopeKit (fun _ h => h)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide)

/-- `IdentityStoreKitPlacedOkI` for `w1IdKitPlaced A.repAlloc B F0 peer`. -/
theorem w1IdKitPlaced_okIE [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv)
    (F0 : FsFiles) (peer : AddrGhost) :
    IdentityStoreKitPlacedOkI A lim (w1IdKitPlaced A.repAlloc B F0 peer)
      (w1IdKitBudgetEnv A.repAlloc B ReadEnv F0 peer)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_placed
    (rd := cliIo.rd) (F0 := F0) (pathOk := cliWrOk) (peer := peer)
    (readStk := B.readFile)
    (s1 := trustShimNeed) (s2 := trustPollNeed B.readFile)
    (s3 := saveShimNeed) (s4 := savePollNeed B.readFile)
    (vtSym := cliIdentityVtRoSym)
    (readProg := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 589)
    hDropNz (fun _ hp => hp.2) (skeletonHooks_of_slotHooks hH) (hH.readFile B.readFile)
    (cliGhostExterns_blackBox_eq mmpl g W)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide)

/-- Stack budget needed by `Dir::put::<&str>` (Block `543`). -/
abbrev cliDirPutStrNeedPlaced : Nat :=
  0x50 + max (0x40 + finishGrowStackX) extHookStack

/-- Budget-threaded Block-`543` (`Dir::put::<&str>`) contract at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
def DirPutStrPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  subroutine_ok (lsProg_543 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 543)
    (dirPutStrSpecPlaced A lim DirPutStrEnv cliDirPutStrNeedPlaced)

theorem dirPutStrPlacedOk_cli [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    DirPutStrPlacedOk mmpl g W A lim :=
  let hh := skeletonHooks_of_slotHooks hH
  dirPutStr_placed_ok_of_deps hh.alloc hh.panics hh.memcpyRO hh.bcmp
    (growProg := lsProg_586 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jGrow := 586)
    (by decide) (by decide) (cliGrowOneDir_placed_ok hh.alloc hh.panics)
    (Nat.le_refl cliDirPutStrNeedPlaced)

/-- Budget-threaded Block-`542` (`Dir::put::<String>`) contract at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem w3DirPut_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    subroutine_ok (lsProg_542 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 542)
      (dirPutSpecPlaced A lim DirPutEnv cliDirPutStk) :=
  let hh := skeletonHooks_of_slotHooks hH
  dirPut_placed_caller_ok_of_deps
    (callerProg := lsProg_542 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 542)
    hh.alloc hh.bcmp
    (growProg := lsProg_586 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jGrow := 586)
    (by decide) (by decide) (cliGrowOneDir_placed_ok hh.alloc hh.panics)
    (Nat.le_refl dirPutNeedPlaced) (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
