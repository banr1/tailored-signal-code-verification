/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Drops
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.Chain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.DropLocal2Ext
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.TripleRatchet.Glue

/-!
# Relocatable Inner Contract Instantiation for `decrypt_signal`

Instantiates `InnerDecryptPlacedOk` and `InnerDecryptFrozenPlacedOk` on Block `463`
(`signal_session_ratchet::decrypt_signal`) under `[LibsignalPlacement]` and
`[LibsignalFullPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.Cli.LibsignalTripleRatchet.Record hiding lsProg_463
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.CliRatchet.DecPlaced
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Reduces `InnerDecryptPlacedOk` on Block `463` to the `recordDecryptPlacedSpecTPTight` region obligation. -/
theorem w2_inner_placed_ok_of_region [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {B : RunBudgets}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((WithStoresVT.recordDecryptPlacedSpecTPTight W.C E2E.HooksE.A0 0#64 uuidTryParse
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩)).withVRegs.restrictPre (fun _ => True))) :
    InnerDecryptPlacedOk mmpl gh W B := by
  intro F0 peer hPeer
  dsimp only [decSessKitPlaced, decIdKitPlaced]
  have hSess : SessionOnlyKitPlacedOkSE (EncryptLemmas.w1SessKitPlaced B F0 peer)
      Slots.scopeKit E2E.Record.encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
    exact KitInst.cliSessKitOkSE_cli_scopeKit_placed mmpl gh W
      (readStk := B.readFile)
      (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
      hDropNz hh hRead
      (KitInst.stage2ContractsMinPlaced_of_runHooks mmpl gh W hh)
      (fun _ h => h)
      (by decide) (Nat.le_refl _) (by decide) (by decide)
  have hId : IdentityStoreKitPlacedOkI (EncryptLemmas.w1IdKitPlaced B F0 peer)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    KitInst.cliIdKitOkIE_cli_placed mmpl gh W (F0 := F0) (peer := peer) (readStk := B.readFile)
      (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
      hDropNz hh hRead
      (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _)
  have hq : (EncryptLemmas.w1SessKitPlaced B F0 peer).Quiet ∧
      (EncryptLemmas.w1IdKitPlaced B F0 peer).Quiet :=
    ⟨SessKit.cliSessionKitSpecPlaced_quiet, IdKit.cliIdentityKitSpecPlaced_quiet⟩
  have hraw := decryptSignalWithStores_placed_okVTP_distinct_fs_cli mmpl gh W
    (A := E2E.HooksE.A0) (ctl := 0#64) (S := E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩)
    (encRecord := E2E.Record.encodeRecord)
    (kit := EncryptLemmas.w1SessKitPlaced B F0 peer)
    (ikit := EncryptLemmas.w1IdKitPlaced B F0 peer)
    (st0 := StoresGhost.opened.sessions) (ist0 := StoresGhost.opened.identity)
    (Scope := Slots.scopeKit) (Q := fun _ => True)
    (DecHypsExtPlaced.of_cliHooks mmpl gh W hG hh.stringClone hSess hId
      (fun _ hr => Slots.scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        Slots.cliDecModelRecOkAt_opened
          (A := E2E.HooksE.A0) (b := 0#64) (pathOk := cliWrOk)
          (Scope₀ := Slots.scopeIn) (F0 := F0) (peer := peer)
          (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
          (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
          (fun _ h => h) hPeer x rec rec' pt haddr hsc hdec))
    hrec
    (fun _ _ ses hsc hcur => ⟨Slots.scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
    (KitFsOk.of_sound hq (hh.fs (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 463))
  refine subroutine_ok_mono hraw ?_ ?_
  · intro x R s0 hpre
    dsimp only [withEnvPre, DecryptLemmas.withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVTP,
      WithStoresVT.withStoresDecPlacedSpecVTP, WithStoresVT.withStoresDecPlacedSpecVTPF,
      Spec.restrictPre] at hpre ⊢
    generalize (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX
      W.C E2E.HooksE.A0 0#64 uuidTryParse (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord
      (EncryptLemmas.w1SessKitPlaced B F0 peer)
      (EncryptLemmas.w1IdKitPlaced B F0 peer)
      StoresGhost.opened.sessions StoresGhost.opened.identity
      Slots.scopeKit (fun _ _ => False)).pre x s0 = Bpre at hpre ⊢
    generalize SpqrV1.GF.Mul2U16.tokenInitPlacedAt = T at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  · intro x R s0 sf hpost
    dsimp only [withEnvPre, DecryptLemmas.withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVTP,
      WithStoresVT.withStoresDecPlacedSpecVTP, WithStoresVT.withStoresDecPlacedSpecVTPF,
      Spec.restrictPre] at hpost ⊢
    exact hpost

/-- Instantiates `InnerDecryptPlacedOk` on Block `463` via `recordDecryptV1_placed_region_vregs_ok_PTight_cli`. -/
theorem w2_inner_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {B : RunBudgets}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hclosure : subroutine_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 462) (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec)) :
    InnerDecryptPlacedOk mmpl gh W B :=
  w2_inner_placed_ok_of_region mmpl gh W hDropNz hG hh hRead
    (region_ok_restrictPre_true
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_placed_region_vregs_ok_PTight_cli
        mmpl gh W 0#64 hG hAesDec hSpqr hclosure))

/-- Reduces `InnerDecryptFrozenPlacedOk` on Block `463` to the `withLsFrozen`-guarded
`recordDecryptPlacedSpecTPTight` region obligation. -/
theorem w2_inner_frozen_placed_ok_of_region [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {B : RunBudgets}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hrec : region_ok (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((withLsFrozen lsmpl
        (WithStoresVT.recordDecryptPlacedSpecTPTight W.C E2E.HooksE.A0 0#64 uuidTryParse
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))).withVRegs.restrictPre (fun _ => True))) :
    InnerDecryptFrozenPlacedOk mmpl gh W B := by
  intro F0 peer hPeer
  dsimp only [decSessKitPlaced, decIdKitPlaced]
  have hSess : SessionOnlyKitPlacedOkSE (EncryptLemmas.w1SessKitPlaced B F0 peer)
      Slots.scopeKit E2E.Record.encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
    exact KitInst.cliSessKitOkSE_cli_scopeKit_placed mmpl gh W
      (readStk := B.readFile)
      (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
      hDropNz hh hRead
      (KitInst.stage2ContractsMinPlaced_of_runHooks mmpl gh W hh)
      (fun _ h => h)
      (by decide) (Nat.le_refl _) (by decide) (by decide)
  have hId : IdentityStoreKitPlacedOkI (EncryptLemmas.w1IdKitPlaced B F0 peer)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    KitInst.cliIdKitOkIE_cli_placed mmpl gh W (F0 := F0) (peer := peer) (readStk := B.readFile)
      (readProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
      hDropNz hh hRead
      (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _)
  have hq : (EncryptLemmas.w1SessKitPlaced B F0 peer).Quiet ∧
      (EncryptLemmas.w1IdKitPlaced B F0 peer).Quiet :=
    ⟨SessKit.cliSessionKitSpecPlaced_quiet, IdKit.cliIdentityKitSpecPlaced_quiet⟩
  have hraw := decryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli mmpl gh W
    (A := E2E.HooksE.A0) (ctl := 0#64) (S := E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩)
    (encRecord := E2E.Record.encodeRecord)
    (kit := EncryptLemmas.w1SessKitPlaced B F0 peer)
    (ikit := EncryptLemmas.w1IdKitPlaced B F0 peer)
    (st0 := StoresGhost.opened.sessions) (ist0 := StoresGhost.opened.identity)
    (Scope := Slots.scopeKit) (Q := fun _ => True)
    (DecHypsExtPlaced.of_cliHooks mmpl gh W hG hh.stringClone hSess hId
      (fun _ hr => Slots.scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        Slots.cliDecModelRecOkAt_opened
          (A := E2E.HooksE.A0) (b := 0#64) (pathOk := cliWrOk)
          (Scope₀ := Slots.scopeIn) (F0 := F0) (peer := peer)
          (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
          (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
          (fun _ h => h) hPeer x rec rec' pt haddr hsc hdec))
    hrec
    (fun _ _ ses hsc hcur => ⟨Slots.scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
    (KitFsOk.of_sound hq (hh.fs (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 463))
  refine subroutine_ok_mono hraw ?_ ?_
  · intro x R s0 hpre
    dsimp only [withEnvPre, DecryptLemmas.withStoresDecFrozenPlacedSpecVTP, withLsFrozen,
      DecryptLemmas.withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVTP,
      WithStoresVT.withStoresDecPlacedSpecVTP, WithStoresVT.withStoresDecPlacedSpecVTPF,
      Spec.restrictPre] at hpre ⊢
    generalize (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX
      W.C E2E.HooksE.A0 0#64 uuidTryParse (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord
      (EncryptLemmas.w1SessKitPlaced B F0 peer)
      (EncryptLemmas.w1IdKitPlaced B F0 peer)
      StoresGhost.opened.sessions StoresGhost.opened.identity
      Slots.scopeKit (fun _ _ => False)).pre x s0 = Bpre at hpre ⊢
    generalize SpqrV1.GF.Mul2U16.tokenInitPlacedAt = T at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  · intro x R s0 sf hpost
    dsimp only [withEnvPre, DecryptLemmas.withStoresDecFrozenPlacedSpecVTP, withLsFrozen,
      DecryptLemmas.withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVTP,
      WithStoresVT.withStoresDecPlacedSpecVTP, WithStoresVT.withStoresDecPlacedSpecVTPF,
      Spec.restrictPre] at hpost ⊢
    exact hpost

/-- Instantiates `InnerDecryptFrozenPlacedOk` on Block `463` under `[LibsignalFullPlacement]`,
discharging the `463 → 462` failure-log closure via `recordDecryptV1_full_placed_region_vregs_ok_PTight_cli`. -/
theorem w2_inner_full_placed_ok [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {B : RunBudgets}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    InnerDecryptFrozenPlacedOk mmpl gh W B :=
  w2_inner_frozen_placed_ok_of_region mmpl gh W hDropNz hG hh hRead
    (region_ok_restrictPre_true
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_full_placed_region_vregs_ok_PTight_cli
        mmpl gh W 0#64 hG hAesDec hSpqr))

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
