/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlaced
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Inner Store-Kit Transfer for `decrypt_signal`

Transfers `InnerDecryptPlacedOk` and `InnerDecryptFrozenPlacedOk` from Block `463`
(`signal_session_ratchet::decrypt_signal`) to any caller block `i < 619` under
`[LibsignalPlacement]` and `[LibsignalFullPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.CliRatchet.DecPlaced
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification

private theorem withStoresDecPlacedSpecVTP_rocl [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {P : State → Prop} {x : DecryptGhost} {R : SepProp} {s : State}
    (h : s.mem ⊨ (withEnvPre
      (withStoresDecPlacedSpecVTP C A ctl parse S encRecord kit ikit st0 ist0 Scope) P).pre x s ∗ R) :
    LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s.mem := by
  dsimp only [withEnvPre, withStoresDecPlacedSpecVTP,
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX,
    StoreKit.withLsCodeRoLoaded] at h
  have h1 : s.mem ⊨
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗
      (⌜P s⌝ ∗
        ⌜Slots.DistinctSid parse x.loc.name.bytes x.rem.name.bytes⌝ ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x4 = kit.ss_vt ∧ s.readReg64 .x6 = ikit.id_vt ∧
          s.readReg64 .x8 = x.ret ∧ wsStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt (s.readReg64 .x3) st0 ∗
        ikit.identityAt (s.readReg64 .x5) ist0 ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗
        CryptoVerification.Cli.CoinsTape.cliTapeAt ctl x.cur x.rest ∗
        FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗
        stackAt s.sp (wsStackV kit ikit) ∗ A.pool) ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) h
  rw [satisfies_pure_sepConj] at h1
  exact h1.1

/-- Transfers `InnerDecryptPlacedOk` from Block `463` (`lsProg_463`) to any caller block `i < 619`. -/
theorem w2_inner_placed_at_block [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (B : RunBudgets) (hInner463 : InnerDecryptPlacedOk mmpl gh W B)
    (hi : i < 619 := by decide)
    (F0 : FsFiles) (peer : AddrGhost) (hok : Slots.FilesOkPeer Slots.scopeIn F0 peer.val) :
    let kit := decSessKitPlaced F0 peer B
    let ikit := decIdKitPlaced F0 peer B
    subroutine_ok callerProg (lsmpl.base 463)
      (withEnvPre
        (withStoresDecPlacedSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord kit ikit
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro kit ikit
  have hsub := hInner463 F0 peer hok
  have hwrap := StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain (pl := lsmpl) hsub
  have htr := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    i 463 (cliGhostExterns gh (cliExternsPlaced mmpl W)) hcaller
    (CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsmpl.base 463) _ hwrap _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono htr (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · have hrocl := withStoresDecPlacedSpecVTP_rocl hpre
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hrocl, hpre⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

private theorem withStoresDecFrozenPlacedSpecVTP_frozen [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {P : State → Prop} {x : DecryptGhost} {R : SepProp} {s : State}
    (h : s.mem ⊨ (withEnvPre
      (withStoresDecFrozenPlacedSpecVTP C A ctl parse S encRecord kit ikit st0 ist0 Scope) P).pre x s ∗ R) :
    CryptoVerification.LibsignalFrozen lsmpl s.mem := by
  obtain ⟨_, hpre⟩ := withEnvPre_pre_elim h
  exact (LibsignalTripleRatchet.extract_withLsFrozen hpre).1

/-- Transfers `InnerDecryptFrozenPlacedOk` from Block `463` (`lsProg_463`) to any caller block
`i < 619` under `[LibsignalFullPlacement]`. -/
theorem w2_inner_full_placed_at_block [LibsignalFullPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (B : RunBudgets) (hInner463 : InnerDecryptFrozenPlacedOk mmpl gh W B)
    (F0 : FsFiles) (peer : AddrGhost) (hok : Slots.FilesOkPeer Slots.scopeIn F0 peer.val) :
    let kit := decSessKitPlaced F0 peer B
    let ikit := decIdKitPlaced F0 peer B
    subroutine_ok callerProg (lsmpl.base 463)
      (withEnvPre
        (withStoresDecFrozenPlacedSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord kit ikit
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro kit ikit
  have hsub := hInner463 F0 peer hok
  have hwrap :=
    LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.subroutine_ok_withLsFrozen_of_plain
      (pl := lsmpl) hsub
  have htr :=
    @LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
      _ _ callerProg (lsProg_463 (cliGhostExterns gh (cliExternsPlaced mmpl W))) i 463
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) hcaller
      (CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 463) _ hwrap (by decide)
  refine subroutine_ok_mono htr (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  have hfroz := withStoresDecFrozenPlacedSpecVTP_frozen hpre
  dsimp only [LibsignalTripleRatchet.withLsFrozen]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hfroz, hpre⟩

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
