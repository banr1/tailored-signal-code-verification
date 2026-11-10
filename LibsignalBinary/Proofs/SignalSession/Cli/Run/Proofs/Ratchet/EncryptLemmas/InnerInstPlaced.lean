/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Inner Contract Transfer and Slot Proof for `encrypt`

Defines `W1InnerPlacedOk` on Block `464` (`signal_session_ratchet::encrypt`), transfers it to any
caller block `i < 619`, and establishes `cliEncrypt_slot_placed` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification

/-- Relocatable Block-`464` inner `withStoresEncPlacedSpecVT_cli` contract for `w1SessKitPlaced` and `w1IdKitPlaced`. -/
def W1InnerPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (F : FsFiles) (peer : AddrGhost),
    Slots.FilesOkPeer Scope F peer.val →
    subroutine_ok (lsProg_464 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli
          (w1SessKitPlaced B F peer) StoresGhost.opened.sessions
          (w1IdKitPlaced B F peer) StoresGhost.opened.identity Slots.scopeKit
          W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
        (fun s => (w1SessKitPlaced B F peer).envOk s.fs.files ∧
          (w1IdKitPlaced B F peer).envOk s.fs.files))

private theorem withStoresEncPlacedSpecVT_cli_rocl [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {P : State → Prop} {x : WithStoresEncGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli kit st0 ikit ist0 Scope C ctl uuidParse S encRecord)
        P).pre x s0 ∗ R) :
    LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem := by
  dsimp only [withEnvPre, withStoresEncPlacedSpecVT_cli,
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpre
  have h1 : s0.mem ⊨
      ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜P s0⌝ ∗
        ⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
          s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
        CryptoVerification.Cli.CoinsTape.cliTapeAt ctl x.cur x.rest ∗
        FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool) ∗ R) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at h1
  exact h1.1

/-- Transfers `W1InnerPlacedOk` from Block `464` (`lsProg_464`) to any caller block `i < 619`. -/
theorem w1_inner_placed_at_block [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (B : RunBudgets) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hInner464 : W1InnerPlacedOk mmpl gh W B Scope)
    (hi : i < 619 := by decide)
    (F : FsFiles) (peer : AddrGhost) (hok : Slots.FilesOkPeer Scope F peer.val) :
    subroutine_ok callerProg (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli
          (w1SessKitPlaced B F peer) StoresGhost.opened.sessions
          (w1IdKitPlaced B F peer) StoresGhost.opened.identity Slots.scopeKit
          W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
        (fun s => (w1SessKitPlaced B F peer).envOk s.fs.files ∧
          (w1IdKitPlaced B F peer).envOk s.fs.files)) := by
  have hsub := hInner464 F peer hok
  have hwrap := LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain (pl := lsmpl) hsub
  have htr := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    (lsProg_464 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    i 464 (cliGhostExterns gh (cliExternsPlaced mmpl W)) hcaller
    (CryptoVerification.CliRatchet.EncPlaced.instIsLsBlockProg_464
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsmpl.base 464) _ hwrap _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono htr (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · have hrocl := withStoresEncPlacedSpecVT_cli_rocl hpre
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hrocl, hpre⟩
  · dsimp only [withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

/-- Establishes `encSlotSpecPlaced` for `signal_session_ratchet::encrypt` on any caller block
`i < 619` under `[LibsignalPlacement]`. -/
theorem cliEncrypt_slot_placed [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hfs : TraceFsSound callerProg)
    (hInner464 : W1InnerPlacedOk mmpl gh W B Scope)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = w1EncDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 464)
      (encSlotSpecPlaced E2E.HooksE.A0 S stk) :=
  cliEncrypt_slot_of_inner_placed W B S Scope hfs hinjK hsub hS hok
    (w1_inner_placed_at_block mmpl gh W B Scope hInner464 hi) stk hstk hstk64

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
