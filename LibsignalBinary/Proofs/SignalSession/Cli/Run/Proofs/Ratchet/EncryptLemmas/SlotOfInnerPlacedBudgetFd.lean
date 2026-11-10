/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.PanicAndWire

/-!
# File-Descriptor-Guarded Outer Slot Reduction for `encrypt` (Placed)

Reduces `withPreGuard (fun s0 => FdsGe3Closed s0.fs) (encSlotSpecPlaced ...)` at `lsmpl.base 464`
(`signal_session_ratchet::encrypt`) to the `FdsGe3Closed`-guarded inner encrypt contract.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option warningAsError false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudgetFd

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (
  ApiError CiphertextMessage PreKeySignalMessage SessionRecord
  StoreAnswers StoreCall encryptFlat messageEncrypt_eq_flat
)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Record (RecordPqEmpty encodeRecord)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi (EncryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (
  WithStoresEncGhost nowAt withStoresEncStackV
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded SessionStoreSpec TraceFsSound
  withEnvPre withEnvPre_pre_intro withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal apiEncResultAt serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost UuidParser protocolAddressAt serviceIdParse uuidTryParse
)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (
  StoresGhost subroutine_ok_withFsInv
  withFsInv withFsInv_entry withFsInv_post_elim withFsInv_pre_intro
)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (
  loadPollNeed loadShimNeed storePollNeedX storeShimNeed
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliWrOk coinsInstalledPlaced storesAt
)
open CryptoVerification.SignalSession.Cli.RunCompose (
  EncGhost RunSem SlotAns encResAt idVtPlaced
  nowCellAt sessVtPlaced slotOut slotTrace unixEpoch
)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (
  apiEncResultAt_to_encResAt cliEncrypt_store_det
  cliSessLoadRel_eq_loadRec_scope cliTraceOfWith_eq_nil
  encOk₀_to_kitScopeAt mkCliStores model_panic_of_loadSession_eq
  model_preKey_serialized_lt preKeyMsg_inner_serialized_lt_of_mem
  scopeKit_of_sub sendPanics_imp_model_panic slotTrace_of_fsInv_trace_eq
  w1CliAnswers w1CliFinal w1EncDef w1EncGhost w1EncKey w1EncryptNeed
  w1IdKit w1SessKit w1UnusedDirsAt
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer coinsAtPlaced_eq_coinsInstalledPlaced
  encOk₀ loadRec scopeIn scopeKit sessLoadAns_loadRec
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux (
  toTempTwinsIkitEnv toTempTwinsKitEnv withStoresEncPlacedSpecV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  SpqrSendBudgetEnv WithStoresEncEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  encSlotSpecPlaced slotFramePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  CliEncryptSlotEnv kits_to_storesAt_placed storesAt_opened_to_kits_placed
  w1IdKitPlaced w1IdKitPlaced_idCallsRel_eq w1IdKitPlaced_idFinal_eq
  w1SessKitPlaced w1SessKitPlaced_callsRel_eq w1SessKitPlaced_storeFinal_eq
  w1_innerStack_le_need_placed withStoresEncPlacedSpecVT_cli withStoresEncPlacedSpecVT_cli_F0
)

private theorem loadSession_some_of_model_ok {C : Crypto} {S : SpqrModel} {uuidParse : UuidParser}
    {x : EncryptGhost} {answers : StoreAnswers (List (BitVec 8)) Unit} {cm : CiphertextMessage}
    (hok : (x.model C S uuidParse answers).1 = .ok cm) :
    ∃ r, answers.loadSession = .ok (some r) := by
  simp only [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat] at hok
  rcases hl : answers.loadSession with _ | (_ | r)
  · simp [hl] at hok
  · simp [hl] at hok
  · exact ⟨r, rfl⟩

private noncomputable def w1SlotAnsOfRc (F : FsFiles)
    (rc : Except (ApiError AddrVal Unit) CiphertextMessage ×
      List (StoreCall AddrVal (List (BitVec 8)))) : SlotAns CiphertextMessage :=
  match rc with
  | (.ok m, calls) => some (some (w1CliFinal F calls, m))
  | (.error .panic, _) => none
  | (.error _, _) => some none

private theorem w1EncDef_eq_slotAnsOfRc (P : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (g : EncryptGhost) (hnow : g.now = unixEpoch) :
    w1EncDef P Scope F g.rem.val g.loc.val g.ptext g.rest =
      w1SlotAnsOfRc F (g.model P.C (pqxdhSpqrModel P) uuidTryParse
        (w1CliAnswers Scope F g.rem.val (w1EncKey Scope F g.rem.val))) := by
  unfold w1EncDef w1SlotAnsOfRc EncryptGhost.model
  rw [hnow]
  generalize CryptoGames.LibsignalSessionApi.messageEncrypt P.C protoSignalCodec
    (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
    (w1CliAnswers Scope F g.rem.val (w1EncKey Scope F g.rem.val))
    g.ptext g.rem.val g.loc.val unixEpoch g.rest = rc
  rcases rc with ⟨err | _, _⟩
  · cases err <;> rfl
  · rfl

private theorem match_panic_eq_none (F : FsFiles)
    {rc : Except (ApiError AddrVal Unit) CiphertextMessage ×
      List (StoreCall AddrVal (List (BitVec 8)))}
    (h : rc.1 = .error .panic) :
    w1SlotAnsOfRc F rc = none := by
  rcases rc with ⟨res, _⟩
  dsimp only at h
  subst h
  rfl

private theorem slotOut_of_rc_eq {F : FsFiles} {ans : SlotAns CiphertextMessage}
    {rc : Except (ApiError AddrVal Unit) CiphertextMessage ×
      List (StoreCall AddrVal (List (BitVec 8)))}
    {s0 sf : State}
    (hans : ans = w1SlotAnsOfRc F rc)
    (hnoPanic : rc.1 ≠ .error .panic)
    (hnoStore : rc.1 ≠ .error (.store ()))
    (hwrOk : ∀ v, rc.1 = .ok v → ∀ pw ∈ (w1CliFinal F rc.2).writes, cliWrOk pw.1) :
    slotOut ans (w1CliFinal F rc.2) rc.1 s0 sf := by
  refine ⟨hnoPanic, hnoStore, ?_⟩
  rcases rc with ⟨err | v, calls⟩
  · dsimp only [w1SlotAnsOfRc] at hnoPanic hans ⊢
    cases err <;> first | exact hans | exact False.elim (hnoPanic rfl)
  · dsimp only [w1SlotAnsOfRc] at hans
    exact ⟨hans, hwrOk v rfl⟩

set_option maxHeartbeats 400000 in
/-- Reduces `withPreGuard (fun s0 => FdsGe3Closed s0.fs) (encSlotSpecPlaced ...)` on `callerProg`
to the inner encrypt contract carrying `FdsGe3Closed s.fs`. -/
theorem cliEncrypt_slot_of_inner_placed_pe_fd [LibsignalPlacement] {callerProg : Program}
    {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hfs : TraceFsSound callerProg)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = w1EncDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (hInner : ∀ (F : FsFiles) (peer : AddrGhost),
      FilesOkPeer Scope F peer.val →
      let kit := w1SessKitPlaced A.repAlloc B F peer
      let ikit := w1IdKitPlaced A.repAlloc B F peer
      subroutine_ok callerProg (lsmpl.base 464)
        (withEnvPre
          (withStoresEncPlacedSpecVT_cli A lim
            kit (kitEnv F peer) StoresGhost.opened.sessions
            ikit (ikitEnv F peer) StoresGhost.opened.identity
            scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) sendEnv encodeRecord)
          (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files ∧ FdsGe3Closed s.fs)))
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 464)
      (withPreGuard (fun s0 => FdsGe3Closed s0.fs)
        (encSlotSpecPlaced A lim (CliEncryptSlotEnv P A B sendEnv kitEnv ikitEnv) S stk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre0 hal _hL => ?_
  dsimp only [withPreGuard] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨hfds0, hpre⟩ := hpre0
  dsimp only [encSlotSpecPlaced, withLsCodeRoLoaded, slotFramePlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
    EncGhost.toSlotCtx] at hpre
  have hpre_flat : s0.mem ⊨
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.peerA ∧ s0.readReg64 .x3 = x.meA ∧
        s0.readReg64 .x4 = x.stores + 0xf0#64 ∧ s0.readReg64 .x5 = sessVtPlaced ∧
        s0.readReg64 .x6 = x.stores ∧ s0.readReg64 .x7 = idVtPlaced ∧
        s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        S.encOk x.F x.peer.val x.coins ∧ stk ≤ s0.sp.toNat ∧ x.meA ≠ 0#64 ∧
        FitsEnv M lim st (CliEncryptSlotEnv P A B sendEnv kitEnv ikitEnv x)⌝ ∗
      (⌜x.coins.length < 2 ^ 63⌝ ∗
      (storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsInstalledPlaced x.coinsP x.coins ∗
        tokenInitPlacedAt ∗
        lsLogOff ∗ A.pool lim st s0 ∗
        (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗
        memRegion x.ret 248 ∗ stackAt s0.sp stk ∗ R))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hfl, hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat
  obtain ⟨⟨hx0, hx1, hptLt, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfiles, hfOk, heOk,
    hsp_le, hme_ne, hfit⟩, hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hcoinsLt, hm0⟩ := hpre_flat
  obtain ⟨hokF, hokE⟩ := hok x.F x.peer.val x.me.val x.coins hfOk heOk

  set kit := w1SessKitPlaced A.repAlloc B x.F x.peer
  set ikit := w1IdKitPlaced A.repAlloc B x.F x.peer
  set innerStk := withStoresEncStackV kit ikit
  set extraStk := stk - innerStk
  have hinner_le : innerStk ≤ stk :=
    Nat.le_trans (w1_innerStack_le_need_placed A.repAlloc B x.F x.peer) hstk
  have hstk_sum : innerStk + extraStk = stk := by omega
  have hstk_split : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk := by
    rw [← hstk_sum]
    exact stackAt_split_bottom s0.sp innerStk extraStk (by omega)
  have hcoins_eq : coinsInstalledPlaced x.coinsP x.coins =
      cliTapeAt 0#64 x.coinsP x.coins :=
    (coinsAtPlaced_eq_coinsInstalledPlaced x.coinsP x.coins hcoinsLt).symm
  have hnow_eq : nowCellAt s0.sp unixEpoch = nowAt s0.sp unixEpoch := rfl
  have hssVt_eq : sessVtPlaced = kit.ss_vt := rfl
  have hidVt_eq : idVtPlaced = ikit.id_vt := rfl
  have hdisj : 64 ≤ x.coins.length ∨
      (∀ r, kit.ScopeAt scopeKit StoresGhost.opened.sessions x.peer.val r →
        RecordPqEmpty r) :=
    encOk₀_to_kitScopeAt (A := A.repAlloc) (b := 0#64)
      (s1 := loadShimNeed) (s2 := loadPollNeed B.readFile)
      (s3 := storeShimNeed) (s4 := storePollNeedX)
      hinjK hsub hokF hokE
  have hpure_in :
      FitsEnv M lim st
        (WithStoresEncEnv kit (toTempTwinsKitEnv (kitEnv x.F x.peer)) StoresGhost.opened.sessions
          ikit (toTempTwinsIkitEnv (ikitEnv x.F x.peer)) StoresGhost.opened.identity
          scopeKit P.C (pqxdhSpqrModel P) sendEnv uuidTryParse (w1EncGhost x)) ∧
      s0.readReg64 .x0 = (w1EncGhost x).ptA ∧
      (s0.readReg64 .x1).toNat = (w1EncGhost x).ptext.length ∧
      (w1EncGhost x).ptext.length < 2 ^ 32 ∧
      s0.readReg64 .x2 = (w1EncGhost x).remA ∧
      s0.readReg64 .x3 = (w1EncGhost x).locA ∧
      (w1EncGhost x).locA ≠ 0#64 ∧
      s0.readReg64 .x4 = (w1EncGhost x).ssA ∧
      s0.readReg64 .x5 = kit.ss_vt ∧
      s0.readReg64 .x6 = (w1EncGhost x).idA ∧
      s0.readReg64 .x7 = ikit.id_vt ∧
      (w1EncGhost x).now.tvNsec.toNat < 10 ^ 9 ∧
      s0.readReg64 .x8 = (w1EncGhost x).ret ∧
      innerStk ≤ s0.sp.toNat ∧
      kit.addrOk (w1EncGhost x).rem.val ∧
      ikit.addrOk (w1EncGhost x).rem.val := by
    refine ⟨hfit, hx0, hx1, hptLt, hx2, hx3, hme_ne, hx4, hssVt_eq ▸ hx5, hx6, hidVt_eq ▸ hx7,
      show unixEpoch.tvNsec.toNat < 10 ^ 9 by decide, hx8, by omega, rfl, rfl⟩

  let R_inner : SepProp :=
    w1UnusedDirsAt A.repAlloc x.stores StoresGhost.opened ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ R
  have hm_unpacked : s0.mem ⊨
      ((kit.storeAt (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        ikit.identityAt x.stores StoresGhost.opened.identity ∗
        w1UnusedDirsAt A.repAlloc x.stores StoresGhost.opened) ∗
      protocolAddressAt A.repAlloc x.peer x.peerA ∗
      protocolAddressAt A.repAlloc x.me x.meA ∗
      cliTapeAt 0#64 x.coinsP x.coins ∗
      tokenInitPlacedAt ∗
      lsLogOff ∗ A.pool lim st s0 ∗
      (x.ptA ↦ₛ x.ptext) ∗ nowAt s0.sp unixEpoch ∗
      memRegion x.ret 248 ∗
      (memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk) ∗ R) := by
    rw [hstk_split, hcoins_eq, hnow_eq] at hm0
    exact Satisfies.mono
      (sepConj_mono_left (storesAt_opened_to_kits_placed A.repAlloc B x.F x.peer x.stores hsub hokF))
      hm0
  have hpre_vt : s0.mem ⊨
      (withStoresEncPlacedSpecVT_cli A lim
        kit (kitEnv x.F x.peer) StoresGhost.opened.sessions
        ikit (ikitEnv x.F x.peer) StoresGhost.opened.identity
        scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) sendEnv encodeRecord).pre
        (w1EncGhost x, st) s0 ∗ R_inner := by
    dsimp only [withStoresEncPlacedSpecVT_cli, withStoresEncPlacedSpecVT_cli_F0,
      withStoresEncPlacedSpecV, withLsCodeRoLoaded, w1EncGhost]
    have hgoal : s0.mem ⊨
        ⌜64 ≤ x.coins.length ∨
          (∀ r, kit.ScopeAt scopeKit StoresGhost.opened.sessions x.peer.val r →
            RecordPqEmpty r)⌝ ∗
        (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜FitsEnv M lim st
            (WithStoresEncEnv kit (toTempTwinsKitEnv (kitEnv x.F x.peer))
              StoresGhost.opened.sessions
              ikit (toTempTwinsIkitEnv (ikitEnv x.F x.peer))
              StoresGhost.opened.identity
              scopeKit P.C (pqxdhSpqrModel P) sendEnv uuidTryParse (w1EncGhost x)) ∧
          s0.readReg64 .x0 = (w1EncGhost x).ptA ∧
          (s0.readReg64 .x1).toNat = (w1EncGhost x).ptext.length ∧
          (w1EncGhost x).ptext.length < 2 ^ 32 ∧
          s0.readReg64 .x2 = (w1EncGhost x).remA ∧
          s0.readReg64 .x3 = (w1EncGhost x).locA ∧
          (w1EncGhost x).locA ≠ 0#64 ∧
          s0.readReg64 .x4 = (w1EncGhost x).ssA ∧
          s0.readReg64 .x5 = kit.ss_vt ∧
          s0.readReg64 .x6 = (w1EncGhost x).idA ∧
          s0.readReg64 .x7 = ikit.id_vt ∧
          (w1EncGhost x).now.tvNsec.toNat < 10 ^ 9 ∧
          s0.readReg64 .x8 = (w1EncGhost x).ret ∧
          innerStk ≤ s0.sp.toNat ∧
          kit.addrOk (w1EncGhost x).rem.val ∧
          ikit.addrOk (w1EncGhost x).rem.val⌝ ∗
        (tokenInitPlacedAt ∗
          kit.storeAt (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
          ikit.identityAt x.stores StoresGhost.opened.identity ∗
          nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          memRegion x.ret 248 ∗
          cliTapeAt 0#64 x.coinsP x.coins ∗
          lsLogOff ∗ stackAt s0.sp innerStk ∗ A.pool lim st s0 ∗ R_inner))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hdisj, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hpure_in, ?_⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by dsimp only [R_inner]; sep_ac_rfl)) hm_unpacked
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  have hpre_env : s0.mem ⊨
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim
          kit (kitEnv x.F x.peer) StoresGhost.opened.sessions
          ikit (ikitEnv x.F x.peer) StoresGhost.opened.identity
          scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) sendEnv encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files ∧ FdsGe3Closed s.fs)).pre
        (w1EncGhost x, st) s0 ∗ R_inner :=
    withEnvPre_pre_intro ⟨hfiles, hfiles, hfds0⟩ hpre_vt
  have hpre_fs : s0.mem ⊨
      (withFsInv
        (withEnvPre
          (withStoresEncPlacedSpecVT_cli A lim
            kit (kitEnv x.F x.peer) StoresGhost.opened.sessions
            ikit (ikitEnv x.F x.peer) StoresGhost.opened.identity
            scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) sendEnv encodeRecord)
          (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files ∧ FdsGe3Closed s.fs))
        s0.fs.files s0.trace).pre (w1EncGhost x, st) s0 ∗ R_inner :=
    withFsInv_pre_intro (withFsInv_entry s0) hpre_env

  have hSub := subroutine_ok_withFsInv hfs (hInner x.F x.peer hokF) s0.fs.files s0.trace
  refine subroutine_ok.mono_outcome hSub (w1EncGhost x, st) R_inner s0 hpc hrun hpre_fs hal ?_
  intro sf hout
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hmpan⟩ | ⟨_c, _hex, hmex⟩ | ⟨_hoom, hmoom⟩
  ·
    refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hinv_f, hpost⟩ := withFsInv_post_elim hpost
    dsimp only [withEnvPre, withStoresEncPlacedSpecVT_cli, withStoresEncPlacedSpecVT_cli_F0,
      withStoresEncPlacedSpecV, withLsCodeRoLoaded] at hpost
    have hpost_ex : sf.mem ⊨
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit, ∃∗ evs : List AllocEvent,
          ⌜((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).1 ≠ .error .panic ∧
            kit.callsRel StoresGhost.opened.sessions answers
              ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2 ∧
            ikit.idCallsRel StoresGhost.opened.identity answers
              ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2 ∧
            sf.trace = s0.trace ++
              ikit.traceOfWith kit encodeRecord answers
                ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2 ∧
            CliEncryptSlotEnv P A B sendEnv kitEnv ikitEnv x evs⌝ ∗
          (tokenInitPlacedAt ∗
            kit.storeAt (x.stores + 0xf0#64)
              (kit.storeFinal StoresGhost.opened.sessions answers
                ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2) ∗
            ikit.identityAt x.stores
              (ikit.idFinal StoresGhost.opened.identity answers
                ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2) ∗
            apiEncResultAt A.repAlloc x.ret
              ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).1 ∗
            nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
            protocolAddressAt A.repAlloc x.peer x.peerA ∗
            protocolAddressAt A.repAlloc x.me x.meA ∗
            cliTapeAfter 0#64 x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel P) answers) ∗
            lsLogOff ∗ stackAt s0.sp innerStk ∗
            A.pool lim (M.stepEvents evs st) sf ∗ R_inner) := by
      have h1 : sf.mem ⊨
          (∃∗ answers : StoreAnswers (List (BitVec 8)) Unit, ∃∗ evs : List AllocEvent,
            ⌜((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).1 ≠ .error .panic ∧
              kit.callsRel StoresGhost.opened.sessions answers
                ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2 ∧
              ikit.idCallsRel StoresGhost.opened.identity answers
                ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2 ∧
              sf.trace = s0.trace ++
                ikit.traceOfWith kit encodeRecord answers
                  ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2 ∧
              WithStoresEncEnv kit (toTempTwinsKitEnv (kitEnv x.F x.peer))
                StoresGhost.opened.sessions
                ikit (toTempTwinsIkitEnv (ikitEnv x.F x.peer))
                StoresGhost.opened.identity
                scopeKit P.C (pqxdhSpqrModel P) sendEnv uuidTryParse
                (w1EncGhost x) evs⌝ ∗
            kit.storeAt (x.stores + 0xf0#64)
              (kit.storeFinal StoresGhost.opened.sessions answers
                ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2) ∗
            ikit.identityAt x.stores
              (ikit.idFinal StoresGhost.opened.identity answers
                ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2) ∗
            apiEncResultAt A.repAlloc x.ret
              ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).1 ∗
            nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
            protocolAddressAt A.repAlloc x.peer x.peerA ∗
            protocolAddressAt A.repAlloc x.me x.meA ∗
            cliTapeAfter 0#64 x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel P) answers) ∗
            lsLogOff ∗ stackAt s0.sp innerStk ∗
            A.pool lim (M.stepEvents evs st) sf) ∗
          (tokenInitPlacedAt ∗ R_inner) :=
        Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at h1
      obtain ⟨answers, h1⟩ := h1
      rw [sepExists_sepConj_left, satisfies_sepExists] at h1
      obtain ⟨evs, h1⟩ := h1
      rw [satisfies_sepExists]
      refine ⟨answers, ?_⟩
      rw [satisfies_sepExists]
      exact ⟨evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) h1⟩
    rw [satisfies_sepExists] at hpost_ex
    obtain ⟨answers, hpost_ex⟩ := hpost_ex
    rw [satisfies_sepExists] at hpost_ex
    obtain ⟨evs, hpost_ans⟩ := hpost_ex
    rw [satisfies_pure_sepConj] at hpost_ans
    obtain ⟨⟨hnoPanic, hcalls, hid, htr_raw, hev⟩, hm_f⟩ := hpost_ans
    let kit0 := w1SessKit B default x.F x.peer
    let ikit0 := w1IdKit B default x.F x.peer
    have htr_nil : ikit.traceOfWith kit encodeRecord answers
        ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2 = [] :=
      show ikit0.traceOfWith kit0 encodeRecord answers
        ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).2 = [] from
        cliTraceOfWith_eq_nil _ _ _
    have htr : sf.trace = s0.trace := by rw [htr_raw, htr_nil, List.append_nil]
    have hslotTr : slotTrace s0 sf := slotTrace_of_fsInv_trace_eq hinv_f htr
    have hcalls0 :=
      (w1SessKitPlaced_callsRel_eq A.repAlloc B x.F x.peer StoresGhost.opened.sessions answers _).mp
        hcalls
    have hid0 :=
      (w1IdKitPlaced_idCallsRel_eq A.repAlloc B x.F x.peer StoresGhost.opened.identity answers _).mp
        hid
    obtain ⟨hmodel_eq, hnoStore, hg'_eq, hwrOk⟩ :=
      cliEncrypt_store_det P (w1EncGhost x).toEncryptGhost answers hinjK hsub hokF hcalls0 hid0
    set resCalls := (w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers
    set e := resCalls.1
    set g' := w1CliFinal x.F resCalls.2
    have hg'_eq_kit : mkCliStores
        (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2)
        (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) = g' := by
      rw [show kit.storeFinal StoresGhost.opened.sessions answers resCalls.2 =
          kit0.storeFinal StoresGhost.opened.sessions answers resCalls.2 from
            w1SessKitPlaced_storeFinal_eq A.repAlloc B x.F x.peer
              StoresGhost.opened.sessions answers resCalls.2,
        show ikit.idFinal StoresGhost.opened.identity answers resCalls.2 =
          ikit0.idFinal StoresGhost.opened.identity answers resCalls.2 from
            w1IdKitPlaced_idFinal_eq A.repAlloc B x.F x.peer
              StoresGhost.opened.identity answers resCalls.2]
      exact hg'_eq
    have hmodel_symm : (w1EncGhost x).toEncryptGhost.model P.C (pqxdhSpqrModel P) uuidTryParse
        (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)) = resCalls :=
      hmodel_eq.symm
    have hS_eval : S.encrypt x.F x.peer.val x.me.val x.ptext x.coins =
        w1SlotAnsOfRc x.F resCalls :=
      (congrFun (congrFun (congrFun (congrFun (congrFun hS x.F) x.peer.val) x.me.val)
        x.ptext) x.coins).trans
        ((w1EncDef_eq_slotAnsOfRc P Scope x.F (w1EncGhost x).toEncryptGhost rfl).trans
          (congrArg (w1SlotAnsOfRc x.F) hmodel_symm))
    have hslotOut : slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf :=
      slotOut_of_rc_eq hS_eval hnoPanic hnoStore hwrOk
    have hwire42 : ∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
        m.serialized.length < 2 ^ 42 := by
      intro m hm_ok
      have hm_api : sf.mem ⊨ apiEncResultAt A.repAlloc x.ret (.ok (.preKeySignalMessage m)) ∗
          (tokenInitPlacedAt ∗
            kit.storeAt (x.stores + 0xf0#64)
              (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
            ikit.identityAt x.stores
              (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
            nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
            protocolAddressAt A.repAlloc x.peer x.peerA ∗
            protocolAddressAt A.repAlloc x.me x.meA ∗
            cliTapeAfter 0#64 x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel P) answers) ∗
            lsLogOff ∗ stackAt s0.sp innerStk ∗
            A.pool lim (M.stepEvents evs st) sf ∗ R_inner) := by
        have hm_f' := hm_f
        change sf.mem ⊨ (tokenInitPlacedAt ∗
          kit.storeAt (x.stores + 0xf0#64)
            (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
          ikit.identityAt x.stores
            (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
          apiEncResultAt A.repAlloc x.ret e ∗
          nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          cliTapeAfter 0#64 x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel P) answers) ∗
          lsLogOff ∗ stackAt s0.sp innerStk ∗
          A.pool lim (M.stepEvents evs st) sf ∗ R_inner) at hm_f'
        rw [hm_ok] at hm_f'
        exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm_f'
      have hmsg40 := preKeyMsg_inner_serialized_lt_of_mem hm_api
      set cliAns := w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)
      have hok_cli : ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse cliAns).1 =
          .ok (.preKeySignalMessage m) :=
        (congrArg Prod.fst hmodel_symm).trans hm_ok
      obtain ⟨r, hlr_cli⟩ := loadSession_some_of_model_ok hok_cli
      have hlr : loadRec Scope x.F x.peer.val = .ok (some r) := hlr_cli
      have hla := sessLoadAns_loadRec hokF
      rw [hlr] at hla
      obtain ⟨bs, hbs, _⟩ := hokF.sessGet
      rw [hbs] at hla
      have hr_sc : Scope r := by
        rcases bs with _ | ⟨_, _⟩
        · cases hla
        · obtain ⟨_, hans, _, hsc⟩ := hla
          cases hans
          exact hsc
      have hr_kit : scopeKit r := scopeKit_of_sub hsub r hr_sc
      exact model_preKey_serialized_lt P.C (pqxdhSpqrModel P) uuidTryParse
        (w1EncGhost x).toEncryptGhost cliAns r m hlr_cli
        (fun s k hs hk => (hr_kit.1.1 s hs).2.2 k hk) hok_cli hmsg40
    dsimp only [withPreGuard, encSlotSpecPlaced, withLsCodeRoLoaded]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨e, ?_⟩
    have hm_reord : sf.mem ⊨
        ((kit.storeAt (x.stores + 0xf0#64)
            (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
          ikit.identityAt x.stores
            (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
          w1UnusedDirsAt A.repAlloc x.stores StoresGhost.opened) ∗
        apiEncResultAt A.repAlloc x.ret e ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        (x.ptA ↦ₛ x.ptext) ∗ nowAt s0.sp unixEpoch ∗ lsLogOff ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk) ∗
        (tokenInitPlacedAt ∗
          cliTapeAfter 0#64 x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel P) answers)) ∗ R) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [R_inner]; sep_ac_rfl)) hm_f
    have hm_post : sf.mem ⊨
        (storesAt A.repAlloc x.stores g' ∗
          encResAt A.repAlloc x.ret e ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap ∗ R) := by
      rw [hstk_split, hnow_eq, ← hg'_eq_kit]
      refine Satisfies.mono ?_ hm_reord
      exact sepConj_mono (kits_to_storesAt_placed A.repAlloc B x.F x.peer x.stores _ _)
        (sepConj_mono (apiEncResultAt_to_encResAt A.repAlloc x.ret e hnoStore)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (entails_anyHeap _))))))))))
    have hgoal_post : sf.mem ⊨
        ⌜CliEncryptSlotEnv P A B sendEnv kitEnv ikitEnv x evs ∧
          slotTrace s0 sf ∧
          slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
          (∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
            m.serialized.length < 2 ^ 42)⌝ ∗
        (storesAt A.repAlloc x.stores g' ∗
          encResAt A.repAlloc x.ret e ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hev, hslotTr, hslotOut, hwire42⟩, hm_post⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal_post
  ·
    refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withFsInv, withEnvPre, withStoresEncPlacedSpecVT_cli,
      withStoresEncPlacedSpecVT_cli_F0, withStoresEncPlacedSpecV,
      withLsCodeRoLoaded] at hmpan
    simp only [sepConj_assoc] at hmpan
    rw [satisfies_pure_sepConj] at hmpan; obtain ⟨_, hmpan⟩ := hmpan
    rw [satisfies_pure_sepConj] at hmpan
    obtain ⟨⟨_, answers, hloadRel, _, hp_or⟩, hm_pan⟩ := hmpan
    have hpan_out : S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = none := by
      have hp_ans : ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).1 =
          .error .panic := by
        rcases hp_or with hp1 | hp2
        · exact hp1
        · exact sendPanics_imp_model_panic P.C (pqxdhSpqrModel P) uuidTryParse
            (w1EncGhost x).toEncryptGhost answers hp2
      have hloadRel0 : (w1SessKit B default x.F x.peer).loadRel StoresGhost.opened.sessions
          (w1EncGhost x).rem.val answers.loadSession := hloadRel
      have hload_eq : answers.loadSession =
          (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)).loadSession :=
        cliSessLoadRel_eq_loadRec_scope hinjK hsub hokF hloadRel0
      have hp_cli := model_panic_of_loadSession_eq P.C (pqxdhSpqrModel P) uuidTryParse
        (w1EncGhost x).toEncryptGhost answers
        (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)) hload_eq hp_ans
      exact (congrFun (congrFun (congrFun (congrFun (congrFun hS x.F) x.peer.val) x.me.val)
        x.ptext) x.coins).trans
        ((w1EncDef_eq_slotAnsOfRc P Scope x.F (w1EncGhost x).toEncryptGhost rfl).trans
          (match_panic_eq_none x.F hp_cli))
    dsimp only [withPreGuard, encSlotSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    dsimp only [R_inner] at hm_pan
    simp only [← sepConj_assoc] at hm_pan
    exact ⟨hpan_out, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
  ·
    dsimp only [withFsInv, withEnvPre, withStoresEncPlacedSpecVT_cli,
      withStoresEncPlacedSpecVT_cli_F0, withStoresEncPlacedSpecV,
      withLsCodeRoLoaded] at hmex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmex
    have hmex2 := hmex.2
    rw [satisfies_pure_sepConj] at hmex2
    exact False.elim hmex2.1
  ·
    dsimp only [withFsInv, withEnvPre, withStoresEncPlacedSpecVT_cli,
      withStoresEncPlacedSpecVT_cli_F0, withStoresEncPlacedSpecV,
      withLsCodeRoLoaded] at hmoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmoom
    have hmoom2 := hmoom.2
    rw [satisfies_pure_sepConj] at hmoom2
    exact False.elim hmoom2.1

theorem cliEncrypt_slot_of_inner_placed_fd [LibsignalPlacement] {callerProg : Program}
    {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hfs : TraceFsSound callerProg)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = w1EncDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (hInner : ∀ (F : FsFiles) (peer : AddrGhost),
      FilesOkPeer Scope F peer.val →
      let kit := w1SessKitPlaced A.repAlloc B F peer
      let ikit := w1IdKitPlaced A.repAlloc B F peer
      subroutine_ok callerProg (lsmpl.base 464)
        (withEnvPre
          (withStoresEncPlacedSpecVT_cli A lim
            kit (kitEnv F peer) StoresGhost.opened.sessions
            ikit (ikitEnv F peer) StoresGhost.opened.identity
            scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) sendEnv encodeRecord)
          (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files ∧ FdsGe3Closed s.fs)))
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 464)
      (withPreGuard (fun s0 => FdsGe3Closed s0.fs)
        (encSlotSpecPlaced A lim (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv kitEnv ikitEnv) S stk)) :=
  cliEncrypt_slot_of_inner_placed_pe_fd ⟨W.C, W.Q⟩ A lim B S Scope sendEnv kitEnv ikitEnv
    hfs hinjK hsub hS hok hInner stk hstk hstk64

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudgetFd
