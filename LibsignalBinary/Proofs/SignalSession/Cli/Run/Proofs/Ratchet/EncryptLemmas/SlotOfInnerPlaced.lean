/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridgePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInner
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.PanicAndWire

/-!
# Relocatable Outer Slot Reduction for `encrypt`

Defines `withStoresEncPlacedSpecVT_cli` and reduces `encSlotSpecPlaced` at `lsmpl.base 464`
(`signal_session_ratchet::encrypt`) to the placed inner encrypt contract under
`[LibsignalPlacement]`.
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
open CryptoVerification

/-! ## Relocatable inner encrypt specification -/

def withStoresEncPlacedSpecVT_cli [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec WithStoresEncGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV
      kit st0 ikit ist0 C ctl uuidParse S encRecord with
    pre := fun x s =>
      ⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).pre x s
    post := fun x s0 sf =>
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf }

/-! ## Outer `encSlotSpecPlaced` reduction -/

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

private theorem w1EncDef_eq_slotAnsOfRc (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (g : CryptoVerification.LibsignalPublicApi.EncryptGhost) (hnow : g.now = unixEpoch) :
    w1EncDef W Scope F g.rem.val g.loc.val g.ptext g.rest =
      w1SlotAnsOfRc F (g.model W.C (pqxdhSpqrModel W) uuidTryParse
        (w1CliAnswers Scope F g.rem.val (w1EncKey Scope F g.rem.val))) := by
  unfold w1EncDef w1SlotAnsOfRc CryptoVerification.LibsignalPublicApi.EncryptGhost.model
  rw [hnow]
  generalize LibsignalSessionApi.messageEncrypt W.C protoSignalCodec (pqxdhSpqrModel W).spqr
    (serializeAddrVals (serviceIdParse uuidTryParse))
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
/-- Reduces `encSlotSpecPlaced` at `lsmpl.base 464` on `callerProg` to the placed inner `withStoresEncPlacedSpecVT_cli` contract. -/
theorem cliEncrypt_slot_of_inner_placed [LibsignalPlacement] {callerProg : Program}
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hfs : TraceFsSound callerProg)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = w1EncDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hInner : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      subroutine_ok callerProg (lsmpl.base 464)
        (withEnvPre
          (withStoresEncPlacedSpecVT_cli (w1SessKitPlaced B F peer) StoresGhost.opened.sessions
            (w1IdKitPlaced B F peer) StoresGhost.opened.identity Slots.scopeKit
            W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
          (fun s => (w1SessKitPlaced B F peer).envOk s.fs.files ∧
            (w1IdKitPlaced B F peer).envOk s.fs.files)))
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 464)
      (encSlotSpecPlaced E2E.HooksE.A0 S stk) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal _hL => ?_
  dsimp only [encSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, slotFramePlaced] at hpre
  have hpre_flat : s0.mem ⊨
      ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.peerA ∧ s0.readReg64 .x3 = x.meA ∧
        s0.readReg64 .x4 = x.stores + 0xf0#64 ∧ s0.readReg64 .x5 = sessVtPlaced ∧
        s0.readReg64 .x6 = x.stores ∧ s0.readReg64 .x7 = idVtPlaced ∧
        s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        S.encOk x.F x.peer.val x.coins ∧ stk ≤ s0.sp.toNat ∧ x.meA ≠ 0#64⌝ ∗
      (⌜x.coins.length < 2 ^ 63⌝ ∗
      (storesAt E2E.HooksE.A0 x.stores StoresGhost.opened ∗
        protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
        protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
        coinsInstalledPlaced x.coinsP x.coins ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
        (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗
        memRegion x.ret 248 ∗ stackAt s0.sp stk ∗ R))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hfl, hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat
  obtain ⟨⟨hx0, hx1, hptLt, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfiles, hfOk, heOk, hsp_le, hme_ne⟩,
    hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hcoinsLt, hm0⟩ := hpre_flat
  obtain ⟨hokF, hokE⟩ := hok x.F x.peer.val x.me.val x.coins hfOk heOk

  set kit := w1SessKitPlaced B x.F x.peer
  set ikit := w1IdKitPlaced B x.F x.peer
  set innerStk := withStoresEncStackV kit ikit
  set extraStk := stk - innerStk
  have hinner_le : innerStk ≤ stk := Nat.le_trans (w1_innerStack_le_need_placed B x.F x.peer) hstk
  have hstk_sum : innerStk + extraStk = stk := by omega
  have hstk_split : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk := by
    rw [← hstk_sum]
    exact stackAt_split_bottom s0.sp innerStk extraStk (by omega)
  have hcoins_eq : coinsInstalledPlaced x.coinsP x.coins =
      CryptoVerification.Cli.CoinsTape.cliTapeAt 0#64 x.coinsP x.coins :=
    (Slots.coinsAtPlaced_eq_coinsInstalledPlaced x.coinsP x.coins hcoinsLt).symm
  have hnow_eq : nowCellAt s0.sp unixEpoch = nowAt s0.sp unixEpoch := rfl
  have hssVt_eq : sessVtPlaced = kit.ss_vt := rfl
  have hidVt_eq : idVtPlaced = ikit.id_vt := rfl
  have hdisj : 64 ≤ x.coins.length ∨
      (∀ r, kit.ScopeAt Slots.scopeKit StoresGhost.opened.sessions x.peer.val r →
        E2E.Record.RecordPqEmpty r) :=
    encOk₀_to_kitScopeAt (A := E2E.HooksE.A0) (b := 0#64)
      (s1 := SessKit.loadShimNeed) (s2 := SessKit.loadPollNeed B.readFile)
      (s3 := SessKit.storeShimNeed) (s4 := SessKit.storePollNeedX)
      hinjK hsub hokF hokE
  have hpure_in :
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
    refine ⟨hx0, hx1, hptLt, hx2, hx3, hme_ne, hx4, hssVt_eq ▸ hx5, hx6, hidVt_eq ▸ hx7,
      show unixEpoch.tvNsec.toNat < 10 ^ 9 by decide, hx8, by omega, rfl, rfl⟩

  let R_inner : SepProp :=
    w1UnusedDirsAt E2E.HooksE.A0 x.stores StoresGhost.opened ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ R
  have hm_unpacked : s0.mem ⊨
      ((kit.storeAt (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        ikit.identityAt x.stores StoresGhost.opened.identity ∗
        w1UnusedDirsAt E2E.HooksE.A0 x.stores StoresGhost.opened) ∗
      protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
      protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
      CryptoVerification.Cli.CoinsTape.cliTapeAt 0#64 x.coinsP x.coins ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
      (x.ptA ↦ₛ x.ptext) ∗ nowAt s0.sp unixEpoch ∗
      memRegion x.ret 248 ∗
      (memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk) ∗ R) := by
    rw [hstk_split, hcoins_eq, hnow_eq] at hm0
    exact Satisfies.mono
      (sepConj_mono_left (storesAt_opened_to_kits_placed B x.F x.peer x.stores hsub hokF)) hm0
  have hpre_vt : s0.mem ⊨
      (withStoresEncPlacedSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
        Slots.scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩)
        E2E.Record.encodeRecord).pre (w1EncGhost x) s0 ∗ R_inner := by
    dsimp only [withStoresEncPlacedSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, w1EncGhost]
    have hgoal : s0.mem ⊨
        ⌜64 ≤ x.coins.length ∨
          (∀ r, kit.ScopeAt Slots.scopeKit StoresGhost.opened.sessions x.peer.val r →
            E2E.Record.RecordPqEmpty r)⌝ ∗
        (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = (w1EncGhost x).ptA ∧
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
        (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          kit.storeAt (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
          ikit.identityAt x.stores StoresGhost.opened.identity ∗
          nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          memRegion x.ret 248 ∗
          CryptoVerification.Cli.CoinsTape.cliTapeAt 0#64 x.coinsP x.coins ∗
          FromRecordCallees.lsLogOff ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool ∗ R_inner))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hdisj, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hpure_in, ?_⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by dsimp only [R_inner]; ac_rfl)) hm_unpacked
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hgoal
  have hpre_env : s0.mem ⊨
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
          Slots.scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)).pre (w1EncGhost x) s0 ∗ R_inner :=
    withEnvPre_pre_intro ⟨hfiles, hfiles⟩ hpre_vt
  have hpre_fs : s0.mem ⊨
      (withFsInv
        (withEnvPre
          (withStoresEncPlacedSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
            Slots.scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
          (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
        s0.fs.files s0.trace).pre (w1EncGhost x) s0 ∗ R_inner :=
    withFsInv_pre_intro (withFsInv_entry s0) hpre_env

  have hSub := subroutine_ok_withFsInv hfs (hInner x.F x.peer hokF) s0.fs.files s0.trace
  refine subroutine_ok.mono_outcome hSub (w1EncGhost x) R_inner s0 hpc hrun hpre_fs hal ?_
  intro sf hout
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hmpan⟩ | ⟨_c, _hex, hmex⟩ | ⟨_hoom, hmoom⟩
  ·
    refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hinv_f, hpost⟩ := withFsInv_post_elim hpost
    dsimp only [withEnvPre, withStoresEncPlacedSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    have hpost_ex : sf.mem ⊨
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).1 ≠ .error .panic ∧
            kit.callsRel StoresGhost.opened.sessions answers
              ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2 ∧
            ikit.idCallsRel StoresGhost.opened.identity answers
              ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2 ∧
            sf.trace = s0.trace ++
              ikit.traceOfWith kit E2E.Record.encodeRecord answers
                ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2⌝ ∗
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
            kit.storeAt (x.stores + 0xf0#64)
              (kit.storeFinal StoresGhost.opened.sessions answers
                ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2) ∗
            ikit.identityAt x.stores
              (ikit.idFinal StoresGhost.opened.identity answers
                ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2) ∗
            apiEncResultAt E2E.HooksE.A0 x.ret
              ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).1 ∗
            nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
            protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
            protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
            CryptoVerification.Cli.CoinsTape.cliTapeAfter 0#64 x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers) ∗
            FromRecordCallees.lsLogOff ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool ∗ R_inner) := by
      have h1 : sf.mem ⊨
          (∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
            ⌜((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).1 ≠ .error .panic ∧
              kit.callsRel StoresGhost.opened.sessions answers
                ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2 ∧
              ikit.idCallsRel StoresGhost.opened.identity answers
                ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2 ∧
              sf.trace = s0.trace ++
                ikit.traceOfWith kit E2E.Record.encodeRecord answers
                  ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2⌝ ∗
            kit.storeAt (x.stores + 0xf0#64)
              (kit.storeFinal StoresGhost.opened.sessions answers
                ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2) ∗
            ikit.identityAt x.stores
              (ikit.idFinal StoresGhost.opened.identity answers
                ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2) ∗
            apiEncResultAt E2E.HooksE.A0 x.ret
              ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).1 ∗
            nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
            protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
            protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
            CryptoVerification.Cli.CoinsTape.cliTapeAfter 0#64 x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers) ∗
            FromRecordCallees.lsLogOff ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool) ∗
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R_inner) :=
        Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at h1
      obtain ⟨answers, h1⟩ := h1
      rw [satisfies_sepExists]
      exact ⟨answers, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) h1⟩
    rw [satisfies_sepExists] at hpost_ex
    obtain ⟨answers, hpost_ans⟩ := hpost_ex
    rw [satisfies_pure_sepConj] at hpost_ans
    obtain ⟨⟨hnoPanic, hcalls, hid, htr_raw⟩, hm_f⟩ := hpost_ans
    let kit0 := w1SessKit B default x.F x.peer
    let ikit0 := w1IdKit B default x.F x.peer
    have htr_nil : ikit.traceOfWith kit E2E.Record.encodeRecord answers
        ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2 = [] :=
      show ikit0.traceOfWith kit0 E2E.Record.encodeRecord answers
        ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2 = [] from
        cliTraceOfWith_eq_nil _ _ _
    have htr : sf.trace = s0.trace := by rw [htr_raw, htr_nil, List.append_nil]
    have hslotTr : slotTrace s0 sf := slotTrace_of_fsInv_trace_eq hinv_f htr
    have hcalls0 := (w1SessKitPlaced_callsRel_eq B x.F x.peer StoresGhost.opened.sessions answers _).mp hcalls
    have hid0 := (w1IdKitPlaced_idCallsRel_eq B x.F x.peer StoresGhost.opened.identity answers _).mp hid
    obtain ⟨hmodel_eq, hnoStore, hg'_eq, hwrOk⟩ :=
      cliEncrypt_store_det ⟨W.C, W.Q⟩ (w1EncGhost x).toEncryptGhost answers hinjK hsub hokF hcalls0 hid0
    set resCalls := (w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers
    set e := resCalls.1
    set g' := w1CliFinal x.F resCalls.2
    have hg'_eq_kit : mkCliStores
        (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2)
        (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) = g' := by
      rw [show kit.storeFinal StoresGhost.opened.sessions answers resCalls.2 =
          kit0.storeFinal StoresGhost.opened.sessions answers resCalls.2 from
            w1SessKitPlaced_storeFinal_eq B x.F x.peer StoresGhost.opened.sessions answers resCalls.2,
        show ikit.idFinal StoresGhost.opened.identity answers resCalls.2 =
          ikit0.idFinal StoresGhost.opened.identity answers resCalls.2 from
            w1IdKitPlaced_idFinal_eq B x.F x.peer StoresGhost.opened.identity answers resCalls.2]
      exact hg'_eq
    have hmodel_symm : (w1EncGhost x).toEncryptGhost.model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse
        (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)) = resCalls :=
      hmodel_eq.symm
    have hS_eval : S.encrypt x.F x.peer.val x.me.val x.ptext x.coins =
        w1SlotAnsOfRc x.F resCalls :=
      (congrFun (congrFun (congrFun (congrFun (congrFun hS x.F) x.peer.val) x.me.val)
        x.ptext) x.coins).trans
        ((w1EncDef_eq_slotAnsOfRc ⟨W.C, W.Q⟩ Scope x.F (w1EncGhost x).toEncryptGhost rfl).trans
          (congrArg (w1SlotAnsOfRc x.F) hmodel_symm))
    have hslotOut : slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf :=
      slotOut_of_rc_eq hS_eval hnoPanic hnoStore hwrOk
    have hwire42 : ∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
        m.serialized.length < 2 ^ 42 := by
      intro m hm_ok
      have hm_api : sf.mem ⊨ apiEncResultAt E2E.HooksE.A0 x.ret (.ok (.preKeySignalMessage m)) ∗
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
            kit.storeAt (x.stores + 0xf0#64)
              (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
            ikit.identityAt x.stores
              (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
            nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
            protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
            protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
            CryptoVerification.Cli.CoinsTape.cliTapeAfter 0#64 x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers) ∗
            FromRecordCallees.lsLogOff ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool ∗ R_inner) := by
        have hm_f' := hm_f
        change sf.mem ⊨ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          kit.storeAt (x.stores + 0xf0#64)
            (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
          ikit.identityAt x.stores
            (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
          apiEncResultAt E2E.HooksE.A0 x.ret e ∗
          nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          CryptoVerification.Cli.CoinsTape.cliTapeAfter 0#64 x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers) ∗
          FromRecordCallees.lsLogOff ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool ∗ R_inner) at hm_f'
        rw [hm_ok] at hm_f'
        exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm_f'
      have hmsg40 := preKeyMsg_inner_serialized_lt_of_mem hm_api
      set cliAns := w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)
      have hok_cli : ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse cliAns).1 =
          .ok (.preKeySignalMessage m) :=
        (congrArg Prod.fst hmodel_symm).trans hm_ok
      obtain ⟨r, hlr_cli⟩ := loadSession_some_of_model_ok hok_cli
      have hlr : Slots.loadRec Scope x.F x.peer.val = .ok (some r) := hlr_cli
      have hla := Slots.sessLoadAns_loadRec hokF
      rw [hlr] at hla
      obtain ⟨bs, hbs, _⟩ := hokF.sessGet
      rw [hbs] at hla
      have hr_sc : Scope r := by
        rcases bs with _ | ⟨_, _⟩
        · cases hla
        · obtain ⟨_, hans, _, hsc⟩ := hla
          cases hans
          exact hsc
      have hr_kit : Slots.scopeKit r := scopeKit_of_sub hsub r hr_sc
      exact model_preKey_serialized_lt W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse
        (w1EncGhost x).toEncryptGhost cliAns r m hlr_cli
        (fun s k hs hk => (hr_kit.1.1 s hs).2.2 k hk) hok_cli hmsg40
    dsimp only [encSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨e, ?_⟩
    have hm_reord : sf.mem ⊨
        ((kit.storeAt (x.stores + 0xf0#64)
            (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
          ikit.identityAt x.stores
            (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
          w1UnusedDirsAt E2E.HooksE.A0 x.stores StoresGhost.opened) ∗
        apiEncResultAt E2E.HooksE.A0 x.ret e ∗
        protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
        protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
        (x.ptA ↦ₛ x.ptext) ∗ nowAt s0.sp unixEpoch ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk) ∗
        (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          CryptoVerification.Cli.CoinsTape.cliTapeAfter 0#64 x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers)) ∗ R) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [R_inner]; ac_rfl)) hm_f
    have hm_post : sf.mem ⊨
        (storesAt E2E.HooksE.A0 x.stores g' ∗
          encResAt E2E.HooksE.A0 x.ret e ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp stk ∗ anyHeap ∗ R) := by
      rw [hstk_split, hnow_eq, ← hg'_eq_kit]
      refine Satisfies.mono ?_ hm_reord
      exact sepConj_mono (kits_to_storesAt_placed B x.F x.peer x.stores _ _)
        (sepConj_mono (apiEncResultAt_to_encResAt E2E.HooksE.A0 x.ret e hnoStore)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (entails_anyHeap _))))))))))
    have hgoal_post : sf.mem ⊨
        ⌜slotTrace s0 sf ∧
          slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
          (∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
            m.serialized.length < 2 ^ 42)⌝ ∗
        (storesAt E2E.HooksE.A0 x.stores g' ∗
          encResAt E2E.HooksE.A0 x.ret e ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp stk ∗ anyHeap ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hslotTr, hslotOut, hwire42⟩, hm_post⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal_post
  ·
    refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withFsInv, withEnvPre, withStoresEncPlacedSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hmpan
    simp only [sepConj_assoc] at hmpan
    rw [satisfies_pure_sepConj] at hmpan; obtain ⟨_, hmpan⟩ := hmpan
    rw [satisfies_pure_sepConj] at hmpan; obtain ⟨⟨_, hpan_or⟩, hm_pan⟩ := hmpan
    have hpan_out : S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = none ∨
        allocFailedIn s0 sf := by
      rcases hpan_or with halloc | ⟨answers, hloadRel, _, hp_or⟩
      · exact Or.inr halloc
      · refine Or.inl ?_
        have hp_ans : ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).1 =
            .error .panic := by
          rcases hp_or with hp1 | hp2
          · exact hp1
          · exact sendPanics_imp_model_panic W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse
              (w1EncGhost x).toEncryptGhost answers hp2
        have hloadRel0 : (w1SessKit B default x.F x.peer).loadRel StoresGhost.opened.sessions
            (w1EncGhost x).rem.val answers.loadSession := hloadRel
        have hload_eq : answers.loadSession =
            (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)).loadSession :=
          cliSessLoadRel_eq_loadRec_scope hinjK hsub hokF hloadRel0
        have hp_cli := model_panic_of_loadSession_eq W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse
          (w1EncGhost x).toEncryptGhost answers
          (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)) hload_eq hp_ans
        exact (congrFun (congrFun (congrFun (congrFun (congrFun hS x.F) x.peer.val) x.me.val)
          x.ptext) x.coins).trans
          ((w1EncDef_eq_slotAnsOfRc ⟨W.C, W.Q⟩ Scope x.F (w1EncGhost x).toEncryptGhost rfl).trans
            (match_panic_eq_none x.F hp_cli))
    dsimp only [encSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    dsimp only [R_inner] at hm_pan
    simp only [← sepConj_assoc] at hm_pan
    exact ⟨hpan_out, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
  ·
    dsimp only [withFsInv, withEnvPre, withStoresEncPlacedSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hmex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmex
    have hmex2 := hmex.2
    rw [satisfies_pure_sepConj] at hmex2
    exact False.elim hmex2.1
  ·
    dsimp only [withFsInv, withEnvPre, withStoresEncPlacedSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hmoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmoom
    have hmoom2 := hmoom.2
    rw [satisfies_pure_sepConj] at hmoom2
    exact False.elim hmoom2.1

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
