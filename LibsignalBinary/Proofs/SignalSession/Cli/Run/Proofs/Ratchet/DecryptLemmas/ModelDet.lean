/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Spec

/-!
# Store Determinism and Panic Equivalence for `decrypt_signal`

Establishes initial session and identity store invariants from `FilesOkPeer`, scope invariance of
`Slots.loadRec`, a closed-form equation and panic characterization for `messageDecryptSignal`, and
full determinism of `DecryptGhost.model` (`decModel_det`) under the CLI store kits.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

theorem sessFileWf_mono {S1 S2 : SessionRecord (List (BitVec 8)) → Prop}
    (hsub : ∀ r, S1 r → S2 r) {bs : List (BitVec 8)} (h : SessFileWf S1 bs) :
    SessFileWf S2 bs := by
  rcases h with rfl | ⟨r, rfl, hr⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨r, rfl, hsub r hr⟩

theorem filesOkPeer_mono {S1 S2 : SessionRecord (List (BitVec 8)) → Prop}
    (hsub : ∀ r, S1 r → S2 r) {F : FsFiles} {peer : AddrVal}
    (h : Slots.FilesOkPeer S1 F peer) :
    Slots.FilesOkPeer S2 F peer where
  nameLt := h.nameLt
  textLt := h.textLt
  sessPathOk := h.sessPathOk
  idPathOk := h.idPathOk
  sessPathLt := h.sessPathLt
  idPathLt := h.idPathLt
  sessGet := let ⟨bs, hget, hwf⟩ := h.sessGet; ⟨bs, hget, sessFileWf_mono hsub hwf⟩
  idGet := h.idGet

theorem cliSessInv_opened_wrOk {Scope S2 : SessionRecord (List (BitVec 8)) → Prop}
    (hsub : ∀ r, Scope r → S2 r) {F : FsFiles} {peer : AddrGhost}
    (h : Slots.FilesOkPeer Scope F peer.val) :
    CliSessInv cliIo.rd F cliWrOk S2 peer StoresGhost.opened.sessions := by
  have h0 := Slots.cliSessInv_opened h
  refine ⟨h0.nameLt, h0.textLt, h0.pathLt, ⟨h.sessPathOk, h.sessPathLt⟩, ?_, h0.changedLt⟩
  obtain ⟨bs, hget, hwf⟩ := h0.getOk
  exact ⟨bs, hget, sessFileWf_mono hsub hwf⟩

theorem cliIdInv_opened_wrOk {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} (h : Slots.FilesOkPeer Scope F peer.val) :
    CliIdInv cliIo.rd F cliWrOk peer StoresGhost.opened.identity := by
  have h0 := Slots.cliIdInv_opened h
  exact ⟨h0.nameLt, h0.pathLt, ⟨h.idPathOk, h.idPathLt⟩, h0.getOk, h0.changedLt⟩

/-- Scope invariance of `Slots.loadRec` under `FilesOkPeer Scope F peer`, `Scope ⊆ S2`, and `EncodeInjOn S2`. -/
theorem loadRec_eq_of_sub {Scope S2 : SessionRecord (List (BitVec 8)) → Prop}
    (hsub : ∀ r, Scope r → S2 r) (hinj2 : Slots.EncodeInjOn S2)
    {F : FsFiles} {peer : AddrVal} (hok : Slots.FilesOkPeer Scope F peer) :
    Slots.loadRec S2 F peer = Slots.loadRec Scope F peer := by
  have hans1 : SessLoadAns Scope (StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer))
      (Slots.loadRec Scope F peer) :=
    Slots.sessLoadAns_loadRec hok
  have hans2 : SessLoadAns S2 (StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer))
      (Slots.loadRec Scope F peer) := by
    rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with _ | bs
    · rw [hget] at hans1; exact hans1
    · cases bs with
      | nil => rw [hget] at hans1; exact hans1
      | cons b bs' =>
        rw [hget] at hans1
        obtain ⟨r, hr, henc, hsc⟩ := hans1
        exact ⟨r, hr, henc, hsub r hsc⟩
  exact (Slots.loadRec_unique hinj2 hans2).symm

/-- `decSessKit.loadRel` at `StoresGhost.opened.sessions` uniquely determines `ans = Slots.loadRec Scope F peer`. -/
theorem decSessKit_loadRel_eq {img : Obj.Image} {F : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer.val)
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hrel : (decSessKit img F peer B).loadRel StoresGhost.opened.sessions peer.val ans) :
    ans = Slots.loadRec Scope F peer.val := by
  obtain ⟨bs, hget, hans⟩ := hrel
  have hans' : SessLoadAns Slots.scopeKit
      (StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer.val)) ans := by
    rw [hget]; exact hans
  rw [Slots.loadRec_unique hinjK hans']
  exact loadRec_eq_of_sub (fun r hr => Slots.scopeKit_of_scopeIn (hsub r hr)) hinjK hok

theorem loadRec_ne_error {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrVal} (hok : Slots.FilesOkPeer Scope F peer) :
    Slots.loadRec Scope F peer ≠ .error () := by
  have hans := Slots.sessLoadAns_loadRec hok
  obtain ⟨bs, hget, _⟩ := hok.sessGet
  rw [hget] at hans
  cases bs with
  | nil =>
    dsimp only [SessLoadAns] at hans
    rw [hans]; intro h; cases h
  | cons b bs' =>
    obtain ⟨_, hr, _, _⟩ := hans
    rw [hr]; intro h; cases h

/-- Trace events emitted by `decSessKit` and `decIdKit` are empty. -/
theorem decIdKit_traceOfWith_nil (img : Obj.Image) (F : FsFiles) (peer : AddrGhost) (B : RunBudgets)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ calls, (decIdKit img F peer B).traceOfWith (decSessKit img F peer B) encRecord ans calls = []
  | [] => rfl
  | c :: cs => by
    cases c <;>
      simpa [StoreKit.Identity.IdentityStoreSpec.traceOfWith,
        StoreKit.Identity.IdentityStoreSpec.callEvs,
        decSessKit, decIdKit, cliSessionStoreSpec, cliIdentityStoreSpec] using
        decIdKit_traceOfWith_nil img F peer B encRecord ans cs

/-- `List.foldl (cliStep F)` agrees with `decSessKit.storeFinal` and `decIdKit.idFinal` while
preserving the five remaining `Dir` fields. -/
theorem cliStep_foldl_eq (img : Obj.Image) (F : FsFiles) (peer : AddrGhost) (B : RunBudgets)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ (calls : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      let g' := calls.foldl (cliStep F) g
      g'.sessions = (decSessKit img F peer B).storeFinal g.sessions ans calls ∧
      g'.identity = (decIdKit img F peer B).idFinal g.identity ans calls ∧
      g'.signed = g.signed ∧ g'.kyber = g.kyber ∧ g'.oneTime = g.oneTime ∧ g'.pub = g.pub
  | [], g => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | c :: cs, g => by
    cases c <;>
      simpa [List.foldl, cliStep, SessionStoreSpec.storeFinal,
        StoreKit.Identity.IdentityStoreSpec.idFinal, decSessKit, decIdKit,
        cliSessionStoreSpec, cliIdentityStoreSpec] using
        cliStep_foldl_eq img F peer B ans cs _

/-- Post-identity-key step of `messageDecryptSignal`. -/
def decAfterKey (rem : AddrVal) (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8)))
    (ik : IdentityKey) (tr : Except Unit Bool) (sa : Except Unit IdentityChange)
    (st : Except Unit Unit) :
    Except (ApiError AddrVal Unit) (List (BitVec 8)) × List (StoreCall AddrVal (List (BitVec 8))) :=
  match tr with
  | .error e =>
    (.error (.store e), [.loadSession rem, .isTrustedIdentity rem ik .receiving])
  | .ok false =>
    (.error (.untrustedIdentity rem), [.loadSession rem, .isTrustedIdentity rem ik .receiving])
  | .ok true =>
    match sa with
    | .error e =>
      (.error (.store e),
        [.loadSession rem, .isTrustedIdentity rem ik .receiving, .saveIdentity rem ik])
    | .ok _ =>
      match st with
      | .error e =>
        (.error (.store e),
          [.loadSession rem, .isTrustedIdentity rem ik .receiving,
           .saveIdentity rem ik, .storeSession rem rec'])
      | .ok () =>
        (.ok pt,
          [.loadSession rem, .isTrustedIdentity rem ik .receiving,
           .saveIdentity rem ik, .storeSession rem rec'])

private theorem decAfterKey_ne_panic {rem : AddrVal} {pt : List (BitVec 8)}
    {rec' : SessionRecord (List (BitVec 8))} {ik : IdentityKey}
    {tr : Except Unit Bool} {sa : Except Unit IdentityChange} {st : Except Unit Unit} :
    (decAfterKey rem pt rec' ik tr sa st).1 ≠ .error .panic := by
  cases tr with
  | error _ => rintro ⟨⟩
  | ok b =>
    cases b with
    | false => rintro ⟨⟩
    | true =>
      cases sa with
      | error _ => rintro ⟨⟩
      | ok _ =>
        cases st with
        | error _ => rintro ⟨⟩
        | ok u => cases u; rintro ⟨⟩

set_option linter.unusedSimpArgs false in
/-- Closed-form characterization of `LibsignalSessionApi.messageDecryptSignal`. -/
theorem messageDecryptSignal_eq {PqCoins : Type} (C : Crypto)
    (spqr : Spqr (List (BitVec 8)) PqCoins)
    (serAddr : AddrVal → AddrVal → Option (List (BitVec 8)))
    (a : StoreAnswers (List (BitVec 8)) Unit)
    (msg : SignalMessage) (rem loc : AddrVal) (coins : BitVec 256) :
    LibsignalSessionApi.messageDecryptSignal C spqr serAddr a msg rem loc coins =
      match a.loadSession with
      | .error e => (.error (.store e), [.loadSession rem])
      | .ok none => (.error (.sessionNotFound rem "message_decrypt_signal"), [.loadSession rem])
      | .ok (some record) =>
        match SessionRecord.tryDecryptFromRecord C spqr (serAddr rem loc) msg coins record with
        | .error pe => (.error (ApiError.ofProtocol pe), [.loadSession rem])
        | .ok (pt, rec') =>
          match rec'.currentSession with
          | none => (.error .panic, [.loadSession rem])
          | some session =>
            match session.state.remoteIdentity with
            | none => (.error .panic, [.loadSession rem])
            | some ik =>
              decAfterKey rem pt rec' ik a.isTrustedIdentity a.saveIdentity a.storeSession := by
  rcases a with ⟨ls, tr, sa, st⟩
  cases ls with
  | error e => rfl
  | ok opt =>
    cases opt with
    | none => rfl
    | some record =>
      simp only [LibsignalSessionApi.messageDecryptSignal, Api.run, storeCall, liftProtocol,
        Functor.map, StateT.map, ExceptT.map,
        bind, pure, modify, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        throw, throwThe, MonadExceptOf.throw, liftM, monadLift, MonadLift.monadLift,
        MonadLiftT.monadLift, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.lift,
        ExceptT.mk, ExceptT.bindCont, StateT.run, StateT.bind, StateT.pure,
        Id.run, Pure.pure, Bind.bind, ApiError.ofProtocol, List.nil_append, List.cons_append]
      rcases SessionRecord.tryDecryptFromRecord C spqr (serAddr rem loc) msg coins record with
        pe | ⟨pt, rec'⟩
      · cases pe <;> rfl
      · simp only [StateT.pure, StateT.bind, StateT.map, StateT.modifyGet, ExceptT.bindCont,
          Pure.pure, Bind.bind, Id.run, List.nil_append, List.cons_append]
        cases rec'.currentSession with
        | none => rfl
        | some session =>
          simp only [StateT.pure, StateT.bind, StateT.map, StateT.modifyGet, ExceptT.bindCont,
            Pure.pure, Bind.bind, Id.run, List.nil_append, List.cons_append]
          cases session.state.remoteIdentity with
          | none => rfl
          | some ik =>
            dsimp only [decAfterKey]
            cases tr with
            | error _ => rfl
            | ok b =>
              cases b with
              | false => rfl
              | true =>
                cases sa with
                | error _ => rfl
                | ok _ =>
                  cases st with
                  | error _ => rfl
                  | ok u => cases u; rfl

/-- Whether `messageDecryptSignal` returns `.error .panic` depends only on `answers.loadSession`. -/
theorem messageDecryptSignal_panic_iff_of_load_eq {PqCoins : Type} (C : Crypto)
    (spqr : Spqr (List (BitVec 8)) PqCoins)
    (serAddr : AddrVal → AddrVal → Option (List (BitVec 8)))
    (a1 a2 : StoreAnswers (List (BitVec 8)) Unit)
    (msg : SignalMessage) (rem loc : AddrVal) (coins : BitVec 256)
    (hload : a1.loadSession = a2.loadSession) :
    (LibsignalSessionApi.messageDecryptSignal C spqr serAddr a1 msg rem loc coins).1 = .error .panic ↔
      (LibsignalSessionApi.messageDecryptSignal C spqr serAddr a2 msg rem loc coins).1 = .error .panic := by
  rcases a1 with ⟨ls1, tr1, sa1, st1⟩
  rcases a2 with ⟨ls2, tr2, sa2, st2⟩
  dsimp only at hload
  subst hload
  rw [messageDecryptSignal_eq, messageDecryptSignal_eq]
  dsimp only
  cases ls1 with
  | error _ => rfl
  | ok opt =>
    cases opt with
    | none => rfl
    | some record =>
      dsimp only
      rcases SessionRecord.tryDecryptFromRecord C spqr (serAddr rem loc) msg coins record with
        pe | ⟨pt, rec'⟩
      · rfl
      · dsimp only
        cases rec'.currentSession with
        | none => rfl
        | some session =>
          dsimp only
          cases session.state.remoteIdentity with
          | none => rfl
          | some ik =>
            dsimp only
            exact ⟨fun h => absurd h decAfterKey_ne_panic,
                   fun h => absurd h decAfterKey_ne_panic⟩

private theorem sessCallsRel_head {img : Obj.Image} {F : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {ans : StoreAnswers (List (BitVec 8)) Unit}
    {calls cs : List (StoreCall AddrVal (List (BitVec 8)))}
    (hc : calls = .loadSession peer.val :: cs)
    (h : (decSessKit img F peer B).callsRel StoresGhost.opened.sessions ans calls) :
    (decSessKit img F peer B).loadRel StoresGhost.opened.sessions peer.val ans.loadSession := by
  subst hc
  exact h.1

private theorem sessCallsRel_store_ok {img : Obj.Image} {F : FsFiles} {peer : AddrGhost}
    {B : RunBudgets} {ans : StoreAnswers (List (BitVec 8)) Unit}
    {ik : IdentityKey} {rec' : SessionRecord (List (BitVec 8))}
    {calls : List (StoreCall AddrVal (List (BitVec 8)))}
    (hc : calls = [.loadSession peer.val, .isTrustedIdentity peer.val ik .receiving,
       .saveIdentity peer.val ik, .storeSession peer.val rec'])
    (h : (decSessKit img F peer B).callsRel StoresGhost.opened.sessions ans calls) :
    ans.storeSession = .ok () := by
  subst hc
  exact h.2.1

private theorem idCallsRel_trust {img : Obj.Image} {F : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {ans : StoreAnswers (List (BitVec 8)) Unit} {ik : IdentityKey}
    {calls cs : List (StoreCall AddrVal (List (BitVec 8)))}
    (hc : calls = .loadSession peer.val :: .isTrustedIdentity peer.val ik .receiving :: cs)
    (h : (decIdKit img F peer B).idCallsRel StoresGhost.opened.identity ans calls) :
    (decIdKit img F peer B).trustRel StoresGhost.opened.identity peer.val ik .receiving
      ans.isTrustedIdentity := by
  subst hc
  exact h.1

private theorem idCallsRel_save {img : Obj.Image} {F : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {ans : StoreAnswers (List (BitVec 8)) Unit} {ik : IdentityKey}
    {calls cs : List (StoreCall AddrVal (List (BitVec 8)))}
    (hc : calls = .loadSession peer.val :: .isTrustedIdentity peer.val ik .receiving ::
       .saveIdentity peer.val ik :: cs)
    (h : (decIdKit img F peer B).idCallsRel StoresGhost.opened.identity ans calls) :
    (decIdKit img F peer B).saveRel StoresGhost.opened.identity peer.val ik ans.saveIdentity := by
  subst hc
  exact h.2.1

private theorem messageDecryptSignal_calls_cons {PqCoins : Type} (C : Crypto)
    (spqr : Spqr (List (BitVec 8)) PqCoins)
    (serAddr : AddrVal → AddrVal → Option (List (BitVec 8)))
    (a : StoreAnswers (List (BitVec 8)) Unit)
    (msg : SignalMessage) (rem loc : AddrVal) (coins : BitVec 256) :
    ∃ cs, (LibsignalSessionApi.messageDecryptSignal C spqr serAddr a msg rem loc coins).2 =
      .loadSession rem :: cs := by
  rw [messageDecryptSignal_eq]
  rcases a with ⟨ls, tr, sa, st⟩
  cases ls with
  | error _ => exact ⟨[], rfl⟩
  | ok opt =>
    cases opt with
    | none => exact ⟨[], rfl⟩
    | some record =>
      dsimp only
      rcases SessionRecord.tryDecryptFromRecord C spqr (serAddr rem loc) msg coins record with
        pe | ⟨pt, rec'⟩
      · exact ⟨[], rfl⟩
      · dsimp only
        cases rec'.currentSession with
        | none => exact ⟨[], rfl⟩
        | some session =>
          dsimp only
          cases session.state.remoteIdentity with
          | none => exact ⟨[], rfl⟩
          | some ik =>
            dsimp only [decAfterKey]
            cases tr with
            | error _ => exact ⟨_, rfl⟩
            | ok b =>
              cases b with
              | false => exact ⟨_, rfl⟩
              | true =>
                cases sa with
                | error _ => exact ⟨_, rfl⟩
                | ok _ =>
                  cases st with
                  | error _ => exact ⟨_, rfl⟩
                  | ok u => cases u; exact ⟨_, rfl⟩

set_option linter.unusedSimpArgs false in
private theorem decModel_det_aux {PqCoins : Type} {img : Obj.Image} (C : Crypto)
    (spqr : Spqr (List (BitVec 8)) PqCoins) (B : RunBudgets)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (x : DecryptGhost) (coins : BitVec 256) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (calls : List (StoreCall AddrVal (List (BitVec 8))))
    (hcEq : (LibsignalSessionApi.messageDecryptSignal C spqr
        (serializeAddrVals (serviceIdParse uuidTryParse)) answers
        x.msg x.rem.val x.loc.val coins).2 = calls)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F x.rem.val)
    (hcalls : (decSessKit img F x.rem B).callsRel StoresGhost.opened.sessions answers calls)
    (hidCalls : (decIdKit img F x.rem B).idCallsRel StoresGhost.opened.identity answers calls) :
    let keyOpt : Option IdentityKey :=
      match Slots.loadRec Scope F x.rem.val with
      | .ok (some r) =>
        match SessionRecord.tryDecryptFromRecord C spqr
            (serializeAddrVals (serviceIdParse uuidTryParse) x.rem.val x.loc.val) x.msg
            coins r with
        | .ok (_, r') => r'.currentSession.bind (·.state.remoteIdentity)
        | .error _ => none
      | _ => none
    let ca := cliAnswers Scope F x.rem.val keyOpt
    LibsignalSessionApi.messageDecryptSignal C spqr
        (serializeAddrVals (serviceIdParse uuidTryParse)) answers
        x.msg x.rem.val x.loc.val coins =
      LibsignalSessionApi.messageDecryptSignal C spqr
        (serializeAddrVals (serviceIdParse uuidTryParse)) ca
        x.msg x.rem.val x.loc.val coins ∧
    (LibsignalSessionApi.messageDecryptSignal C spqr
        (serializeAddrVals (serviceIdParse uuidTryParse)) answers
        x.msg x.rem.val x.loc.val coins).1 ≠ .error (.store ()) ∧
    (∀ pt, (LibsignalSessionApi.messageDecryptSignal C spqr
        (serializeAddrVals (serviceIdParse uuidTryParse)) answers
        x.msg x.rem.val x.loc.val coins).1 = .ok pt →
      ∀ pw ∈ (cliFinal F calls).writes,
        cliWrOk pw.1) := by
  intro keyOpt ca
  have hloadRel : (decSessKit img F x.rem B).loadRel StoresGhost.opened.sessions
      x.rem.val answers.loadSession := by
    obtain ⟨cs, hcs0⟩ := messageDecryptSignal_calls_cons C spqr
      (serializeAddrVals (serviceIdParse uuidTryParse)) answers x.msg x.rem.val x.loc.val coins
    exact sessCallsRel_head (hcEq.symm.trans hcs0) hcalls
  have hloadEq := decSessKit_loadRel_eq hinjK hsub hok hloadRel
  have hloadNeErr := loadRec_ne_error hok
  rcases answers with ⟨ls, tr, sa, st⟩
  dsimp only at hloadEq
  rw [messageDecryptSignal_eq] at hcEq
  rw [messageDecryptSignal_eq, messageDecryptSignal_eq]
  dsimp only [ca, cliAnswers]
  cases hlr : Slots.loadRec Scope F x.rem.val with
  | error u => cases u; exact absurd hlr hloadNeErr
  | ok opt =>
    rw [hlr] at hloadEq
    subst hloadEq
    cases opt with
    | none =>
      dsimp only at hcEq ⊢
      subst hcEq
      refine ⟨rfl, by rintro ⟨⟩, fun _ h => by cases h⟩
    | some record =>
      have hkeyOpt : keyOpt =
          match SessionRecord.tryDecryptFromRecord C spqr
              (serializeAddrVals (serviceIdParse uuidTryParse) x.rem.val x.loc.val) x.msg
              coins record with
          | .ok (_, r') => r'.currentSession.bind (·.state.remoteIdentity)
          | .error _ => none := by
        dsimp only [keyOpt]
        rw [hlr]
      rw [hkeyOpt]
      dsimp only at hcEq ⊢
      rcases hdec : SessionRecord.tryDecryptFromRecord C spqr
          (serializeAddrVals (serviceIdParse uuidTryParse) x.rem.val x.loc.val) x.msg
          coins record with pe | ⟨pt, rec'⟩
      · simp only [hdec] at hcEq ⊢
        subst hcEq
        refine ⟨trivial, by cases pe <;> rintro ⟨⟩, fun _ h => by cases h⟩
      · simp only [hdec] at hcEq ⊢
        cases hcs : rec'.currentSession with
        | none =>
          simp only [hcs] at hcEq ⊢
          subst hcEq
          refine ⟨trivial, by rintro ⟨⟩, fun _ h => by cases h⟩
        | some session =>
          simp only [hcs, Option.bind] at hcEq ⊢
          cases hik : session.state.remoteIdentity with
          | none =>
            simp only [hik] at hcEq ⊢
            subst hcEq
            refine ⟨trivial, by rintro ⟨⟩, fun _ h => by cases h⟩
          | some ik =>
            simp only [hik, Option.bind, decAfterKey] at hcEq ⊢
            have htrustRel : (decIdKit img F x.rem B).trustRel StoresGhost.opened.identity
                x.rem.val ik .receiving tr := by
              have hcons : ∃ cs, calls =
                  .loadSession x.rem.val :: .isTrustedIdentity x.rem.val ik .receiving :: cs := by
                rw [← hcEq]
                cases tr with
                | error _ => exact ⟨[], rfl⟩
                | ok b =>
                  cases b with
                  | false => exact ⟨[], rfl⟩
                  | true =>
                    cases sa with
                    | error _ => exact ⟨_, rfl⟩
                    | ok _ =>
                      cases st with
                      | error _ => exact ⟨_, rfl⟩
                      | ok u => cases u; exact ⟨_, rfl⟩
              obtain ⟨cs, hcs'⟩ := hcons
              exact idCallsRel_trust hcs' hidCalls
            obtain ⟨t, ht_model, ht_ans⟩ := htrustRel
            subst ht_ans
            rw [ht_model]
            cases t with
            | false =>
              dsimp only at hcEq ⊢
              subst hcEq
              refine ⟨rfl, by rintro ⟨⟩, fun _ h => by cases h⟩
            | true =>
              dsimp only at hcEq ⊢
              have hsaveRel : (decIdKit img F x.rem B).saveRel StoresGhost.opened.identity
                  x.rem.val ik sa := by
                have hcons : ∃ cs, calls =
                    .loadSession x.rem.val :: .isTrustedIdentity x.rem.val ik .receiving ::
                    .saveIdentity x.rem.val ik :: cs := by
                  rw [← hcEq]
                  cases sa with
                  | error _ => exact ⟨[], rfl⟩
                  | ok _ =>
                    cases st with
                    | error _ => exact ⟨_, rfl⟩
                    | ok u => cases u; exact ⟨_, rfl⟩
                obtain ⟨cs, hcs'⟩ := hcons
                exact idCallsRel_save hcs' hidCalls
              obtain ⟨c, hc_model, hc_ans⟩ := hsaveRel
              subst hc_ans
              rw [hc_model]
              dsimp only at hcEq ⊢
              have hstoreEq : st = .ok () := by
                have hcons : calls =
                    [.loadSession x.rem.val, .isTrustedIdentity x.rem.val ik .receiving,
                     .saveIdentity x.rem.val ik, .storeSession x.rem.val rec'] := by
                  rw [← hcEq]
                  cases st with
                  | error _ => rfl
                  | ok u => cases u; rfl
                exact sessCallsRel_store_ok hcons hcalls
              subst hstoreEq
              dsimp only at hcEq ⊢
              subst hcEq
              refine ⟨rfl, by rintro ⟨⟩, ?_⟩
              intro pt' _ pw hpw
              have hidInv := cliIdInv_opened_wrOk hok
              have hupd := CliIdInv.saveUpd_eq hidInv ik
              dsimp only [cliFinal, List.foldl, cliStep] at hpw
              rw [hupd] at hpw
              simp only [StoresGhost.writes, StoresGhost.opened, DirGhost.put, DirGhost.new,
                DirGhost.setOrPush, DirGhost.writes, List.map, List.cons_append, List.append_nil,
                List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hpw
              rcases hpw with rfl | rfl
              · exact ⟨hok.idPathOk, hok.idPathLt⟩
              · exact ⟨hok.sessPathOk, hok.sessPathLt⟩

/-- Determinism of `DecryptGhost.model` under `decSessKit.callsRel` and `decIdKit.idCallsRel`,
matching `cliAnswers Scope F x.rem.val (decKeyAux ...)` and establishing `cliWrOk` on committed writes. -/
theorem decModel_det {img : Obj.Image} (W : CliHooks) (B : RunBudgets)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (x : DecryptGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (_hrem : x.rem.val = x.rem.val)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F x.rem.val)
    (hcalls : (decSessKit img F x.rem B).callsRel StoresGhost.opened.sessions answers
      (x.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2)
    (hidCalls : (decIdKit img F x.rem B).idCallsRel StoresGhost.opened.identity answers
      (x.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2) :
    let ca := cliAnswers Scope F x.rem.val
      (decKeyAux ⟨W.C, W.Q⟩ Scope F x.rem.val x.loc.val x.msg x.rest)
    x.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers =
      x.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse ca ∧
    (x.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).1 ≠ .error (.store ()) ∧
    (∀ pt, (x.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).1 = .ok pt →
      ∀ pw ∈ (cliFinal F (x.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2).writes,
        cliWrOk pw.1) :=
  decModel_det_aux W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr B Scope F x
    (LibsignalTripleRatchetRepr.coinsOf x.rest) answers
    (x.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2 rfl
    hinjK hsub hok hcalls hidCalls

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
