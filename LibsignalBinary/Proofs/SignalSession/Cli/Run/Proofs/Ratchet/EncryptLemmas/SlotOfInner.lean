/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridge
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seams
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.PanicAndWire
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridge
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Outer Slot Reduction for `encrypt`

Discharges the `EncEnv` record-scope invariants (`w1_scopeIn`, `w1_scopeQ`, `w1_recOk`) for
`w1SessKit` and reduces `encSlotSpec` (`cliEncrypt_slot_of_inner` and its
`PEParams`/`RustAlloc`-generic counterparts) to the inner `withStoresEncSpecVT_cli` contract.
-/

@[expose] public section

set_option autoImplicit false

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

/-! ## Record-scope obligations (`scopeIn`, `scopeQ`, `recOk`) -/

theorem w1_scopeIn {B : RunBudgets} {img : Obj.Image} {F : FsFiles} {peer : AddrGhost}
    {st0 : (w1SessKit B img F peer).StoreState} {rem : AddrVal}
    (r : SessionRecord (List (BitVec 8)))
    (hsc : (w1SessKit B img F peer).ScopeAt Slots.scopeKit st0 rem r) :
    RecordInScopeEnc r :=
  fun s hs => ⟨trivial, hsc.1.1.1 s hs⟩

theorem w1_scopeQ {B : RunBudgets} {img : Obj.Image} {F : FsFiles} {peer : AddrGhost}
    {st0 : (w1SessKit B img F peer).StoreState} {rem : AddrVal}
    (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8)))
    (hsc : (w1SessKit B img F peer).ScopeAt Slots.scopeKit st0 rem r)
    (hs : r.currentSession = some s) :
    s.state.pqRatchetState.length < 2 ^ 32 :=
  hsc.1.1.2.1 s hs

private theorem fromSessionState_pqr_and_taken {s taken : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (otr, taken)) :
    otr.pqrState = s.pqRatchetState ∧ taken = { s with pqRatchetState := [] } := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals (try split_ifs at h) <;>
    simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨(congrArg OutgoingTripleRatchet.pqrState h.1).symm, h.2.symm⟩

private theorem otr_encrypt_send_step_aux {PQ PQC : Type} {C : Crypto} {codec : SignalMessageProtoCodec}
    {spqr : Spqr PQ PQC} {ptext : List (BitVec 8)} {ad : Option (List (BitVec 8))} {rest : PQC}
    {otr otr' : OutgoingTripleRatchet PQ} {sm : SignalMessage}
    (h : execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext ad rest) otr = .ok (sm, otr')) :
    ∃ salt pm, spqr.send otr.pqrState rest = some (otr'.pqrState, salt, pm) := by
  unfold execOk Mut.exec OutgoingTripleRatchet.encrypt at h
  dsimp only [ExceptT.run, ExceptT.mk, ExceptT.lift, StateT.run, StateT.bind, StateT.map,
    Functor.map, ExceptT.map, ExceptT.bind, ExceptT.bindCont, StateT.pure, ExceptT.pure,
    StateT.get, StateT.set, set, MonadStateOf.set, liftE, StateT.lift, liftM, monadLift,
    MonadLift.monadLift, MonadLiftT.monadLift, get, getThe, MonadStateOf.get, bind, pure,
    throw, throwThe, MonadExceptOf.throw] at h
  cases hpan : spqr.sendPanics otr.pqrState rest
  case true =>
    simp [hpan, ExceptT.bindCont, StateT.bind, StateT.pure, bind, pure] at h
  case false =>
    simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
    rcases hs : spqr.send otr.pqrState rest with _ | ⟨pq', salt, pm⟩
    · simp [hs, StateT.pure, pure] at h
    · simp only [hs] at h
      rcases hn : otr.senderChainKey.nextChainKey C.F with _ | next
      · simp [hn, StateT.bind, StateT.pure, ExceptT.bindCont, bind, pure] at h
      · simp only [hn, StateT.bind, StateT.pure, StateT.map, StateT.set, ExceptT.bindCont,
          bind, pure, Except.ok.injEq, Prod.mk.injEq] at h
        have hpq : pq' = otr'.pqrState := congrArg OutgoingTripleRatchet.pqrState h.2
        subst hpq
        exact ⟨salt, pm, rfl⟩

private theorem otr_encrypt_send_step {C : Crypto} {S : SpqrModel}
    {ptext : List (BitVec 8)} {ad : Option (List (BitVec 8))} {rest : List (BitVec 8)}
    {otr otr' : OutgoingTripleRatchet (List (BitVec 8))} {sm : SignalMessage}
    (h : execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr ptext ad rest) otr =
      .ok (sm, otr')) :
    ∃ salt pm, S.send otr.pqrState rest = some (otr'.pqrState, salt, pm) :=
  otr_encrypt_send_step_aux h

/-- One encrypt step from `StoresGhost.opened.sessions` under `FilesOkPeer Scope` and
`Scope ⊆ Slots.scopeIn` preserves `Slots.scopeKit` and the `< 2^32` encoded-record bound. -/
theorem w1_recOk (W : PEParams) {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {img : Obj.Image} {F : FsFiles} {peer : AddrGhost}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer.val)
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (hrem_eq : x.rem.val = peer.val)
    (h15 : StepsThroughEncrypt
      ((w1SessKit B img F peer).ScopeAt Slots.scopeKit StoresGhost.opened.sessions x.rem.val)
      W.C (pqxdhSpqrModel W) uuidTryParse x r sess otr taken k m otr') :
    (w1SessKit B img F peer).RecOk (storedRecord sess otr' taken) := by
  rcases h15 with ⟨hcur, hScAt, hfrom, _hremId, hstep⟩
  have hok_rem : Slots.FilesOkPeer Scope F x.rem.val := hrem_eq ▸ hok
  have hlr : Slots.loadRec Scope F x.rem.val = .ok (some r) :=
    (cliSessLoadRel_eq_loadRec_scope hinjK hsub hok_rem hScAt.2).symm
  have hla := Slots.sessLoadAns_loadRec hok_rem
  rw [hlr] at hla
  obtain ⟨bs, hbs, _⟩ := hok_rem.sessGet
  rw [hbs] at hla
  have hr_scope : Scope r := by
    rcases bs with _ | ⟨_, _⟩
    · cases hla
    · obtain ⟨_, hans, _, hsc⟩ := hla
      cases hans
      exact hsc
  have hr_in : Slots.scopeIn r := hsub r hr_scope
  obtain ⟨⟨hInP, hPqIn, hRepr⟩, s0, hs0, hSessP⟩ := hr_in
  have hsess_eq : s0 = sess := Option.some.inj (hs0.symm.trans hcur)
  subst s0
  have hInSess := hInP sess hcur
  have hPqSess : Slots.PqValid.PqInV1 sess.state.pqRatchetState := hPqIn sess hcur
  have hReprSess := hRepr sess hcur
  obtain ⟨hpqr_eq, htaken⟩ := fromSessionState_pqr_and_taken hfrom
  subst htaken
  have hStepV1 := Slots.PqValid.pqStep_spqrV1 W.C.F W.Q.K
  have hotr_pq : Slots.PqValid.PqInV1 otr.pqrState := hpqr_eq ▸ hPqSess
  have hotr'_pq : Slots.PqValid.PqOutV1 otr'.pqrState := by
    unfold EncEncryptStep at hstep
    cases hp : sess.pendingPreKey with
    | none =>
      rw [hp] at hstep
      obtain ⟨sm, henc, _⟩ := hstep
      obtain ⟨salt, pm, hs⟩ := otr_encrypt_send_step henc
      exact hStepV1.send _ _ _ _ _ hotr_pq hs
    | some items =>
      rw [hp] at hstep
      obtain ⟨_, _, sm, _, _, _, henc, _⟩ := hstep
      obtain ⟨salt, pm, hs⟩ := otr_encrypt_send_step henc
      exact hStepV1.send _ _ _ _ _ hotr_pq hs
  have hotr'_lt32 : otr'.pqrState.length < 2 ^ 32 := hStepV1.out_bound _ hotr'_pq
  have hRecIn' : E2E.RecordX.RecordInScopeP (storedRecord sess otr' { sess.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    unfold OutgoingTripleRatchet.applyToSessionState
    exact ⟨hInSess.1, hInSess.2.1, hInSess.2.2⟩
  have hRepr' : E2E.Record.RecordRepr (storedRecord sess otr' { sess.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    refine ⟨hReprSess.1, ?_, ?_, hReprSess.2.2.2⟩
    · intro sc' hsc'
      simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_eq_some_iff] at hsc'
      obtain ⟨sc, hsc, rfl⟩ := hsc'
      exact hReprSess.2.1 sc hsc
    · simpa [Session.Wf, OutgoingTripleRatchet.applyToSessionState] using hReprSess.2.2.1
  have hSessP' : E2E.RecordX.SessionScopeP
      { sess with state := otr'.applyToSessionState { sess.state with pqRatchetState := [] } } := by
    exact ⟨hSessP.1, hSessP.2.1, hSessP.2.2.1, hSessP.2.2.2⟩
  have hScopeKit' : Slots.scopeKit (storedRecord sess otr' { sess.state with pqRatchetState := [] }) := by
    refine ⟨⟨hRecIn', ?_, hRepr'⟩, _, rfl, hSessP'⟩
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    exact hotr'_lt32
  have hStripBounded : E2E.RecordX.DeserializeScopeBounded
      ⟨some (Slots.PqValid.stripPq
        { sess with state := otr'.applyToSessionState { sess.state with pqRatchetState := [] } })⟩ := by
    have hSessB := E2E.RecordX.sessionScopeBounded_of_sessionScopeP hSessP'
    refine ⟨⟨?_, ?_, ?_⟩, _, rfl, ⟨hSessB.1, hSessB.2.1, hSessB.2.2.1, hSessB.2.2.2⟩⟩
    · intro s' hs'
      simp only [Option.some.injEq] at hs'; subst hs'
      exact ⟨hInSess.1, hInSess.2.1, hInSess.2.2⟩
    · intro s' hs'
      simp only [Option.some.injEq] at hs'; subst hs'; rfl
    · intro s' hs'
      simp only [Option.some.injEq] at hs'; subst hs'
      refine ⟨hReprSess.1, ?_, ?_, hReprSess.2.2.2⟩
      · intro sc' hsc'
        dsimp only [Slots.PqValid.stripPq] at hsc'
        simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_eq_some_iff] at hsc'
        obtain ⟨sc, hsc, rfl⟩ := hsc'
        exact hReprSess.2.1 sc hsc
      · simpa [Slots.PqValid.stripPq, Session.Wf, OutgoingTripleRatchet.applyToSessionState]
          using hReprSess.2.2.1
  have hLen32 : (E2E.Record.encodeRecord
      (storedRecord sess otr' { sess.state with pqRatchetState := [] })).length < 2 ^ 32 :=
    Slots.PqValid.encodeRecord_length_lt_32_of_stripPq_bounded hStripBounded hotr'_pq
  exact ⟨hScopeKit', hLen32⟩

/-! ## Inner disjunctive encrypt specification -/

/-- Disjunctive (`64 ≤ rest.length ∨ ∀ r, ScopeAt ... → RecordPqEmpty r`) and `TokenInit`-framed inner encrypt specification. -/
def withStoresEncSpecVT_cli {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec WithStoresEncGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
      kit st0 ikit ist0 C ctl uuidParse S encRecord with
    pre := fun x s =>
      ⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).pre x s
    post := fun x s0 sf =>
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf }

def w1EncGhost (x : EncGhost) : WithStoresEncGhost where
  ret := x.ret
  ptA := x.ptA
  ptext := x.ptext
  remA := x.peerA
  rem := x.peer
  locA := x.meA
  loc := x.me
  now := unixEpoch
  cur := x.coinsP
  rest := x.coins
  ssA := x.stores + 0xf0#64
  idA := x.stores

/-! ## Outer `encSlotSpec` reduction -/

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
/-- Reduces `encSlotSpec` for `signal_session_ratchet::encrypt` to the inner `withStoresEncSpecVT_cli` contract. -/
theorem cliEncrypt_slot_of_inner {img : Obj.Image} (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (_himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = w1EncDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hInner : ∀ (F : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Scope F peer.val →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
        ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapEncryptName)
        (withEnvPre
          (withStoresEncSpecVT_cli (w1SessKit B img F peer) StoresGhost.opened.sessions
            (w1IdKit B img F peer) StoresGhost.opened.identity Slots.scopeKit
            W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
          (fun s => (w1SessKit B img F peer).envOk s.fs.files ∧
            (w1IdKit B img F peer).envOk s.fs.files)))
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr wrapEncryptName)
      (encSlotSpec E2E.HooksE.A0 img S stk) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal _hL => ?_
  dsimp only [encSlotSpec, Spec.inImage, slotFrame] at hpre
  have hpre_flat : s0.mem ⊨
      ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.peerA ∧ s0.readReg64 .x3 = x.meA ∧
        s0.readReg64 .x4 = x.stores + 0xf0#64 ∧ s0.readReg64 .x5 = sessVt img ∧
        s0.readReg64 .x6 = x.stores ∧ s0.readReg64 .x7 = idVt img ∧
        s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        S.encOk x.F x.peer.val x.coins ∧ stk ≤ s0.sp.toNat ∧ x.meA ≠ 0#64⌝ ∗
      (⌜x.coins.length < 2 ^ 63⌝ ∗
      (storesAt E2E.HooksE.A0 x.stores StoresGhost.opened ∗
        protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
        protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
        coinsInstalled img x.coinsP x.coins ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        logOff img ∗ E2E.HooksE.A0.pool ∗
        (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗
        memRegion x.ret 248 ∗ stackAt s0.sp stk ∗ R))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hfl, hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat
  obtain ⟨⟨hx0, hx1, hptLt, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfiles, hfOk, heOk, hsp_le, hme_ne⟩,
    hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hcoinsLt, hm0⟩ := hpre_flat
  obtain ⟨hokF, hokE⟩ := hok x.F x.peer.val x.me.val x.coins hfOk heOk

  set kit := w1SessKit B img x.F x.peer
  set ikit := w1IdKit B img x.F x.peer
  set innerStk := withStoresEncStackV kit ikit
  set extraStk := stk - innerStk
  have hinner_le : innerStk ≤ stk := Nat.le_trans (w1_innerStack_le_need B img x.F x.peer) hstk
  have hstk_sum : innerStk + extraStk = stk := by omega
  have hstk_split : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk := by
    rw [← hstk_sum]
    exact stackAt_split_bottom s0.sp innerStk extraStk (by omega)
  have hcoins_eq : coinsInstalled img x.coinsP x.coins =
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.coinsP x.coins :=
    (Slots.coinsAt_eq_coinsInstalled img x.coinsP x.coins hcoinsLt).symm
  have hnow_eq : nowCellAt s0.sp unixEpoch = nowAt s0.sp unixEpoch := rfl
  have hssVt_eq : sessVt img = kit.ss_vt := rfl
  have hidVt_eq : idVt img = ikit.id_vt := rfl
  have hdisj := encOk₀_to_kitScopeAt (A := E2E.HooksE.A0) (b := img.base)
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
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.coinsP x.coins ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      logOff img ∗ E2E.HooksE.A0.pool ∗
      (x.ptA ↦ₛ x.ptext) ∗ nowAt s0.sp unixEpoch ∗
      memRegion x.ret 248 ∗
      (memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk) ∗ R) := by
    rw [hstk_split, hcoins_eq, hnow_eq] at hm0
    exact Satisfies.mono
      (sepConj_mono_left (storesAt_opened_to_kits B img x.F x.peer x.stores hsub hokF)) hm0
  have hpre_vt : s0.mem ⊨
      (withStoresEncSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
        Slots.scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩)
        E2E.Record.encodeRecord).pre (w1EncGhost x) s0 ∗ R_inner := by
    dsimp only [withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage, w1EncGhost]
    have hgoal : s0.mem ⊨
        ⌜64 ≤ x.coins.length ∨
          (∀ r, kit.ScopeAt Slots.scopeKit StoresGhost.opened.sessions x.peer.val r →
            E2E.Record.RecordPqEmpty r)⌝ ∗
        (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
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
        (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
          kit.storeAt (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
          ikit.identityAt x.stores StoresGhost.opened.identity ∗
          nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          memRegion x.ret 248 ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base x.coinsP x.coins ∗
          logOff img ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool ∗ R_inner))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hdisj, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hpure_in, ?_⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by dsimp only [R_inner]; ac_rfl)) hm_unpacked
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hgoal
  have hpre_env : s0.mem ⊨
      (withEnvPre
        (withStoresEncSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
          Slots.scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)).pre (w1EncGhost x) s0 ∗ R_inner :=
    withEnvPre_pre_intro ⟨hfiles, hfiles⟩ hpre_vt
  have hpre_fs : s0.mem ⊨
      (withFsInv
        (withEnvPre
          (withStoresEncSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
            Slots.scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord)
          (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
        s0.fs.files s0.trace).pre (w1EncGhost x) s0 ∗ R_inner :=
    withFsInv_pre_intro (withFsInv_entry s0) hpre_env

  have hSub := subroutine_ok_withFsInv hh.fs (hInner x.F x.peer hokF) s0.fs.files s0.trace
  refine subroutine_ok.mono_outcome hSub (w1EncGhost x) R_inner s0 hpc hrun hpre_fs hal ?_
  intro sf hout
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hmpan⟩ | ⟨_c, _hex, hmex⟩ | ⟨_hoom, hmoom⟩
  ·
    refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hinv_f, hpost⟩ := withFsInv_post_elim hpost
    dsimp only [withEnvPre, withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage] at hpost
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
          (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
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
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers) ∗
            logOff img ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool ∗ R_inner) := by
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
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers) ∗
            logOff img ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool) ∗
          (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ R_inner) :=
        Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at h1
      obtain ⟨answers, h1⟩ := h1
      rw [satisfies_sepExists]
      exact ⟨answers, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) h1⟩
    rw [satisfies_sepExists] at hpost_ex
    obtain ⟨answers, hpost_ans⟩ := hpost_ex
    rw [satisfies_pure_sepConj] at hpost_ans
    obtain ⟨⟨hnoPanic, hcalls, hid, htr_raw⟩, hm_f⟩ := hpost_ans
    have htr_nil : ikit.traceOfWith kit E2E.Record.encodeRecord answers
        ((w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2 = [] :=
      cliTraceOfWith_eq_nil _ _ _
    have htr : sf.trace = s0.trace := by rw [htr_raw, htr_nil, List.append_nil]
    have hslotTr : slotTrace s0 sf := slotTrace_of_fsInv_trace_eq hinv_f htr
    obtain ⟨hmodel_eq, hnoStore, hg'_eq, hwrOk⟩ :=
      cliEncrypt_store_det ⟨W.C, W.Q⟩ (w1EncGhost x).toEncryptGhost answers hinjK hsub hokF hcalls hid
    set resCalls := (w1EncGhost x).model W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers
    set e := resCalls.1
    set g' := w1CliFinal x.F resCalls.2
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
          (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
            kit.storeAt (x.stores + 0xf0#64)
              (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
            ikit.identityAt x.stores
              (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
            nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
            protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
            protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers) ∗
            logOff img ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool ∗ R_inner) := by
        have hm_f' := hm_f
        change sf.mem ⊨ (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
          kit.storeAt (x.stores + 0xf0#64)
            (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
          ikit.identityAt x.stores
            (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
          apiEncResultAt E2E.HooksE.A0 x.ret e ∗
          nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers) ∗
          logOff img ∗ stackAt s0.sp innerStk ∗ E2E.HooksE.A0.pool ∗ R_inner) at hm_f'
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
    dsimp only [encSlotSpec, Spec.inImage]
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
        (x.ptA ↦ₛ x.ptext) ∗ nowAt s0.sp unixEpoch ∗ logOff img ∗ E2E.HooksE.A0.pool ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk) ∗
        (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel ⟨W.C, W.Q⟩) answers)) ∗ R) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [R_inner]; ac_rfl)) hm_f
    have hm_post : sf.mem ⊨
        (storesAt E2E.HooksE.A0 x.stores g' ∗
          encResAt E2E.HooksE.A0 x.ret e ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ logOff img ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp stk ∗ anyHeap ∗ R) := by
      rw [hstk_split, hnow_eq, ← hg'_eq]
      refine Satisfies.mono ?_ hm_reord
      exact sepConj_mono (kits_to_storesAt B img x.F x.peer x.stores _ _)
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
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ logOff img ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp stk ∗ anyHeap ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hslotTr, hslotOut, hwire42⟩, hm_post⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal_post
  ·
    refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withFsInv, withEnvPre, withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage] at hmpan
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
        have hload_eq : answers.loadSession =
            (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)).loadSession :=
          cliSessLoadRel_eq_loadRec_scope hinjK hsub hokF hloadRel
        have hp_cli := model_panic_of_loadSession_eq W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse
          (w1EncGhost x).toEncryptGhost answers
          (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)) hload_eq hp_ans
        exact (congrFun (congrFun (congrFun (congrFun (congrFun hS x.F) x.peer.val) x.me.val)
          x.ptext) x.coins).trans
          ((w1EncDef_eq_slotAnsOfRc ⟨W.C, W.Q⟩ Scope x.F (w1EncGhost x).toEncryptGhost rfl).trans
            (match_panic_eq_none x.F hp_cli))
    dsimp only [encSlotSpec, Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    dsimp only [R_inner] at hm_pan
    simp only [← sepConj_assoc] at hm_pan
    exact ⟨hpan_out, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
  ·
    dsimp only [withFsInv, withEnvPre, withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage] at hmex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmex
    have hmex2 := hmex.2
    rw [satisfies_pure_sepConj] at hmex2
    exact False.elim hmex2.1
  ·
    dsimp only [withFsInv, withEnvPre, withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage] at hmoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmoom
    have hmoom2 := hmoom.2
    rw [satisfies_pure_sepConj] at hmoom2
    exact False.elim hmoom2.1

/-! ## Allocator- and extern-parametric generalization -/

theorem w1_scopeIn_ext {A : RustAlloc} {B : RunBudgets} {img : Obj.Image} {F : FsFiles}
    {peer : AddrGhost} {st0 : (w1SessKitExt A B img F peer).StoreState} {rem : AddrVal}
    (r : SessionRecord (List (BitVec 8)))
    (hsc : (w1SessKitExt A B img F peer).ScopeAt Slots.scopeKit st0 rem r) :
    RecordInScopeEnc r :=
  fun s hs => ⟨trivial, hsc.1.1.1 s hs⟩

theorem w1_scopeQ_ext {A : RustAlloc} {B : RunBudgets} {img : Obj.Image} {F : FsFiles}
    {peer : AddrGhost} {st0 : (w1SessKitExt A B img F peer).StoreState} {rem : AddrVal}
    (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8)))
    (hsc : (w1SessKitExt A B img F peer).ScopeAt Slots.scopeKit st0 rem r)
    (hs : r.currentSession = some s) :
    s.state.pqRatchetState.length < 2 ^ 32 :=
  hsc.1.1.2.1 s hs

theorem w1_recOk_ext (P : PEParams) {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustAlloc} {B : RunBudgets} {img : Obj.Image} {F : FsFiles} {peer : AddrGhost}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit) (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer.val)
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (hrem_eq : x.rem.val = peer.val)
    (h15 : StepsThroughEncrypt
      ((w1SessKitExt A B img F peer).ScopeAt Slots.scopeKit StoresGhost.opened.sessions x.rem.val)
      P.C (pqxdhSpqrModel P) uuidTryParse x r sess otr taken k m otr') :
    (w1SessKitExt A B img F peer).RecOk (storedRecord sess otr' taken) :=
  w1_recOk P (B := B) (img := img) hinjK hsub hok hrem_eq h15

/-- Extern-parametric inner `withStores_okVT_fs_ext` hypothesis on `tripleRatchetProgAtExt img.base ext_p`. -/
def WithStoresOkVTExtStmt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (ext_p : String → Option (State → State)) : Prop :=
  ∀ {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} (ctl : BitVec 64),
    Obj.Loads libsignalSessionImage img →
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyKitOkSE kit Scope encRecord ext_p →
    CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreKitOkIE img ikit ext_p →
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyVtablesOk img kit →
    IdentityVtablesOk img ikit →
    KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAtExt img.base ext_p) →
    (∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r) →
    (∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8)))
      (p : PendingPreKey),
      kit.ScopeAt Scope st0 rem r → r.currentSession = some s →
      s.pendingPreKey = some p → p.timestamp = 0) →
    (∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → r.currentSession = some s →
      s.state.pqRatchetState.length < 2 ^ 32) →
    (∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
      {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
      {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
      {otr' : OutgoingTripleRatchet (List (BitVec 8))},
      kit.addrOk x.rem.val →
      StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) P.C (pqxdhSpqrModel P) uuidTryParse
        x r sess otr taken k m otr' →
      kit.RecOk (storedRecord sess otr' taken)) →
    subroutine_ok (tripleRatchetProgAtExt img.base ext_p)
      ((tripleRatchetProgAtExt img.base ext_p).fnAddr wrapEncryptName)
      (withEnvPre (withStoresEncSpecVT_cli kit st0 ikit ist0 Scope P.C ctl uuidTryParse (pqxdhSpqrModel P) encRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))

theorem w1_inner_ok_of_vt_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext_p : String → Option (State → State))
    (B : RunBudgets) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext_p))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit) (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hVT : WithStoresOkVTExtStmt img P A ext_p)
    (hSessKit : ∀ (F : FsFiles) (peer : AddrGhost), Slots.FilesOkPeer Scope F peer.val →
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyKitOkSE
        (w1SessKitExt A B img F peer) Slots.scopeKit E2E.Record.encodeRecord ext_p)
    (hIdKit : ∀ (F : FsFiles) (peer : AddrGhost), Slots.FilesOkPeer Scope F peer.val →
      CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreKitOkIE
        img (w1IdKitExt A B img F peer) ext_p)
    (F : FsFiles) (peer : AddrGhost) (hok : Slots.FilesOkPeer Scope F peer.val) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext_p)
      ((tripleRatchetProgAtExt img.base ext_p).fnAddr wrapEncryptName)
      (withEnvPre
        (withStoresEncSpecVT_cli (w1SessKitExt A B img F peer) StoresGhost.opened.sessions
          (w1IdKitExt A B img F peer) StoresGhost.opened.identity Slots.scopeKit
          P.C 0#64 uuidTryParse (pqxdhSpqrModel P) E2E.Record.encodeRecord)
        (fun s => (w1SessKitExt A B img F peer).envOk s.fs.files ∧
          (w1IdKitExt A B img F peer).envOk s.fs.files)) :=
  hVT (kit := w1SessKitExt A B img F peer) (st0 := StoresGhost.opened.sessions)
    (ikit := w1IdKitExt A B img F peer) (ist0 := StoresGhost.opened.identity)
    (Scope := Slots.scopeKit) (encRecord := E2E.Record.encodeRecord) 0#64 himg
    (hSessKit F peer hok) (hIdKit F peer hok)
    (cliSessionStoreSpec_vtablesOk himg) (cliIdentityStoreSpec_vtablesOk himg)
    (Or.inr ⟨⟨cliSessionStoreSpec_quiet, cliIdentityStoreSpec_quiet⟩, hFs⟩)
    w1_scopeIn_ext w1_scopeKit_pendingPreKey_ts_zero w1_scopeQ_ext
    (fun haddr h15 => w1_recOk_ext P hinjK hsub hok haddr h15)

set_option maxHeartbeats 400000 in
/-- Generalizes `cliEncrypt_slot_of_inner` to arbitrary `P : PEParams`, `A : RustAlloc`, and extern
table `ext_p` under `TraceFsSound`. -/
theorem cliEncrypt_slot_of_inner_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext_p : String → Option (State → State))
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (_himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext_p))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit) (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = w1EncDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hInner : ∀ (F : FsFiles) (peer : AddrGhost), Slots.FilesOkPeer Scope F peer.val →
      subroutine_ok (tripleRatchetProgAtExt img.base ext_p)
        ((tripleRatchetProgAtExt img.base ext_p).fnAddr wrapEncryptName)
        (withEnvPre
          (withStoresEncSpecVT_cli (w1SessKitExt A B img F peer) StoresGhost.opened.sessions
            (w1IdKitExt A B img F peer) StoresGhost.opened.identity Slots.scopeKit
            P.C 0#64 uuidTryParse (pqxdhSpqrModel P) E2E.Record.encodeRecord)
          (fun s => (w1SessKitExt A B img F peer).envOk s.fs.files ∧
            (w1IdKitExt A B img F peer).envOk s.fs.files)))
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext_p)
      ((tripleRatchetProgAtExt img.base ext_p).fnAddr wrapEncryptName)
      (encSlotSpec A img S stk) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal _hL => ?_
  dsimp only [encSlotSpec, Spec.inImage, slotFrame] at hpre
  have hpre_flat : s0.mem ⊨
      ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.peerA ∧ s0.readReg64 .x3 = x.meA ∧
        s0.readReg64 .x4 = x.stores + 0xf0#64 ∧ s0.readReg64 .x5 = sessVt img ∧
        s0.readReg64 .x6 = x.stores ∧ s0.readReg64 .x7 = idVt img ∧
        s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        S.encOk x.F x.peer.val x.coins ∧ stk ≤ s0.sp.toNat ∧ x.meA ≠ 0#64⌝ ∗
      (⌜x.coins.length < 2 ^ 63⌝ ∗
      (storesAt A x.stores StoresGhost.opened ∗ protocolAddressAt A x.peer x.peerA ∗
        protocolAddressAt A x.me x.meA ∗ coinsInstalled img x.coinsP x.coins ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ A.pool ∗
        (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗
        memRegion x.ret 248 ∗ stackAt s0.sp stk ∗ R))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hfl, hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat
  obtain ⟨⟨hx0, hx1, hptLt, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfiles, hfOk, heOk, hsp_le, hme_ne⟩,
    hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hcoinsLt, hm0⟩ := hpre_flat
  obtain ⟨hokF, hokE⟩ := hok x.F x.peer.val x.me.val x.coins hfOk heOk
  set kit := w1SessKitExt A B img x.F x.peer; set ikit := w1IdKitExt A B img x.F x.peer
  set innerStk := withStoresEncStackV kit ikit; set extraStk := stk - innerStk
  have hinner_le : innerStk ≤ stk := Nat.le_trans (w1_innerStack_le_need_ext A B img x.F x.peer) hstk
  have hstk_sum : innerStk + extraStk = stk := by omega
  have hstk_split : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk := by
    rw [← hstk_sum]; exact stackAt_split_bottom s0.sp innerStk extraStk (by omega)
  have hcoins_eq : coinsInstalled img x.coinsP x.coins =
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.coinsP x.coins :=
    (Slots.coinsAt_eq_coinsInstalled img x.coinsP x.coins hcoinsLt).symm
  have hnow_eq : nowCellAt s0.sp unixEpoch = nowAt s0.sp unixEpoch := rfl
  have hssVt_eq : sessVt img = kit.ss_vt := rfl
  have hidVt_eq : idVt img = ikit.id_vt := rfl
  have hdisj := encOk₀_to_kitScopeAt (A := A) (b := img.base) (s1 := SessKit.loadShimNeed)
    (s2 := SessKit.loadPollNeed B.readFile) (s3 := SessKit.storeShimNeed)
    (s4 := SessKit.storePollNeedX) hinjK hsub hokF hokE
  have hpure_in :
      s0.readReg64 .x0 = (w1EncGhost x).ptA ∧ (s0.readReg64 .x1).toNat = (w1EncGhost x).ptext.length ∧
      (w1EncGhost x).ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = (w1EncGhost x).remA ∧
      s0.readReg64 .x3 = (w1EncGhost x).locA ∧ (w1EncGhost x).locA ≠ 0#64 ∧
      s0.readReg64 .x4 = (w1EncGhost x).ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
      s0.readReg64 .x6 = (w1EncGhost x).idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
      (w1EncGhost x).now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = (w1EncGhost x).ret ∧
      innerStk ≤ s0.sp.toNat ∧ kit.addrOk (w1EncGhost x).rem.val ∧
      ikit.addrOk (w1EncGhost x).rem.val := by
    refine ⟨hx0, hx1, hptLt, hx2, hx3, hme_ne, hx4, hssVt_eq ▸ hx5, hx6, hidVt_eq ▸ hx7,
      show unixEpoch.tvNsec.toNat < 10 ^ 9 by decide, hx8, by omega, rfl, rfl⟩
  let R_inner : SepProp :=
    w1UnusedDirsAt A x.stores StoresGhost.opened ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ R
  have hm_unpacked : s0.mem ⊨
      ((kit.storeAt (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        ikit.identityAt x.stores StoresGhost.opened.identity ∗
        w1UnusedDirsAt A x.stores StoresGhost.opened) ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.coinsP x.coins ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ A.pool ∗
      (x.ptA ↦ₛ x.ptext) ∗ nowAt s0.sp unixEpoch ∗ memRegion x.ret 248 ∗
      (memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk) ∗ R) := by
    rw [hstk_split, hcoins_eq, hnow_eq] at hm0
    exact Satisfies.mono
      (sepConj_mono_left (storesAt_opened_to_kits_ext A B img x.F x.peer x.stores hsub hokF)) hm0
  have hpre_vt : s0.mem ⊨
      (withStoresEncSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
        Slots.scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P)
        E2E.Record.encodeRecord).pre (w1EncGhost x) s0 ∗ R_inner := by
    dsimp only [withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage, w1EncGhost]
    have hgoal : s0.mem ⊨
        ⌜64 ≤ x.coins.length ∨
          (∀ r, kit.ScopeAt Slots.scopeKit StoresGhost.opened.sessions x.peer.val r →
            E2E.Record.RecordPqEmpty r)⌝ ∗
        (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.readReg64 .x0 = (w1EncGhost x).ptA ∧
          (s0.readReg64 .x1).toNat = (w1EncGhost x).ptext.length ∧
          (w1EncGhost x).ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = (w1EncGhost x).remA ∧
          s0.readReg64 .x3 = (w1EncGhost x).locA ∧ (w1EncGhost x).locA ≠ 0#64 ∧
          s0.readReg64 .x4 = (w1EncGhost x).ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
          s0.readReg64 .x6 = (w1EncGhost x).idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
          (w1EncGhost x).now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = (w1EncGhost x).ret ∧
          innerStk ≤ s0.sp.toNat ∧ kit.addrOk (w1EncGhost x).rem.val ∧
          ikit.addrOk (w1EncGhost x).rem.val⌝ ∗
        (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
          kit.storeAt (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
          ikit.identityAt x.stores StoresGhost.opened.identity ∗
          nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          memRegion x.ret 248 ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base x.coinsP x.coins ∗
          logOff img ∗ stackAt s0.sp innerStk ∗ A.pool ∗ R_inner))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hdisj, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hpure_in, ?_⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by dsimp only [R_inner]; ac_rfl)) hm_unpacked
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hgoal
  have hpre_env : s0.mem ⊨
      (withEnvPre
        (withStoresEncSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
          Slots.scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) E2E.Record.encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)).pre (w1EncGhost x) s0 ∗ R_inner :=
    withEnvPre_pre_intro ⟨hfiles, hfiles⟩ hpre_vt
  have hpre_fs : s0.mem ⊨
      (withFsInv
        (withEnvPre
          (withStoresEncSpecVT_cli kit StoresGhost.opened.sessions ikit StoresGhost.opened.identity
            Slots.scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) E2E.Record.encodeRecord)
          (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
        s0.fs.files s0.trace).pre (w1EncGhost x) s0 ∗ R_inner :=
    withFsInv_pre_intro (withFsInv_entry s0) hpre_env

  have hSub := subroutine_ok_withFsInv hFs (hInner x.F x.peer hokF) s0.fs.files s0.trace
  refine subroutine_ok.mono_outcome hSub (w1EncGhost x) R_inner s0 hpc hrun hpre_fs hal ?_
  intro sf hout
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hmpan⟩ | ⟨_c, _hex, hmex⟩ | ⟨_hoom, hmoom⟩
  ·
    refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hinv_f, hpost⟩ := withFsInv_post_elim hpost
    dsimp only [withEnvPre, withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage] at hpost
    let mrc := fun ans => (w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse ans
    have hpost_ex : sf.mem ⊨ ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
        ⌜(mrc answers).1 ≠ .error .panic ∧
          kit.callsRel StoresGhost.opened.sessions answers (mrc answers).2 ∧
          ikit.idCallsRel StoresGhost.opened.identity answers (mrc answers).2 ∧
          sf.trace = s0.trace ++ ikit.traceOfWith kit E2E.Record.encodeRecord answers (mrc answers).2⌝ ∗
        (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
          kit.storeAt (x.stores + 0xf0#64) (kit.storeFinal StoresGhost.opened.sessions answers (mrc answers).2) ∗
          ikit.identityAt x.stores (ikit.idFinal StoresGhost.opened.identity answers (mrc answers).2) ∗
          apiEncResultAt A x.ret (mrc answers).1 ∗ nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel P) answers) ∗
          logOff img ∗ stackAt s0.sp innerStk ∗ A.pool ∗ R_inner) := by
      have h1 : sf.mem ⊨ (∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(mrc answers).1 ≠ .error .panic ∧
            kit.callsRel StoresGhost.opened.sessions answers (mrc answers).2 ∧
            ikit.idCallsRel StoresGhost.opened.identity answers (mrc answers).2 ∧
            sf.trace = s0.trace ++ ikit.traceOfWith kit E2E.Record.encodeRecord answers (mrc answers).2⌝ ∗
          kit.storeAt (x.stores + 0xf0#64) (kit.storeFinal StoresGhost.opened.sessions answers (mrc answers).2) ∗
          ikit.identityAt x.stores (ikit.idFinal StoresGhost.opened.identity answers (mrc answers).2) ∗
          apiEncResultAt A x.ret (mrc answers).1 ∗ nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel P) answers) ∗
          logOff img ∗ stackAt s0.sp innerStk ∗ A.pool) ∗
          (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ R_inner) :=
        Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [mrc]; ac_rfl)) hpost
      rw [sepExists_sepConj_left, satisfies_sepExists] at h1; obtain ⟨answers, h1⟩ := h1
      rw [satisfies_sepExists]; exact ⟨answers, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) h1⟩
    rw [satisfies_sepExists] at hpost_ex; obtain ⟨answers, hpost_ans⟩ := hpost_ex
    rw [satisfies_pure_sepConj] at hpost_ans
    obtain ⟨⟨hnoPanic, hcalls, hid, htr_raw⟩, hm_f⟩ := hpost_ans
    have htr_nil : ikit.traceOfWith kit E2E.Record.encodeRecord answers (mrc answers).2 = [] :=
      cliTraceOfWith_eq_nil _ _ _
    have htr : sf.trace = s0.trace := by rw [htr_raw, htr_nil, List.append_nil]
    have hslotTr : slotTrace s0 sf := slotTrace_of_fsInv_trace_eq hinv_f htr
    obtain ⟨hmodel_eq, hnoStore, hg'_eq, hwrOk⟩ :=
      cliEncrypt_store_det P (w1EncGhost x).toEncryptGhost answers hinjK hsub hokF hcalls hid
    set resCalls := mrc answers; set e := resCalls.1; set g' := w1CliFinal x.F resCalls.2
    have hmodel_symm : (w1EncGhost x).toEncryptGhost.model P.C (pqxdhSpqrModel P) uuidTryParse
        (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)) = resCalls :=
      hmodel_eq.symm
    have hS_eval : S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = w1SlotAnsOfRc x.F resCalls :=
      (congrFun (congrFun (congrFun (congrFun (congrFun hS x.F) x.peer.val) x.me.val)
        x.ptext) x.coins).trans
        ((w1EncDef_eq_slotAnsOfRc P Scope x.F (w1EncGhost x).toEncryptGhost rfl).trans
          (congrArg (w1SlotAnsOfRc x.F) hmodel_symm))
    have hslotOut : slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf :=
      slotOut_of_rc_eq hS_eval hnoPanic hnoStore hwrOk
    have hwire42 : ∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
        m.serialized.length < 2 ^ 42 := by
      intro m hm_ok
      have hm_api : sf.mem ⊨ apiEncResultAt A x.ret (.ok (.preKeySignalMessage m)) ∗
          (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
            kit.storeAt (x.stores + 0xf0#64) (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
            ikit.identityAt x.stores (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
            nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
            protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
              ((w1EncGhost x).draws (pqxdhSpqrModel P) answers) ∗
            logOff img ∗ stackAt s0.sp innerStk ∗ A.pool ∗ R_inner) := by
        have hm_f' := hm_f
        change sf.mem ⊨ (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
          kit.storeAt (x.stores + 0xf0#64) (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
          ikit.identityAt x.stores (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
          apiEncResultAt A x.ret e ∗ nowAt s0.sp unixEpoch ∗ (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel P) answers) ∗
          logOff img ∗ stackAt s0.sp innerStk ∗ A.pool ∗ R_inner) at hm_f'
        rw [hm_ok] at hm_f'; exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm_f'
      have hmsg40 := preKeyMsg_inner_serialized_lt_of_mem hm_api
      set cliAns := w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)
      have hok_cli : ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse cliAns).1 =
          .ok (.preKeySignalMessage m) :=
        (congrArg Prod.fst hmodel_symm).trans hm_ok
      obtain ⟨r, hlr_cli⟩ := loadSession_some_of_model_ok hok_cli
      have hlr : Slots.loadRec Scope x.F x.peer.val = .ok (some r) := hlr_cli
      have hla := Slots.sessLoadAns_loadRec hokF; rw [hlr] at hla
      obtain ⟨bs, hbs, _⟩ := hokF.sessGet; rw [hbs] at hla
      have hr_sc : Scope r := by
        rcases bs with _ | ⟨_, _⟩
        · cases hla
        · obtain ⟨_, hans, _, hsc⟩ := hla; cases hans; exact hsc
      have hr_kit : Slots.scopeKit r := scopeKit_of_sub hsub r hr_sc
      exact model_preKey_serialized_lt P.C (pqxdhSpqrModel P) uuidTryParse
        (w1EncGhost x).toEncryptGhost cliAns r m hlr_cli
        (fun s k hs hk => (hr_kit.1.1 s hs).2.2 k hk) hok_cli hmsg40
    dsimp only [encSlotSpec, Spec.inImage]
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨g', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨e, ?_⟩
    have hm_reord : sf.mem ⊨
        ((kit.storeAt (x.stores + 0xf0#64)
            (kit.storeFinal StoresGhost.opened.sessions answers resCalls.2) ∗
          ikit.identityAt x.stores
            (ikit.idFinal StoresGhost.opened.identity answers resCalls.2) ∗
          w1UnusedDirsAt A x.stores StoresGhost.opened) ∗
        apiEncResultAt A x.ret e ∗ protocolAddressAt A x.peer x.peerA ∗
        protocolAddressAt A x.me x.meA ∗ (x.ptA ↦ₛ x.ptext) ∗ nowAt s0.sp unixEpoch ∗
        logOff img ∗ A.pool ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) extraStk ∗ stackAt s0.sp innerStk) ∗
        (CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.coinsP x.coins
            ((w1EncGhost x).draws (pqxdhSpqrModel P) answers)) ∗ R) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [R_inner]; ac_rfl)) hm_f
    have hm_post : sf.mem ⊨
        (storesAt A x.stores g' ∗ encResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap ∗ R) := by
      rw [hstk_split, hnow_eq, ← hg'_eq]
      refine Satisfies.mono ?_ hm_reord
      exact sepConj_mono (kits_to_storesAt_ext A B img x.F x.peer x.stores _ _)
        (sepConj_mono (apiEncResultAt_to_encResAt A x.ret e hnoStore)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (entails_anyHeap _))))))))))
    have hgoal_post : sf.mem ⊨
        ⌜slotTrace s0 sf ∧
          slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
          (∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
            m.serialized.length < 2 ^ 42)⌝ ∗
        (storesAt A x.stores g' ∗ encResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hslotTr, hslotOut, hwire42⟩, hm_post⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal_post
  ·
    refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withFsInv, withEnvPre, withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage] at hmpan
    simp only [sepConj_assoc] at hmpan
    rw [satisfies_pure_sepConj] at hmpan; obtain ⟨_, hmpan⟩ := hmpan
    rw [satisfies_pure_sepConj] at hmpan; obtain ⟨⟨_, hpan_or⟩, hm_pan⟩ := hmpan
    have hpan_out : S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = none ∨
        allocFailedIn s0 sf := by
      rcases hpan_or with halloc | ⟨answers, hloadRel, _, hp_or⟩
      · exact Or.inr halloc
      · refine Or.inl ?_
        have hp_ans : ((w1EncGhost x).model P.C (pqxdhSpqrModel P) uuidTryParse answers).1 =
            .error .panic :=
          hp_or.elim id (sendPanics_imp_model_panic P.C (pqxdhSpqrModel P) uuidTryParse
            (w1EncGhost x).toEncryptGhost answers)
        have hload_eq := cliSessLoadRel_eq_loadRec_scope hinjK hsub hokF hloadRel
        have hp_cli := model_panic_of_loadSession_eq P.C (pqxdhSpqrModel P) uuidTryParse
          (w1EncGhost x).toEncryptGhost answers
          (w1CliAnswers Scope x.F x.peer.val (w1EncKey Scope x.F x.peer.val)) hload_eq hp_ans
        exact (congrFun (congrFun (congrFun (congrFun (congrFun hS x.F) x.peer.val) x.me.val)
          x.ptext) x.coins).trans
          ((w1EncDef_eq_slotAnsOfRc P Scope x.F (w1EncGhost x).toEncryptGhost rfl).trans
            (match_panic_eq_none x.F hp_cli))
    dsimp only [encSlotSpec, Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    dsimp only [R_inner] at hm_pan; simp only [← sepConj_assoc] at hm_pan
    exact ⟨hpan_out, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
  ·
    dsimp only [withFsInv, withEnvPre, withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage] at hmex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmex
    have hmex2 := hmex.2; rw [satisfies_pure_sepConj] at hmex2; exact False.elim hmex2.1
  ·
    dsimp only [withFsInv, withEnvPre, withStoresEncSpecVT_cli,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage] at hmoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmoom
    have hmoom2 := hmoom.2; rw [satisfies_pure_sepConj] at hmoom2; exact False.elim hmoom2.1

theorem cliEncrypt_slot_of_vt_ext {img : Obj.Image}
    (P : PEParams) (A : RustAlloc) (ext_p : String → Option (State → State))
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext_p))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit) (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.encrypt = w1EncDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Scope F peer ∧ Slots.encOk₀ Scope F peer coins)
    (hVT : WithStoresOkVTExtStmt img P A ext_p)
    (hSessKit : ∀ (F : FsFiles) (peer : AddrGhost), Slots.FilesOkPeer Scope F peer.val →
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyKitOkSE
        (w1SessKitExt A B img F peer) Slots.scopeKit E2E.Record.encodeRecord ext_p)
    (hIdKit : ∀ (F : FsFiles) (peer : AddrGhost), Slots.FilesOkPeer Scope F peer.val →
      CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreKitOkIE
        img (w1IdKitExt A B img F peer) ext_p)
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext_p)
      ((tripleRatchetProgAtExt img.base ext_p).fnAddr wrapEncryptName)
      (encSlotSpec A img S stk) :=
  cliEncrypt_slot_of_inner_ext P A ext_p B S Scope himg hFs hinjK hsub hS hok
    (w1_inner_ok_of_vt_ext P A ext_p B Scope himg hFs hinjK hsub hVT hSessKit hIdKit)
    stk hstk hstk64

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
