/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendCoinsBridge
public import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPureC
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendEvalBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRecordInj

/-!
# Send Evaluation and Canonical Post-State Bridge

Connects `SessionState.messageEncryptW` and `pqSendModel` under `ModelHookBridge interp W` and
`PqxdhPartyInSpecDomain W st` to `pureEvalSendWire`, `SndWhisperRetOut`, and `SndPendingRetOut`
under the coin prefix `sendCoinsOf interp g.session.pqRatchetState r_coins`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E
open CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (interpW)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.SendWire (pqHarnessAddrBytes)
open Symbolic.Swarm.CREF.CliPure.SndPure
open Symbolic.Swarm.CREF.TR.Pure (PureRecordRepr slots_SessionScopeP slots_NonEmptyV1Q
  slots_DeserializeScopeP_Q slots_RecordScopeP slots_RecordInScopeP slots_RecordCanonical_Q)

attribute [local simp] mut_exec_pure mut_exec_throw mut_exec_get mut_exec_set
  mut_exec_modify mut_exec_modifyGet mut_exec_liftE mut_exec_bind mut_exec_onRatchet

/-! ## `messageEncryptW` to `pureEvalSendWire` -/

private theorem sendAddrs_A_eq_pqHarnessAddrBytes (W : PEParams) :
    (pqxdhSessionParams W).sendAddrs .A = some pqHarnessAddrBytes := by
  change serializedPartyAddresses CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse Party.A Party.B =
    some pqHarnessAddrBytes
  decide +kernel

theorem sendAddrs_A_getD_eq_serializeAddresses (W : PEParams) :
    ((pqxdhSessionParams W).sendAddrs .A).getD [] =
      DY.Libsignal.Composed.Refinement.Cli.serializeAddresses
        ⟨DY.Libsignal.Composed.Refinement.Cli.aliceUuid, 1⟩
        ⟨DY.Libsignal.Composed.Refinement.Cli.bobUuid, 1⟩ := by
  rw [sendAddrs_A_eq_pqHarnessAddrBytes]
  decide +kernel

private theorem fromSessionState_extra_props {PQ : Type} [Inhabited PQ] (s : SessionState PQ)
    (o : OutgoingTripleRatchet PQ) (taken : SessionState PQ)
    (h : Mut.exec OutgoingTripleRatchet.fromSessionState s = (.ok o, taken)) :
    o.localIdentityKey = s.localIdentity ∧ taken.pendingPreKey = s.pendingPreKey := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc
  · simp [hs] at h
  · simp only [hs, mut_exec_bind, mut_exec_get, mut_exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hr : s.remoteIdentity with _ | k
      · simp [hr] at h
      · simp only [hr, mut_exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
        rw [← h.1, ← h.2]
        exact ⟨rfl, rfl⟩

/-- Relates `SessionState.messageEncryptW` on `g.session` to `pureEvalSendWire`, giving the updated
encoded `pqSession` and wire bytes for both acknowledged and Alice-pending sessions. -/
theorem pureEvalSendWire_of_messageEncryptW
    {interp : ExternInterpretation} {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (pt coins : HwBytes) (msg : SignalMessage) (s : SessionState HwBytes)
    (hpend_party : g.session.pendingPreKey = true → g.party = .A)
    (hencW : Proofs.libsignal.SR.SessionState.messageEncryptW
      (cryptoOf' interp) (interpW interp) protoSignalCodec (pureSpqrOf interp)
      ((pqxdhSessionParams W).sendAddrs g.party) pt coins g.session = (.ok msg, s)) :
    let pendingAddrs := if g.session.pendingPreKey then some pqHarnessAddrBytes else none
    let wire := if g.session.pendingPreKey
      then wirePrekey :: firstMessageBody x g.session msg
      else wireWhisper :: msg.serialized
    TR.SendRetCoinsCliPure.pureEvalSendWire
      (cryptoOf' interp) (interpW interp) (spqrModelOf interp)
      (pqSession x g) pendingAddrs pt coins =
      some (encodeRecordUnderExtras (fun _ => x) { g with session := s }, wire) ∧
    s.pendingPreKey = g.session.pendingPreKey ∧
    s.receiverChains = g.session.receiverChains ∧
    ∃ salt msgPq, (spqrModelOf interp).send g.session.pqRatchetState coins =
      some (s.pqRatchetState, salt, msgPq) := by
  intro pendingAddrs wire
  obtain ⟨⟨hver, _, _, _, _, _, _, _, _, _, _⟩, _, _⟩ := reachPqInvPure_of_wfPq hwf hsess
  unfold Proofs.libsignal.SR.SessionState.messageEncryptW at hencW
  have hspqr_eq : TR.SendRetCoinsCliPure.spqrOfModel (spqrModelOf interp) =
      pureSpqrOf interp := rfl
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState g.session with ⟨err | otr, taken⟩
  · rw [hfrom] at hencW; cases hencW
  · obtain ⟨hpqr, hrc_taken⟩ :=
      TR.SendRetCoinsCliPure.mut_exec_fromSessionState_props g.session otr taken hfrom
    obtain ⟨hloc, hpend_taken⟩ := fromSessionState_extra_props g.session otr taken hfrom
    rw [hfrom] at hencW; dsimp only at hencW
    cases hp : g.session.pendingPreKey with
    | false =>
      have had : g.session.encryptAddresses ((pqxdhSessionParams W).sendAddrs g.party) = none := by
        simp [SessionState.encryptAddresses, hp]
      have hppk : (pqSession x g).pendingPreKey = none := by simp [pqSession, hp]
      have hpkyb : (pqSession x g).pendingKyberPreKey = none := by simp [pqSession, hp]
      rw [had, ← hspqr_eq] at hencW
      rcases henc_otr : Mut.exec (Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW
          (cryptoOf' interp) (interpW interp) protoSignalCodec
          (TR.SendRetCoinsCliPure.spqrOfModel (spqrModelOf interp)) pt none coins) otr with
        ⟨e | sm, otr'⟩
      · rw [henc_otr] at hencW; cases hencW
      · rw [henc_otr] at hencW; dsimp only at hencW
        have hpair : sm = msg ∧ otr'.applyToSessionState taken = s :=
          ⟨by injection hencW with h1 _; injection h1, by injection hencW⟩
        rcases hpair with ⟨rfl, rfl⟩
        obtain ⟨_, salt, msgPq, hsend⟩ := TR.SendRetCoinsCliPure.mut_exec_encryptW_ok_inv henc_otr
        have hs_pend : (otr'.applyToSessionState taken).pendingPreKey = false :=
          hpend_taken.trans hp
        have hwire_eq : wire = wireWhisper :: sm.serialized := by simp [wire, hp]
        have heval_eq : TR.SendRetCoinsCliPure.pureEvalSendWire
            (cryptoOf' interp) (interpW interp) (spqrModelOf interp)
            (pqSession x g) pendingAddrs pt coins =
            some (encodeRecordUnderExtras (fun _ => x) { g with session := otr'.applyToSessionState taken },
              wire) := by
          unfold TR.SendRetCoinsCliPure.pureEvalSendWire
          rw [pqSession_state, hfrom]; dsimp only
          rw [hppk, hpkyb]; dsimp only
          rw [henc_otr]; dsimp only
          rw [hwire_eq, encodeRecordX_eq_encodeRecord_pqSession]
          unfold pqSession
          rw [hs_pend]; rfl
        exact ⟨heval_eq, hs_pend, hrc_taken, salt, msgPq, hpqr ▸ hsend⟩
    | true =>
      have hpartyA := hpend_party hp
      have had : g.session.encryptAddresses ((pqxdhSessionParams W).sendAddrs g.party) =
          some pqHarnessAddrBytes := by
        simp [SessionState.encryptAddresses, hp, hpartyA, sendAddrs_A_eq_pqHarnessAddrBytes]
      have hpad : pendingAddrs = some pqHarnessAddrBytes := by dsimp [pendingAddrs]; rw [hp]; rfl
      have hppk : (pqSession x g).pendingPreKey = some x.pending := by simp [pqSession, hp]
      have hpkyb : (pqSession x g).pendingKyberPreKey = x.kyber := by simp [pqSession, hp]
      rw [had, ← hspqr_eq] at hencW
      rcases henc_otr : Mut.exec (Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW
          (cryptoOf' interp) (interpW interp) protoSignalCodec
          (TR.SendRetCoinsCliPure.spqrOfModel (spqrModelOf interp)) pt
          (some pqHarnessAddrBytes) coins) otr with ⟨e | sm, otr'⟩
      · rw [henc_otr] at hencW; cases hencW
      · rw [henc_otr] at hencW; dsimp only at hencW
        have hpair : sm = msg ∧ otr'.applyToSessionState taken = s :=
          ⟨by injection hencW with h1 _; injection h1, by injection hencW⟩
        rcases hpair with ⟨rfl, rfl⟩
        obtain ⟨_, salt, msgPq, hsend⟩ := TR.SendRetCoinsCliPure.mut_exec_encryptW_ok_inv henc_otr
        have hs_pend : (otr'.applyToSessionState taken).pendingPreKey = true :=
          hpend_taken.trans hp
        have hver8 : BitVec.ofNat 8 g.session.version.toNat = 4#8 := by
          simp [SessionState.version, hver]
        have hbody : (PreKeySignalMessage.new 4#8 (pqSession x g).localRegistrationId
            x.pending.preKeyId x.pending.signedPreKeyId
            (x.kyber.map fun k => ⟨k.preKeyId, k.ciphertext⟩)
            x.pending.baseKey otr.localIdentityKey sm).serialized =
            firstMessageBody x g.session sm := by
          unfold firstMessageBody; rw [hver8, hloc]; rfl
        have hwire_eq : wire = wirePrekey :: firstMessageBody x g.session sm := by
          simp [wire, hp]
        have heval_eq : TR.SendRetCoinsCliPure.pureEvalSendWire
            (cryptoOf' interp) (interpW interp) (spqrModelOf interp)
            (pqSession x g) pendingAddrs pt coins =
            some (encodeRecordUnderExtras (fun _ => x) { g with session := otr'.applyToSessionState taken },
              wire) := by
          unfold TR.SendRetCoinsCliPure.pureEvalSendWire
          rw [pqSession_state, hfrom]; dsimp only
          rw [hppk, hpkyb, hpad]; dsimp only
          rw [henc_otr]; dsimp only
          rw [hbody, hwire_eq, encodeRecordX_eq_encodeRecord_pqSession]
          unfold pqSession
          rw [hs_pend]; rfl
        exact ⟨heval_eq, hs_pend, hrc_taken, salt, msgPq, hpqr ▸ hsend⟩

/-! ## Post-Session Canonicality and Return Contracts -/

theorem postSend_canon_of_reachPq {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g g₀' : GhostState HwBytes} {s : SessionState HwBytes}
    (hR' : ReachablePqxdhSession W me x g₀') (hs' : g₀'.session = s)
    (hlen32 : (encodeRecordUnderExtras (fun _ => x) { g with session := s }).length < 2 ^ 32) :
    let sess' := pqSession x { g with session := s }
    let retState := encodeRecordUnderExtras (fun _ => x) { g with session := s }
    slots_RecordCanonical_Q slots_NonEmptyV1Q retState sess' ∧
    slots_RecordInScopeP ⟨some sess'⟩ ∧
    slots_RecordScopeP slots_NonEmptyV1Q ⟨some sess'⟩ ∧
    sess'.state.remoteIdentity.isSome = true := by
  subst hs'
  intro sess' retState
  obtain ⟨_, hseeds₀, hrcLe₀, _, ⟨rem, hrem₀⟩, hrep₀, _, hts, _, habk, hkyb₀⟩ := reachPq_inv hR'
  have hkyb : ∀ k, (pqSession x { g with session := g₀'.session }).pendingKyberPreKey = some k →
      k.ciphertext.length < 2 ^ 20 := by
    intro k hk
    simp only [pqSession_pendingKyberPreKey] at hk
    split at hk
    · have hklen := hkyb₀ k hk; omega
    · cases hk
  have hscope_in : slots_RecordInScopeP ⟨some sess'⟩ := by
    intro sx hsx; injection hsx with hsx'; subst hsx'
    refine ⟨hseeds₀, by dsimp [sess', pqSession]; unfold maxReceiverChains at hrcLe₀; omega,
      fun k hk => by have := hkyb k hk; omega⟩
  have hscope_q : slots_RecordScopeP slots_NonEmptyV1Q ⟨some sess'⟩ :=
    recordScopeP_of_encodeRecordX_length x { g with session := g₀'.session } hlen32
  have hrepr : PureRecordRepr ⟨some sess'⟩ := by
    intro sx hsx; injection hsx with hsx'; subst hsx'
    refine ⟨hrep₀.1, hrep₀.2, ?_, by simp only [sess', pqSession_aliceBaseKey]; omega⟩
    dsimp [Session.Wf, sess', pqSession]; cases g₀'.session.pendingPreKey <;> rfl
  have hsp : slots_SessionScopeP sess' := by
    refine ⟨hrcLe₀, fun p hp => ?_, fun k hk => ?_,
      Or.inr (by simpa only [sess', pqSession_aliceBaseKey] using habk)⟩
    · simp only [sess', pqSession_pendingPreKey] at hp
      split at hp
      · injection hp with hp'; subst hp'; exact hts
      · cases hp
    · simp only [sess', pqSession_pendingKyberPreKey] at hk
      split at hk
      · exact hkyb₀ k hk
      · cases hk
  have hdeser : slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some sess'⟩ :=
    ⟨⟨hscope_in, hscope_q, hrepr⟩, sess', rfl, hsp⟩
  have henc : retState = CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩ :=
    encodeRecordX_eq_encodeRecord_pqSession x { g with session := g₀'.session }
  have hcanon : slots_RecordCanonical_Q slots_NonEmptyV1Q retState sess' :=
    ⟨henc, hdeser, pureBinCanonSession_of_deserializeScopeP_Q_any hdeser⟩
  have hrem_some : sess'.state.remoteIdentity.isSome = true := by
    change g₀'.session.remoteIdentity.isSome = true
    rw [hrem₀]; rfl
  exact ⟨hcanon, hscope_in, hscope_q, hrem_some⟩

/-- Establishes `SndWhisperRetOut` from a successful `pqSendModel` run on an acknowledged session. -/
theorem sndWhisperRetOut_of_pqSendModel
    {interp : ExternInterpretation} {W : PEParams} (hb : ModelHookBridge interp W)
    (r : ProtocolSetup) (p : Participant)
    {st st' : PqParty} {x : RecordExtras} {g : GhostState HwBytes}
    {pt r_coins wire : HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hpfalse : g.session.pendingPreKey = false)
    (hooo : SpqrOooBounded g.session.pqRatchetState)
    (hpt : pt.length < 2 ^ 32) (hrcoins : r_coins.length = 64)
    (hmodel : pqSendModel W st pt r_coins = some (some (st', wire))) :
    let coins := sendCoinsOf interp g.session.pqRatchetState r_coins
    let retState := encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams W).send g pt r_coins).1
    SndWhisperRetOut interp r p (encodeRecordUnderExtras (fun _ => x) g) pt r_coins
      (sendMidOf coins) retState wire := by
  intro coins retState
  obtain ⟨msg, s, _, henc, _, _, hsend1, _, hwire⟩ := pqSendModel_eq_some_some hsess hmodel
  have hmsg_lt := pqSendModel_wire_lt_2_64 hwf hsess hpt hmodel
  have hencW₀ := (messageEncrypt_eq_messageEncryptW_of_bridge hb
    ((pqxdhSessionParams W).sendAddrs g.party) pt r_coins g.session).symm.trans henc
  have hencW : Proofs.libsignal.SR.SessionState.messageEncryptW
      (cryptoOf' interp) (interpW interp) protoSignalCodec (pureSpqrOf interp)
      ((pqxdhSessionParams W).sendAddrs g.party) pt coins g.session = (.ok msg, s) := by
    rw [sessionState_messageEncryptW_sendCoinsOf interp (cryptoOf' interp) (interpW interp)
      protoSignalCodec ((pqxdhSessionParams W).sendAddrs g.party) pt hrcoins g.session]
    exact hencW₀
  obtain ⟨heval, hs_pend, hs_rc, salt, msgPq, hsend⟩ :=
    pureEvalSendWire_of_messageEncryptW hwf hsess pt coins msg s
      (fun hp => by rw [hpfalse] at hp; cases hp) hencW
  have hs_pend_false : s.pendingPreKey = false := hs_pend.trans hpfalse
  have hrc₀ := recordCanonical_Q_of_wfPq hwf hsess
  have hlen31 := (reachPqInvPure_of_wfPq hwf hsess).2.2
  have hrec_lt₀ : (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩).length <
      2 ^ 32 - 2 ^ 20 := by
    rw [← encodeRecordX_eq_encodeRecord_pqSession]; omega
  obtain ⟨hooo', hpost32_rec⟩ := TR.SendRetCoinsCliPure.encodeRecord_lt_32_of_send_growth
    interp (pqSession x g) s coins salt msgPq hrc₀.2.2 hooo hrec_lt₀ hs_rc hsend
  have hsess_upd : { pqSession x g with state := s } = pqSession x { g with session := s } := by
    simp [pqSession, hpfalse, hs_pend_false]
  rw [hsess_upd, ← encodeRecordX_eq_encodeRecord_pqSession] at hpost32_rec
  have hret_eq : retState = encodeRecordUnderExtras (fun _ => x) { g with session := s } := by
    dsimp [retState]; rw [hsend1]; rfl
  obtain ⟨g₀', hR', _, hs'⟩ := reachPq_afterSend_of_wfPq hwf hsess henc
  obtain ⟨hrc', hscope_in', hscope_q', hrem_some'⟩ := postSend_canon_of_reachPq hR' hs' hpost32_rec
  refine ⟨by rw [hret_eq]; omega, hmsg_lt, ?_, ?_⟩
  · intro _ hfit
    rw [hret_eq] at hfit ⊢
    exact ⟨pqSession x { g with session := s }, hrc', hscope_in', hscope_q', hrem_some',
      by omega, pqSession_pendingPreKey_of_false x { g with session := s } hs_pend_false,
      hfit, hooo'⟩
  · intro _
    refine ⟨pqSession x g, coins, hrc₀, sendMidOf_cases coins,
      sendCoinsOf_prefix interp g.session.pqRatchetState r_coins, ?_⟩
    rw [hret_eq, hwire]
    simpa [hpfalse] using heval

/-- Establishes `SndPendingRetOut` from a successful `pqSendModel` run on Alice's pending-prekey
session. -/
theorem sndPendingRetOut_of_pqSendModel
    {interp : ExternInterpretation} {W : PEParams} (hb : ModelHookBridge interp W)
    (r : ProtocolSetup)
    {st st' : PqParty} {x : RecordExtras} {g : GhostState HwBytes}
    {pt r_coins wire : HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hpend : g.session.pendingPreKey = true) (hpartyA : g.party = .A)
    (hpt : pt.length < 2 ^ 32) (hrcoins : r_coins.length = 64)
    (hmodel : pqSendModel W st pt r_coins = some (some (st', wire))) :
    let coins := sendCoinsOf interp g.session.pqRatchetState r_coins
    let retState := encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams W).send g pt r_coins).1
    SndPendingRetOut interp r (encodeRecordUnderExtras (fun _ => x) g) pt r_coins
      (sendMidOf coins) retState wire := by
  intro coins retState
  obtain ⟨msg, s, _, henc, _, _, hsend1, _, hwire⟩ := pqSendModel_eq_some_some hsess hmodel
  have hmsg_lt := pqSendModel_wire_lt_2_64 hwf hsess hpt hmodel
  have hencW₀ := (messageEncrypt_eq_messageEncryptW_of_bridge hb
    ((pqxdhSessionParams W).sendAddrs g.party) pt r_coins g.session).symm.trans henc
  have hencW : Proofs.libsignal.SR.SessionState.messageEncryptW
      (cryptoOf' interp) (interpW interp) protoSignalCodec (pureSpqrOf interp)
      ((pqxdhSessionParams W).sendAddrs g.party) pt coins g.session = (.ok msg, s) := by
    rw [sessionState_messageEncryptW_sendCoinsOf interp (cryptoOf' interp) (interpW interp)
      protoSignalCodec ((pqxdhSessionParams W).sendAddrs g.party) pt hrcoins g.session]
    exact hencW₀
  obtain ⟨heval, hs_pend, hs_rc, salt, msgPq, hsend⟩ :=
    pureEvalSendWire_of_messageEncryptW hwf hsess pt coins msg s
      (fun _ => hpartyA) hencW
  have hs_pend_true : s.pendingPreKey = true := hs_pend.trans hpend
  have hrc₀ := recordCanonical_Q_of_wfPq hwf hsess
  refine ⟨hmsg_lt, ?_⟩
  intro sess hrc_sess _ _ _ _ hrec_lt hooo_sess
  have hsess_eq : sess = pqSession x g := recordCanonical_Q_inj hrc_sess hrc₀
  subst hsess_eq
  have hrec_lt₀ : (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩).length <
      2 ^ 32 - 2 ^ 20 := by
    rw [← encodeRecordX_eq_encodeRecord_pqSession]; exact hrec_lt
  obtain ⟨_, hpost32_rec⟩ := TR.SendRetCoinsCliPure.encodeRecord_lt_32_of_send_growth
    interp (pqSession x g) s coins salt msgPq hrc₀.2.2 hooo_sess hrec_lt₀ hs_rc hsend
  have hsess_upd : { pqSession x g with state := s } = pqSession x { g with session := s } := by
    simp [pqSession, hpend, hs_pend_true]
  rw [hsess_upd, ← encodeRecordX_eq_encodeRecord_pqSession] at hpost32_rec
  have hret_eq : retState = encodeRecordUnderExtras (fun _ => x) { g with session := s } := by
    dsimp [retState]; rw [hsend1]; rfl
  obtain ⟨g₀', hR', _, hs'⟩ := reachPq_afterSend_of_wfPq hwf hsess henc
  obtain ⟨hrc', hscope_in', hscope_q', hrem_some'⟩ := postSend_canon_of_reachPq hR' hs' hpost32_rec
  have hpwc' : PendingWireRecCanon retState := by
    rw [hret_eq]
    exact ⟨pqSession x { g with session := s }, hrc', hscope_in', hscope_q', hrem_some', by omega⟩
  refine ⟨hpwc', coins, sendMidOf_cases coins,
    sendCoinsOf_prefix interp g.session.pqRatchetState r_coins, ?_⟩
  rw [hret_eq, hwire]
  simpa [hpend] using heval

end Symbolic.Swarm.CREF.Cli.Slots
