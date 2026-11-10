/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts
public import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendEvalBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRecordInj
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRetBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendSlot
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlotsSend
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.SendWire.RecvSimV3SendPure
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPure
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L03StickyAndBridgeAPt
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L04BridgeBQuietFail
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L08SlotSendCli
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.PendingPreKey

/-!
# Whisper `send` Slot Branch

Proves `send_w_branch`: preservation of `PqTurnSim1A` and `UAInv` across an exit-`0` Whisper
`send` call (`¬ PureRecPending` on the caller's clean record), parameterized by `XlateInvSpec`
and `WhisperEncryptStepSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.SendW

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant Traceful)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (RunEvent CliEvent)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Composed.Refinement
  (Step VisEntry ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost ExplainsClassical
   pendingPreKey runTrace runTraceMoves gamma callStarts)
open _root_.DY.Libsignal.Composed.Refinement.Cli
  (CliCall CliTurn DirectorySnapshot PqModelRel CollisionAfterExplainedPrefixClassical ReadCollisionCliClassical runEventOf runInput peerOf
   BobCallAllowed FilesBounded InputsFor ModelAgree ExternContractsHoldCli cliEntryEvents
   cliExitEvents StdinBounded coinsLen scrub ValidCall)
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
  (PqTurnSim1A toCliCallNone clean_dirs_caller_eq inputsFor_toCliCallNone)
open _root_.DY.Libsignal.TripleRatchet (TRState isCurrentSnapshot)
open CryptoVerification.E2E (PEParams encodeRecordUnderExtras pqxdhSessionParams)
open CryptoVerification.SignalSession
  (Inputs Address partyAddress encodeDir filesOf pqSendInputs pqSendModel)
open Symbolic.Proofs.Swarm.UA.Defs
  (UASlotPost UAInv XlateInvSpec AliceRecordPendingInSession
   callsOf flatEvents failedSend runOk)
open Symbolic.Proofs.Swarm.UA.Base
  (callsOf_append callsOf_run_call schedFits_of_append flatEvents_append flatEvents_run_call
   callStarts_flatEvents_length collisionAtCli_append)
open Symbolic.Proofs.Swarm.UA.PendingPreKey
  (aliceNotPendingOn_of_explains_append aliceRecordPendingInSession_of_explains_append
   aliceRecordPendingInSession_of_not_pending pendingPreKey_eq_none_of_initiator_false
   handshakeSessionValid_reachable modelRunWF_reachable)
open Symbolic.Swarm.CREF
  (compSemOf SemReady compSemOf_ready SpqrOooBounded)
open Symbolic.Swarm.CREF.CliPure (leakRecords_party_eq_of_cliNextCall)
open Symbolic.Swarm.CREF.CliPure.SndPure
  (PureRecPending not_alice_and_aliceInitPending_of_not_recPending snd_ret_eval_clause
   snd_stateRel_keyShape_sendGhost pureCRel_trRecordStateInv ns_ne_u32Max_of_trNsBound
   pqStateOf_of_canonical_Q_pend)
open Symbolic.Swarm.CREF.Cli
  (interpOfParams externContractsHoldCli_interpOfParams modelAgree_interpOfParams
   modelHookBridge_interpOfParams ModelHookBridge pqDispatch_send_party
   reachPqInvPure_of_wfPq recordCanonical_Q_of_wfPq
   peerOf_eq_addrE_other inputsEquiv_pqSendInputs PqPartyInv pqPartyInv_of_pqSendModel
   scrub_filesOf_pqInputs_accept pqSendModel_some_session_oneTime records_of_pqPartyInv)
open Symbolic.Swarm.CREF.Cli.Slots
  (pqObserve_send_exited_cases recPending_encodeRecordX_iff recPending_iff_pureRecPending
   singleSession_encodeRecordX_of_wfPq
   sndWhisperRetOut_of_pqSendModel cliEntryEvents_of_send cliExitEvents_of_send_ok)
open Symbolic.Swarm.Coinsplit.Lift (CliLiveAtCli explainsCli_toClean)

attribute [local instance 2000]
  _root_.DY.Libsignal.Composed.instBytesFunctor_symbolic _root_.DY.Libsignal.Composed.instBytesLength_symbolic
  _root_.DY.Libsignal.Composed.instAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instExecTraceTypes_symbolic
  _root_.DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instHasExecBytes
  _root_.DY.Libsignal.Composed.instHasExecEntryT _root_.DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasExecTrace _root_.DY.Libsignal.Composed.instHasSubF
  _root_.DY.Libsignal.Composed.instHasSubFAttackerKnowledge _root_.DY.Libsignal.Composed.instHasSubFLength
  _root_.DY.Libsignal.Composed.HasExecBytes.toPQXDHExecBytes _root_.DY.Libsignal.Composed.toTripleRatchet
  _root_.DY.Libsignal.Composed.toPQXDHSpqr

/-- Step-level clean-explanation extension for an exit-`0` Whisper `send` run. -/
def WhisperEncryptStepSpec : Prop :=
  ∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry} {evs_pre : List CliEvent}
    {ev : RunEvent} {p : Participant} {peer : Address} {out coins : HwBytes}
    {stateIdx₀ : Nat} {st₀ : TRState},
    ProtocolSetupWF r → SemReady interp' r S →
    ExplainsClassical interp' r S g₀ ss₀ vis₀ evs_pre →
    ¬ ReadCollisionCliClassical interp' r S g₀ ss₀ evs_pre →
    ev.party = p →
    ev.cmd = .send peer →
    ev.exit = some (0, out) →
    ((_root_.DY.PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run
      (runTrace r ss₀)).1 = some st₀ →
    isCurrentSnapshot (runTrace r ss₀) stateIdx₀ = true →
    st₀.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max →
    pendingPreKey (runTrace r ss₀) stateIdx₀ = none →
    coins <+: ev.coins →
    (coins.length = 0 ∨ coins.length = 32 ∨ coins.length = 64) →
    out = wireWhisperTag :: gamma interp' S
      (Symbolic.Swarm.CREF.SendWire.sendGhost g₀ (runTrace r ss₀).length ev.input coins)
      (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st₀ coins.length
        (runTrace r ss₀).length) →
    ∃ g' ss' vis',
      ExplainsClassical interp' r S g' ss' vis' (evs_pre ++ [.run ev]) ∧
      ¬ ReadCollisionCliClassical interp' r S g' ss' (evs_pre ++ [.run ev])

private theorem postSend_not_pending
    {interp' : ExternInterpretation} {P : PEParams} (hb' : ModelHookBridge interp' P)
    {st st' : CryptoVerification.SignalSession.PqParty}
    {x : CryptoVerification.E2E.RecordExtras}
    {g_st : CryptoGames.LibsignalSession.GhostState HwBytes}
    {pt r_coins out : HwBytes}
    (hwf_st : CryptoVerification.SignalSession.PqxdhPartyInSpecDomain P st)
    (hsess : st.session = some (x, g_st))
    (hlen31 : (encodeRecordUnderExtras (fun _ => x) g_st).length < 2 ^ 31)
    (hp_b : g_st.session.pendingPreKey = false)
    (hooo₀ : SpqrOooBounded g_st.session.pqRatchetState)
    (hcoins : r_coins.length = 64)
    (hmod' : pqSendModel P st pt r_coins = some (some (st', out))) :
    ∀ sess,
      Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
        Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q
        (encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams P).send g_st pt r_coins).1) sess →
      sess.pendingPreKey = none := by
  obtain ⟨msg_s, s_post, _, henc_s, _, _, hsend1, _, _⟩ :=
    Symbolic.Swarm.CREF.Cli.Slots.pqSendModel_eq_some_some hsess hmod'
  have hencW₀ := (Symbolic.Swarm.CREF.Cli.messageEncrypt_eq_messageEncryptW_of_bridge hb'
    ((pqxdhSessionParams P).sendAddrs g_st.party) pt r_coins g_st.session).symm.trans henc_s
  have hencW : Proofs.libsignal.SR.SessionState.messageEncryptW
      (Proofs.libsignal.Hooks2.cryptoOf' interp') (Proofs.libsignal.SR.interpW interp')
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec
      (Symbolic.Swarm.CREF.Cli.pureSpqrOf interp')
      ((pqxdhSessionParams P).sendAddrs g_st.party) pt
      (Symbolic.Swarm.CREF.Cli.Slots.sendCoinsOf interp' g_st.session.pqRatchetState r_coins)
      g_st.session = (.ok msg_s, s_post) := by
    rw [Symbolic.Swarm.CREF.Cli.Slots.sessionState_messageEncryptW_sendCoinsOf interp'
      (Proofs.libsignal.Hooks2.cryptoOf' interp') (Proofs.libsignal.SR.interpW interp')
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec
      ((pqxdhSessionParams P).sendAddrs g_st.party) pt hcoins g_st.session]
    exact hencW₀
  obtain ⟨_, hs_pend, hs_rc, salt_s, msgPq_s, hsend_spqr⟩ :=
    Symbolic.Swarm.CREF.Cli.Slots.pureEvalSendWire_of_messageEncryptW
      hwf_st hsess pt _ msg_s s_post
      (fun hp => by rw [hp_b] at hp; cases hp) hencW
  have hs_pend_false : s_post.pendingPreKey = false := hs_pend.trans hp_b
  have hrc₀ := recordCanonical_Q_of_wfPq hwf_st hsess
  have hrec_lt₀ :
      (CryptoVerification.E2E.Record.encodeRecord
        ⟨some (Symbolic.Swarm.CREF.Cli.pqSession x g_st)⟩).length < 2 ^ 32 - 2 ^ 20 := by
    rw [← Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession]; omega
  obtain ⟨_, hpost32_rec⟩ :=
    Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encodeRecord_lt_32_of_send_growth
      interp' (Symbolic.Swarm.CREF.Cli.pqSession x g_st) s_post _ salt_s msgPq_s
      hrc₀.2.2 hooo₀ hrec_lt₀ hs_rc hsend_spqr
  have hsess_upd :
      { Symbolic.Swarm.CREF.Cli.pqSession x g_st with state := s_post } =
        Symbolic.Swarm.CREF.Cli.pqSession x { g_st with session := s_post } := by
    simp [Symbolic.Swarm.CREF.Cli.pqSession, hp_b, hs_pend_false]
  rw [hsess_upd, ← Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_encodeRecord_pqSession]
    at hpost32_rec
  obtain ⟨_, hR', _, hs'⟩ :=
    Symbolic.Swarm.CREF.Cli.Slots.reachPq_afterSend_of_wfPq hwf_st hsess henc_s
  obtain ⟨hcan_ret, _, _, _⟩ :=
    Symbolic.Swarm.CREF.Cli.Slots.postSend_canon_of_reachPq hR' hs' hpost32_rec
  have hp_ret_none :
      (Symbolic.Swarm.CREF.Cli.pqSession x { g_st with session := s_post }).pendingPreKey = none := by
    simp [Symbolic.Swarm.CREF.Cli.pqSession, hs_pend_false]
  intro sess hcan
  have hcan' :
      Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q
        Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q
        (encodeRecordUnderExtras (fun _ => x) { g_st with session := s_post }) sess := by
    rwa [hsend1] at hcan
  exact (Symbolic.Swarm.CREF.Cli.Slots.recordCanonical_Q_inj hcan_ret hcan') ▸ hp_ret_none

private theorem send_run_noStart {r : ProtocolSetup} {c : CliCall} {peer : Address} {out : HwBytes}
    (hcmd : c.cmd = .send peer) :
    ∀ ev', .run ev' ∈ [CliEvent.run (runEventOf c (some (0, out)))] →
      (∀ p d, ev'.cmd ≠ .init p d) ∧
      (ev'.party = r.alice → ∀ p, ev'.cmd = .recv p → ev'.input.head? = some wireWhisperTag) := by
  intro ev' hev'
  simp only [List.mem_singleton, CliEvent.run.injEq] at hev'
  subst hev'
  have hc_eq : (runEventOf c (some (0, out))).cmd = .send peer := hcmd
  refine ⟨?_, ?_⟩
  · intro _ _ hc
    rw [hc_eq] at hc
    cases hc
  · intro _ _ hc
    rw [hc_eq] at hc
    cases hc

/-- Invariant preservation for an exit-`0` Whisper `send` run (`¬ PureRecPending` on the caller's
clean record). -/
theorem send_w_branch
    (hXInv : XlateInvSpec)
    (hWStep : WhisperEncryptStepSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {evs_pre : List CliEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hp : c.party = r.alice ∨ c.party = r.bob)
    (hcmd : c.cmd = .send (peerOf r c.party))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 64)
    (hsb : c.stdin.length < 2 ^ 32)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hsent : t.sent.length < 2 ^ 32 - 1)
    (hrec_ne : t.records r c.party ≠ none)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files)))
    (hcode0 : code = 0)
    (hnpend_t : ∀ rec_, t_clean.leakRecords r c.party = some rec_ →
      ¬ Symbolic.Swarm.CREF.CliPure.SndPure.PureRecPending rec_) :
    UASlotPost interp P r t t_clean c code out files accepted evs_pre := by
  subst hcode0
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hagree' : ModelAgree interp' P := (modelAgree_interpOfParams interp P).mpr hagree
  have hb' : ModelHookBridge interp' P := modelHookBridge_interpOfParams hagree
  let c1 := toCliCallNone c
  have hcmd1 : c1.cmd = .send (peerOf r c1.party) := hcmd
  obtain ⟨hd_eq, hrec_eq, hbca1⟩ := clean_dirs_caller_eq hwf hsim hbca hp
  have hrec_ne1 : t_clean.records r c1.party ≠ none := by
    change t_clean.records r c.party ≠ none; rwa [hrec_eq]
  have hfb1 : FilesBounded (t_clean.dirs c1.party) := hd_eq.symm ▸ hfb
  have hsent1 : t_clean.sent.length < 2 ^ 32 - 1 := hsim.sent_eq.symm ▸ hsent
  have hnext1 : ValidCall interp' r t_clean c1 := by
    refine ⟨by simpa [c1, toCliCallNone, hcmd, coinsLen] using hcoins,
      by simpa [StdinBounded, c1, toCliCallNone, hcmd] using hsb, hfb1, hbca1, ?_⟩
    dsimp only [c1, toCliCallNone]; rw [hcmd]
    exact ⟨hp, rfl, rfl, hsent1, hrec_ne1⟩
  have hin1 : InputsFor c1 (t_clean.dirs c1.party) i := hd_eq.symm ▸ inputsFor_toCliCallNone hbun hin
  obtain ⟨st, hwf_st, hrec_st, hinvP⟩ := pqDispatch_send_party hsim.dirInv hbca1 hp hfb1
  have hcmd' : c1.cmd = .send (partyAddress st.party.other) := by
    rw [peerOf_eq_addrE_other, ← hinvP.party_eq] at hcmd1; exact hcmd1
  let coinsVec : List.Vector (BitVec 8) 64 := ⟨c1.coins, hcoins⟩
  have hi' : InputsFor c1 (filesOf (encodeDir P st)) i := by rwa [hinvP.dir_eq] at hin1
  have hobs_eq := (PqModelRel.exited_iff.mp hRel).send st c1.stdin coinsVec hwf_st hsb
    (inputsEquiv_pqSendInputs hi' hcmd' rfl rfl)
  cases hsess : st.session with
  | none =>
    exfalso; apply hrec_ne1; simpa [hsess] using hrec_st
  | some xg =>
    rcases xg with ⟨x, g_st⟩
    let rec_ := encodeRecordUnderExtras (fun _ => x) g_st
    have hrec_t : t_clean.records r c1.party = some rec_ := by simpa [hsess] using hrec_st
    have hleak_rec : t_clean.leakRecords r c.party = some rec_ :=
      (leakRecords_party_eq_of_cliNextCall hnext1).trans hrec_t
    have hss := singleSession_encodeRecordX_of_wfPq hwf_st hsess
    have hlen31 : rec_.length < 2 ^ 31 := (reachPqInvPure_of_wfPq hwf_st hsess).2.2
    have hreclen : rec_.length < 2 ^ 32 - 2 ^ 20 := by omega
    have hnpend_pure : ¬ PureRecPending rec_ := hnpend_t rec_ hleak_rec
    have hp_b : g_st.session.pendingPreKey = false := by
      cases hp_v : g_st.session.pendingPreKey
      · rfl
      · exfalso
        exact hnpend_pure
          (recPending_iff_pureRecPending.mp ((recPending_encodeRecordX_iff hwf_st hsess).mpr hp_v))
    rcases pqObserve_send_exited_cases hobs_eq with ⟨_, st', hmod, rfl⟩ | ⟨h01, _, _, _⟩
    · have hmod' : pqSendModel P st c.stdin c.coins = some (some (st', out)) := hmod
      obtain ⟨hst', hsub⟩ := pqPartyInv_of_pqSendModel hinvP hwf_st hmod'
      let files₀ := filesOf ((pqSendInputs P st c1.stdin coinsVec).files ++ encodeDir P st')
      have hscr : scrub files₀ = filesOf (encodeDir P st') :=
        scrub_filesOf_pqInputs_accept P st st' _ [] _ _
          (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
      let retState := encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams P).send g_st c.stdin c.coins).1
      obtain ⟨t_clean', accepted', hsim', hlive_step⟩ :=
        Symbolic.Swarm.Coinsplit.Lift.L08.slot_send_cli_gen
          Symbolic.Swarm.Coinsplit.Lift.L02.outcomeFaithfulCli_of_goodExit0Cut
          Symbolic.Swarm.Coinsplit.Lift.L03.bridgeA_pt
          Symbolic.Swarm.Coinsplit.Lift.L04.bridgeB_quiet_fail
          interp P r hext hagree hwf (σ_pre := flatEvents evs_pre)
          hsim hp hcmd hbun hcoins hsb hfb hbca hsent hrec_ne hin hRel
      have hlr_clean' : t_clean'.leakRecords r r.alice = t_clean'.records r r.alice :=
        congrFun (CliTurn.leakRecords_eq_records_of_bobOff_false hsim'.clean_bobOff) r.alice
      have hlr_clean : t_clean.leakRecords r r.alice = t_clean.records r r.alice :=
        congrFun (CliTurn.leakRecords_eq_records_of_bobOff_false hsim.clean_bobOff) r.alice
      have hdirs_alice' : t_clean'.dirs r.alice = (CliTurn.after t r c 0 out files₀).dirs r.alice :=
        hsim'.dirs_other r.alice hwf.1
      have hdirs_alice : t_clean.dirs r.alice = t.dirs r.alice :=
        hsim.dirs_other r.alice hwf.1
      let ev := runEventOf c (some (0, out))
      let evs := evs_pre ++ [.run ev]
      have hfail : failedSend ev = false := by
        simp [failedSend, runOk, ev, runEventOf, hcmd]
      have hcalls : callsOf evs = callsOf evs_pre ++ [(c.party, true)] := by
        rw [callsOf_append, callsOf_run_call c 0 out hfail]; rfl
      have hflat_ev : flatEvents evs = flatEvents evs_pre ++ (cliEntryEvents c ++ cliExitEvents c 0 out) := by
        rw [flatEvents_append, flatEvents_run_call c 0 out hfail]
      refine ⟨t_clean', accepted', hsim', fun who ok hsched hinv => ?_⟩
      by_cases hcol_post : CollisionAfterExplainedPrefixClassical interp' r S evs
      · exact Or.inl hcol_post
      · rcases hinv with hcol_pre | ⟨hlive, hpend_all, g₀, ss₀, vis₀, hex₀, hnrc₀⟩
        · exact absurd (collisionAtCli_append [.run ev] hcol_pre) hcol_post
        · have hsched_pre := schedFits_of_append (b := [(c.party, true)]) (by rwa [← hcalls])
          let k := (callsOf evs_pre).length
          have hk_cs : (callStarts (flatEvents evs_pre)).length = k :=
            callStarts_flatEvents_length evs_pre
          have hget_ev : (callsOf evs)[k]? = some (c.party, true) := by
            rw [hcalls, List.getElem?_append_right (Nat.le_refl k), Nat.sub_self]; rfl
          obtain ⟨tl, htl⟩ := hsched.1
          have hwho_k : who[k]? = some c.party := by
            rw [← htl, hcalls, List.map_append, List.append_assoc,
              List.getElem?_append_right (by simp [k])]
            simp [k]
          have hok_k : ok k = true := hsched.2 k c.party true hget_ev
          have hwho : who[(callStarts (flatEvents evs_pre)).length]? = some c.party := by
            rwa [hk_cs]
          have hok : ok (callStarts (flatEvents evs_pre)).length = decide (0 = 0) := by
            rw [hk_cs, hok_k]; rfl
          have hlive' : CliLiveAtCli interp' r S who ok t_clean' accepted' (flatEvents evs) := by
            rw [hflat_ev]
            exact hlive_step who ok hwho hlive trivial hok
          have hReady : SemReady interp' r S := compSemOf_ready interp' r hwf
          obtain ⟨τ₀, ms₀, hex_cli₀, hnrc_cli₀, htr_eq, _, _, _⟩ :=
            hXInv hwf hReady hsched_pre hex₀ hnrc₀
          have hc₀ := explainsCli_toClean hex_cli₀ hnrc_cli₀
          obtain ⟨hrel₀, _⟩ := hlive.cutRel τ₀ ⟨g₀, ms₀, hex_cli₀, hnrc_cli₀⟩
          have hooo₀ : SpqrOooBounded g_st.session.pqRatchetState := by
            have h0 := hrel₀.oooAll c.party rec_ hleak_rec
            rwa [pqStateOf_of_canonical_Q_pend (recordCanonical_Q_of_wfPq hwf_st hsess)] at h0
          have hretOut₀ :=
            sndWhisperRetOut_of_pqSendModel hb' r c.party hwf_st hsess hp_b hooo₀ hsb hcoins hmod'
          obtain ⟨hinv₀, hbook₀, _, hrole₀⟩ := pureCRel_trRecordStateInv interp' r S who ok
            (t_clean.leakRecords r) t_clean.sent accepted τ₀ g₀ ms₀ c.party rec_ hrel₀ hc₀
            hleak_rec hss (not_alice_and_aliceInitPending_of_not_recPending hnpend_pure)
          obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel_st₀, _, hcanon0, hks₀, _⟩ :=
            hinv₀ c.party rec_ (by simp)
          obtain ⟨hcanon_ret, coins, hmid, hcoins_pref, heval⟩ :=
            snd_ret_eval_clause interp' hext' r hwf S rfl g₀ ms₀ (hcanon0 hreclen) hnpend_pure hretOut₀
          have hcoins_len : coins.length = 0 ∨ coins.length = 32 ∨ coins.length = 64 := by
            rcases hmid with ⟨rfl, _⟩ | ⟨_, hmid_eq⟩
            · exact Or.inl rfl
            · change Symbolic.Swarm.CREF.Cli.Slots.sendMidOf
                  (Symbolic.Swarm.CREF.Cli.Slots.sendCoinsOf interp' g_st.session.pqRatchetState c.coins) = _
                at hmid_eq
              rcases Symbolic.Swarm.CREF.Cli.Slots.sendMidOf_cases
                  (Symbolic.Swarm.CREF.Cli.Slots.sendCoinsOf interp' g_st.session.pqRatchetState c.coins)
                with ⟨_, h0⟩ | ⟨_, h1⟩
              · rw [h0] at hmid_eq; cases hmid_eq
              · rw [h1] at hmid_eq
                injection (List.cons.inj hmid_eq).1 with hcoins_eq
                rw [← hcoins_eq, Symbolic.Swarm.CREF.Cli.Slots.sendCoinsOf, List.length_take, hcoins]
                rcases Symbolic.Swarm.CREF.Cli.Slots.trSendDrawSizeOf_cases interp'
                    g_st.session.pqRatchetState with h | h | h <;>
                  (rw [h]; omega)
          have hst_lt := Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_at?_st
            (Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp' S g₀
              (runTraceMoves r ms₀).length hc₀.matched.2.1.2.2.1.1 (Nat.le_refl _))
            (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
          obtain ⟨hrel_sg, hks_sg⟩ :=
            snd_stateRel_keyShape_sendGhost (pt := c.stdin) (coins := coins) hst_lt hrel_st₀ hks₀
          obtain ⟨_, _, _, _, hmsg⟩ :=
            heval rec₀ st₀ hrecBytes₀ hrel_sg hks_sg
              (Symbolic.Swarm.CREF.CliPure.TR.spqrInitA2BKdf_of_getLocalState hst₀)
          have hns := ns_ne_u32Max_of_trNsBound hbook₀.2.1 hsent1 hst₀
          refine Or.inr ⟨hlive', ?_, ?_⟩
          · intro g ss vis hex hnrc
            by_cases hpA : c.party = r.alice
            · have hrec_alice' : t_clean'.leakRecords r r.alice = some retState := by
                rw [hlr_clean']
                have hd_eq' : t_clean'.dirs r.alice = filesOf (encodeDir P st') := by
                  rw [hdirs_alice']
                  simp [CliTurn.after, hpA, hscr]
                have hst'_alice : PqPartyInv interp' P r accepted r.alice st' (t_clean'.dirs r.alice) := by
                  rw [hd_eq']; exact hpA ▸ hst'
                obtain ⟨_, hmap⟩ := pqSendModel_some_session_oneTime hsess hmod'
                exact (records_of_pqPartyInv hst'_alice).trans hmap
              refine aliceRecordPendingInSession_of_not_pending (fun rec sess hrec hcan => ?_) ?_
              · rw [hrec_alice', Option.some.injEq] at hrec
                subst hrec
                exact postSend_not_pending hb' hwf_st hsess hlen31 hp_b hooo₀ hcoins hmod' sess hcan
              · exact aliceNotPendingOn_of_explains_append hwf hex hnrc (send_run_noStart hcmd)
                  fun ss₁ vis₁ hex₁ hnrc₁ =>
                    (hpend_all g ss₁ vis₁ hex₁ hnrc₁ rec_
                      (Symbolic.Swarm.CREF.Cli.pqSession x g_st) (hpA ▸ hleak_rec)
                      (recordCanonical_Q_of_wfPq hwf_st hsess)).2
                      (by simp [Symbolic.Swarm.CREF.Cli.pqSession, hp_b])
            · have hrec_same : t_clean'.leakRecords r r.alice = t_clean.leakRecords r r.alice := by
                rw [hlr_clean', hlr_clean]
                have hd_same : t_clean'.dirs r.alice = t_clean.dirs r.alice := by
                  rw [hdirs_alice', hdirs_alice]
                  simp [CliTurn.after, Ne.symm hpA]
                simp [CliTurn.records, hd_same]
              exact aliceRecordPendingInSession_of_explains_append hwf hex hnrc
                (by intro ev' hev'
                    simp only [List.mem_singleton, CliEvent.run.injEq] at hev'
                    subst hev'
                    refine ⟨fun _ _ hc => ?_, fun _ _ _ hc => ?_⟩ <;>
                      { dsimp [ev, runEventOf] at hc; rw [hcmd] at hc; cases hc })
                hrec_same
                fun ss₁ vis₁ hex₁ hnrc₁ => hpend_all g ss₁ vis₁ hex₁ hnrc₁
          · have hppk₀ : pendingPreKey (runTrace r ss₀) stateIdx₀ = none := by
              by_cases hpA : c.party = r.alice
              · exact (hpend_all g₀ ss₀ vis₀ hex₀ hnrc₀ rec_
                  (Symbolic.Swarm.CREF.Cli.pqSession x g_st) (hpA ▸ hleak_rec)
                  (recordCanonical_Q_of_wfPq hwf_st hsess)).2
                  (by simp [Symbolic.Swarm.CREF.Cli.pqSession, hp_b])
                  stateIdx₀ st₀ (hpA ▸ htr_eq ▸ hst₀) (htr_eq ▸ hcur₀)
              · have hat₀ :=
                  Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀
                have hinit_false : st₀.initiator = false := by
                  rw [hrole₀ c.party st₀ stateIdx₀ hat₀]
                  exact decide_eq_false hpA
                exact pendingPreKey_eq_none_of_initiator_false
                  (handshakeSessionValid_reachable (modelRunWF_reachable hex₀.2.2.1))
                  (htr_eq ▸ hat₀) hinit_false
            rw [htr_eq] at hst₀ hcur₀ hmsg
            have hinp_eq : (runEventOf c (some (0, out))).input = c.stdin := by
              simp [runEventOf, runInput, hcmd]
            exact hWStep hwf hReady hex₀ hnrc₀
              rfl
              hcmd
              rfl
              hst₀ hcur₀ hns hppk₀
              hcoins_pref hcoins_len
              (by rw [← hinp_eq] at hmsg; exact hmsg)
    · cases h01

end Symbolic.Proofs.Swarm.UA.SendW
