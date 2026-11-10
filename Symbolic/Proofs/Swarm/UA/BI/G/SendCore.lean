/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
public import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRecordInj
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRetBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendSlot
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlotsSend
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.SendPA
import Symbolic.Proofs.Swarm.CREF.SendWire.GhostInvariance
import Symbolic.Proofs.Swarm.CREF.SendWire.RecvSimV3SendPure
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPure
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L02GoodExit0Cut
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L03StickyAndBridgeAPt
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L04BridgeBQuietFail
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L08SlotSendCli
import Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey
import Symbolic.Proofs.Swarm.UA.BI.G.SendTransfer
import Symbolic.Proofs.Swarm.UA.BI.G.SendW
import Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer
import Symbolic.Proofs.Swarm.UA.BI.RAB.Base
import Symbolic.Proofs.Swarm.UA.Base

/-!
# Send Slot Refinement under Break and Invert Events

Proves `slot_send_of_xlate : XlateInvSpecB -> UASlotSendSpecB`, preserving `PqTurnSim1A` and
`UAInvB` across CLI `send` calls by dispatching rejected runs, whisper sends, and pending-PreKey
sends.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.G.SendCore

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (CliEvent)
open _root_.DY.Libsignal.Composed (reachability)
open _root_.DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost RunRejected SendMatches runTrace runSteps
   activeBundleIds ecKey kyberKey pubBytes secretBytes gamma callStarts runTraceMoves sentBody)
open _root_.DY.Libsignal.Composed.Refinement.Cli
  (CliCall CliTurn DirectorySnapshot PqModelRel PreKeyNoMatch
   CollisionAfterExplainedPrefix runEventOf peerOf BobCallAllowed FilesBounded
   InputsFor ModelAgree ExternContractsHoldCli cliEntryEvents cliExitEvents sessionPathOf
   ValidCall coinsLen StdinBounded scrub)
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
  (PqTurnSim1A pqTurnSim1A_caller_after toCliCallNone inputsFor_toCliCallNone clean_dirs_caller_eq)
open _root_.DY.Libsignal.TripleRatchet (isCurrentSnapshot)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.E2E (PEParams encodeRecordUnderExtras pqxdhSessionParams)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (Inputs partyAddress filesOf encodeDir pqSendInputs)
open Proofs.libsignal.Hooks2 (cryptoOf' cryptoOf'_F)
open Proofs.libsignal.SR (interpW)
open Symbolic.Proofs.Swarm.UA.Defs
  (AliceRecordPendingInSession SchedFits callsOf flatEvents failedSend)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Defs
  (UASlotSendSpecB UASlotPostB UAInvB XlateInvSpecB)
open Symbolic.Proofs.Swarm.UA.Base
  (activeBundleIds_append_of_no_init failedSend_runEventOf callsOf_append callsOf_run_call
   schedFits_of_append callStarts_flatEvents_length flatEvents_append flatEvents_run_call
   flatEvents_run_failedSend)
open Symbolic.Proofs.Swarm.UA.BI.RAB.Base
  (collisionAtCli_append explains_snoc_rejected)
open Symbolic.Proofs.Swarm.UA.BI.G.SlotInitTransfer (runSteps_reachable)
open Symbolic.Proofs.Swarm.UA.BI.G.PendingPreKey
  (alicePendingKeysOn_of_explains_append aliceRecordPendingInSession_of_explains_append)
open Symbolic.Proofs.Swarm.UA.BI.G.SendTransfer
  (pendingPreKey_stampsLt_send not_readCollisionCli_snoc_send_rejected
   explains_and_clean_snoc_whisper explains_and_clean_snoc_pending)
open Symbolic.Proofs.Swarm.UA.BI.G.SendW (send_w_branch)
open Symbolic.Swarm.CREF (compSemOf compSemOf_ready)
open Symbolic.Swarm.CREF.Grow (SpqrOooBounded)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.CREF.Cli
  (interpOfParams externContractsHoldCli_interpOfParams modelAgree_interpOfParams
   modelHookBridge_interpOfParams ModelHookBridge
   pqDispatch_send_party
   partyOf_alice peerOf_eq_addrE_other inputsEquiv_pqSendInputs
   scrub_filesOf_pqInputs_accept scrub_filesOf_pqInputs_reject
   pqPartyInv_of_pqSendModel PqPartyInv PqDirInv pqDirInv_after_accept_same pqDirInv_after_reject
   records_of_pqPartyInv PqBobInv opkUsed_eq_of_pqBobInv_oneTime_eq
   reachPqInvPure_of_wfPq recordCanonical_Q_of_wfPq
   pqSendModel_some_session_oneTime)
open Symbolic.Swarm.CREF.Cli.Slots
  (pqObserve_send_exited_cases singleSession_encodeRecordX_of_wfPq
   recPending_iff_pureRecPending recPending_encodeRecordX_iff
   sndPendingRetOut_of_pqSendModel recordCanonical_Q_inj snd_after_sent_of_ne_zero
   after_leakRecords_of_send_ok after_leakRecords_of_send_fail after_sent_of_send_ok)
open Symbolic.Swarm.CREF.CliPure
  (leakRecords_party_eq_of_cliNextCall
   leakRecords_eq_records_of_bobOff_false)
open Symbolic.Swarm.CREF.CliPure.SndPure
  (PureRecPending recPending_imp_alice_pending_of_recRel
   pendingRecordCanon_of_aliceInitPending pqStateOf_of_canonical_Q_pend
   ns_ne_u32Max_of_trNsBound
   gamma_sendPendingGhost_of_stampsLt
   psm_field_lengths_lt_of_wire_lt innerMsg_serialized_eq_gamma_encMsg
   preKeySignalMessage_serialized_eq_preKeyWire sendMatches_of_preKeyWire_comp
   recordCanonical_of_sendPending_step)
open Symbolic.Swarm.CREF.SendWire (sendPendingGhost pqHarnessAddrBytes)
open Symbolic.Swarm.Coinsplit.Lift (explainsCli_toClean)

attribute [local instance 2000]
  _root_.DY.Libsignal.Composed.instBytesFunctor_symbolic _root_.DY.Libsignal.Composed.instBytesLength_symbolic
  _root_.DY.Libsignal.Composed.instAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instExecTraceTypes_symbolic
  _root_.DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic _root_.DY.Libsignal.Composed.instHasExecBytes
  _root_.DY.Libsignal.Composed.instHasExecEntryT _root_.DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasExecTrace _root_.DY.Libsignal.Composed.instHasSubF
  _root_.DY.Libsignal.Composed.instHasSubFAttackerKnowledge _root_.DY.Libsignal.Composed.instHasSubFLength
  _root_.DY.Libsignal.Composed.HasExecBytes.toPQXDHExecBytes _root_.DY.Libsignal.Composed.toTripleRatchet
  _root_.DY.Libsignal.Composed.toPQXDHSpqr

/-- Contract for the non-pending whisper `send` branch. -/
def SendWBranchSpec : Prop :=
  ∀ (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup),
    ExternContractsHoldCli interp → ModelAgree interp P → ProtocolSetupWF r →
    ∀ {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
      {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
      {accepted : List HwBytes} {evs_pre : List CliEvent},
      PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted →
      (c.party = r.alice ∨ c.party = r.bob) →
      c.cmd = .send (peerOf r c.party) →
      c.bundle = [] →
      c.coins.length = 64 →
      c.stdin.length < 2 ^ 32 →
      FilesBounded (t.dirs c.party) →
      BobCallAllowed r t c →
      t.sent.length < 2 ^ 32 - 1 →
      t.records r c.party ≠ none →
      InputsFor c (t.dirs c.party) i →
      PqModelRel interp P i (some (.exited code out files)) →
      code = 0 →
      (∀ rec_, t_clean.leakRecords r c.party = some rec_ → ¬ PureRecPending rec_) →
      UASlotPostB interp P r t t_clean c code out files accepted evs_pre

private theorem sched_send_ok_facts {evs_pre : List CliEvent} {c : CliCall} {out : HwBytes}
    {who : List Participant} {ok : Nat → Bool}
    (hsched : SchedFits (callsOf (evs_pre ++ [.run (runEventOf c (some (0, out)))])) who ok) :
    failedSend (runEventOf c (some (0, out))) = false ∧
    SchedFits (callsOf evs_pre) who ok ∧
    who[(callStarts (flatEvents evs_pre)).length]? = some c.party ∧
    ok (callStarts (flatEvents evs_pre)).length = true := by
  have hfs : failedSend (runEventOf c (some (0, out))) = false :=
    Bool.eq_false_iff.mpr fun ht => ((failedSend_runEventOf c 0 out).mp ht).2 rfl
  have hcalls : callsOf (evs_pre ++ [.run (runEventOf c (some (0, out)))]) =
      callsOf evs_pre ++ [(c.party, true)] := by
    rw [callsOf_append, callsOf_run_call c 0 out hfs]
    simp
  rw [hcalls] at hsched
  have hsched_pre : SchedFits (callsOf evs_pre) who ok := schedFits_of_append hsched
  have hlen : (callStarts (flatEvents evs_pre)).length = (callsOf evs_pre).length :=
    callStarts_flatEvents_length evs_pre
  obtain ⟨rest, hwho_eq⟩ := hsched.1
  have hwho_k : who[(callStarts (flatEvents evs_pre)).length]? = some c.party := by
    rw [← hwho_eq, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, hlen,
      List.getElem?_append_right (by simp),
      show (callsOf evs_pre).length - ((callsOf evs_pre).map Prod.fst).length = 0 by simp]
    rfl
  have hok_k : ok (callStarts (flatEvents evs_pre)).length = true := by
    rw [hlen]
    exact hsched.2 (callsOf evs_pre).length c.party true
      (by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
  exact ⟨hfs, hsched_pre, hwho_k, hok_k⟩

private theorem leakRecords_alice_eq_after {interp' : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {t t_clean t_clean' : CliTurn}
    {accepted accepted' : List HwBytes} {c : CliCall} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hsim : PqTurnSim1A interp' P r t t_clean accepted)
    (hsim' : PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted') :
    t_clean'.leakRecords r r.alice =
      (t_clean.after r (toCliCallNone c) code out files).leakRecords r r.alice := by
  have h1 : t_clean'.leakRecords r r.alice = t_clean'.records r r.alice := by
    rw [leakRecords_eq_records_of_bobOff_false r hsim'.clean_bobOff]
  have h2 : (t_clean.after r (toCliCallNone c) code out files).leakRecords r r.alice =
      (t_clean.after r (toCliCallNone c) code out files).records r r.alice := by
    unfold CliTurn.leakRecords
    simp [hwf.1]
  rw [h1, h2]
  unfold CliTurn.records
  have hd1 := hsim'.dirs_other r.alice hwf.1
  have hd0 := hsim.dirs_other r.alice hwf.1
  have hp_eq : (toCliCallNone c).party = c.party := rfl
  have hdir_eq : t_clean'.dirs r.alice =
      (t_clean.after r (toCliCallNone c) code out files).dirs r.alice := by
    rw [hd1]
    unfold CliTurn.after
    dsimp only
    rw [hp_eq]
    by_cases ha : r.alice = c.party
    · simp [ha]
    · simp [ha, hd0]
  rw [hdir_eq]

/-- Proves `UASlotSendSpecB` from `XlateInvSpecB` and `SendWBranchSpec`. -/
theorem slot_send_of_xlate_and_w
    (hXInv : XlateInvSpecB)
    (hSendW : SendWBranchSpec) :
    UASlotSendSpecB := by
  intro interp P r hext hagree hwf t t_clean c i code out files accepted evs_pre
    hsim hp hcmd hbun hcoins hsb hfb hbca hsent hrec_ne hin hRel
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hb' : ModelHookBridge interp' P := modelHookBridge_interpOfParams hagree
  have hReady : Symbolic.Swarm.CREF.SemReady interp' r S := compSemOf_ready interp' r hwf
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
  have hgA : ∀ x g, st.session = some (x, g) → c1.party = r.alice → g.party = .A :=
    fun x g hs hpA => (hwf_st.1 x g hs).2.1.trans (hinvP.party_eq.trans (hpA ▸ partyOf_alice r))
  have hcmd' : c1.cmd = .send (partyAddress st.party.other) := by
    rw [peerOf_eq_addrE_other, ← hinvP.party_eq] at hcmd1; exact hcmd1
  let coinsVec : List.Vector (BitVec 8) 64 := ⟨c1.coins, hcoins⟩
  have hi' : InputsFor c1 (filesOf (encodeDir P st)) i := by rwa [hinvP.dir_eq] at hin1
  have hobs_eq := (PqModelRel.exited_iff.mp hRel).send st c1.stdin coinsVec hwf_st hsb
    (inputsEquiv_pqSendInputs hi' hcmd' rfl rfl)
  have hn3 : ¬ PreKeyNoMatch r t c := fun ⟨_, ⟨_, hc⟩, _⟩ => by rw [hcmd] at hc; cases hc
  have hn1 : ¬ PreKeyNoMatch r t_clean c1 := fun ⟨_, ⟨_, hc⟩, _⟩ => by
    change c.cmd = _ at hc; rw [hcmd] at hc; cases hc
  cases hsess : st.session with
  | none =>
    exfalso; apply hrec_ne1; simpa [hsess] using hrec_st
  | some xg =>
    rcases xg with ⟨x, g_st⟩
    let rec_ := encodeRecordUnderExtras (fun _ => x) g_st
    have hrec_t : t_clean.records r c1.party = some rec_ := by simpa [hsess] using hrec_st
    have hleak_rec : t_clean.leakRecords r c.party = some rec_ :=
      (leakRecords_party_eq_of_cliNextCall hnext1).trans hrec_t
    have hlen31 : rec_.length < 2 ^ 31 := (reachPqInvPure_of_wfPq hwf_st hsess).2.2
    have hreclen : rec_.length < 2 ^ 32 - 2 ^ 20 := by omega
    rcases pqObserve_send_exited_cases hobs_eq with ⟨rfl, st', hmod, rfl⟩ | ⟨rfl, rfl, _, rfl⟩
    ·
      cases hp_b : g_st.session.pendingPreKey
      ·
        have hnpend_pure : ¬ PureRecPending rec_ := fun hp_p => by
          have hp_t := (recPending_encodeRecordX_iff hwf_st hsess).mp
            (recPending_iff_pureRecPending.mpr hp_p)
          rw [hp_b] at hp_t; cases hp_t
        have hnpend_t : ∀ r0, t_clean.leakRecords r c.party = some r0 → ¬ PureRecPending r0 := by
          intro r0 hr0
          rw [hleak_rec, Option.some.injEq] at hr0
          subst hr0
          exact hnpend_pure
        exact hSendW interp P r hext hagree hwf hsim hp hcmd hbun hcoins hsb hfb hbca hsent
          hrec_ne hin hRel rfl hnpend_t
      ·
        have hmod' : CryptoVerification.SignalSession.pqSendModel P st c.stdin c.coins =
            some (some (st', out)) := hmod
        obtain ⟨hst', hsub⟩ := pqPartyInv_of_pqSendModel hinvP hwf_st hmod'
        let files₀ := filesOf ((pqSendInputs P st c1.stdin coinsVec).files ++ encodeDir P st')
        have hscr : scrub files₀ = filesOf (encodeDir P st') :=
          scrub_filesOf_pqInputs_accept P st st' _ [] _ _
            (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
        let retState := encodeRecordUnderExtras (fun _ => x) ((pqxdhSessionParams P).send g_st c.stdin c.coins).1
        have hrec_after : (t_clean.after r c1 0 out files₀).records r c1.party = some retState := by
          obtain ⟨_, hmap⟩ := pqSendModel_some_session_oneTime hsess hmod'
          have hst'_after : PqPartyInv interp' P r accepted c1.party st'
              ((t_clean.after r c1 0 out files₀).dirs c1.party) := by
            simpa [CliTurn.after, hscr] using hst'
          exact (records_of_pqPartyInv hst'_after).trans hmap
        have hlr_ok : (t_clean.after r c1 0 out files₀).leakRecords r =
            fun q => if q = c.party then some retState else t_clean.leakRecords r q :=
          after_leakRecords_of_send_ok hnext1 hcmd1 hrec_after
        obtain ⟨t_clean', accepted', hsim', hlive_step⟩ :=
          Symbolic.Swarm.Coinsplit.Lift.L08.slot_send_cli_gen
            Symbolic.Swarm.Coinsplit.Lift.L02.outcomeFaithfulCli_of_goodExit0Cut
            Symbolic.Swarm.Coinsplit.Lift.L03.bridgeA_pt
            Symbolic.Swarm.Coinsplit.Lift.L04.bridgeB_quiet_fail
            interp P r hext hagree hwf (σ_pre := flatEvents evs_pre)
            hsim hp hcmd hbun hcoins hsb hfb hbca hsent hrec_ne hin hRel
        have hlr_alice : t_clean'.leakRecords r r.alice =
            if r.alice = c.party then some retState else t_clean.leakRecords r r.alice := by
          rw [leakRecords_alice_eq_after hwf hsim hsim']
          exact congrFun hlr_ok r.alice
        refine ⟨t_clean', accepted', hsim', fun who ok hsched hinv_pre => ?_⟩
        let ev := runEventOf c (some (0, out))
        let evs := evs_pre ++ [.run ev]
        rcases hinv_pre with hcol_pre | ⟨hlive, harps_all, g₀, ss₀, vis₀, hex₀, hnrc₀⟩
        · exact Or.inl (collisionAtCli_append _ hcol_pre)
        · by_cases hcol : CollisionAfterExplainedPrefix interp' r S evs
          · exact Or.inl hcol
          · obtain ⟨hfs_false, hsched_pre, hwho_k, hok_k⟩ := sched_send_ok_facts hsched
            have hflat_evs : flatEvents evs =
                flatEvents evs_pre ++ (cliEntryEvents c ++ cliExitEvents c 0 out) := by
              rw [flatEvents_append, flatEvents_run_call c 0 out hfs_false]
            have hlive' : Symbolic.Swarm.Coinsplit.Lift.CliLiveAtCli interp' r S who ok
                t_clean' accepted' (flatEvents evs) := by
              rw [hflat_evs]
              exact hlive_step who ok hwho_k hlive trivial (by simpa using hok_k)
            have hpend_pure : PureRecPending rec_ :=
              recPending_iff_pureRecPending.mp ((recPending_encodeRecordX_iff hwf_st hsess).mpr hp_b)
            obtain ⟨τ₀, ms₀, hex_cli₀, hnrc_cli₀, htr_eq, _, _, _⟩ :=
              hXInv hwf hReady hsched_pre hex₀ hnrc₀
            have hc₀ := explainsCli_toClean hex_cli₀ hnrc_cli₀
            obtain ⟨hrel₀, _⟩ := hlive.cutRel τ₀ ⟨g₀, ms₀, hex_cli₀, hnrc_cli₀⟩
            obtain ⟨⟨hrecs₀, hbook₀, _, _⟩, _⟩ := hrel₀.clean g₀ ms₀ hc₀
            obtain ⟨hpA, hpend₀⟩ := recPending_imp_alice_pending_of_recRel interp' r S c.party rec_
              g₀ ms₀ hreclen hpend_pure (hrecs₀ c.party rec_ hleak_rec).2.2
            have hcanon :=
              pendingRecordCanon_of_aliceInitPending interp' r S g₀ ms₀ rec_ hpend₀ hreclen
                (hrel₀.oooAll c.party rec_ hleak_rec)
            have hlen62 : rec_.length < 2 ^ 62 := by
              rcases hcanon with ⟨_, _, _, _, _, h, _, _⟩; exact h
            obtain ⟨sess, sc, remote, items, kpk, st₀, stateIdx₀, _, _, _, _,
              hrc, hscope1, hscope2, hget, hcur, _, _, _, _,
              hreg, hver, hpn, hlid, hrem, hrem_ser, hsc, hrk, hck, hidx,
              hppk, _, _, hkpk, _, hpq, _, _, _, _, _, _⟩ := hpend₀
            have hooo : SpqrOooBounded sess.state.pqRatchetState :=
              pqStateOf_of_canonical_Q_pend hrc ▸ hrel₀.oooAll c.party rec_ hleak_rec
            have hrid : sess.state.remoteIdentity.isSome = true := by rw [hrem]; rfl
            have hout_p := sndPendingRetOut_of_pqSendModel hb' r hwf_st hsess hp_b
              (hgA x g_st hsess hpA) hsb hcoins hmod'
            obtain ⟨hwc, coins, hmid, hpref, hev⟩ :=
              hout_p.eval sess hrc hscope1 hscope2 hrid hlen62 hreclen hooo
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
            have hsend_some :=
              Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.pureEvalSendWire_some_send_isSome
                _ _ _ sess (some pqHarnessAddrBytes) c.stdin coins (retState, out) hev
            obtain ⟨⟨newPqState, salt?, pqMsgBytes⟩, hsend⟩ := Option.isSome_iff_exists.mp hsend_some
            obtain ⟨_, hexec⟩ :=
              Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.pureEvalSendWire_exec_pending
                (cryptoOf' interp') (interpW interp') (spqrModelOf interp')
                sess (some pqHarnessAddrBytes) c.stdin coins (retState, out)
                sc remote items kpk newPqState pqMsgBytes salt?
                hev hver hsc hrem hppk hkpk hsend
            rw [cryptoOf'_F] at hexec
            injection hexec with hstate_eq hmsg_eq
            have hrc_post :=
              (recordCanonical_of_sendPending_step hrc hscope1 hscope2 hsc hwc hstate_eq).1
            refine Or.inr ⟨hlive', ?_, ?_⟩
            ·
              have habi_evs : activeBundleIds evs = activeBundleIds evs_pre :=
                activeBundleIds_append_of_no_init fun ev' hev' p' d' hc' => by
                  simp only [List.mem_singleton, CliEvent.run.injEq] at hev'
                  subst hev'
                  dsimp [ev, runEventOf] at hc'; rw [hcmd] at hc'; cases hc'
              intro g ss vis hex hnrc rec₁ sess₁ hrec₁ hcan₁
              rw [habi_evs]
              have hrec_alice₀ : t_clean.leakRecords r r.alice = some rec_ := hpA ▸ hleak_rec
              have hrec_alice₁ : t_clean'.leakRecords r r.alice = some retState := by
                rw [hlr_alice, ite_eq_left_iff.mpr fun h => absurd hpA.symm h]
              rw [hrec_alice₁, Option.some.injEq] at hrec₁
              subst hrec₁
              have hsess₁_eq := recordCanonical_Q_inj hcan₁ hrc_post
              subst hsess₁_eq
              refine ⟨fun items₁ kpk₁ hp₁ hk₁ => ?_, fun hp_none => ?_⟩
              · refine ⟨((harps_all g₀ ss₀ vis₀ hex₀ hnrc₀ rec_ sess hrec_alice₀ hrc).1
                    items₁ kpk₁ hp₁ hk₁).1, ?_⟩
                exact alicePendingKeysOn_of_explains_append hwf hex hnrc
                  (by intro ev' hev'
                      simp only [List.mem_singleton, CliEvent.run.injEq] at hev'
                      subst hev'
                      refine ⟨fun p' d' hc' => ?_, fun _ p' _ hc' => ?_⟩ <;>
                        { dsimp [ev, runEventOf] at hc'; rw [hcmd] at hc'; cases hc' })
                  (fun ss₁ vis₁ hex₁ hnrc₁ =>
                    ((harps_all g ss₁ vis₁ hex₁ hnrc₁ rec_ sess hrec_alice₀ hrc).1
                      items₁ kpk₁ hp₁ hk₁).2)
              · change sess.pendingPreKey = none at hp_none
                rw [hppk] at hp_none
                cases hp_none
            ·
              have harps₀ := harps_all g₀ ss₀ vis₀ hex₀ hnrc₀
              have hget_ss₀ :
                  ((_root_.DY.PersistentLocalState.getLocalState r.alice stateIdx₀ :
                    _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run
                    (runTrace r ss₀)).1 = some st₀ := htr_eq ▸ hget
              have hcur_ss₀ : isCurrentSnapshot (runTrace r ss₀) stateIdx₀ = true :=
                htr_eq ▸ hcur
              obtain ⟨habi₀, hap_keys₀⟩ :=
                (harps₀ rec_ sess (hpA ▸ hleak_rec) hrc).1 items kpk hppk hkpk
              obtain ⟨ek_p, ct_p, hppk_tr, hbk_p, hct_p⟩ :=
                hap_keys₀ stateIdx₀ st₀ hget_ss₀ hcur_ss₀
              let ts := (runTrace r ss₀).length
              let g' := sendPendingGhost g₀ ts c.stdin coins
              have hReach₀ := runSteps_reachable ss₀ hex₀.2.2.1.2.1 hex₀.2.2.1.2.2.1
              obtain ⟨hek_lt, hct_lt0⟩ :=
                pendingPreKey_stampsLt_send (interp := interp') (S := S) (g := g₀)
                  hReach₀ (Nat.le_refl ts) hppk_tr
              have htr_lt :
                  Symbolic.Swarm.CREF.TR.FreshSigma.TraceEntriesLt interp' S g₀ ts
                    (runTrace r ss₀) :=
                Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_of_reachable interp' S g₀ ts
                  hReach₀ (Nat.le_refl ts)
              have hst_lt : Symbolic.Swarm.CREF.TR.FreshSigma.StateStampsLt interp' S g₀ ts st₀ :=
                Symbolic.Swarm.CREF.TR.FreshSigma.traceEntriesLt_at?_st htr_lt
                  (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hget_ss₀)
              have hdhs_pk_lt :
                  Symbolic.Swarm.CREF.TR.FreshSigma.StampsLt interp' S g₀ ts
                    (_root_.DY.DiffieHellman.CanDH.dhPk st₀.dhs) :=
                (Symbolic.Swarm.CREF.TR.FreshSigma.stampsLt_dhPk_pack interp' S g₀ ts
                  ⟨st₀.dhs⟩).mpr hst_lt.2.2.2.1
              have hlid' : sess.state.localIdentity.serialize = gamma interp' S g' st₀.myIk := by
                rw [gamma_sendPendingGhost_of_stampsLt hst_lt.1]; exact hlid
              have hrem_ser' : remote.serialize = gamma interp' S g' st₀.peerIk := by
                rw [gamma_sendPendingGhost_of_stampsLt hst_lt.2.1]; exact hrem_ser
              have hrk' : sc.ratchetKey.publicKey.bytes.toList =
                  gamma interp' S g' (_root_.DY.DiffieHellman.CanDH.dhPk st₀.dhs) := by
                rw [gamma_sendPendingGhost_of_stampsLt hdhs_pk_lt]; exact hrk
              have hck' : CryptoGames.HMAC.keyToBytes32 sc.chainKey.key =
                  gamma interp' S g' st₀.cks := by
                rw [gamma_sendPendingGhost_of_stampsLt hst_lt.2.2.2.2.1]; exact hck
              have hbk' : items.baseKey.serialize = ecKey (gamma interp' S g' ek_p) := by
                rw [gamma_sendPendingGhost_of_stampsLt hek_lt]; exact hbk_p
              have hct_ser' : kpk.ciphertext = kyberKey (gamma interp' S g' ct_p) := by
                rw [gamma_sendPendingGhost_of_stampsLt hct_lt0]; exact hct_p
              have hpq' : sess.state.pqRatchetState = gamma interp' S g' st₀.spqr := by
                rw [gamma_sendPendingGhost_of_stampsLt hst_lt.2.2.2.2.2.1]; exact hpq
              have hns₀ : st₀.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max :=
                ns_ne_u32Max_of_trNsBound hbook₀.2.1 hsent1 hget
              set F := _root_.DY.Libsignal.Refinement.sha256CompressFunction interp'
              set mk := (sc.chainKey.messageKeys F).generateKeys F salt?
              set ctext := (interpW interp').enc mk.cipherKey mk.iv c.stdin
              set innerMsg := SignalMessage.new F protoSignalCodec 4#8 mk.macKey
                (some pqHarnessAddrBytes) sc.ratchetKey.publicKey sc.chainKey.index
                sess.state.previousCounter ctext sess.state.localIdentity remote pqMsgBytes
              have hw_lt : (_root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag ::
                  (PreKeySignalMessage.new 4#8 r.regIdA items.preKeyId
                    items.signedPreKeyId (some ⟨kpk.preKeyId, kpk.ciphertext⟩)
                    items.baseKey sess.state.localIdentity innerMsg).serialized).length <
                  2 ^ 64 := by
                rw [← hreg, ← hmsg_eq]; exact hout_p.msg_lt
              obtain ⟨hct_lt, hinner_lt⟩ := psm_field_lengths_lt_of_wire_lt r.regIdA
                items.preKeyId items.signedPreKeyId kpk.preKeyId kpk.ciphertext
                items.baseKey sess.state.localIdentity innerMsg hw_lt
              have hsend_g' :
                  (spqrModelOf interp').send (gamma interp' S g' st₀.spqr) coins =
                    some (newPqState, salt?, pqMsgBytes) := by
                rw [← hpq']; exact hsend
              have hinner_eq := innerMsg_serialized_eq_gamma_encMsg
                interp' r hext'.1 g₀ ts c.stdin coins st₀ sc sess.state.localIdentity remote
                sess.state.previousCounter newPqState pqMsgBytes salt?
                (Symbolic.Swarm.CREF.CliPure.TR.spqrInitA2BKdf_of_getLocalState hget) hsend_g'
                hidx hpn hck' hrk' hlid' hrem_ser' hinner_lt
              have hcompat_g' : _root_.DY.Libsignal.Composed.Refinement.GhostAndSemMatchSetup interp' r S g' := by
                have hc := (Symbolic.Swarm.CREF.SendWire.matchedPrefix_sendPendingGhost
                  hc₀.matched c.stdin coins).1
                rwa [htr_eq] at hc
              have hpub_a : gamma interp' S g' st₀.myIk =
                  ecKey (pubBytes interp' (secretBytes r 0)) := by
                rw [Symbolic.Swarm.CREF.AliceIk.alice_myIk_of_getLocalState hwf.1
                    hc₀.matched.2.1 hget,
                  Symbolic.Swarm.CREF.TR.gamma_serializedIk,
                  (Symbolic.Swarm.CREF.TR.gamma_setupPublic_0_2_6 interp' r S g'
                    hcompat_g' hwf.1).1]
              have hwire_eq := preKeySignalMessage_serialized_eq_preKeyWire
                r.regIdA items.preKeyId items.signedPreKeyId kpk.preKeyId
                (gamma interp' S g' ek_p) (gamma interp' S g' ct_p)
                items.baseKey sess.state.localIdentity
                (ecKey (pubBytes interp' (secretBytes r 0))) innerMsg
                hbk' (hlid'.trans hpub_a) (by rw [← hct_ser']; exact hct_lt) hinner_lt
              have hsend_match : SendMatches interp' r S g' (activeBundleIds evs_pre) out
                  [ek_p, ct_p,
                    Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg
                      st₀ coins.length ts] := by
                rw [habi₀, hmsg_eq, hreg, hct_ser', hwire_eq, hinner_eq.2.2]
                exact sendMatches_of_preKeyWire_comp interp' r S g'
                  items.preKeyId items.signedPreKeyId kpk.preKeyId ek_p ct_p
                  (Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg st₀ coins.length ts)
              have hinp_ev : ev.input = c.stdin := by
                dsimp [ev, runEventOf, _root_.DY.Libsignal.Composed.Refinement.Cli.runInput]
                rw [hcmd]
              have hsend_match' : SendMatches interp' r S
                  (sendPendingGhost g₀ ts ev.input coins) (activeBundleIds evs_pre) out
                  [ek_p, ct_p,
                    Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure.encMsg
                      st₀ coins.length ts] := by
                simpa only [hinp_ev] using hsend_match
              exact explains_and_clean_snoc_pending hwf hReady hex₀ hnrc₀
                hpA hcmd rfl hget_ss₀ hcur_ss₀ hns₀ hppk_tr hpref hcoins_len hsend_match'
    ·
      let files₁ := filesOf (pqSendInputs P st c1.stdin coinsVec).files
      have hscr : scrub files₁ = t_clean.dirs c1.party := by
        rw [hinvP.dir_eq]
        exact scrub_filesOf_pqInputs_reject P st _ [] _ _
          (fun _ h => nomatch h) (fun _ h => nomatch h)
      have hDir' := pqDirInv_after_reject (out := []) hsim.dirInv hscr
      have hdirs_eq : ∀ q, (t_clean.after r c1 1 [] files₁).dirs q = t_clean.dirs q := fun q => by
        by_cases hq : q = c1.party <;> simp [CliTurn.after, hq, hscr]
      have hrec_after : (t_clean.after r c1 1 [] files₁).records r c1.party =
          t_clean.records r c1.party := by
        simp [CliTurn.records, hdirs_eq c1.party]
      have hlr_fail : (t_clean.after r c1 1 [] files₁).leakRecords r = t_clean.leakRecords r :=
        after_leakRecords_of_send_fail hcmd1 hrec_after
      have hsent_fail : (t_clean.after r c1 1 [] files₁).sent = t_clean.sent :=
        snd_after_sent_of_ne_zero (by decide) [] files₁
      have hopk_fail : (t_clean.after r c1 1 [] files₁).opkUsed r = t_clean.opkUsed r := by
        simp only [CliTurn.opkUsed, hdirs_eq r.bob]
      refine ⟨t_clean.after r c1 1 [] files₁, accepted,
        pqTurnSim1A_caller_after hwf hsim hbca hp hn3 hn1 hDir', fun who ok _hsched hinv_pre => ?_⟩
      let ev := runEventOf c (some (1, []))
      let evs := evs_pre ++ [.run ev]
      rcases hinv_pre with hcol_pre | ⟨hlive, harps_all, g₀, ss₀, vis₀, hex₀, hnrc₀⟩
      · exact Or.inl (collisionAtCli_append _ hcol_pre)
      · have hfs : failedSend ev = true :=
          (failedSend_runEventOf c 1 []).mpr ⟨⟨peerOf r c.party, hcmd⟩, by decide⟩
        have hflat_eq : flatEvents evs = flatEvents evs_pre := by
          rw [flatEvents_append, flatEvents_run_failedSend hfs, List.append_nil]
        refine Or.inr ⟨?_, ?_, ?_⟩
        · rw [hflat_eq]
          exact ⟨hlive.noAdjRng, hlive.witness, fun τ' hinh => by
            rw [hlr_fail, hsent_fail, hopk_fail]
            exact hlive.cutRel τ' hinh⟩
        · intro g ss vis hex hnrc
          exact aliceRecordPendingInSession_of_explains_append hwf hex hnrc
            (by intro ev' hev'
                simp only [List.mem_singleton, CliEvent.run.injEq] at hev'
                subst hev'
                refine ⟨fun p' d' hc' => ?_, fun _ p' _ hc' => ?_⟩ <;>
                  { dsimp [ev, runEventOf] at hc'; rw [hcmd] at hc'; cases hc' })
            (congrFun hlr_fail r.alice)
            (fun ss₁ vis₁ hex₁ hnrc₁ => harps_all g ss₁ vis₁ hex₁ hnrc₁)
        · have hrej : RunRejected ev := fun out' h => by simp [ev, runEventOf] at h
          have hcmd_ev : ev.cmd = .send (peerOf r c.party) := hcmd
          exact ⟨g₀, ss₀, vis₀, explains_snoc_rejected hrej hex₀,
            not_readCollisionCli_snoc_send_rejected hcmd_ev hnrc₀⟩

/-- Proves `UASlotSendSpecB` from `XlateInvSpecB`. -/
theorem slot_send_of_xlate (hXInv : XlateInvSpecB) : UASlotSendSpecB :=
  slot_send_of_xlate_and_w hXInv
    (send_w_branch hXInv
      (fun hwf hReady hex₀ hnrc₀ hp_ev hcmd_ev hexit_ev hst₀ hcur₀ hns₀ hppk₀ hpref hcoins_len hout =>
        explains_and_clean_snoc_whisper
          hwf hReady hex₀ hnrc₀ hp_ev hcmd_ev hexit_ev hst₀ hcur₀ hns₀ hppk₀ hpref hcoins_len hout))

end Symbolic.Proofs.Swarm.UA.BI.G.SendCore
