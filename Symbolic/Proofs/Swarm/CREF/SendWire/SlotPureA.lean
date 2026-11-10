/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.OpkRelC
public import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
public import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Initiate.TransferPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendWire.GhostInvariance
import Symbolic.Proofs.Swarm.CREF.SendWire.PendingPureA
import Symbolic.Proofs.Swarm.CREF.SendWire.StateInv
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPure
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach

/-!
# Whisper `SendWire` Outcome Specifications and Evaluation Helpers

Defines `SndWhisperFailOut` and `SndWhisperRetOut`, and proves `matchedPrefix_snoc_encrypt`,
`snd_ret_eval_clause`, and `snd_ret_cOooAll`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.SndPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.IniSndPure
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)
open Symbolic.Swarm.CREF.SendWire
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open Proofs.libsignal.SR
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

/-- Pure hardware draw outcome of a failed / aborted `send_wire` call given CLI `coins_cli`. -/
def SndWhisperFailOut (coins_cli : HwBytes) (mid : List MachineEvent) : Prop :=
  mid = [] ∨ ∃ coins : HwBytes, coins.length ≠ 0 ∧ coins <+: coins_cli ∧ mid = [.rng coins]

/-- Pure postcondition of an exit-`0` `send_wire` call on a canonical Whisper record. -/
structure SndWhisperRetOut (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (p : Participant) (recBytes pt coins_cli : HwBytes)
    (mid : List MachineEvent) (retState retMessage : HwBytes) : Prop where
  state_lt : retState.length < 2 ^ 64
  msg_lt : retMessage.length < 2 ^ 64
  canon_out : TR.Pure.TRRecordCanon r p recBytes →
    retState.length < 2 ^ 32 - 2 ^ 20 → TR.Pure.TRRecordCanon r p retState
  eval : TR.Pure.TRRecordCanon r p recBytes →
    ∃ (sess : Session HwBytes) (coins : HwBytes),
      TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes sess ∧
      ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      coins <+: coins_cli ∧
      TR.SendRetCoinsCliPure.pureEvalSendWire (cryptoOf' interpretation) (interpW interpretation)
        (spqrModelOf interpretation) sess none pt coins = some (retState, retMessage)

theorem roleSnapshots_xplBlock_send {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ δ : List Move} {acc blk : List MachineEvent}
    {p : Participant}
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (hf : DeltaFaithful p (runTraceMoves r ms₀) δ)
    (hshape : SendBlockShape blk)
    (h0 : RoleSnapshots r (runTraceMoves r ms₀)) :
    RoleSnapshots r (runTraceMoves r (ms₀ ++ δ)) := by
  rw [TR.runTrace_append]
  refine roleSnapshots_of_oneMove (fun _ m hm hr => ?_) (xplInv_send hB hf hshape) h0
  have hsb := hm.1
  clear hm
  cases m <;> try exact False.elim hsb
  case encrypt me stateIdx coinsLen pqIdx wrap =>
    exact roleSnapshots_encrypt me stateIdx coinsLen pqIdx wrap hr
  case encryptAbort me stateIdx =>
    exact roleSnapshots_encryptAbort me stateIdx hr
  case encryptFail me stateIdx coinsLen =>
    exact roleSnapshots_encryptFail me stateIdx coinsLen hr

theorem sndW_eventIdx_eq_none_of_noSessionEffect
    {tr : ExecTrace} {m : Move} (p : DY.Libsignal.PQXDH.PQXDHEvent → Bool)
    (hno : NoSessionEffect tr m)
    (hp : p .BrokenDH = false ∧ p .BrokenKEM = false := by exact ⟨rfl, rfl⟩) :
    eventIdx p tr (m.next tr) = none := by
  have hq : XplQuiet.QuietExt tr (m.next tr) := XplQuiet.quietExt_of_noSessionEffect hno
  exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.eventIdx_eq_none_of_nonSessionPQExt hq.1
    (fun i h1 h2 => (hq.2 i h1 h2).2.1) hp

theorem sndW_move_encryptAbort_noSessionEffect (tr : ExecTrace) (p : Participant) (si : Nat) :
    NoSessionEffect tr (.encryptAbort p si) :=
  XplSteps.xpl_noEff_of_quietFrom
    (XplSteps.xquiet_bind (xquiet_messageEncryptAbort p si)
      (fun _ => XplSteps.xquiet_of_fix (XplSteps.xfix_pure _)) tr)

theorem sndW_aliceBaseKey_eq_of_recordBytes_eq {r₁ r₂ : RecordRec}
    (h : recordBytes r₁ = recordBytes r₂) :
    r₁.current.aliceBaseKey = r₂.current.aliceBaseKey := by
  have hn := TR.recordBytes_injective h
  simpa [TR.normPending, TR.normPendingS] using
    congrArg (fun r : RecordRec => r.current.aliceBaseKey) hn

theorem sndW_encSession_length_le_encodeRecord (s) :
    (CryptoVerification.E2E.Record.encSession s).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  simp only [Option.map_some, List.length_append]; omega

theorem sndW_pqRatchetState_length_le_encSession (s) :
    s.state.pqRatchetState.length ≤ (CryptoVerification.E2E.Record.encSession s).length := by
  unfold CryptoVerification.E2E.Record.encSession
  have : s.state.pqRatchetState.length ≤
      (CryptoVerification.E2E.Record.bytesField 15 s.state.pqRatchetState).length := by
    unfold CryptoVerification.E2E.Record.bytesField CryptoVerification.E2E.Record.lenField
    split_ifs <;> simp <;> omega
  simp only [List.length_append]; omega

theorem pureCRel_trRecordStateInv (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes)
    (acc : List MachineEvent) (g : Ghost) (ms : List Move) (p : Participant) (rec : HwBytes)
    (hrel : PureCRel interpretation r S who ok records sent accepted acc)
    (hc : Clean interpretation r S who ok g ms acc) (hrec : records p = some rec)
    (hss : SingleSession rec)
    (hnp : ¬ (p = r.alice ∧ PureAliceInitPending interpretation r S g ms rec)) :
    TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms
      (fun q => if q = p then some rec else none) ∧
    CBook interpretation r S g ms sent accepted acc ∧
    CHist interpretation r S g ms ∧ RoleSnapshots r (runTraceMoves r ms) := by
  obtain ⟨⟨hrecs, hbook, hhist, hrole⟩, _⟩ := hrel.clean g ms hc
  rcases pureCRecRelH_single (hrecs p rec hrec).2.2 hss with htr | ⟨rfl, hpend⟩
  · exact ⟨htr, hbook, hhist, hrole⟩
  · exact False.elim (hnp ⟨rfl, hpend⟩)

theorem not_alice_and_aliceInitPending_of_not_recPending {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {p : Participant} {rec : HwBytes}
    (hnpend : ¬ PureRecPending rec) :
    ¬ (p = r.alice ∧ PureAliceInitPending interpretation r S g ms rec) :=
  fun ⟨_, hp⟩ => not_aliceInitPending_of_not_recPending hnpend hp

theorem sentBodies_send_callBlock (acc evs mid : List MachineEvent) (pt msg coins : HwBytes)
    (hmid : (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) :
    TR.sentBodies (acc ++ (evs ++ ((.pt pt :: mid) ++ [.send msg]))) =
      TR.sentBodies (acc ++ evs) ++ (sentBody msg).toList := by
  rcases hmid with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    (simp [TR.sentBodies, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_assoc];
     cases sentBody msg <;> rfl)

theorem matchedPrefix_snoc_encrypt {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₁ : List Move}
    {τ₁ evs mid : List MachineEvent} {p : Participant} {stateIdx : Nat} {st : TripleRatchet.TRState}
    {pt msg coins : HwBytes}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ (τ₁ ++ evs))
    (hwho : who[(callStarts (τ₁ ++ evs)).length]? = some p)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hcur : TripleRatchet.isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hns : st.ns ≠ TripleRatchet.u32Max)
    (hmid : (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins]))
    (hmsg : msg = wireWhisperTag :: gamma interpretation S
      (sendGhost g (runTraceMoves r₀ ms₁).length pt coins)
      (encMsg st coins.length (runTraceMoves r₀ ms₁).length)) :
    MatchedPrefix interpretation r₀ S who (sendGhost g (runTraceMoves r₀ ms₁).length pt coins)
      (ms₁ ++ [Move.encrypt p stateIdx coins.length ((runTraceMoves r₀ ms₁).length + 2) none])
      (τ₁ ++ (evs ++ ((.pt pt :: mid) ++ [.send msg]))) := by
  have hmp' : MatchedPrefix interpretation r₀ S who
      (sendGhost g (runTraceMoves r₀ ms₁).length pt coins) ms₁ (τ₁ ++ evs) :=
    matchedPrefix_sendGhost hmp pt coins
  have hrun' : ModelRun r₀
      (ms₁ ++ [Move.encrypt p stateIdx coins.length ((runTraceMoves r₀ ms₁).length + 2) none]) :=
    modelRun_snoc_encrypt (p := p) (coinsLen := coins.length) hmp.2.1 hcur
  have hcs : callStarts ((MachineEvent.pt pt :: mid) ++ [MachineEvent.send msg]) = [.pt pt] :=
    snd_callStarts_ret pt msg ⟨coins, hmid⟩
  rw [← List.append_assoc]
  refine matchedPrefix_snoc_send
    (m := Move.encrypt p stateIdx coins.length ((runTraceMoves r₀ ms₁).length + 2) none)
    (evs := (.pt pt :: mid) ++ [.send msg])
    hmp' hrun' rfl hwho rfl hcs ?_ ?_
  · rcases hmid with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
    · rw [List.length_nil, visOf_encrypt_zero hst hns]
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> nofun
    · have hcl : coins.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
      rw [visOf_encrypt_ne_zero hst hns hcl]
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> nofun
  · rcases hmid with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
    · rw [List.length_nil, visOf_encrypt_zero hst hns]
      refine List.Forall₂.cons ⟨rfl, ?_⟩
        (List.Forall₂.cons ⟨rfl, _, rfl, ?_⟩ List.Forall₂.nil)
      · show [gamma interpretation S (sendGhost g (runTraceMoves r₀ ms₁).length pt [])
          (randTerm (runTraceMoves r₀ ms₁).length 32)] = [pt]
        rw [gamma_sendGhost_pt]
      · exact hmsg
    · have hcl : coins.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
      rw [visOf_encrypt_ne_zero hst hns hcl]
      refine List.Forall₂.cons ⟨rfl, ?_⟩
        (List.Forall₂.cons ⟨rfl, ?_⟩
          (List.Forall₂.cons ⟨rfl, _, rfl, ?_⟩ List.Forall₂.nil))
      · show [gamma interpretation S (sendGhost g (runTraceMoves r₀ ms₁).length pt coins)
          (randTerm (runTraceMoves r₀ ms₁).length 32)] = [pt]
        rw [gamma_sendGhost_pt]
      · show [gamma interpretation S (sendGhost g (runTraceMoves r₀ ms₁).length pt coins)
          (randTerm ((runTraceMoves r₀ ms₁).length + 1) coins.length)] = [coins]
        rw [gamma_sendGhost_coins _ _ _ _ _ _ hcl]
      · exact hmsg

theorem snd_ret_eval_clause (interpretation : ExternInterpretation)
    (hext : ExternContractsHoldCli interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (S : OpaqueSymbolSemantics) (hSeq : S = compSemOf interpretation r)
    {p : Participant} {recBytes pt coins_cli retState retMessage : HwBytes}
    {mid : List MachineEvent}
    (g : Ghost) (ms₁ : List Move)
    (hcanon : TR.Pure.TRRecordCanon r p recBytes)
    (hnpend : ¬ PureRecPending recBytes)
    (hout : SndWhisperRetOut interpretation r p recBytes pt coins_cli mid retState retMessage) :
    (retState.length < 2 ^ 32 - 2 ^ 20 → TR.Pure.TRRecordCanon r p retState) ∧
    ∃ coins : HwBytes,
      ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      coins <+: coins_cli ∧
      (∀ (rec : RecordRec) (st : TripleRatchet.TRState),
        recBytes = recordBytes rec →
        TR.StateRel interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins) st rec →
        TR.TRKeyShape interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins) st →
        TR.SendRetCoinsCliPure.SpqrInitA2BKdf st.spqr →
        ∃ rec' : RecordRec,
          retState = recordBytes rec' ∧
          TR.StateRel interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins)
            (TR.SendRetCoinsCliPure.encSt st coins.length (runTraceMoves r ms₁).length) rec' ∧
          rec'.current.receiverChains = rec.current.receiverChains ∧
          retMessage = wireWhisperTag ::
            gamma interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins)
              (TR.SendRetCoinsCliPure.encMsg st coins.length (runTraceMoves r ms₁).length)) := by
  obtain ⟨sess, coins, hrc, hmid, hpref, hev⟩ := hout.eval hcanon
  have hppk : sess.pendingPreKey = none := by
    cases h : sess.pendingPreKey with
    | none => rfl
    | some ppk => exact False.elim (hnpend ⟨sess, hrc, by rw [h]; rfl⟩)
  refine ⟨hout.canon_out hcanon, coins, hmid, hpref, fun rec st hrecBytes hrel hks hinit_kdf => ?_⟩
  subst hSeq
  exact TR.SendRetCoinsCliPure.pureEvalSendWire_stateRel_and_message_64
    interpretation r hwf
    ⟨hext.1.x25519_public_key_length (clamp (secretBytes r 0)),
     hext.1.x25519_public_key_length (clamp (secretBytes r 2))⟩
    (compSemOf interpretation r) rfl hext.1
    p recBytes pt coins g ms₁ retState retMessage hout.msg_lt hout.state_lt
    sess hrc hppk hev rec st hrecBytes hrel hks hinit_kdf

theorem snd_ret_cOooAll (interpretation : ExternInterpretation)
    (hext : ExternContractsHoldCli interpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (hSeq : S = compSemOf interpretation r)
    {records : Participant → Option HwBytes} {mid : List MachineEvent}
    {p : Participant} {recBytes pt coins_cli retState retMessage : HwBytes}
    {g : Ghost} {ms₁ : List Move} {st₀ : DY.Libsignal.TripleRatchet.TRState}
    {rec₀ rec' : RecordRec} {coins : HwBytes}
    (hooo_pre : COooAll records)
    (hcanon : TR.Pure.TRRecordCanon r p recBytes)
    (hout : SndWhisperRetOut interpretation r p recBytes pt coins_cli mid retState retMessage)
    (hmid : (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins]))
    (hrecBytes₀ : recBytes = recordBytes rec₀)
    (hrel₀ : TR.StateRel interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins) st₀ rec₀)
    (hinit₀ : TR.SendRetCoinsCliPure.SpqrInitA2BKdf st₀.spqr)
    (hnew : retState = recordBytes rec')
    (hrel' : TR.StateRel interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins)
      (TR.SendRetCoinsCliPure.encSt st₀ coins.length (runTraceMoves r ms₁).length) rec') :
    COooAll (fun q => if q = p then some retState else records q) := by
  refine cOOO_step_update hooo_pre ?_
  obtain ⟨sess, coins', hrc, hmid', _, hev⟩ := hout.eval hcanon
  have hcoins_eq : coins = coins' := snd_coins_eq_of_mid hmid hmid'
  subst hcoins_eq
  obtain ⟨hooo₀, hpqlen₀⟩ := ooo_of_pureTRRecordCanon_sess (r := r) (p := p) hcanon hrc
  have hsend_some := TR.SendRetCoinsCliPure.pureEvalSendWire_some_send_isSome _ _ _ sess none
    pt coins (retState, retMessage) hev
  obtain ⟨⟨newPqState, salt?, pqMsgBytes⟩, hsend⟩ := Option.isSome_iff_exists.mp hsend_some
  have hooo' := (TR.SendRetCoinsCliPure.spqrModelOf_send_growth_pure
    interpretation sess.state.pqRatchetState coins newPqState salt? pqMsgBytes
    hooo₀ hpqlen₀ hsend).1
  have hpq₀ : pqStateOf recBytes = sess.state.pqRatchetState := pqStateOf_of_canonical_Q_pend hrc
  have hpq₀_gam : pqStateOf recBytes =
      gamma interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins) st₀.spqr :=
    pqStateOf_eq_gamma_of_stateRel_pure hrecBytes₀ hrel₀
  have hpq'_gam : pqStateOf retState =
      gamma interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins)
        (TR.SendRetCoinsCliPure.encSt st₀ coins.length (runTraceMoves r ms₁).length).spqr :=
    pqStateOf_eq_gamma_of_stateRel_pure hnew hrel'
  have hcoins_gam : gamma interpretation S
      (sendGhost g (runTraceMoves r ms₁).length pt coins)
      (randTerm ((runTraceMoves r ms₁).length + 1) coins.length) = coins :=
    gamma_sendGhost_coins_all interpretation S g (runTraceMoves r ms₁).length pt coins
  have hsend_gam : (spqrModelOf interpretation).send
      (gamma interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins) st₀.spqr)
      (gamma interpretation S (sendGhost g (runTraceMoves r ms₁).length pt coins)
        (randTerm ((runTraceMoves r ms₁).length + 1) coins.length)) =
      some (newPqState, salt?, pqMsgBytes) := by
    rw [← hpq₀_gam, hpq₀, hcoins_gam]; exact hsend
  have hspqr1 : gamma interpretation S
      (sendGhost g (runTraceMoves r ms₁).length pt coins)
      (DY.Spqr.spqrSend st₀.spqr (randTerm ((runTraceMoves r ms₁).length + 1) coins.length)).1 =
      newPqState := by
    subst hSeq
    exact (TR.SendRetCoinsCliPure.gamma_spqrSend_bridge interpretation hext.1 r
      (sendGhost g (runTraceMoves r ms₁).length pt coins) st₀.spqr
      (randTerm ((runTraceMoves r ms₁).length + 1) coins.length)
      (TR.SendRetCoinsCliPure.spqrInitA2B32_of_kdf interpretation (compSemOf interpretation r) _ hinit₀)
      hsend_gam).1
  rw [hpq'_gam]
  exact hspqr1.symm ▸ hooo'

end Symbolic.Swarm.CREF.CliPure.SndPure
