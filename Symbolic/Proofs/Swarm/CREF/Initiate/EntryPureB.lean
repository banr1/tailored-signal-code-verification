/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureA
public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
public import Symbolic.Proofs.Swarm.CREF.OpkRelC
public import Symbolic.Proofs.Swarm.CREF.Sanitize
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyFrame
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyTR
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedKeyRunInvPure
import Symbolic.Proofs.Swarm.CREF.Initiate.ModelPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.ReadVis
public import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep

/-!
# `session_initiate` `PureCRelAt` and `Clean` Stepping

Proves `CHist` and `PureCRelAt` preservation across accepted `aliceStart` explanations, `Clean`
extensions for rejected and accepted `session_initiate` calls, and `BobRecordBaseKeyInSession`
preservation (`bks_ini_ok`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.IniPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.IniSndPure
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Symbolic.Swarm.COMPOSED

theorem cHist_aliceStart {interpretation : ExternInterpretation} (hext : PureExternContracts interpretation) {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    {bundle : HwBytes} {ds : List HwBytes} (bh : PQXDH.BundleHandles)
    (hhon : HonestBundle interpretation r bundle)
    (hds_lens : ds.map List.length = initiateFullDrawLengths)
    (hm : MatchedPrefix interpretation r S who g
      (ms ++ [.aliceStart r.alice r.bob 4 6 bh 35])
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)))
    (hch : CHist interpretation r S g ms) :
    CHist interpretation r S g (ms ++ [.aliceStart r.alice r.bob 4 6 bh 35]) := by
  obtain ⟨hlens, hlow, hbf, hhist⟩ := hch
  have hbf' : TR.SkippedInstallByteFresh interpretation S g r
      (ms ++ [.aliceStart r.alice r.bob 4 6 bh 35]) :=
    RpkCli.Skr.skippedInstallByteFresh_snoc_of_noNewSk' interpretation S g r ms _
      (RpkCli.Skr.noNewSkSnoc_aliceStart r ms r.alice r.bob 4 6 bh 35) hbf
  let tr := runTraceMoves r ms
  have htr_lens := TR.RecvHistStep2.traceStatesP_runTrace_of_forall r ms hlens
  have htr_low := TR.RecvHistStep2.traceStatesP_runTrace_of_forall r ms hlow
  have htr_hist := TR.RecvHistStep2.traceStatesP_runTrace_of_forall r ms hhist
  rcases aliceStart_next_cases r.alice r.bob 4 6 bh 35 tr with h_id | h_rnd |
    ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest,
      hstA, hregB, hspk_msg, hspkSig_msg, hpq_msg, hpqSig_msg, hopkH, h_ok⟩
  · refine ⟨fun st hst => ?_, fun st hst => ?_, hbf', fun st hst => ?_⟩
    all_goals
      rw [TR.runTrace_snoc, h_id] at hst
      first | exact hlens st hst | exact hlow st hst | exact hhist st hst
  · refine ⟨fun st hst => ?_, fun st hst => ?_, hbf', fun st hst => ?_⟩
    · rw [TR.runTrace_snoc, h_rnd] at hst
      exact TR.RecvHistStep2.forall_availableStates_of_traceStatesP r
        (TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) htr_lens) st hst
    · rw [TR.runTrace_snoc, h_rnd] at hst
      exact TR.RecvHistStep2.forall_availableStates_of_traceStatesP r
        (TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) htr_low) st hst
    · rw [TR.runTrace_snoc, h_rnd] at hst
      exact TR.RecvHistStep2.forall_availableStates_of_traceStatesP r
        (TR.RecvHistStep2.traceStatesP_append (fun _ h => by cases h) htr_hist) st hst
  · have hds_len : ds.length = 34 := by
      have h := congrArg List.length hds_lens
      simpa [initiateFullDrawLengths] using h
    have hF_all := hm.2.2.2.2.2
    rw [runVis_snoc, vis_aliceStart_35 h_ok] at hF_all
    have hlen35 :
        ((.recv bundle :: ds.map MachineEvent.rng) : List MachineEvent).length =
        ((⟨.recv, received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList), .bundle, none⟩ : VisEntry) ::
          (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
            [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }])).length := by
      simp [kyberCoinEntries, hds_len]
    have hF_tail := forall₂_append_suffix_of_length_eq hF_all hlen35
    cases hF_tail with
    | cons hhead _ =>
      have hspk_get := getMessageSentAt_of_netMsgAt hspk_msg
      have hspkSig_get := getMessageSentAt_of_netMsgAt hspkSig_msg
      have hpq_get := getMessageSentAt_of_netMsgAt hpq_msg
      have hpqSig_get := getMessageSentAt_of_netMsgAt hpqSig_msg
      have hrec_eq : received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
          [spk, spkSig, pqpk, pqpkSig] ++ opk.toList := by
        rcases hopkH with ⟨hbh_none, rfl⟩ | ⟨idx, u, hbh_some, rfl, hu_msg⟩
        · simp [received, hbh_none, hspk_get, hspkSig_get, hpq_get, hpqSig_get]
        · have hu_get := getMessageSentAt_of_netMsgAt hu_msg
          simp [received, hbh_some, hspk_get, hspkSig_get, hpq_get, hpqSig_get, hu_get]
      have hBM : PreKeyBundleLayoutMatches interpretation S g bundle ([spk, spkSig, pqpk, pqpkSig] ++ opk.toList) := by
        rw [← hrec_eq]; exact hhead.2
      obtain ⟨hγ_spk, -, -⟩ := bundleMatches_honest hBM hhon
      have hsec2_len : (clamp (secretBytes r 2)).length = 32 := by
        have hlen2 : (secretBytes r 2).length = 32 := by
          rw [(TR.secretBytes_eq r hwf.1).2.2.1]
          exact hwf.2.1 (10, 32) (by rw [TR.setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> simp)
        change (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).length = 32
        unfold DY.Libsignal.TripleRatchet.Refinement.clamp
        simp [hlen2]
      let o := CompTrace.aliceOut tr ikA ikB spk pqpk opk
      have ho_spk : o.spk = spk := rfl
      refine ⟨fun st hst => ?_, fun st hst => ?_, hbf', fun st hst => ?_⟩
      · rw [TR.runTrace_snoc, h_ok] at hst
        refine availableStates_aliceStartTrOfOut_forall r.alice r.bob o ?_ htr_lens st hst
        intro c hc
        dsimp only [aliceStartState] at hc
        rw [List.mem_singleton] at hc
        subst hc
        dsimp only
        rw [ho_spk, hγ_spk]
        exact hext.1.x25519_public_key_length (clamp (secretBytes r 2))
      · rw [TR.runTrace_snoc, h_ok] at hst
        refine availableStates_aliceStartTrOfOut_forall r.alice r.bob o ?_ htr_low st hst
        intro c hc
        dsimp only [aliceStartState] at hc
        rw [List.mem_singleton] at hc
        subst hc
        dsimp only
        rw [ho_spk, hγ_spk]
        exact hext.1.x25519_public_key_not_low_order (clamp (secretBytes r 2)) hsec2_len
      · rw [TR.runTrace_snoc, h_ok] at hst
        refine availableStates_aliceStartTrOfOut_forall r.alice r.bob o ?_ htr_hist st hst
        dsimp only [aliceStartState, List.map_cons, List.map_nil]
        exact List.nodup_singleton _

theorem b2_encodeRecord_ne_nil (s : Session (List (BitVec 8))) :
    CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ ≠ [] := by
  unfold CryptoVerification.E2E.Record.encodeRecord
    CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  have hk : CryptoVerification.LibsignalProtoCodec.encodeKey 1 .lengthDelimited = [0x0a#8] := rfl
  rw [hk]
  simp

theorem ne_nil_of_pureAliceInitPending {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {rec : HwBytes}
    (hp : PureAliceInitPending interpretation r S g ms rec) : rec ≠ [] := by
  obtain ⟨sess, -, -, -, -, -, -, -, -, -, -, hcanon, -⟩ := hp
  have henc : CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩ = rec := by
    unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    exact hcanon.1.symm
  rw [← henc]
  exact b2_encodeRecord_ne_nil sess

theorem ini_ok_roleSnapshots {r : ProtocolSetup} {ms₀ pre post : List Move}
    (bh : PQXDH.BundleHandles)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.aliceStart r.alice r.bob 4 6 bh 35).next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hrole₀ : RoleSnapshots r (runTraceMoves r ms₀)) :
    RoleSnapshots r
      (runTraceMoves r (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh 35 :: post))) := by
  have hrole_pre : RoleSnapshots r (runMoves pre (runTraceMoves r ms₀)).1 :=
    roleSnapshots_of_movesFrom_invisibleNoEffect hpre hrole₀
  have hrole_mid : RoleSnapshots r
      ((Move.aliceStart r.alice r.bob 4 6 bh 35).next (runMoves pre (runTraceMoves r ms₀)).1) :=
    roleSnapshots_aliceStart rfl r.bob 4 6 bh 35 hrole_pre
  have hrole_post : RoleSnapshots r
      (runMoves post ((Move.aliceStart r.alice r.bob 4 6 bh 35).next (runMoves pre (runTraceMoves r ms₀)).1)).1 :=
    roleSnapshots_of_movesFrom_invisibleNoEffect hpost hrole_mid
  rw [TR.runTrace_append, runMoves_append]
  exact hrole_post

/-- Per-explanation `PureCRelAt` step across an accepted `initiate` block at `shown = 35`. -/
theorem ini_ok_step_pureCRelAt (interpretation : ExternInterpretation)
    (hext : PureExternContracts interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    {who : List Participant}
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes)
    (acc : List MachineEvent) (bundle : HwBytes) (ds : List HwBytes) (recState : HwBytes)
    (hhon : HonestBundle interpretation r bundle)
    (hV1 : AliceInitiatedV1PostPure interpretation r bundle ds recState)
    (hlens : ds.map List.length = initiateFullDrawLengths)
    {g : Ghost} {ms₀ pre post : List Move} (bh : PQXDH.BundleHandles)
    (hm_mid : MatchedPrefix interpretation r (compSemOf interpretation r) who g
      (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35])
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.aliceStart r.alice r.bob 4 6 bh 35).next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hrel₀ : PureCRelAt interpretation r (compSemOf interpretation r) g ms₀
      records sent accepted acc) :
    PureCRelAt interpretation r (compSemOf interpretation r) g
      (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh 35 :: post))
      (fun q => if q = r.alice then some recState else records q) sent accepted
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) := by
  let S := compSemOf interpretation r
  have hq_pre : XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := b2_quietPre hpre
  have hq_post : XplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35]))
      (runTraceMoves r (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh 35 :: post))) :=
    b2_quietPost hpost
  have hpend_mid : PureAliceInitPending interpretation r S g
      (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35]) recState :=
    initiate_post_bridge interpretation hext r hwf g (ms₀ ++ pre) acc
      bundle ds recState bh hhon hV1 hlens hm_mid
  have hpend_full : PureAliceInitPending interpretation r S g
      (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh 35 :: post)) recState :=
    XplQuiet.quiet_pureAliceInitPending hq_post hpend_mid
  obtain ⟨hrecs₀, ⟨hsent₀, hns₀, hacc1₀, hacc2₀⟩, hch₀, hrole₀⟩ := hrel₀
  have hch_pre : CHist interpretation r S g (ms₀ ++ pre) :=
    XplQuiet.quiet_cHist hq_pre hch₀
  have hch_mid : CHist interpretation r S g (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35]) :=
    cHist_aliceStart hext hwf bh hhon hlens hm_mid hch_pre
  have hch_full : CHist interpretation r S g
      (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh 35 :: post)) :=
    XplQuiet.quiet_cHist hq_post hch_mid
  have hns_pre : b2NsInv sent.length (runTraceMoves r (ms₀ ++ pre)) :=
    b2NsInv_quiet hq_pre hns₀
  have hns_mid : b2NsInv sent.length
      (runTraceMoves r (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35])) := by
    rw [TR.runTrace_snoc]
    exact b2NsInv_next_aliceStart r.alice r.bob 4 6 bh 35 hns_pre
  have hns_full : TR.TRNsBound r
      (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh 35 :: post)) sent :=
    b2NsInv_quiet hq_post hns_mid
  have hbd_eq : bobDoneBaseKeys
      (runTraceMoves r (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh 35 :: post))) =
      bobDoneBaseKeys (runTraceMoves r ms₀) := by
    rw [XplQuiet.quiet_bobDoneBaseKeys hq_post, TR.runTrace_snoc,
        bobDoneBaseKeys_next_aliceStart, XplQuiet.quiet_bobDoneBaseKeys hq_pre]
  have hsent_eq : TR.sentBodies (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) =
      TR.sentBodies acc := by
    rw [TR.sentBodies_append, ini_sentBodies_nil, List.append_nil]
  refine ⟨fun p bs hpb => ?_,
    ⟨hsent₀.trans hsent_eq.symm, hns_full,
      by rw [hbd_eq]; exact hacc1₀,
      by rw [hbd_eq]; exact hacc2₀⟩,
    hch_full,
    ini_ok_roleSnapshots bh hpre hpost hrole₀⟩
  by_cases hp : p = r.alice
  · subst hp
    simp only [↓reduceIte, Option.some.injEq] at hpb
    subst hpb
    exact ⟨Or.inl rfl, ne_nil_of_pureAliceInitPending hpend_full,
      Or.inl (Or.inr ⟨rfl, hpend_full⟩)⟩
  · simp only [hp, ↓reduceIte] at hpb
    obtain ⟨hwho_p, hne_p, hrel_p⟩ := hrecs₀ p bs hpb
    refine ⟨hwho_p, hne_p, ini_pureCRecRelH_mono (fun b' hb' => ?_) hrel_p⟩
    have hb'_pre := XplQuiet.quiet_pureCRecRel hq_pre hb'
    have hfr_mid : b2Frame r.alice (runTraceMoves r (ms₀ ++ pre))
        (runTraceMoves r (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35])) := by
      rw [TR.runTrace_snoc]
      exact b2Frame_next_aliceStart _ r.alice r.bob 4 6 bh 35
    have hb'_mid := b2Frame_pureCRecRel_alice hfr_mid hp hb'_pre
    exact XplQuiet.quiet_pureCRecRel hq_post hb'_mid

theorem ini_no_readColMove_in_initOk_delta {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms_opk : List Move}
    (hms : ms_opk = [] ∨ ∃ t, ms_opk = [.attackerSend t])
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : PQXDH.BundleHandles) (shown : Nat) :
    ∀ m ∈ (ms_opk ++ [Move.aliceStart a b idStateIdx regIdxB bh shown]),
      ∀ pre e, ¬ MoveReadsCollidingMsg interpretation r S g pre e m := by
  intro m hm pre e hc
  rcases hms with rfl | ⟨t, rfl⟩ <;>
    simp only [List.nil_append, List.singleton_append, List.mem_cons, List.not_mem_nil,
      or_false] at hm
  · subst hm; exact hc
  · rcases hm with rfl | rfl <;> exact hc

theorem ini_clean_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} (bundle : HwBytes) (ds : List HwBytes)
    (hc : Clean interpretation r S who ok g ms acc)
    (hok : ok (callStarts acc).length = false) :
    Clean interpretation r S who ok g
      (Sanitize.sanitizeMoves (setupTrace r) ms ++ [.reject (ds.map List.length)])
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) := by
  have hex := ini_explains_reject interpretation r S who ok g ms acc bundle ds hc.1 hok
  have hnrc_s : ¬ ReadCollision interpretation r S g
      (Sanitize.sanitizeMoves (setupTrace r) ms) acc :=
    mt Sanitize.readCollision_sanitizeMoves_iff.mp hc.2
  have hnrc' : ¬ ReadCollision interpretation r S g
      (Sanitize.sanitizeMoves (setupTrace r) ms ++ [.reject (ds.map List.length)])
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) :=
    not_readCollision_append_noAccept hnrc_s
      (fun e he pt heq => by subst heq; exact ini_no_accept_in_blk bundle ds _ he rfl)
      (fun m hm _ _ hcol => by simp at hm; subst hm; exact hcol)
  exact ⟨hex, hnrc'⟩

theorem ini_clean_initOk (interpretation : ExternInterpretation)
    (hext : PureExternContracts interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (acc : List MachineEvent) (bundle : HwBytes) (ds : List HwBytes)
    (hc : Clean interpretation r (compSemOf interpretation r) who ok g ms acc)
    (hwho : who[(callStarts acc).length]? = some r.alice)
    (hok_call : ok (callStarts acc).length = true)
    (hhon : HonestBundle interpretation r bundle) (hok : IniOkBin bundle ds) :
    let ms₀ := Sanitize.sanitizeMoves (setupTrace r) ms
    ∃ (ms_opk : List Move) (bh : DY.Libsignal.PQXDH.BundleHandles) (g' : Ghost),
      (ms_opk = [] ∨ ∃ t, ms_opk = [.attackerSend t] ∧ t.AttackerKnows (runTraceMoves r ms₀)) ∧
      g'.addr = g.addr ∧ (∀ i j, i < (runTraceMoves r ms).length → g'.σ i j = g.σ i j) ∧
      Clean interpretation r (compSemOf interpretation r) who ok g'
        (ms₀ ++ ms_opk ++ [.aliceStart r.alice r.bob 4 6 bh 35])
        (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) := by
  intro ms₀
  let S := compSemOf interpretation r
  obtain ⟨ms_opk, bh, g', hms, haddr, hσ, hex'⟩ :=
    ini_explains_initOk interpretation hext r hwf who ok g ms acc bundle ds
      hc.1 hwho hok_call hhon hok
  have hframe : CBadSigmaFrame g g' (runTraceMoves r ms).length := ⟨fun ts hts len => hσ ts len hts, haddr⟩
  have hc_g' : Clean interpretation r S who ok g' ms acc :=
    cbadG2_cleanBy_transfer hframe hc
  have hnrc_s : ¬ ReadCollision interpretation r S g' ms₀ acc :=
    mt Sanitize.readCollision_sanitizeMoves_iff.mp hc_g'.2
  have hms_shape : ms_opk = [] ∨ ∃ t, ms_opk = [.attackerSend t] := by
    rcases hms with rfl | ⟨t, rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨t, rfl⟩
  have hnrc' : ¬ ReadCollision interpretation r S g'
      (ms₀ ++ (ms_opk ++ [.aliceStart r.alice r.bob 4 6 bh 35]))
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng)) :=
    not_readCollision_append_noAccept hnrc_s
      (fun e he pt heq => by subst heq; exact ini_no_accept_in_blk bundle ds _ he rfl)
      (ini_no_readColMove_in_initOk_delta hms_shape r.alice r.bob 4 6 bh 35)
  rw [← List.append_assoc] at hnrc'
  exact ⟨ms_opk, bh, g', hms, haddr, hσ, ⟨hex', hnrc'⟩⟩

theorem ini_ok_bka {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {records : Participant → Option HwBytes} {accepted : List HwBytes} (recState : HwBytes)
    (hbka : BobRecordBaseKeyInAccepted r records accepted) :
    BobRecordBaseKeyInAccepted r
      (fun q => if q = r.alice then some recState else records q) accepted := by
  intro rr hrr
  simp only [hwf.1.symm, ↓reduceIte] at hrr
  exact hbka rr hrr

theorem ini_runMoves_fst_aliceStart_eq_35 (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) (shown : Nat) (pre post : List Move) (tr : ExecTrace) :
    (runMoves (pre ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post) tr).1 =
      (runMoves (pre ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post) tr).1 := by
  rw [runMoves_append, runMoves_append]
  rfl

theorem ini_runTrace_aliceStart_eq_35 (r : ProtocolSetup) (ms₀ pre post : List Move)
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : PQXDH.BundleHandles) (shown : Nat) :
    runTraceMoves r (ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post)) =
      runTraceMoves r (ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post)) := by
  rw [TR.runTrace_append, TR.runTrace_append]
  exact ini_runMoves_fst_aliceStart_eq_35 a b idStateIdx regIdxB bh shown pre post (runTraceMoves r ms₀)

theorem ini_pureCRelAt_aliceStart_of_35 {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {records : Participant → Option HwBytes}
    {sent accepted : List HwBytes} {acc : List MachineEvent} {g : Ghost}
    {ms₀ pre post : List Move} {a b : Participant} {idStateIdx regIdxB : Nat}
    {bh : PQXDH.BundleHandles} {shown : Nat}
    (hrel : PureCRelAt interpretation r S g
      (ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post))
      records sent accepted acc) :
    PureCRelAt interpretation r S g
      (ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post))
      records sent accepted acc := by
  have htr := ini_runTrace_aliceStart_eq_35 r ms₀ pre post a b idStateIdx regIdxB bh shown
  have hq : XplQuiet.QuietExt
      (runTraceMoves r (ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh 35 :: post)))
      (runTraceMoves r (ms₀ ++ (pre ++ Move.aliceStart a b idStateIdx regIdxB bh shown :: post))) := by
    rw [htr]
    exact XplQuiet.quietExt_refl _
  obtain ⟨hrecs, ⟨hsent, hns, hbk1, hbk2⟩, hch, hrole⟩ := hrel
  refine ⟨fun p bs hpb => ?_, ⟨hsent, ?_, ?_, ?_⟩, XplQuiet.quiet_cHist hq hch, ?_⟩
  · obtain ⟨hp, hne, hcr⟩ := hrecs p bs hpb
    exact ⟨hp, hne, ini_pureCRecRelH_mono (fun _ => XplQuiet.quiet_pureCRecRel hq) hcr⟩
  · change b2NsInv sent.length (runTraceMoves r _)
    rw [htr]; exact hns
  · rw [XplQuiet.quiet_bobDoneBaseKeys hq]; exact hbk1
  · rw [XplQuiet.quiet_bobDoneBaseKeys hq]; exact hbk2
  · rw [htr]; exact hrole

theorem newBobSinfo_of_b2Frame_alice {r : ProtocolSetup} (hab : r.alice ≠ r.bob)
    {tr₀ tr : ExecTrace} (hf : b2Frame r.alice tr₀ tr) : NewBobSinfo r.bob tr₀ tr := by
  intro j st hj hat
  exact False.elim (hab ((hf.2 j hj).1 ⟨⟨r.bob, st⟩⟩ hat).symm)

theorem bks_ini_ok {interpretation : ExternInterpretation} {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ pre post : List Move} (bh : PQXDH.BundleHandles)
    (shown : Nat) {records records' : Participant → Option HwBytes}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.aliceStart r.alice r.bob 4 6 bh 35).next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hrec : records' r.bob = records r.bob)
    (hbks : BobRecordBaseKeyInSession interpretation r S g ms₀ records) :
    BobRecordBaseKeyInSession interpretation r S g
      (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh shown :: post)) records' := by
  have hpre_noeff : MovesFrom (fun tr m => NoSessionEffect tr m) (runTraceMoves r ms₀) pre :=
    movesFrom_mono (fun _ _ h => h.2) _ _ hpre
  have hpost_noeff : MovesFrom (fun tr m => NoSessionEffect tr m)
      (runTraceMoves r (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35])) post := by
    rw [TR.runTrace_snoc, TR.runTrace_append]
    exact movesFrom_mono (fun _ _ h => h.2) _ _ hpost
  have hbks1 : BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ pre) records :=
    bks_frame hpre_noeff rfl hbks
  have hnew_as : NewBobSinfo r.bob (runTraceMoves r (ms₀ ++ pre))
      (runTraceMoves r (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35])) := by
    rw [TR.runTrace_snoc]
    exact newBobSinfo_of_b2Frame_alice hwf.1
      (b2Frame_next_aliceStart (runTraceMoves r (ms₀ ++ pre)) r.alice r.bob 4 6 bh 35)
  have hbks2 : BobRecordBaseKeyInSession interpretation r S g
      (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35]) records :=
    bks_of_ext hnew_as (bks_rec_of_eq rfl) hbks1
  have hbks3 : BobRecordBaseKeyInSession interpretation r S g
      ((ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35]) ++ post) records' :=
    bks_frame hpost_noeff hrec hbks2
  intro rr hrr
  show BobBaseKeyOn interpretation S g r.bob
    (runTraceMoves r (ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh shown :: post)))
    rr.current.aliceBaseKey
  rw [ini_runTrace_aliceStart_eq_35 r ms₀ pre post r.alice r.bob 4 6 bh shown]
  rw [show ms₀ ++ (pre ++ Move.aliceStart r.alice r.bob 4 6 bh 35 :: post) =
      (ms₀ ++ pre ++ [.aliceStart r.alice r.bob 4 6 bh 35]) ++ post by simp [List.append_assoc]]
  exact hbks3 rr hrr

end Symbolic.Swarm.CREF.CliPure.IniPure
