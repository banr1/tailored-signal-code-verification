/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPureA
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyTR
import Symbolic.Proofs.Swarm.CREF.CBad
import Symbolic.Proofs.Swarm.CREF.Initiate.TransferPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendWire.RecvSimV3SendPure
import Symbolic.Proofs.Swarm.CREF.SendWire.StateInv
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPure
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Returning Whisper `SendWire` Refinement Step

Proves Bob base-key and Kyber record preservation (`snd_ret_bka`, `snd_ret_bks_rec`, `snd_ret_bkn`),
the per-explanation `PureCRelAt` step (`snd_ret_step_at`), and the returning Whisper `send_wire`
step (`snd_ret_pure_step`).
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
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)
open Symbolic.Swarm.CREF.SendWire
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open Proofs.libsignal.SR
open Proofs.libsignal.Hooks2 (cryptoOf' cryptoOf'_F)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.COMPOSED

theorem sessionToRecordRecPending_pendingKyberPreKey_eq_none_iff (s : Session HwBytes) :
    (TR.SendRetCoinsCliPure.sessionToRecordRecPending s).current.pendingKyberPreKey = none ↔
      s.pendingKyberPreKey = none := by
  dsimp only [TR.SendRetCoinsCliPure.sessionToRecordRecPending]
  exact Option.map_eq_none_iff

theorem recordBytes_pendingKyberPreKey_eq_none_iff {r₁ r₂ : RecordRec}
    (h : recordBytes r₁ = recordBytes r₂) :
    r₁.current.pendingKyberPreKey = none ↔ r₂.current.pendingKyberPreKey = none := by
  have hn := TR.recordBytes_injective h
  have hp := congrArg (fun r => r.current.pendingKyberPreKey) hn
  dsimp only [TR.normPending, TR.normPendingS] at hp
  constructor <;> intro hnone
  · cases h2 : r₂.current.pendingKyberPreKey with
    | none => rfl
    | some k2 => rw [hnone, h2] at hp; simp at hp
  · cases h1 : r₁.current.pendingKyberPreKey with
    | none => rfl
    | some k1 => rw [h1, hnone] at hp; simp at hp

private theorem snd_ret_session_out (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    {mid : List MachineEvent} {p : Participant}
    {recBytes pt coins_cli retState retMessage : HwBytes} {rec₀ : RecordRec}
    {g' : Ghost} {st₀ : DY.Libsignal.TripleRatchet.TRState}
    (hcanon : TR.Pure.TRRecordCanon r p recBytes)
    (hnpend : ¬ PureRecPending recBytes)
    (hout : SndWhisperRetOut interpretation r p recBytes pt coins_cli mid retState retMessage)
    (hrecBytes₀ : recBytes = recordBytes rec₀)
    (hrel_old : TR.StateRel interpretation S g' st₀ rec₀) :
    ∃ (sess : Session HwBytes) (sc : SenderChain) (nextCk : ChainKey) (newPqState : HwBytes),
      TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes sess ∧
      TR.normPending rec₀ = TR.normPending (TR.SendRetCoinsCliPure.sessionToRecordRecPending sess) ∧
      recordBytes (TR.SendRetCoinsCliPure.sessionToRecordRecPending
        { sess with state :=
          { sess.state with
            senderChain := some { sc with chainKey := nextCk }
            pqRatchetState := newPqState } }) = retState := by
  obtain ⟨sess, coins', hrc, _, _, hev⟩ := hout.eval hcanon
  have hppk : sess.pendingPreKey = none := by
    cases h : sess.pendingPreKey with
    | none => rfl
    | some ppk => exact False.elim (hnpend ⟨sess, hrc, by rw [h]; rfl⟩)
  obtain ⟨hnorm_eq, _, hseeds⟩ :=
    TR.SendRetCoinsCliPure.rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes₀ hrc
  have hrel_sess : TR.StateRel interpretation S g' st₀
      (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec sess) := by
    rw [← TR.SendRetCoinsCliPure.stateRel_sessionToRecordRecPending_iff,
        ← TR.SendRetCoinsCliPure.stateRel_normPending_iff, ← hnorm_eq,
        TR.SendRetCoinsCliPure.stateRel_normPending_iff]
    exact hrel_old
  obtain ⟨hver, _, _, _, ⟨remote, hrem, _⟩, ⟨sc, hsc, _, _, _, _⟩⟩ :=
    TR.SendRetCoinsCliPure.stateRel_sessionToRecordRec_extract_TR interpretation S g' st₀ sess hrel_sess
  have hsend_some :=
    TR.SendRetCoinsCliPure.pureEvalSendWire_some_send_isSome _ _ _ sess none pt coins' (retState, retMessage) hev
  obtain ⟨⟨newPqState, salt?, pqMsgBytes⟩, hsend⟩ := Option.isSome_iff_exists.mp hsend_some
  obtain ⟨_, hexec⟩ := TR.SendRetCoinsCliPure.pureEvalSendWire_exec
    (cryptoOf' interpretation) (interpW interpretation)
    (spqrModelOf interpretation) sess none pt coins' (retState, retMessage) sc remote newPqState pqMsgBytes salt? hev hppk hver hsc hrem hsend
  rw [cryptoOf'_F] at hexec; injection hexec with hstate_eq _
  set F := DY.Libsignal.Refinement.sha256CompressFunction interpretation
  set nextCk : ChainKey :=
    ⟨CryptoGames.HKDF.bytesToKey32 (CryptoGames.Ratchet.chainHmac F sc.chainKey.key CryptoGames.Ratchet.chainKeySeed),
      sc.chainKey.index + 1⟩
  set sess' :=
    { sess with state := { sess.state with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } }
  have hsess'_len : (CryptoVerification.E2E.Record.encSession sess').length < 2 ^ 64 :=
    lt_of_le_of_lt (sndW_encSession_length_le_encodeRecord sess') (hstate_eq ▸ hout.state_lt)
  have hpq'_len : sess'.state.pqRatchetState.length < 2 ^ 64 := by
    have := sndW_pqRatchetState_length_le_encSession sess'; omega
  refine ⟨sess, sc, nextCk, newPqState, hrc, hnorm_eq, ?_⟩
  rw [hstate_eq]
  exact TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_eq_encodeRecord_64 sess'
    (by dsimp only [sess']; omega) hpq'_len hseeds hsess'_len

theorem snd_ret_bka (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    {records : Participant → Option HwBytes} {accepted : List HwBytes}
    {mid : List MachineEvent} {p : Participant}
    {recBytes pt coins_cli retState retMessage : HwBytes} {rec₀ : RecordRec}
    {g' : Ghost} {st₀ : DY.Libsignal.TripleRatchet.TRState}
    (hcanon : TR.Pure.TRRecordCanon r p recBytes)
    (hnpend : ¬ PureRecPending recBytes)
    (hout : SndWhisperRetOut interpretation r p recBytes pt coins_cli mid retState retMessage)
    (hrec : records p = some recBytes)
    (hrecBytes₀ : recBytes = recordBytes rec₀)
    (hrel_old : TR.StateRel interpretation S g' st₀ rec₀)
    (hbka : BobRecordBaseKeyInAccepted r records accepted) :
    BobRecordBaseKeyInAccepted r
      (fun q => if q = p then some retState else records q) accepted := by
  obtain ⟨sess, sc, nextCk, newPqState, _, hnorm_eq, hrec'_bytes⟩ :=
    snd_ret_session_out interpretation r S hcanon hnpend hout hrecBytes₀ hrel_old
  set sess' :=
    { sess with state := { sess.state with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } }
  have hbase : (TR.SendRetCoinsCliPure.sessionToRecordRecPending sess').current.aliceBaseKey =
      rec₀.current.aliceBaseKey := by
    have h := congrArg (fun x : RecordRec => x.current.aliceBaseKey) hnorm_eq
    dsimp only [TR.normPending, TR.normPendingS, TR.SendRetCoinsCliPure.sessionToRecordRecPending,
      Swarm.Phase0WholeFunctionBridge.sessionToSessionRec, sess'] at h ⊢
    exact h.symm
  intro rr hrr; dsimp only at hrr
  by_cases hbp : r.bob = p
  · simp only [hbp, ↓reduceIte, Option.some.injEq] at hrr
    have heq : rr.current.aliceBaseKey = rec₀.current.aliceBaseKey := by
      rw [← hbase]; exact sndW_aliceBaseKey_eq_of_recordBytes_eq (hrr.symm.trans hrec'_bytes.symm)
    rw [heq]; exact hbka rec₀ (by rw [hbp, hrec, hrecBytes₀])
  · simp only [hbp, ↓reduceIte] at hrr; exact hbka rr hrr

theorem snd_ret_bks_rec (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    {records : Participant → Option HwBytes} {mid : List MachineEvent} {p : Participant}
    {recBytes pt coins_cli retState retMessage : HwBytes} {rec₀ : RecordRec}
    {g' : Ghost} {st₀ : DY.Libsignal.TripleRatchet.TRState}
    (hcanon : TR.Pure.TRRecordCanon r p recBytes)
    (hnpend : ¬ PureRecPending recBytes)
    (hout : SndWhisperRetOut interpretation r p recBytes pt coins_cli mid retState retMessage)
    (hrec : records p = some recBytes)
    (hrecBytes₀ : recBytes = recordBytes rec₀)
    (hrel_old : TR.StateRel interpretation S g' st₀ rec₀) :
    ∀ rr' : RecordRec, (if r.bob = p then some retState else records r.bob) = some (recordBytes rr') →
      ∃ rr : RecordRec, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey := by
  obtain ⟨sess, sc, nextCk, newPqState, _, hnorm_eq, hrec'_bytes⟩ :=
    snd_ret_session_out interpretation r S hcanon hnpend hout hrecBytes₀ hrel_old
  set sess' :=
    { sess with state := { sess.state with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } }
  have hbase : (TR.SendRetCoinsCliPure.sessionToRecordRecPending sess').current.aliceBaseKey =
      rec₀.current.aliceBaseKey := by
    have h := congrArg (fun x : RecordRec => x.current.aliceBaseKey) hnorm_eq
    dsimp only [TR.normPending, TR.normPendingS, TR.SendRetCoinsCliPure.sessionToRecordRecPending,
      Swarm.Phase0WholeFunctionBridge.sessionToSessionRec, sess'] at h ⊢
    exact h.symm
  intro rr' hrr'
  by_cases hbp : r.bob = p
  · simp only [hbp, ↓reduceIte, Option.some.injEq] at hrr'
    refine ⟨rec₀, by rw [hbp, hrec, hrecBytes₀], ?_⟩
    rw [← hbase]; exact sndW_aliceBaseKey_eq_of_recordBytes_eq (hrr'.symm.trans hrec'_bytes.symm)
  · simp only [hbp, ↓reduceIte] at hrr'; exact ⟨rr', hrr', rfl⟩

theorem snd_ret_bkn (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    {records : Participant → Option HwBytes} {mid : List MachineEvent} {p : Participant}
    {recBytes pt coins_cli retState retMessage : HwBytes} {rec₀ : RecordRec}
    {g₀ : Ghost} {st₀ : DY.Libsignal.TripleRatchet.TRState}
    (hcanon : TR.Pure.TRRecordCanon r p recBytes)
    (hnpend : ¬ PureRecPending recBytes)
    (hout : SndWhisperRetOut interpretation r p recBytes pt coins_cli mid retState retMessage)
    (hrec : records p = some recBytes)
    (hrecBytes₀ : recBytes = recordBytes rec₀)
    (hrel_st₀ : TR.StateRel interpretation S g₀ st₀ rec₀)
    (hbkn : PureBobKyberNone r records) :
    PureBobKyberNone r (fun q => if q = p then some retState else records q) := by
  intro rr hrr; dsimp only at hrr
  by_cases hbp : r.bob = p
  · subst hbp
    simp only [↓reduceIte, Option.some.injEq] at hrr
    obtain ⟨sess, sc, nextCk, newPqState, hrc, _, hrec'_bytes⟩ :=
      snd_ret_session_out interpretation r S hcanon hnpend hout hrecBytes₀ hrel_st₀
    set sess' :=
      { sess with state := { sess.state with senderChain := some { sc with chainKey := nextCk }, pqRatchetState := newPqState } }
    have hbs_in := TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q hrc
    have hkyb0 : sess.pendingKyberPreKey = none :=
      (sessionToRecordRecPending_pendingKyberPreKey_eq_none_iff sess).mp
        (hbkn (TR.SendRetCoinsCliPure.sessionToRecordRecPending sess)
          (by rw [hbs_in, ← hrc.1]; exact hrec))
    have hkyb_rec' : (TR.SendRetCoinsCliPure.sessionToRecordRecPending sess').current.pendingKyberPreKey = none := by
      dsimp only [TR.SendRetCoinsCliPure.sessionToRecordRecPending, sess']
      rw [hkyb0]; rfl
    exact (recordBytes_pendingKyberPreKey_eq_none_iff (hrr.symm.trans hrec'_bytes.symm)).mpr hkyb_rec'
  · simp only [hbp, ↓reduceIte] at hrr; exact hbkn rr hrr

private theorem pureTRRecordStateInv_snoc_encrypt_wrap_single
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots} {g : Ghost} {ms₁ : List Move}
    {p : Participant} {stateIdx coinsLen : Nat}
    {wrap : Option (Nat × Nat)} {st : TripleRatchet.TRState} {rec rec' : RecordRec}
    {newBytes : HwBytes}
    (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max)
    (hnew : newBytes = recordBytes rec')
    (hrel' : TR.StateRel interpretation S g
      (encSt st coinsLen (runTraceMoves r₀ ms₁).length) rec')
    (hchains : rec'.current.receiverChains = rec.current.receiverChains)
    (hsk : ∀ c ∈ rec.current.receiverChains, ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r₀ ms₁).EventLoggedAt
          (TripleRatchet.TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec k.1) seed
            rIdx srcIdx) skIdx ∧
        !TripleRatchet.skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx ∧
        !TripleRatchet.receiverKeyUsedB (runTraceMoves r₀ ms₁) (st.sessionInfo p) seed (UInt32.ofBitVec k.1)
          rIdx ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = TR.serializedKey (gamma interpretation S g pk) ∧
        (TripleRatchet.findRecvChain st.toDRState.recv pk).isSome = true)
    (hcanon' : newBytes.length < 2 ^ 32 - 2 ^ 20 → Z.canon p newBytes)
    (hks : TR.TRKeyShape interpretation S g st)
    (hnd : (rec.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
      (∀ c ∈ rec.current.receiverChains, (c.messageKeys.map Prod.fst).Nodup) ∧
      ∀ c ∈ rec.current.receiverChains, ∀ k ∈ c.messageKeys,
        ∃ ck, c.chainKey = some ck ∧ k.1 < ck.1) :
    TR.PureTRRecordStateInv interpretation r₀ S Z g
      (ms₁ ++ [Move.encrypt p stateIdx coinsLen ((runTraceMoves r₀ ms₁).length + 2) wrap])
      (fun q => if q = p then some newBytes else none) := by
  have htr : runTraceMoves r₀
      (ms₁ ++ [Move.encrypt p stateIdx coinsLen ((runTraceMoves r₀ ms₁).length + 2) wrap]) =
      encTr (runTraceMoves r₀ ms₁) p stateIdx coinsLen st := by
    rw [TR.runTrace_snoc, encrypt_wrap_next_of_some (wrap := wrap) hst hns]
  intro q b hqb
  by_cases hqp : q = p
  · subst hqp
    simp only [↓reduceIte, Option.some.injEq] at hqb
    subst hqb
    refine ⟨hp_mem, rec', encSt st coinsLen (runTraceMoves r₀ ms₁).length,
      (runTraceMoves r₀ ms₁).length + 5, hnew,
      by rw [htr, getLocalState_fst_encTr_new],
      by rw [htr, isCurrentSnapshot_encTr_new],
      hrel', ?_, hcanon',
      trKeyShape_encSt hks coinsLen (runTraceMoves r₀ ms₁).length,
      by rw [hchains]; exact hnd⟩
    intro c hc k hk
    rw [hchains] at hc
    obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam⟩ := hsk c hc k hk
    have hsk_lt : skIdx < (runTraceMoves r₀ ms₁).length := by
      have hlog' := hlog
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog'
      have := DY.Trace.at?_eq_some_implies_length_le (EntryT := TR.TREntry) (runTraceMoves r₀ ms₁) skIdx
      rw [hlog'] at this; exact this
    exact ⟨pk, rIdx, srcIdx, skIdx, seed,
      by rw [htr, eventLoggedAt_encTr_of_lt _ _ _ _ _ hsk_lt]; exact hlog,
      by rw [htr, skippedKeyUsedB_encTr]; exact hsu,
      by rw [htr, receiverKeyUsedB_encTr]; exact hru,
      hgam⟩
  · simp only [hqp, ↓reduceIte] at hqb
    cases hqb

/-- Per-explanation `PureCRelAt` step for a returning Whisper `send_wire` call. -/
theorem snd_ret_step_at (interpretation : ExternInterpretation)
    (hext : ExternContractsHoldCli interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (S : OpaqueSymbolSemantics) (hSeq : S = compSemOf interpretation r)
    {who : List Participant} {records : Participant → Option HwBytes}
    {sent accepted : List HwBytes} {acc mid : List MachineEvent}
    {p : Participant} {recBytes pt coins_cli retState retMessage coins : HwBytes}
    (hp : p = r.alice ∨ p = r.bob)
    (hrec : records p = some recBytes) (hss : SingleSession recBytes)
    (hnpend : ¬ PureRecPending recBytes)
    (hcanon : TR.Pure.TRRecordCanon r p recBytes)
    (hout : SndWhisperRetOut interpretation r p recBytes pt coins_cli mid retState retMessage)
    (hcanon' : retState.length < 2 ^ 32 - 2 ^ 20 → (pureTrSlots r).canon p retState)
    (hmid : (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins]))
    {g : Ghost} {ms₀ δ : List Move}
    (hB : XplBlock interpretation r S who g ms₀ δ acc ((.pt pt :: mid) ++ [.send retMessage]))
    (hfaith : DeltaFaithful p (runTraceMoves r ms₀) δ)
    (hrel₀ : PureCRelAt interpretation r S g ms₀ records sent accepted acc) :
    PureCRelAt interpretation r S g (ms₀ ++ δ)
      (fun q => if q = p then some retState else records q)
      (sent ++ (sentBody retMessage).toList) accepted
      (acc ++ ((.pt pt :: mid) ++ [.send retMessage])) := by
  have hshape := snd_ret_blockShape pt retMessage mid ⟨coins, hmid⟩
  obtain ⟨hrecs₀, ⟨hsent₀, hnsBound₀, hacc1₀, hacc2₀⟩, hhist₀, hrole₀⟩ := hrel₀
  have hrole_out := roleSnapshots_xplBlock_send hB hfaith hshape hrole₀
  obtain ⟨pre, m, post, rfl, hpre, ⟨hsb, hsend⟩, hpost⟩ := xplInv_send hB hfaith hshape
  obtain ⟨me, stateIdx, cLen, pqIdx, wrap, rfl⟩ := hsend ⟨.send retMessage, by simp, rfl⟩
  have hme_eq : p = me := hsb.symm; subst me
  have hpq : pqIdx = (runTraceMoves r (ms₀ ++ pre)).length + 2 := snd_encrypt_pqIdx hB.run.2.2.2.2.1; subst hpq
  rw [← TR.runTrace_append r ms₀ pre] at hpost
  have hm_vis : List.Forall₂ (EventMatchesEntry interpretation r S g)
      ((.pt pt :: mid) ++ [.send retMessage])
      ((Move.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap).vis (runTraceMoves r (ms₀ ++ pre))) := by
    have hfor := hB.matched
    rw [TR.runMoves_append, (snd_invisible_runMoves hpre).1, List.nil_append, ← TR.runTrace_append] at hfor
    simpa [runMoves, (snd_invisible_runMoves hpost).1] using hfor
  obtain ⟨⟨st_m, hst_m, hns_m⟩, _, hcoins_gam⟩ := snd_encrypt_vis_match hm_vis hmid
  have hcur_m := snd_isCurrentSnapshot_of_encrypt hB.run.2.2.1.1 hst_m hns_m
  have hq1 : XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]; exact XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hrole₁ : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) :=
    snd_roleSnapshots_quiet (movesFrom_mono (fun _ _ h => h.2) _ _ hpre) hrole₀
  have hinv_p₀ : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms₀
      (fun q => if q = p then some recBytes else none) :=
    Or.resolve_right (pureCRecRelH_single (hrecs₀ p recBytes hrec).2.2 hss)
      (not_alice_and_aliceInitPending_of_not_recPending hnpend)
  obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀_0, hcur₀_0, hrel_st₀, hsk₀, _, hks₀, hnd₀⟩ :=
    hinv_p₀ p recBytes (by simp)
  have hst₀_1 : ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TripleRatchet.TRState).run
      (runTraceMoves r (ms₀ ++ pre))).1 = some st₀ := by rwa [XplQuiet.quiet_getLocalState hq1]
  have hcur₀_1 : TripleRatchet.isCurrentSnapshot (runTraceMoves r (ms₀ ++ pre)) stateIdx₀ = true := by
    rwa [XplQuiet.quiet_isCurrentSnapshot hq1]
  obtain ⟨rfl, rfl⟩ := isCurrentSnapshot_unique_of_role hrole₁ hst_m hst₀_1 hcur_m hcur₀_1
  have hsk₁ : ∀ c ∈ rec₀.current.receiverChains, ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r (ms₀ ++ pre)).EventLoggedAt
          (TripleRatchet.TREvent.SkippedKeyStored (st_m.sessionInfo p) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        !TripleRatchet.skippedKeyUsedB (runTraceMoves r (ms₀ ++ pre)) skIdx ∧
        !TripleRatchet.receiverKeyUsedB (runTraceMoves r (ms₀ ++ pre)) (st_m.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = TR.serializedKey (gamma interpretation S g pk) ∧
        (TripleRatchet.findRecvChain st_m.toDRState.recv pk).isSome = true := by
    intro c hc k hk
    obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu, hru, hgam, hsrk, hfind⟩ := hsk₀ c hc k hk
    refine ⟨pk, rIdx, srcIdx, skIdx, seed, (XplQuiet.quiet_eventLoggedAt hq1 _ _).mpr hlog, ?_, ?_, hgam, hsrk, hfind⟩
    · unfold TripleRatchet.skippedKeyUsedB at hsu ⊢; rw [XplQuiet.quiet_someEventOnTraceB hq1]; exact hsu
    · unfold TripleRatchet.receiverKeyUsedB at hru ⊢; rw [XplQuiet.quiet_someEventOnTraceB hq1]; exact hru
  have hst_lt : TR.FreshSigma.StateStampsLt interpretation S g (runTraceMoves r (ms₀ ++ pre)).length st_m :=
    TR.FreshSigma.traceEntriesLt_at?_st
      (TR.FreshSigma.traceEntriesLt_of_reachable interpretation S g (runTraceMoves r (ms₀ ++ pre)).length
        hB.pre.2.1.2.2.1.1 (XplQuiet.quietExt_len hq1))
      (TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀_0)
  obtain ⟨hrel_sg, hks_sg⟩ := snd_stateRel_keyShape_sendGhost (pt := pt) (coins := coins) hst_lt hrel_st₀ hks₀
  obtain ⟨_, coins', hmid', _, heval⟩ :=
    snd_ret_eval_clause interpretation hext r hwf S hSeq g (ms₀ ++ pre) hcanon hnpend hout
  have hcoins_eq : coins = coins' := snd_coins_eq_of_mid hmid hmid'; subst coins'
  obtain ⟨rec', hnew, hrel'_sg, hchains, hmsg⟩ :=
    heval rec₀ st_m hrecBytes₀ hrel_sg hks_sg (TR.spqrInitA2BKdf_of_getLocalState hst_m)
  have hrel' := snd_stateRel_encSt_of_sendGhost hst_lt hcoins_gam hrel'_sg
  have hpost' : MovesFrom InvisibleNoEffect
      (runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap])) post := by
    rwa [TR.runTrace_snoc]
  have htr_wrap : runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) none]) =
      runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) := by
    rw [TR.runTrace_snoc, TR.runTrace_snoc]; rfl
  have hq2 : XplQuiet.QuietExt
      (runTraceMoves r ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) none]))
      (runTraceMoves r (((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) ++ post)) := by
    rw [htr_wrap, TR.runTrace_append r _ post]
    exact XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost')
  have hms_eq : ms₀ ++ (pre ++ .encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap :: post) =
      ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) wrap]) ++ post := by simp
  have hkeys := snd_frame_bobDoneBaseKeys hpre hst_m hns_m hpost
  have hbody_eq : (sentBody retMessage).toList = [retMessage.drop 1] := by rw [hmsg]; rfl
  refine ⟨fun q b hqb => ?_, ⟨?_, ?_, by rw [hkeys]; exact hacc1₀, by rw [hkeys]; exact hacc2₀⟩,
    snd_cHist_step interpretation r S g ms₀ pre post p stateIdx cLen _ wrap hpre hpost hhist₀,
    hrole_out⟩
  · dsimp only at hqb
    by_cases hqp : q = p
    · subst q; simp only [↓reduceIte, Option.some.injEq] at hqb; subst b
      have hinv_enc : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g
          ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) none])
          (fun x => if x = p then some retState else none) :=
        pureTRRecordStateInv_snoc_encrypt_wrap_single
          hp hst_m hns_m hnew hrel' hchains hsk₁ hcanon' hks₀ hnd₀
      have hinv_post := XplQuiet.quiet_trRecordStateInv hq2 hinv_enc
      rw [← hms_eq] at hinv_post
      exact ⟨hp, hnew ▸ snd_recordBytes_ne_nil rec', Or.inl (Or.inl hinv_post)⟩
    · simp only [hqp, ↓reduceIte] at hqb
      obtain ⟨hq_mem, hb_ne, hc_q₀⟩ := hrecs₀ q b hqb
      exact ⟨hq_mem, hb_ne, ini_pureCRecRelH_mono (fun _ => snd_frame_other hpre hst_m hns_m hpost hqp) hc_q₀⟩
  · have hsb_eq := sentBodies_send_callBlock acc [] mid pt retMessage coins hmid
    simp only [List.append_nil, List.nil_append] at hsb_eq
    rw [hsb_eq, hsent₀]
  · have hns₁ : TR.TRNsBound r (ms₀ ++ pre) sent := XplQuiet.quiet_trNsBound hq1 hnsBound₀
    have hns_enc : TR.TRNsBound r
        ((ms₀ ++ pre) ++ [.encrypt p stateIdx cLen ((runTraceMoves r (ms₀ ++ pre)).length + 2) none])
        (sent ++ [retMessage.drop 1]) :=
      trNsBound_snoc_encrypt_wrap (wrap := none) (retMessage.drop 1) hns₁ hst_m hns_m
    have hns_post := XplQuiet.quiet_trNsBound hq2 hns_enc
    rw [hbody_eq, hms_eq]; exact hns_post

def SndRetStepByPure (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (who : List Participant)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes)
    (records' : Participant → Option HwBytes) (sent' accepted' : List HwBytes)
    (acc blk : List MachineEvent) (p : Participant) : Prop :=
  ∀ g ms₀ δ,
    XplBlock interpretation r S who g ms₀ δ acc blk →
    DeltaFaithful p (runTraceMoves r ms₀) δ →
    PureCRelAt interpretation r S g ms₀ records sent accepted acc →
    PureCRelAt interpretation r S g (ms₀ ++ δ) records' sent' accepted' (acc ++ blk)

theorem sndW_ret_pureCRel
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {p : Participant}
    {records records' : Participant → Option HwBytes}
    {sent accepted sent' accepted' : List HwBytes}
    {acc mid : List MachineEvent} {pt retMessage : HwBytes}
    (hrel : PureCRel interpretation r S who ok records sent accepted acc)
    (hwho : who[(callStarts acc).length]? = some p)
    (hmsg_lt : retMessage.length < 2 ^ 64)
    (hmid : ∃ coins : HwBytes, (coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins]))
    (hooo' : COooAll records')
    (hbka' : BobRecordBaseKeyInAccepted r records' accepted')
    (hbkn' : PureBobKyberNone r records')
    (hbks_rec : ∀ rr', records' r.bob = some (recordBytes rr') →
      ∃ rr, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey)
    (hstep : SndRetStepByPure interpretation r S who records sent accepted
      records' sent' accepted' acc ((.pt pt :: mid) ++ [.send retMessage]) p) :
    PureCRel interpretation r S who ok records' sent' accepted'
      (acc ++ ((.pt pt :: mid) ++ [.send retMessage])) := by
  let blk := (MachineEvent.pt pt :: mid) ++ [MachineEvent.send retMessage]
  refine ⟨hooo', TR.sendsFit_append hrel.sendsFit (snd_ret_sendsFit pt hmid hmsg_lt),
    hbka', hbkn', fun g ms hc => ?_⟩
  have hmp := hc.matched
  obtain ⟨ms₀, δ, rfl, hpre, hmatch⟩ :=
    matchedPrefix_split hmp (snd_ret_blockHead pt retMessage mid)
      (matchedPrefix_prefix_reachable hmp)
  have hc₀ : Clean interpretation r S who ok g ms₀ acc :=
    cleanBy_prefix hc hpre.2.2.2.2.2.length_eq
  obtain ⟨hrelAt₀, hbks₀⟩ := hrel.clean g ms₀ hc₀
  have hB : XplBlock interpretation r S who g ms₀ δ acc blk := ⟨hpre, hmp.2.1, hmatch⟩
  have hB' : XplBlock interpretation r S who g ms₀ δ acc (.pt pt :: (mid ++ [.send retMessage])) := by
    dsimp only [blk] at hB
    simpa only [List.cons_append] using hB
  have hdf : DeltaFaithful p (runTraceMoves r ms₀) δ :=
    snd_deltaFaithful_of_roleFaithful hB' (snd_ret_tail_kinds retMessage hmid) hmp.2.2.1 hwho
  exact ⟨hstep g ms₀ δ hB hdf hrelAt₀,
    bks_xplBlock_send hB hdf (snd_ret_blockShape pt retMessage mid hmid) hbks_rec hbks₀⟩

/-- Returning Whisper `send_wire` step over `PureCRel` and `COpkRelC`. -/
theorem snd_ret_pure_step (interpretation : ExternInterpretation)
    (hext : ExternContractsHoldCli interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (S : OpaqueSymbolSemantics) (hSeq : S = compSemOf interpretation r)
    (who : List Participant) (ok : Nat → Bool)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes) (opkUsed : Bool)
    (acc mid : List MachineEvent)
    (p : Participant) (rec pt coins_cli retState retMessage : HwBytes)
    (hclean₀ : ∃ g₀ ms₀, Clean interpretation r S who ok g₀ ms₀ acc)
    (hrel : PureCRel interpretation r S who ok records sent accepted acc)
    (hopk : COpkRelC interpretation r S who ok opkUsed acc)
    (hp : p = r.alice ∨ p = r.bob)
    (hwho : who[(callStarts acc).length]? = some p)
    (hrec : records p = some rec)
    (hss : SingleSession rec)
    (hnpend : ¬ PureRecPending rec)
    (hreclen : rec.length < 2 ^ 32 - 2 ^ 20)
    (hsent_lt : sent.length < 2 ^ 32 - 1)
    (hout : SndWhisperRetOut interpretation r p rec pt coins_cli mid retState retMessage) :
    let blk := (MachineEvent.pt pt :: mid) ++ [MachineEvent.send retMessage]
    let records' := fun q => if q = p then some retState else records q
    let sent' := sent ++ (sentBody retMessage).toList
    (callStarts blk).length = 1 ∧
    (∃ coins : HwBytes, ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      coins <+: coins_cli) ∧
    (∃ g ms, MatchedPrefix interpretation r S who g ms (acc ++ blk)) ∧
    (ok (callStarts acc).length = true →
      (∃ g ms, Clean interpretation r S who ok g ms (acc ++ blk)) ∧
      PureCRel interpretation r S who ok records' sent' accepted (acc ++ blk) ∧
      COpkRelC interpretation r S who ok opkUsed (acc ++ blk)) := by
  intro blk records' sent'
  obtain ⟨g₀, ms₀, hc₀⟩ := hclean₀
  have hmp₀ := hc₀.matched
  have ⟨hinv₀, hbook₀, _, _⟩ := pureCRel_trRecordStateInv interpretation r S who ok
    records sent accepted acc g₀ ms₀ p rec hrel hc₀ hrec hss
    (not_alice_and_aliceInitPending_of_not_recPending hnpend)
  have hrec_self : (fun q => if q = p then some rec else none) p = some rec := by simp
  obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel_st₀, _, hcanon0, hks₀, _⟩ :=
    hinv₀ p rec hrec_self
  have hcanon : TR.Pure.TRRecordCanon r p rec := hcanon0 hreclen
  obtain ⟨hcanon', coins, hmid, hpref, heval⟩ :=
    snd_ret_eval_clause interpretation hext r hwf S hSeq g₀ ms₀ hcanon hnpend hout
  have hcs_blk : (callStarts blk).length = 1 := by
    dsimp only [blk]; rw [snd_callStarts_ret pt retMessage ⟨coins, hmid⟩]; rfl
  have hst_lt : TR.FreshSigma.StateStampsLt interpretation S g₀ (runTraceMoves r ms₀).length st₀ :=
    TR.FreshSigma.traceEntriesLt_at?_st
      (TR.FreshSigma.traceEntriesLt_of_reachable interpretation S g₀ (runTraceMoves r ms₀).length
        hmp₀.2.1.2.2.1.1 (Nat.le_refl _))
      (TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  obtain ⟨hrel_sg, hks_sg⟩ :=
    snd_stateRel_keyShape_sendGhost (pt := pt) (coins := coins) hst_lt hrel_st₀ hks₀
  have hinit₀ := TR.spqrInitA2BKdf_of_getLocalState hst₀
  obtain ⟨rec', hnew, hrel'_sg, _, hmsg⟩ := heval rec₀ st₀ hrecBytes₀ hrel_sg hks_sg hinit₀
  have hns₀ : st₀.ns ≠ TripleRatchet.u32Max :=
    ns_ne_u32Max_of_trNsBound hbook₀.2.1 hsent_lt hst₀
  have hm_ext : MatchedPrefix interpretation r S who
      (sendGhost g₀ (runTraceMoves r ms₀).length pt coins)
      (ms₀ ++ [Move.encrypt p stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) none])
      (acc ++ blk) := by
    simpa only [List.append_nil, List.nil_append] using
      matchedPrefix_snoc_encrypt (evs := [])
        (by simpa only [List.append_nil] using hmp₀)
        (by simpa only [List.append_nil] using hwho)
        hst₀ hcur₀ hns₀ hmid hmsg
  refine ⟨hcs_blk, ⟨coins, hmid, hpref⟩, ⟨_, _, hm_ext⟩, fun hok_j => ?_⟩
  have hc_sg := clean_sendGhost pt coins hc₀
  have hcc_ms₀ : callCount (runVis r ms₀) = (callStarts acc).length :=
    Stage1Wire.callCount_of_forall₂_eventMatchesEntry hmp₀.2.2.2.2.2
  have hok_ext : OutcomeFaithful r ok
      (ms₀ ++ [Move.encrypt p stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) none]) :=
    Stage1Wire.outcomeFaithful_snoc hc₀.1.2 (fun _ h => by cases h)
      (fun _ => by rw [hcc_ms₀]; exact hok_j)
  have hc_ext : Clean interpretation r S who ok
      (sendGhost g₀ (runTraceMoves r ms₀).length pt coins)
      (ms₀ ++ [Move.encrypt p stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) none])
      (acc ++ blk) := by
    refine ⟨⟨hm_ext, hok_ext⟩,
      not_readCollision_append_noAccept hc_sg.not_readCollision
        (fun e he q heq => snd_ret_noAccept pt retMessage mid ⟨coins, hmid⟩ e he (by subst heq; rfl)) ?_⟩
    intro m' hm' pre e
    simp only [List.mem_singleton] at hm'
    subst hm'
    exact snd_not_readColMove_encrypt pre e
  have hooo' : COooAll records' :=
    snd_ret_cOooAll interpretation hext r S hSeq hrel.oooAll hcanon hout
      hmid hrecBytes₀ hrel_sg hinit₀ hnew hrel'_sg
  have hbka' : BobRecordBaseKeyInAccepted r records' accepted :=
    snd_ret_bka interpretation r S hcanon hnpend hout hrec hrecBytes₀ hrel_st₀ hrel.bka
  have hbkn' : PureBobKyberNone r records' :=
    snd_ret_bkn interpretation r S hcanon hnpend hout hrec hrecBytes₀ hrel_st₀ hrel.bkn
  have hbks_rec :=
    snd_ret_bks_rec interpretation r S hcanon hnpend hout hrec hrecBytes₀ hrel_st₀
  exact ⟨⟨_, _, hc_ext⟩,
    sndW_ret_pureCRel hrel hwho hout.msg_lt ⟨coins, hmid⟩ hooo' hbka' hbkn' hbks_rec
      (fun g ms_pre δ hB hdf hrel₀ =>
        snd_ret_step_at interpretation hext r hwf S hSeq
          hp hrec hss hnpend hcanon hout hcanon' hmid hB hdf hrel₀),
    cOpkRelC_of_no_accept hopk (fun h => h)
      (snd_ret_blockHead pt retMessage mid) (fun _ _ h => matchedPrefix_prefix_reachable h)
      (snd_ret_noAccept pt retMessage mid ⟨coins, hmid⟩)⟩

end Symbolic.Swarm.CREF.CliPure.SndPure
