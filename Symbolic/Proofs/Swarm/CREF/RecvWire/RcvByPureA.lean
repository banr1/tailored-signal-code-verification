/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.OpkRelC
public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.TRREF.SrHonestVerPure -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.RecvWire.BinPendPure
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepPure
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRecv
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.ReadVis
import Symbolic.Proofs.Swarm.CREF.RecvWire.HistHwPure
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure

/-!
# `PureRcvAcceptCall` Bundle and Whisper Receive Step Lemmas

Defines `PureRcvAcceptCall` for an accepting whisper receive call and proves output record
decoding, `DeltaFaithful` from `RoleFaithful`, Bob base-key preservation, entry record
canonicity, and reject-step `Clean` preservation.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

/-- Hypothesis bundle for an accepting whisper receive call. -/
structure PureRcvAcceptCall (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (j : Nat) (p : Participant)
    (records : Participant → Option HwBytes)
    (sent accepted : List HwBytes) (opkUsed : Bool)
    (acc mid : List MachineEvent) (rec body : HwBytes)
    (sm : StateAndMessage) : Prop where
  hclean₀    : ∃ g ms, CleanBy interpretation r S who ok g ms acc
  hrel       : PureCRel interpretation r S who ok records sent accepted acc
  hopk       : COpkRelC interpretation r S who ok opkUsed acc
  hwho       : who[j]? = some p
  hj         : (callStarts acc).length = j
  hp         : p = r.alice ∨ p = r.bob
  hrec       : records p = some rec
  hne        : rec ≠ []
  hss        : SingleSession rec
  hlen       : rec.length < 2 ^ 32 - 2 ^ 20
  hpq        : PqFromHonest sent body
  hcanonP    : TRRecordCanonPend rec
  hrec4      : ∃ rr : RecordRec, rec = recordBytes rr ∧ rr.current.sessionVersion = 4#32
  hmid       : mid = [] ∨ ∃ rb : HwBytes, rb.length = 32 ∧ mid = [.rng rb]
  hstate_lt  : sm.state.length < 2 ^ 64
  hwc        : TR.Pure.WireRecCanon sm.state
  hcanon_out : sm.state.length < 2 ^ 32 - 2 ^ 20 → TR.Pure.TRRecordCanon r p sm.state
  heval      : ∃ (g_rw : RecvWireGhost) (coins : BitVec 256),
    g_rw.who = (if p = r.alice then 0 else 1) ∧
    g_rw.wireBytes = wireWhisperTag :: body ∧
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec g_rw.sess ∧
    ((coins = 0#256 ∧ mid = [] ∧
        Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.recvWireMissFact (cryptoOf' interpretation)
          (Proofs.libsignal.SR.interpW interpretation)
          (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
          g_rw) ∨
      (∃ rngBytes : List (BitVec 8), mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧
        coins = Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes) ∧
        (∀ msg, SignalMessage.tryFrom protoSignalCodec body = .ok msg →
          TR.PureRecvEval.pureDrawsCoins (cryptoOf' interpretation) g_rw.sess.state msg.senderRatchetKey = true))) ∧
    (∀ msg, SignalMessage.tryFrom protoSignalCodec body = .ok msg →
      TR.PureRecvEval.PureDecryptCoinsOk (cryptoOf' interpretation) g_rw.sess.state msg.senderRatchetKey coins) ∧
    TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
      g_rw coins = some (sm.state, sm.message)

variable (interpretation : ExternInterpretation)

/-- Across `pureEvalRecvWireWithCoinsW`, `rec_out` decodes to a `RecordRec` preserving
`current.aliceBaseKey`. -/
theorem rcv_evalRecvWireWithCoinsW_out_recordBytes
    {recBytes rec_out pt_out : HwBytes} {g : RecvWireGhost}
    {coins : BitVec 256} {rr₀ : RecordRec}
    (hrec : recBytes = recordBytes rr₀)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g.sess)
    (hwc : TR.Pure.WireRecCanon rec_out)
    (hev : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
      g coins =
      some (rec_out, pt_out)) :
    ∃ rr' : RecordRec,
      rec_out = recordBytes rr' ∧ rr'.current.aliceBaseKey = rr₀.current.aliceBaseKey := by
  obtain ⟨_body, msg, role, _hw, _hm, _hopen, henc⟩ :=
    TR.PureRecvEval.pureEvalRecvWireWithCoinsW_some_inv hev
  have hbytes_out :=
    recordBytes_storedSession_decryptW_eq_encodeRecord
      (C := cryptoOf' interpretation)
      (W := Proofs.libsignal.SR.interpW interpretation)
      (S := Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
      hcanon_q hwc henc
  have hnorm_in : TR.normPending rr₀ =
      TR.normPending (TR.RecvDecStep.sessionToRecordRecPending g.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrec hcanon_q
  have hbk_in : rr₀.current.aliceBaseKey = g.sess.aliceBaseKey :=
    congrArg (fun r : RecordRec => r.current.aliceBaseKey) hnorm_in
  refine ⟨_, hbytes_out.symm, ?_⟩
  rcases storedSession_decryptW_post_hw
      (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)
      TR.PureRecvEval.pureSerializeRole msg
      role.peer role coins g.sess with heq | ⟨_, _, heq, _⟩
  · exact (congrArg (fun s => s.aliceBaseKey) heq).trans hbk_in.symm
  · exact (congrArg (fun s => s.aliceBaseKey) heq).trans hbk_in.symm

theorem rcv_invisible_runMoves {tr : ExecTrace} {ms : List Move}
    (h : MovesFrom InvisibleNoEffect tr ms) :
    (runMoves ms tr).2 = [] ∧ visActorsFrom ms tr = [] := by
  induction ms generalizing tr with
  | nil => exact ⟨rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨⟨hvis, _⟩, hms⟩ := h
    obtain ⟨hrun, hact⟩ := ih hms
    refine ⟨?_, ?_⟩
    · simp [runMoves, hvis, hrun]
    · simp [visActorsFrom, hvis, hact]

theorem rcv_moveActor_eq_party {m : Move} (h : ¬ LeakKind m) : moveActor m = m.party? := by
  cases m <;> first | rfl | exact False.elim (h trivial)

/-- Under `XplBlock` for a receive block (`RecvBlockShape blk`), `RoleFaithful r who (ms₀ ++ δ)`
and `who[(callStarts acc).length]? = some p` imply `DeltaFaithful p (runTraceMoves r ms₀) δ`. -/
theorem rcv_deltaFaithful_of_roleFaithful
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ δ : List Move} {acc blk : List MachineEvent} {p : Participant}
    (hB : XplBlock interpretation r S who g ms₀ δ acc blk)
    (hshape : RecvBlockShape blk)
    (hrf : RoleFaithful r who (ms₀ ++ δ))
    (hwho : who[(callStarts acc).length]? = some p) :
    DeltaFaithful p (runTraceMoves r ms₀) δ := by
  obtain ⟨body, hhd⟩ := hshape.head
  have hne : blk ≠ [] := by rintro rfl; simp at hhd
  have hhead_ok : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    rw [hhd, Option.mem_def, Option.some.injEq] at he
    subst he
    exact Or.inl rfl
  have htail_ok : ∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    rcases hshape.tail e he with h | h <;> rw [h]
    · exact ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩
    · exact ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩
  obtain ⟨pre, m, post, hδ, hpre, ⟨_, _, hm_rel⟩, hpost⟩ :=
    xpl_oneMove hB hhead_ok hne htail_ok
  subst hδ
  obtain ⟨hpre_vis, hpre_act⟩ := rcv_invisible_runMoves hpre
  obtain ⟨_, hpost_act⟩ := rcv_invisible_runMoves hpost
  obtain ⟨t_blk, hblk_eq⟩ : ∃ t_blk, blk = .recv (wireWhisperTag :: body) :: t_blk := by
    cases blk with
    | nil => simp at hhd
    | cons e t_blk =>
      simp only [List.head?_cons, Option.some.injEq] at hhd
      exact ⟨t_blk, by rw [hhd]⟩
  rw [hblk_eq] at hm_rel
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm_rel rfl
  have hnot_leak : ¬ LeakKind m := by
    have hrk := xpl_recvHeadKind m (runMoves pre (runTraceMoves r ms₀)).1 hv hvk
    cases m <;> first | exact not_false | exact False.elim hrk
  have hidx : (ms₀ ++ (pre ++ m :: post))[ms₀.length + pre.length]? = some m := by
    rw [← List.append_assoc]
    have hlen : (ms₀ ++ pre).length = ms₀.length + pre.length := List.length_append
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have htake : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
    rw [← List.append_assoc]
    have hlen : (ms₀ ++ pre).length = ms₀.length + pre.length := List.length_append
    rw [← hlen, List.take_left]
  have hvis_pre : runVis r (ms₀ ++ pre) = runVis r ms₀ := by
    rw [runVis_append, hpre_vis, List.append_nil]
  have hcc : callCount (runVis r (ms₀ ++ pre)) = (callStarts acc).length := by
    rw [hvis_pre]
    exact matchedPrefix_callCount_eq hB.pre
  unfold DeltaFaithful
  rw [visActorsFrom_append, hpre_act, List.nil_append]
  simp only [visActorsFrom, hpost_act, List.append_nil]
  intro a ha
  have ha_eq : a = moveActor m := (List.mem_replicate.mp ha).2
  subst ha_eq
  cases hact : moveActor m with
  | none => exact Or.inl rfl
  | some q =>
    have hparty : m.party? = some q := by
      rw [← rcv_moveActor_eq_party hnot_leak, hact]
    have hrf_m := hrf (ms₀.length + pre.length) m q hidx hparty
    rw [htake, hcc, hwho] at hrf_m
    exact Or.inr (Or.inr (congrArg some (Option.some.inj hrf_m).symm))

theorem aliceBaseKey_eq_of_recordBytes_eq {r₁ r₂ : RecordRec}
    (h : recordBytes r₁ = recordBytes r₂) :
    r₁.current.aliceBaseKey = r₂.current.aliceBaseKey := by
  have hn := Symbolic.Swarm.CREF.TR.recordBytes_injective h
  simpa [Symbolic.Swarm.CREF.TR.normPending, Symbolic.Swarm.CREF.TR.normPendingS] using
    congrArg (fun r : RecordRec => r.current.aliceBaseKey) hn

theorem rcv_bka_of_non_bob {r : ProtocolSetup} {records : Participant → Option HwBytes}
    {accepted : List HwBytes} {p : Participant} {st' : HwBytes}
    (hp : p ≠ r.bob)
    (hbka : BobRecordBaseKeyInAccepted r records accepted) :
    BobRecordBaseKeyInAccepted r (fun q => if q = p then some st' else records q) accepted := by
  intro rr hrr
  have hne : r.bob ≠ p := Ne.symm hp
  simp only [hne, ↓reduceIte] at hrr
  exact hbka rr hrr

theorem rcv_bka_of_same_baseKey {r : ProtocolSetup} {records : Participant → Option HwBytes}
    {accepted : List HwBytes} {p : Participant} {rec st' : HwBytes} {rr₀ rr₁ : RecordRec}
    (hrec : records p = some rec)
    (hrr₀ : rec = recordBytes rr₀)
    (hrr₁ : st' = recordBytes rr₁)
    (hbase : rr₁.current.aliceBaseKey = rr₀.current.aliceBaseKey)
    (hbka : BobRecordBaseKeyInAccepted r records accepted) :
    BobRecordBaseKeyInAccepted r (fun q => if q = p then some st' else records q) accepted := by
  by_cases hp : r.bob = p
  · intro rr hrr
    simp only [hp, ↓reduceIte, Option.some.injEq] at hrr
    have heq : rr.current.aliceBaseKey = rr₀.current.aliceBaseKey := by
      rw [← hbase]
      exact aliceBaseKey_eq_of_recordBytes_eq (hrr.symm.trans hrr₁)
    rw [heq]
    exact hbka rr₀ (by rw [hp, hrec, hrr₀])
  · exact rcv_bka_of_non_bob (Ne.symm hp) hbka

/-- Derives `TRRecordCanonPend rec` and the version-4 `RecordRec` witness directly from `PureCRel`,
a clean explanation of `acc`, `SingleSession rec`, and `rec.length < 2 ^ 32 - 2 ^ 20`. -/
theorem rcv_canonPend_of_pureCRel {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {acc : List MachineEvent} {p : Participant} {rec : HwBytes}
    (hclean₀ : ∃ g ms, CleanBy interpretation r S who ok g ms acc)
    (hrel : PureCRel interpretation r S who ok records sent accepted acc)
    (hrec : records p = some rec)
    (hss : SingleSession rec)
    (hlen : rec.length < 2 ^ 32 - 2 ^ 20) :
    TRRecordCanonPend rec ∧
      ∃ rr : RecordRec, rec = recordBytes rr ∧ rr.current.sessionVersion = 4#32 := by
  obtain ⟨g₀, ms₀, hc₀⟩ := hclean₀
  have hcr₀ : PureCRecRel interpretation r S g₀ ms₀ p rec :=
    pureCRecRelH_single (hrel.recs hc₀ p rec hrec).2.2 hss
  exact rcv_canonPend_of_recRel hcr₀ (hrel.oooAll p rec hrec) hlen

theorem rcv_accMid_filter_head {mid : List MachineEvent} {pt : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, rb.length = 32 ∧ mid = [.rng rb]) :
    ((mid ++ [MachineEvent.accept pt]).filter fun e => eventKind e != .rng).head? =
      some (.accept pt) := by
  rcases hmid with rfl | ⟨rb, -, rfl⟩ <;> rfl

theorem rcv_callStarts_fail_blk' (body : HwBytes) (ds : List HwBytes) :
    callStarts (.recv (wireWhisperTag :: body) :: ds.map MachineEvent.rng) =
      [.recv (wireWhisperTag :: body)] := by
  have hds : callStarts (ds.map MachineEvent.rng) = [] := by
    induction ds with
    | nil => rfl
    | cons _ _ ih => exact ih
  change MachineEvent.recv (wireWhisperTag :: body) :: callStarts (ds.map MachineEvent.rng) = _
  rw [hds]

theorem rcv_cleanBy_reject {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent} {body : HwBytes} {ds : List HwBytes}
    (hc : Clean interpretation r S who ok g ms acc)
    (hok : ok (callStarts acc).length = false) :
    Clean interpretation r S who ok g (ms ++ [Move.reject (ds.map List.length)])
      (acc ++ (.recv (wireWhisperTag :: body) :: ds.map MachineEvent.rng)) := by
  have hcc_ms : callCount (runVis r ms) = (callStarts acc).length :=
    matchedPrefix_callCount_eq hc.1.1
  have hpath_ext : PathFaithful interpretation r S g ms
      (acc ++ (.recv (wireWhisperTag :: body) :: ds.map MachineEvent.rng)) := by
    intro i m promote b p hi hpath hcs hparse
    have hcs_app :
        callStarts (acc ++ (.recv (wireWhisperTag :: body) :: ds.map MachineEvent.rng)) =
          callStarts acc ++ [.recv (wireWhisperTag :: body)] := by
      unfold callStarts
      rw [List.filter_append]
      exact congrArg (callStarts acc ++ ·) (rcv_callStarts_fail_blk' body ds)
    rw [hcs_app] at hcs
    by_cases hk : callCount (runVis r (ms.take i)) < (callStarts acc).length
    · rw [List.getElem?_append_left hk] at hcs
      exact hc.1.1.2.2.2.1 i m promote b p hi hpath hcs hparse
    · have hk_lt :
          callCount (runVis r (ms.take i)) <
            (callStarts acc ++ [MachineEvent.recv (wireWhisperTag :: body)]).length :=
        (List.getElem?_eq_some_iff.mp hcs).1
      simp only [List.length_append, List.length_singleton] at hk_lt
      have hk_eq : callCount (runVis r (ms.take i)) = (callStarts acc).length := by omega
      rw [hk_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq, MachineEvent.recv.injEq] at hcs
      subst hcs
      rw [xpl_parsePreKeyWire_whisper] at hparse
      cases hparse
  refine ⟨⟨Symbolic.Swarm.Leaves.IC12Stage1MP.matchedPrefix_snoc_reject
    (wireWhisperTag :: body) ds hc.1.1 hpath_ext,
    outcomeFaithful_snoc_reject (ds.map List.length) hc.1.2 (by rwa [hcc_ms])⟩, ?_⟩
  exact not_readCollision_append_noAccept hc.2
    (fun e he pt heq => by
      subst heq
      simp only [List.mem_cons, List.mem_map] at he
      rcases he with h | ⟨_, _, h⟩ <;> cases h)
    (fun m hm _ _ hc_m => by
      simp only [List.mem_singleton] at hm
      subst hm
      exact hc_m)

private theorem rcv_attackerKnows_of_getMessageSentAt {tr : ExecTrace} {idx : Nat} {t : DY.Bytes}
    (hget : tr.getMessageSentAt idx = some t) : t.AttackerKnows tr :=
  Trace.MessageSentAt_implies_AttackerKnows tr t idx
    ((Trace.MessageSentAt_eq_getMessageSentAt t idx tr).mpr hget)

private theorem rcv_invisible_vis_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    rw [runMoves_cons_snd, hv, rcv_invisible_vis_nil δ (m.next tr) hδ, List.nil_append]

theorem rcv_rep_of_clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move} {acc mid : List MachineEvent}
    {body : HwBytes} {sm : StateAndMessage} {t : DY.Bytes}
    (hc : Clean interpretation r S who ok g (ms₀ ++ (pre ++ m :: post))
      (acc ++ (.recv (wireWhisperTag :: body) :: (mid ++ [.accept sm.message]))))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc
      (.recv (wireWhisperTag :: body) :: (mid ++ [.accept sm.message])))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (ht : rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t) :
    t ∈ recvRepresentations interpretation r S g (ms₀ ++ pre) body := by
  have hpre_vis : (runMoves pre (runTraceMoves r ms₀)).2 = [] := rcv_invisible_vis_nil pre _ hpre
  have hpost_vis : (runMoves post (m.next (runMoves pre (runTraceMoves r ms₀)).1)).2 = [] :=
    rcv_invisible_vis_nil post _ hpost
  have hvis_all : runVis r (ms₀ ++ (pre ++ m :: post)) =
      runVis r ms₀ ++ m.vis (runTraceMoves r (ms₀ ++ pre)) := by
    rw [runVis_append, b5_runMoves_append_snd, hpre_vis, List.nil_append,
      runMoves_cons_snd, hpost_vis, List.append_nil, TR.runTrace_append]
  have hlen_acc : acc.length = (runVis r ms₀).length := hB.pre.2.2.2.2.2.length_eq
  have hbv : List.Forall₂ (EventMatchesEntry interpretation r S g)
      (.recv (wireWhisperTag :: body) :: (mid ++ [.accept sm.message]))
      (m.vis (runTraceMoves r (ms₀ ++ pre))) := by
    have hm := hB.matched
    rw [b5_runMoves_append_snd, hpre_vis, List.nil_append, runMoves_cons_snd,
      hpost_vis, List.append_nil] at hm
    rwa [TR.runTrace_append]
  have hrf_all := hc.matched.2.2.2.2.1
  clear hc hB hpre hpost hpre_vis hpost_vis
  have hwrap_vis : ∀ stateIdx msgIdx wrapped,
      (runTraceMoves r (ms₀ ++ pre)).getMessageSentAt msgIdx = some t →
      m.vis (runTraceMoves r (ms₀ ++ pre)) =
        decVis (runTraceMoves r (ms₀ ++ pre)) (m.next (runTraceMoves r (ms₀ ++ pre))) stateIdx msgIdx wrapped ++
          exposures (runTraceMoves r (ms₀ ++ pre)) (m.next (runTraceMoves r (ms₀ ++ pre))) →
      t ∈ recvRepresentations interpretation r S g (ms₀ ++ pre) body := by
    intro stateIdx msgIdx wrapped hget hmvis
    cases wrapped with
    | false =>
      let v₀ : VisEntry := ⟨.recv, [t], .whisper, none⟩
      have hmvis' : ∃ vs, m.vis (runTraceMoves r (ms₀ ++ pre)) = v₀ :: vs := by
        rw [hmvis]; unfold decVis; rw [hget]; exact ⟨_, rfl⟩
      obtain ⟨vs, hmvis_cons⟩ := hmvis'
      have hmem_zip : (MachineEvent.recv (wireWhisperTag :: body), v₀) ∈
          (acc ++ (MachineEvent.recv (wireWhisperTag :: body) :: (mid ++ [MachineEvent.accept sm.message]))).zip
            (runVis r (ms₀ ++ (pre ++ m :: post))) := by
        rw [hvis_all, hmvis_cons, List.zip_append hlen_acc]
        exact List.mem_append_right _ List.mem_cons_self
      have hrf := hrf_all (MachineEvent.recv (wireWhisperTag :: body), v₀) hmem_zip rfl
      exact ⟨rcv_attackerKnows_of_getMessageSentAt hget, hrf.2⟩
    | true =>
      have hmvis' : ∃ vs, m.vis (runTraceMoves r (ms₀ ++ pre)) =
          ⟨.recv, [t], .preKeyInner (sessionBaseKeys (runTraceMoves r (ms₀ ++ pre)) stateIdx), none⟩ :: vs := by
        rw [hmvis]; unfold decVis; rw [hget]; exact ⟨_, rfl⟩
      obtain ⟨vs, hmvis_cons⟩ := hmvis'
      rw [hmvis_cons] at hbv
      match hbv with
      | .cons hhead _ =>
        obtain ⟨_, _, pf, _, hpf, _⟩ := hhead
        change parsePreKeyWire (wireWhisperTag :: body) = some pf at hpf
        rw [parsePreKeyWire_whisperTag_none] at hpf
        cases hpf
  clear hbv hrf_all hvis_all hlen_acc
  cases m with
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    exact hwrap_vis stateIdx msgIdx wrapped ht rfl
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    exact hwrap_vis stateIdx msgIdx wrapped ht rfl
  | _ => simp [rcvMoveTerm, Move.decryptMsgIdx?] at ht

theorem rcv_not_recvCollision_of_clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc mid : List MachineEvent} {body : HwBytes} {sm : StateAndMessage} {t : DY.Bytes}
    (hc : Clean interpretation r S who ok g (ms₀ ++ (pre ++ m :: post))
      (acc ++ (.recv (wireWhisperTag :: body) :: (mid ++ [.accept sm.message]))))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc
      (.recv (wireWhisperTag :: body) :: (mid ++ [.accept sm.message])))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hmid : mid = [] ∨ ∃ rb : HwBytes, rb.length = 32 ∧ mid = [.rng rb])
    (ht : rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t) :
    ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t :=
  not_recvCollision_of_not_readCollision hc.not_readCollision
    hB.pre.2.2.2.2.2 (rcv_invisible_vis_nil pre _ hpre)
    (rcv_accMid_filter_head hmid) (Or.inl ⟨rfl, rfl⟩) ht

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
