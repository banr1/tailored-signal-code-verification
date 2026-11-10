/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvIni
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvSend
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.X25519
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompInv Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
cref_open
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent TRState)
open Symbolic.Swarm.CREF.XplSteps Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED.CompTermAlgebra Symbolic.Swarm.COMPOSED.CompKeyInversion Symbolic.Swarm.COMPOSED.CompInv.CompPubInv
@[simp] private theorem length_append_entry {T : Type} [ExecTraceTypes.Has T] (tr : ExecTrace) (x : T) :
    (tr.append x).length = tr.length + 1 :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq tr x
def isSentEv : TREvent → Bool | .Sent .. => true | _ => false
def AllSentNet (n₀ : Nat) (P : DY.Bytes → Prop) (t : ExecTrace) : Prop := ∀ k ev, n₀ ≤ k → t.getEventAt TREvent k = some ev → isSentEv ev = true → ∃ raw, k + 3 < t.length ∧ NetAt t raw (k + 3) ∧ P raw
def XNoSent (n : Nat) (t : ExecTrace) : Prop := ∀ k ev, n ≤ k → t.getEventAt TREvent k = some ev → isSentEv ev = false
theorem allSentNet_self (P : DY.Bytes → Prop) (tr₀ : ExecTrace) : AllSentNet tr₀.length P tr₀ :=
  fun _ _ hk hev _ => absurd (xlt_of_getEventAt hev) (by omega)
theorem allSentNet_of_xnoSent {n₀ : Nat} {P : DY.Bytes → Prop} {tr t : ExecTrace} (hle : tr ≤ t) (htr : AllSentNet n₀ P tr) (hns : XNoSent tr.length t) : AllSentNet n₀ P t := by
  intro k ev hk hev hs; by_cases hlt : k < tr.length
  · rw [xgetEventAt_le_eq hle hlt] at hev; obtain ⟨raw, hlen, hnet, hp⟩ := htr k ev hk hev hs
    exact ⟨raw, Nat.lt_of_lt_of_le hlen (Trace.length_le tr t hle), hnet.mono hle, hp⟩
  · have hfalse := hns k ev (by omega) hev; rw [hs] at hfalse; cases hfalse
theorem xnoSent_trans {n : Nat} {t t' : ExecTrace} (hle : t ≤ t') (h1 : XNoSent n t) (h2 : XNoSent t.length t') : XNoSent n t' := by
  intro k ev hk hev; by_cases hlt : k < t.length
  · rw [xgetEventAt_le_eq hle hlt] at hev; exact h1 k ev hk hev
  · exact h2 k ev (by omega) hev
theorem xnoSent_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) (h : ∀ ev, ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT TREvent)) = some ev → isSentEv ev.ev = false) : XNoSent tr.length (tr.append e) := by
  have hlen : (tr.append e).length = tr.length + 1 := length_append_entry tr e
  intro k ev hk hev; have hlt := xlt_of_getEventAt hev; obtain rfl : k = tr.length := by omega
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at? (E := TREvent)] at hev
  rcases hx : ((tr.append e).at? tr.length : Option (ProtocolEvent.ExecEntryT TREvent)) with _ | x <;> rw [hx] at hev
  · cases hev
  · simp only [Option.some.injEq] at hev; subst hev; exact h x hx
theorem xnoSent_append_tr (tr : ExecTrace) (ev : TREvent) (h : isSentEv ev = false) : XNoSent tr.length (tr.append (CompTrace.TREvE ev)) := by refine xnoSent_append tr (CompTrace.TREvE ev) (fun x hx => ?_); rw [Trace.at?_append] at hx; cases hx; exact h
theorem xnoSent_append_other {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option (ProtocolEvent.ExecEntryT TREvent)) = none) : XNoSent tr.length (tr.append e) := by
  refine xnoSent_append tr e (fun x hx => ?_)
  rw [Symbolic.Swarm.CREF.at?_append_length, hnone] at hx; cases hx
theorem allSentNet_of_noSessionEffect {n₀ : Nat} {P : DY.Bytes → Prop} {tr : ExecTrace} {m : Move} (heff : NoSessionEffect tr m) (htr : AllSentNet n₀ P tr) : AllSentNet n₀ P (m.next tr) := by
  refine allSentNet_of_xnoSent (m.le_next tr) htr (fun k ev hk hev => ?_)
  have hnone := (heff k (xpl_mem_newIndices hk (xlt_of_getEventAt hev))).2.2.1; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at? (E := TREvent), hnone] at hev; cases hev
theorem allSentNet_runMoves_of_movesFrom {n₀ : Nat} {P : DY.Bytes → Prop} {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom InvisibleNoEffect tr δ) (htr : AllSentNet n₀ P tr) : AllSentNet n₀ P (runMoves δ tr).1 := by induction δ generalizing tr with | nil => exact htr | cons _ _ ih => exact ih hδ.2 (allSentNet_of_noSessionEffect hδ.1.2 htr)
theorem allSentNet_xplBlock_ini {n₀ : Nat} {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ δ : List Move} {acc : List MachineEvent} {bun : HwBytes} {rs : List MachineEvent} (hB : XplBlock6 i r S g ms₀ δ acc (.recv bun :: rs)) (hrs : ∀ e ∈ rs, eventKind e = .rng) (htr : AllSentNet n₀ P (runTraceMoves r ms₀)) : AllSentNet n₀ P (runTraceMoves r (ms₀ ++ δ)) := by
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨hs, ha, hm⟩, hpost_inv⟩ :=
    xpl6_oneMove hB (by intro e he; simp at he; subst he; exact Or.inl rfl) (by simp) (by intro e he; rw [hrs e he]; decide)
  have hact : ActorIn ((moveActor m).getD r.alice) m := by unfold ActorIn; cases moveActor m <;> simp
  have hstep := xplStep_ini hs ha hm ⟨⟨bun, rfl⟩, hrs⟩ hact; have htr_pre : AllSentNet n₀ P (runMoves pre (runTraceMoves r ms₀)).1 := allSentNet_runMoves_of_movesFrom hpre_inv htr
  have htr_m : AllSentNet n₀ P (m.next (runMoves pre (runTraceMoves r ms₀)).1) := by
    rcases hstep.2 with hini | hneff
    · unfold IniKind at hini; cases m <;> try exact False.elim hini
      case aliceStart a b idS regB hb shown =>
        rcases aliceStart_next_cases a b idS regB hb shown (runMoves pre (runTraceMoves r ms₀)).1 with h | h | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ <;> rw [h]
        · exact htr_pre
        · exact allSentNet_of_xnoSent (Trace.append_le _ _) htr_pre (xnoSent_append_other _ (CompTrace.RndE 32) rfl)
        · dsimp only [aliceStartTrOfOut]
          exact allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) htr_pre (xnoSent_append_other _ (CompTrace.RndE 32) rfl)) (xnoSent_append_other _ (CompTrace.RndE 32) rfl)) (xnoSent_append_other _ (CompTrace.RndE 32) rfl)) (xnoSent_append_other _ (CompTrace.NetE _) rfl)) (xnoSent_append_other _ (CompTrace.NetE _) rfl)) (xnoSent_append_other _ (CompTrace.PQEvE _) rfl)) (xnoSent_append_tr _ _ rfl)) (xnoSent_append_other _ (CompTrace.CEvE _) rfl)) (xnoSent_append_other _ (CompTrace.TRStE a _) rfl)
      case reject draws =>
        have hnext : (Move.reject draws).next (runMoves pre (runTraceMoves r ms₀)).1 = (runMoves pre (runTraceMoves r ms₀)).1 := by
          unfold Move.next Move.act; simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_pure_snd]
        rw [hnext]; exact htr_pre
      case attackerSend msg =>
        unfold Move.next Move.act; rw [xrun_bind_unit, (TR.Runs.sendMessage _ msg).2]
        exact allSentNet_of_xnoSent (Trace.append_le _ _) htr_pre (xnoSent_append_other _ (CompTrace.NetE msg) rfl)
    · exact allSentNet_of_noSessionEffect hneff htr_pre
  rw [CompPrefixInvStruct.runTrace_append, runMoves_append_fst, runMoves_cons_fst]; exact allSentNet_runMoves_of_movesFrom hpost_inv htr_m
theorem allSentNet_append_sent {n₀ : Nat} {P : DY.Bytes → Prop} {tr t : ExecTrace} {ev : TREvent} {raw : DY.Bytes} (htr : AllSentNet n₀ P tr) (hle : tr.append (CompTrace.TREvE ev) ≤ t) (hns : XNoSent (tr.length + 1) t) (hlt : tr.length + 3 < t.length) (hnet : NetAt t raw (tr.length + 3)) (hp : P raw) : AllSentNet n₀ P t := by
  intro k ev' hk hev' hs; have hle0 : tr ≤ t := Trace.le_trans _ _ _ (Trace.append_le tr _) hle
  by_cases hklt : k < tr.length
  · rw [xgetEventAt_le_eq hle0 hklt] at hev'; obtain ⟨raw', hlt', hnet', hp'⟩ := htr k ev' hk hev' hs
    exact ⟨raw', Nat.lt_of_lt_of_le hlt' (Trace.length_le tr t hle0), hnet'.mono hle0, hp'⟩
  · by_cases hkeq : k = tr.length
    · subst hkeq; exact ⟨raw, hlt, hnet, hp⟩
    · have hfalse := hns k ev' (by omega) hev'; rw [hs] at hfalse; cases hfalse
theorem allSentNet_encrypt {n₀ : Nat} {P : DY.Bytes → Prop} (me : Participant) (sIdx cl pq : Nat) (wrap : Option (Nat × Nat)) (tr : ExecTrace) (htr : AllSentNet n₀ P tr) (hraw : ∀ raw, lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) = some raw → P raw) : AllSentNet n₀ P ((Move.encrypt me sIdx cl pq wrap).next tr) := by
  have hmove : (Move.encrypt me sIdx cl pq wrap).next tr =
      ((DY.Libsignal.TripleRatchet.messageEncrypt me sIdx cl pq).run tr).2.val := by unfold Move.next Move.act; exact xrun_bind_unit _ tr
  rw [hmove]; unfold DY.Libsignal.TripleRatchet.messageEncrypt; apply CompTrace.bind_getLocalState_tr_at me sIdx tr htr; intro st hst; apply CompTrace.bind_guardP_at _ tr htr; intro hns; rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd]; dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
  let m := rnd tr.length 32; let tr1 := tr.append (CompTrace.RndE 32)
  let coins := rnd tr1.length cl; let tr2 := tr1.append (CompTrace.RndE cl)
  let key := (DY.Spqr.spqrSend st.spqr coins).2.1; let tr3 := tr2.append (CompTrace.NetE key)
  have htr3 : AllSentNet n₀ P tr3 := allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) htr (xnoSent_append_other _ (CompTrace.RndE 32) rfl)) (xnoSent_append_other _ (CompTrace.RndE cl) rfl)) (xnoSent_append_other _ (CompTrace.NetE key) rfl)
  apply CompTrace.bind_receiveMessage_at pq tr3 htr3; intro pqSalt hpq _; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_logMessageKeyAndStore_bind_snd, CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (CompTrace.TREvE (TREvent.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns m))
  let st' : TRState := { st with cks := (DY.Libsignal.TripleRatchet.kdfCk st.cks).1, ns := st.ns + 1, spqr := (DY.Spqr.spqrSend st.spqr coins).1 }
  let tr5 := tr4.append (CompTrace.TREvE (TREvent.MessageKey (st.sinfo me) .sender (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pqSalt st.ns st.rIdx sIdx))
  let tr6 := tr5.append (CompTrace.TRStE me st'); let mk := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt (DY.Libsignal.TripleRatchet.kdfCk st.cks).2
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn (DY.SymEnc.symEnc mk.cipherKey mk.iv m) (DY.Spqr.spqrSend st.spqr coins).2.2
  let mac := DY.Libsignal.TripleRatchet.computeMac mk.macKey st.myIk st.peerIk wire
  let raw := DY.Concat.concat wire mac; let tr7 := tr6.append (CompTrace.NetE raw)
  have hle47 : tr4 ≤ tr7 := Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.append_le _ _)); have hns47 : XNoSent tr4.length tr7 := xnoSent_trans (Trace.append_le _ _) (xnoSent_trans (Trace.append_le _ _) (xnoSent_append_tr tr4 _ rfl) (xnoSent_append_other tr5 (CompTrace.TRStE me st') rfl)) (xnoSent_append_other tr6 (CompTrace.NetE raw) rfl)
  have hnet : NetAt tr7 raw (tr3.length + 3) := by
    have h6 : tr6.length = tr3.length + 3 := by simp [tr6, tr5, tr4]
    exact h6 ▸ CompTrace.at?_append_here tr6 (CompTrace.NetE raw)
  have hnext : (Move.encrypt me sIdx cl pq wrap).next tr = tr7 := by
    rw [hmove]; unfold DY.Libsignal.TripleRatchet.messageEncrypt; rw [CompTrace.run_bind_snd, CompTrace.getLocalState_tr_fst, CompTrace.getLocalState_tr_snd, hst]
    simp only [↓reduceIte]; unfold _root_.guard; rw [ite_eq_left_iff.mpr fun h => absurd hns h]
    rw [CompTrace.run_pure_bind_snd, CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd]; try dsimp only
    rw [CompPresTRExp.run_sendMessage_bind_snd]; change ((DY.Network.receiveMessage pq >>= _).run tr3).2.val = tr7; rw [CompTrace.run_bind_snd, CompTrace.receiveMessage_fst, CompTrace.receiveMessage_snd, hpq]; try dsimp only
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_logMessageKeyAndStore_bind_snd, CompPresTRExp.run_sendMessage_snd]
  have hp : P raw := by
    apply hraw; rw [hnext]; unfold lastSent
    have hlt : tr.length < tr7.length := by simp only [tr7, tr6, tr5, tr4, tr3, tr2, tr1, length_append_entry]; omega
    have hsub : tr7.length - 1 = tr6.length := by simp only [tr7, length_append_entry]; omega
    simp only [hlt, ↓reduceIte, hsub]; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?, CompTrace.at?_append_here tr6 (CompTrace.NetE raw)]
  have h4 : tr4.length = tr3.length + 1 := by simp [tr4]
  rw [h4] at hns47
  exact allSentNet_append_sent htr3 hle47 hns47 (by simp only [length_append_entry]; omega) hnet hp
theorem allSentNet_xplBlock_send {n₀ : Nat} {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ δ : List Move} {acc : List MachineEvent} {pt0 c0 w : HwBytes} {q₀ : PreKeyFields} (hB : XplBlock6 i r S g ms₀ δ acc [.pt pt0, .rng c0, .send w]) (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀) (htr : AllSentNet n₀ P (runTraceMoves r ms₀)) (hpw : ∀ raw, gamma i S g raw = q₀.message → P raw) : AllSentNet n₀ P (runTraceMoves r (ms₀ ++ δ)) := by
  have hhead : ∀ e ∈ ([.pt pt0, .rng c0, .send w] : List MachineEvent).head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp at he; subst he; exact Or.inr rfl
  have htail : ∀ e ∈ ([.pt pt0, .rng c0, .send w] : List MachineEvent).tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl <;> { dsimp [eventKind]; decide }
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨_, _, hm⟩, hpost_inv⟩ := xpl6_oneMove hB hhead (by simp) htail
  let tr_pre := (runMoves pre (runTraceMoves r ms₀)).1
  have htr_pre : AllSentNet n₀ P tr_pre := allSentNet_runMoves_of_movesFrom hpre_inv htr; obtain ⟨me, sIdx, cl, pq, wrap, rfl, _, hwrap_none, hm_vis⟩ := invert_send_move hm
  rcases wrap with _ | ⟨e, c'⟩
  · exact False.elim (hw (hwrap_none rfl))
  · have htr_m : AllSentNet n₀ P ((Move.encrypt me sIdx cl pq (some (e, c'))).next tr_pre) :=
      allSentNet_encrypt me sIdx cl pq (some (e, c')) tr_pre htr_pre (fun raw hls => by
        obtain ⟨v, hv, hev⟩ := xpl_forall₂_mem_left hm_vis (.send w) (by simp)
        have hvk : v.kind = .send := xpl_kind_of_matches hev; unfold encVis at hv; simp only [↓reduceIte, List.mem_append] at hv
        rcases hv with hd | hsnd
        · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk] at hk; cases hk)
        · unfold encSend at hsnd; rw [hls, List.mem_singleton] at hsnd; subst hsnd
          obtain ⟨_, hsm⟩ : Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire.SendMatchesMoves i r S g w (received tr_pre [e, c'] ++ [raw]) := hev.2
          have hgamma : gamma i S g raw = q₀.message := by
            match received tr_pre [e, c'], hsm with
            | [_, _], ⟨_, _, _, _, hw'⟩ => exact (CompRPreKeyWire.parsePreKeyWire_preKeyWire_inv hw' hlen hq₀).2.2.2.symm
            | [], hsm => exact (hsm : False).elim | [_], hsm => exact (hsm : False).elim
            | _ :: _ :: _ :: t, hsm => cases t <;> exact (hsm : False).elim
          exact hpw raw hgamma)
    rw [CompPrefixInvStruct.runTrace_append, runMoves_append_fst, runMoves_cons_fst]; exact allSentNet_runMoves_of_movesFrom hpost_inv htr_m
section CleanKnowsSection
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH
open Symbolic.Swarm.COMPOSED.CompTermAlgebra Symbolic.Swarm.COMPOSED.CompKeyInversion Symbolic.Swarm.COMPOSED.CompInv.CompPubInv
def SentMac (tr : ExecTrace) (x : Bytes) : Prop :=
  ∃ t j keys rkChain pk sk counter pqSalt ikA ikB wire me peer dhs ns m, j < t ∧ t + 6 < tr.length ∧ HandshakeKeysAt tr j keys ∧ tr.EventLoggedAt (TREvent.Sent me peer dhs ns m) (t + 3) ∧ NetAt tr (Concat.concat wire (Trunc.trunc8 x)) (t + 6) ∧ (rkChain = keys.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) ∧
    let seed := (kdfCk (chainKeyAt (createChain rkChain pk sk).2 counter)).2
    let mk := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed
    x = hmac mk.macKey (Concat.concat ikA (Concat.concat ikB wire))
theorem SentMac.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {x : Bytes} (h : SentMac tr x) : SentMac tr' x := by obtain ⟨t, j, keys, rkChain, pk, sk, counter, pqSalt, ikA, ikB, wire, me, peer, dhs, ns, m, hjt, ht, hkeys, hsent, hnet, hrk, hx⟩ := h; exact ⟨t, j, keys, rkChain, pk, sk, counter, pqSalt, ikA, ikB, wire, me, peer, dhs, ns, m, hjt, Nat.lt_of_lt_of_le ht (Trace.length_le tr tr' hle), handshakeKeysAt_mono hle hkeys, evAt_mono hle hsent, hnet.mono hle, hrk, hx⟩
theorem SentMac.to_honestMac {tr : ExecTrace} {x : Bytes} (h : SentMac tr x) : HonestMac tr x := by
  obtain ⟨t, j, keys, rkChain, pk, sk, counter, pqSalt, ikA, ikB, wire, _, _, _, _, _, hjt, ht, hkeys, _, _, hrk, hx⟩ := h
  exact ⟨j, keys, rkChain, pk, sk, counter, pqSalt, ikA, ikB, wire, by omega, hkeys, hrk, hx⟩
def IsNonSubterm (b : Bytes) : Prop := b.view? KdfExtract.KdfExtract.SubF = none ∧ b.view? Trunc.Trunc8.SubF = none ∧ b.view? Concat.Concat.SubF = none ∧ b.view? SymEnc.Enc.SubF = none ∧ b.view? TrWire.TrWireMsg.SubF = none ∧ b.view? X25519.Variant.SubF = none ∧ b.view? Spqr.InitState.SubF = none ∧ b.view? Spqr.SendState.SubF = none ∧ b.view? Spqr.RecvState.SubF = none
def IsOpaqueAtom (b : Bytes) : Prop := IsNonSubterm b ∧ b.view? DiffieHellman.Dh.SubF = none ∧ b.view? DY.Random.SubF = none
inductive CleanKnows (tr : ExecTrace) : Bytes → Prop where
  | atom {b : Bytes} (hpub : Pub tr b) (hview : IsNonSubterm b) : CleanKnows tr b
  | opaqueAtom {b : Bytes} (hop : IsOpaqueAtom b) : CleanKnows tr b
  | dh (pk sk : Bytes) (hsk : CleanKnows tr sk) : CleanKnows tr (DiffieHellman.dh pk sk)
  | cat {l r : Bytes} (hl : CleanKnows tr l) (hr : CleanKnows tr r) : CleanKnows tr (Concat.concat l r)
  | kdf {s m : Bytes} (hs : CleanKnows tr s) (hm : CleanKnows tr m) : CleanKnows tr (KdfExtract.kdfExtract s m)
  | trunc {m : Bytes} (hm : CleanKnows tr m) : CleanKnows tr (Trunc.trunc8 m)
  | truncSent {m : Bytes} (hm : SentMac tr m) : CleanKnows tr (Trunc.trunc8 m)
  | enc {k iv m : Bytes} (hm : CleanKnows tr m) : CleanKnows tr (SymEnc.symEnc k iv m)
  | trWire {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : TrWire.EncodingVariation}
      (hrk : CleanKnows tr rk) (hct : CleanKnows tr ct) (hpq : CleanKnows tr pq) : CleanKnows tr (TrWire.trWireMsg v rk c pc ct pq ev)
  | var {key : Bytes} (v : Fin 4) {t : Fin 8} (hkey : CleanKnows tr key) :
      CleanKnows tr ((({ key := key, variation := v, torsion := t } : X25519.Variant.SubF Bytes)).pack)
  | spqrInit {authKey params : Bytes} (hk : CleanKnows tr authKey) (hp : CleanKnows tr params) : CleanKnows tr (Spqr.spqrInit authKey params)
  | spqrSendState {st coins : Bytes} (hst : CleanKnows tr st) (hc : CleanKnows tr coins) :
      CleanKnows tr ((({ st := st, coins := coins } : Spqr.SendState.SubF Bytes)).pack)
  | spqrRecvState {st msg : Bytes} (hst : CleanKnows tr st) (hm : CleanKnows tr msg) :
      CleanKnows tr ((({ st := st, msg := msg } : Spqr.RecvState.SubF Bytes)).pack)
theorem CleanKnows.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes} (h : CleanKnows tr b) : CleanKnows tr' b := by
  induction h with
  | atom hpub hview => exact .atom (Pub.mono hle hpub) hview | opaqueAtom hop => exact .opaqueAtom hop
  | dh pk _ _ ihsk => exact .dh pk _ ihsk | cat _ _ ihl ihr => exact .cat ihl ihr
  | kdf _ _ ihs ihm => exact .kdf ihs ihm | trunc _ ihm => exact .trunc ihm | truncSent hm => exact .truncSent (hm.mono hle)
  | enc _ ihm => exact .enc ihm
  | trWire _ _ _ ihrk ihct ihpq => exact .trWire ihrk ihct ihpq | var v _ ihk => exact .var v ihk
  | spqrInit _ _ ihk ihp => exact .spqrInit ihk ihp | spqrSendState _ _ ihst ihc => exact .spqrSendState ihst ihc
  | spqrRecvState _ _ ihst ihm => exact .spqrRecvState ihst ihm
section CleanInversions
unseal Bytes
set_option hygiene false in
local macro "ns_rfl" : term => `(by
  try dsimp only [_root_.DY.Literal.literalToBytes, _root_.DY.Literal.CanLiteral.literalToBytes,
    rnd, _root_.DY.Random.mkRand, _root_.DY.Random.rand,
    _root_.DY.DiffieHellman.dhPk, _root_.DY.DiffieHellman.CanDH.dhPk,
    _root_.DY.PQKem.kemPk, _root_.DY.PQKem.CanPQKem.kemPk,
    _root_.DY.PQKem.kemEncap, _root_.DY.PQKem.CanPQKem.kemEncap,
    _root_.DY.PQKem.kemRejKey, _root_.DY.PQKem.CanPQKem.kemRejKey,
    _root_.DY.Signature.vk, _root_.DY.Signature.CanSign.vk,
    _root_.DY.Signature.sign, _root_.DY.Signature.CanSign.sign,
    _root_.DY.Spqr.spqrChainKey, _root_.DY.Spqr.spqrSend]
  exact ⟨Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _⟩)
set_option hygiene false in
local macro "op_rfl" : term => `(⟨ns_rfl, by
  try dsimp only [_root_.DY.Literal.literalToBytes, _root_.DY.Literal.CanLiteral.literalToBytes,
    _root_.DY.DiffieHellman.dhPk, _root_.DY.DiffieHellman.CanDH.dhPk,
    _root_.DY.PQKem.kemPk, _root_.DY.PQKem.CanPQKem.kemPk,
    _root_.DY.PQKem.kemEncap, _root_.DY.PQKem.CanPQKem.kemEncap,
    _root_.DY.PQKem.kemRejKey, _root_.DY.PQKem.CanPQKem.kemRejKey,
    _root_.DY.Signature.vk, _root_.DY.Signature.CanSign.vk,
    _root_.DY.Signature.sign, _root_.DY.Signature.CanSign.sign,
    _root_.DY.Spqr.spqrChainKey, _root_.DY.Spqr.spqrSend]
  exact ⟨Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _,
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _⟩⟩)
set_option hygiene false in
local macro "clean_inv_other" hq:ident : tactic => `(tactic| (
  try dsimp [rnd, _root_.DY.Random.mkRand, _root_.DY.Random.rand,
    _root_.DY.Literal.literalToBytes, _root_.DY.Literal.CanLiteral.literalToBytes,
    _root_.DY.Concat.concat, _root_.DY.Concat.CanConcat.concat,
    _root_.DY.KdfExtract.kdfExtract, _root_.DY.KdfExtract.CanKdfExtract.kdfExtract,
    _root_.DY.Trunc.trunc8, _root_.DY.Trunc.CanTrunc8.trunc8,
    _root_.DY.TrWire.trWireMsg, _root_.DY.TrWire.CanTrWireMsg.trWireMsg,
    _root_.DY.SymEnc.symEnc, _root_.DY.SymEnc.CanSymEnc.symEnc,
    _root_.DY.DiffieHellman.dhPk, _root_.DY.DiffieHellman.CanDH.dhPk,
    _root_.DY.PQKem.kemPk, _root_.DY.PQKem.CanPQKem.kemPk,
    _root_.DY.PQKem.kemEncap, _root_.DY.PQKem.CanPQKem.kemEncap,
    _root_.DY.PQKem.kemRejKey, _root_.DY.PQKem.CanPQKem.kemRejKey,
    _root_.DY.Signature.vk, _root_.DY.Signature.CanSign.vk,
    _root_.DY.Signature.sign, _root_.DY.Signature.CanSign.sign,
    _root_.DY.Spqr.spqrInit, _root_.DY.Spqr.spqrChainKey] at $hq:ident
  exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none $hq:ident)))
set_option hygiene false in
local macro "clean_inv_atom" hq:ident hv:ident : tactic => `(tactic| (
  rw [← $hq:ident] at $hv:ident
  simp only [Concat.concat, Concat.CanConcat.concat,
    KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract,
    Trunc.trunc8, Trunc.CanTrunc8.trunc8,
    TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg,
    SymEnc.symEnc, SymEnc.CanSymEnc.symEnc,
    Spqr.spqrInit, BytesView.view_pack, reduceCtorEq] at $hv:ident))
theorem isOpaqueAtom_literal (bs : ByteArray) : IsOpaqueAtom (Literal.literalToBytes bs) := op_rfl
theorem isOpaqueAtom_dhPk (sk : Bytes) : IsOpaqueAtom (DiffieHellman.dhPk sk) := op_rfl
theorem isOpaqueAtom_kemPk (sk : Bytes) : IsOpaqueAtom (PQKem.kemPk sk) := op_rfl
theorem isOpaqueAtom_kemEncap_fst (pk e : Bytes) : IsOpaqueAtom (PQKem.kemEncap pk e).1 := op_rfl
theorem isOpaqueAtom_kemEncap_snd (pk e : Bytes) : IsOpaqueAtom (PQKem.kemEncap pk e).2 := op_rfl
theorem isOpaqueAtom_kemRejKey (sk ct : Bytes) : IsOpaqueAtom (PQKem.kemRejKey sk ct) := op_rfl
theorem isOpaqueAtom_vk (sk : Bytes) : IsOpaqueAtom (Signature.vk sk) := op_rfl
theorem isOpaqueAtom_sign (sk nonce msg : Bytes) : IsOpaqueAtom (Signature.sign sk nonce msg) := op_rfl
theorem isOpaqueAtom_spqrChainKey (authKey params idx : Bytes) : IsOpaqueAtom (Spqr.spqrChainKey authKey params idx) := op_rfl
theorem isOpaqueAtom_spqrSendKey (st coins : Bytes) : IsOpaqueAtom (Spqr.spqrSend st coins).2.1 := by unfold Spqr.spqrSend; dsimp only; cases st.view? Spqr.InitState.SubF <;> exact op_rfl
theorem isOpaqueAtom_spqrSendMsg (st coins : Bytes) : IsOpaqueAtom (Spqr.spqrSend st coins).2.2 := op_rfl
theorem isOpaqueAtom_spqrRecvKey {st msg : Bytes} {idx : UInt32} {spqr' key : Bytes} (hrecv : Spqr.spqrRecv st msg idx = some (spqr', key)) : IsOpaqueAtom key := by
  unfold Spqr.spqrRecv at hrecv; split at hrecv
  · cases hrecv
  · cases hv : st.view? Spqr.InitState.SubF with
    | none => rw [hv] at hrecv; injection hrecv with h'; injection h' with _ hk; subst hk; exact op_rfl
    | some x =>
      rw [hv] at hrecv; rcases x with ⟨authKey, params⟩; dsimp only at hrecv
      cases hd : Spqr.spqrParamsDir? params <;> rw [hd] at hrecv
      · cases hrecv
      · injection hrecv with h'; injection h' with _ hk; subst hk; split <;> exact op_rfl
theorem isNonSubterm_literal (bs : ByteArray) : IsNonSubterm (Literal.literalToBytes bs) := (isOpaqueAtom_literal bs).1
theorem isNonSubterm_rnd (t n : Nat) : IsNonSubterm (rnd t n) := ns_rfl
theorem isNonSubterm_dhPk (sk : Bytes) : IsNonSubterm (DiffieHellman.dhPk sk) := (isOpaqueAtom_dhPk sk).1
theorem isNonSubterm_dh (pk sk : Bytes) : IsNonSubterm (DiffieHellman.dh pk sk) := by dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh]; repeat' (first | split | exact ns_rfl)
theorem isNonSubterm_kemPk (sk : Bytes) : IsNonSubterm (PQKem.kemPk sk) := (isOpaqueAtom_kemPk sk).1
theorem isNonSubterm_kemEncap_fst (pk e : Bytes) : IsNonSubterm (PQKem.kemEncap pk e).1 := (isOpaqueAtom_kemEncap_fst pk e).1
theorem isNonSubterm_kemEncap_snd (pk e : Bytes) : IsNonSubterm (PQKem.kemEncap pk e).2 := (isOpaqueAtom_kemEncap_snd pk e).1
theorem isNonSubterm_vk (sk : Bytes) : IsNonSubterm (Signature.vk sk) := (isOpaqueAtom_vk sk).1
theorem isNonSubterm_sign (sk nonce msg : Bytes) : IsNonSubterm (Signature.sign sk nonce msg) := (isOpaqueAtom_sign sk nonce msg).1
theorem isNonSubterm_spqrChainKey (authKey params idx : Bytes) : IsNonSubterm (Spqr.spqrChainKey authKey params idx) := (isOpaqueAtom_spqrChainKey authKey params idx).1
theorem isNonSubterm_spqrSendKey (st coins : Bytes) : IsNonSubterm (Spqr.spqrSend st coins).2.1 := (isOpaqueAtom_spqrSendKey st coins).1
theorem isNonSubterm_spqrSendMsg (st coins : Bytes) : IsNonSubterm (Spqr.spqrSend st coins).2.2 := (isOpaqueAtom_spqrSendMsg st coins).1
theorem isNonSubterm_spqrRecvKey {st msg : Bytes} {idx : UInt32} {spqr' key : Bytes} (hrecv : Spqr.spqrRecv st msg idx = some (spqr', key)) : IsNonSubterm key := (isOpaqueAtom_spqrRecvKey hrecv).1
theorem CleanKnows.inv_kdf {tr : ExecTrace} {s m : Bytes} (h : CleanKnows tr (KdfExtract.kdfExtract s m)) : CleanKnows tr s ∧ CleanKnows tr m := by
  generalize hq : KdfExtract.kdfExtract s m = q at h; cases h with
  | atom _ hview => have hv := hview.1; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.1; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).1; clean_inv_atom hq hv
  | kdf hs hm => obtain ⟨rfl, rfl⟩ := kdfExtract_inj hq; exact ⟨hs, hm⟩
  | _ => clean_inv_other hq
theorem CleanKnows.inv_trunc {tr : ExecTrace} {m : Bytes} (h : CleanKnows tr (Trunc.trunc8 m)) : CleanKnows tr m ∨ SentMac tr m := by
  generalize hq : Trunc.trunc8 m = q at h; cases h with
  | atom _ hview => have hv := hview.2.1; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.2.1; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).2.1; clean_inv_atom hq hv
  | trunc hm => obtain rfl := Trunc.trunc8_inj _ _ hq; exact .inl hm
  | truncSent hm => obtain rfl := Trunc.trunc8_inj _ _ hq; exact .inr hm
  | _ => clean_inv_other hq
theorem CleanKnows.inv_cat {tr : ExecTrace} {l r : Bytes} (h : CleanKnows tr (Concat.concat l r)) : CleanKnows tr l ∧ CleanKnows tr r := by
  generalize hq : Concat.concat l r = q at h; cases h with
  | atom _ hview => have hv := hview.2.2.1; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.2.2.1; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).2.2.1; clean_inv_atom hq hv
  | cat hl hr => obtain ⟨rfl, rfl⟩ := concat_inj hq; exact ⟨hl, hr⟩
  | _ => clean_inv_other hq
theorem CleanKnows.inv_enc {tr : ExecTrace} {k iv m : Bytes} (h : CleanKnows tr (SymEnc.symEnc k iv m)) : CleanKnows tr m := by
  generalize hq : SymEnc.symEnc k iv m = q at h; cases h with
  | atom _ hview => have hv := hview.2.2.2.1; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.2.2.2.1; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).2.2.2.1; clean_inv_atom hq hv
  | enc hm =>
    have hv := congrArg (fun b : Bytes => b.view? SymEnc.Enc.SubF) hq
    simp only [SymEnc.symEnc, SymEnc.CanSymEnc.symEnc, BytesView.view_pack, Option.some.injEq, SymEnc.Enc.SubF.mk.injEq] at hv; obtain ⟨_, _, rfl⟩ := hv; exact hm
  | _ => clean_inv_other hq
theorem CleanKnows.inv_trWire {tr : ExecTrace} {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : TrWire.EncodingVariation} (h : CleanKnows tr (TrWire.trWireMsg v rk c pc ct pq ev)) : CleanKnows tr rk ∧ CleanKnows tr ct ∧ CleanKnows tr pq := by
  generalize hq : TrWire.trWireMsg v rk c pc ct pq ev = q at h; cases h with
  | atom _ hview => have hv := hview.2.2.2.2.1; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.2.2.2.2.1; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).2.2.2.2.1; clean_inv_atom hq hv
  | trWire hrk hct hpq =>
    have hv := congrArg (fun b : Bytes => b.view? TrWire.TrWireMsg.SubF) hq
    simp only [TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg, BytesView.view_pack, Option.some.injEq, TrWire.TrWireMsg.SubF.mk.injEq] at hv; obtain ⟨_, rfl, _, _, rfl, rfl, _⟩ := hv; exact ⟨hrk, hct, hpq⟩
  | _ => clean_inv_other hq
theorem CleanKnows.inv_variant {tr : ExecTrace} {x : X25519.Variant.SubF Bytes} (h : CleanKnows tr x.pack) : CleanKnows tr x.key := by
  generalize hq : x.pack = q at h; cases h with
  | atom _ hview => have hv := hview.2.2.2.2.2.1; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.2.2.2.2.2.1; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).2.2.2.2.2.1; clean_inv_atom hq hv
  | var v hkey =>
    have hv := congrArg (fun b : Bytes => b.view? X25519.Variant.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv; cases x; cases hv; exact hkey
  | _ => clean_inv_other hq
theorem CleanKnows.inv_spqrInitPack {tr : ExecTrace} {x : Spqr.InitState.SubF Bytes} (h : CleanKnows tr x.pack) : CleanKnows tr x.authKey ∧ CleanKnows tr x.params := by
  generalize hq : x.pack = q at h; cases h with
  | atom _ hview => have hv := hview.2.2.2.2.2.2.1; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.2.2.2.2.2.2.1; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).2.2.2.2.2.2.1; clean_inv_atom hq hv
  | spqrInit hk hp =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.InitState.SubF) hq
    simp only [Spqr.spqrInit, BytesView.view_pack, Option.some.injEq] at hv; cases x; cases hv; exact ⟨hk, hp⟩
  | _ => clean_inv_other hq
theorem CleanKnows.inv_spqrSendStatePack {tr : ExecTrace} {x : Spqr.SendState.SubF Bytes} (h : CleanKnows tr x.pack) : CleanKnows tr x.st ∧ CleanKnows tr x.coins := by
  generalize hq : x.pack = q at h; cases h with
  | atom _ hview => have hv := hview.2.2.2.2.2.2.2.1; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.2.2.2.2.2.2.2.1; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).2.2.2.2.2.2.2.1; clean_inv_atom hq hv
  | spqrSendState hst hc =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.SendState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv; cases x; cases hv; exact ⟨hst, hc⟩
  | _ => clean_inv_other hq
theorem CleanKnows.inv_spqrRecvStatePack {tr : ExecTrace} {x : Spqr.RecvState.SubF Bytes} (h : CleanKnows tr x.pack) : CleanKnows tr x.st ∧ CleanKnows tr x.msg := by
  generalize hq : x.pack = q at h; cases h with
  | atom _ hview => have hv := hview.2.2.2.2.2.2.2.2; clean_inv_atom hq hv
  | opaqueAtom hop => have hv := hop.1.2.2.2.2.2.2.2.2; clean_inv_atom hq hv
  | dh pk sk _ => have hv := (isNonSubterm_dh pk sk).2.2.2.2.2.2.2.2; clean_inv_atom hq hv
  | spqrRecvState hst hm =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.RecvState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv; cases x; cases hv; exact ⟨hst, hm⟩
  | _ => clean_inv_other hq
theorem CleanKnows.inv_rnd {tr : ExecTrace} {t n : Nat} (h : CleanKnows tr (rnd t n)) : Pub tr (rnd t n) := by
  generalize hq : rnd t n = q at h; cases h with
  | atom hpub _ => exact hpub
  | opaqueAtom hop =>
    have hv := hop.2.2; rw [← hq] at hv
    dsimp [rnd] at hv; simp only [BytesView.view_pack, reduceCtorEq] at hv
  | dh pk sk _ =>
    dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh] at hq
    repeat' (first | split at hq | clean_inv_other hq)
  | _ => clean_inv_other hq
theorem CleanKnows.inv_agree_dhPk {tr : ExecTrace} (hinv : SpqrInv tr) {tA tS : Nat}
    (h : CleanKnows tr (agree (DiffieHellman.dhPk (rnd tA 32)) (rnd tS 32))) :
    Pub tr (rnd tA 32) ∨ Pub tr (rnd tS 32) := by
  generalize hq : agree (DiffieHellman.dhPk (rnd tA 32)) (rnd tS 32) = q at h; cases h with
  | atom hpub _ => rw [← hq] at hpub; exact pub_agree_dhPk hinv hpub
  | opaqueAtom hop =>
    have hv := hop.2.1; rw [← hq] at hv
    unfold agree at hv; rw [CompTermAlgebra.x25519Key_dhPk] at hv
    dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh] at hv
    repeat' (first | split at hv | simp only [BytesView.view_pack, reduceCtorEq] at hv)
  | dh pk sk hsk =>
    unfold agree at hq; rw [CompTermAlgebra.x25519Key_dhPk] at hq
    rcases CompTermAlgebra.dh_eq_dh_dhPk_cases hq.symm with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact .inr (CleanKnows.inv_rnd hsk)
    · exact .inl (CleanKnows.inv_rnd hsk)
  | _ =>
    unfold agree at hq; rw [CompTermAlgebra.x25519Key_dhPk] at hq
    dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh] at hq
    repeat' (first | split at hq | clean_inv_other hq)
end CleanInversions
private theorem kemRejKey_attackerKnowledge_pred (p : Bytes → Prop) (out : Bytes) :
    PQKem.kemRejKey.attackerKnowledge.pred p out =
      (∃ sk cipher, out = PQKem.kemRejKey sk cipher ∧ p sk ∧ p cipher) := rfl
theorem CleanKnows.x25519Key {tr : ExecTrace} {pk : Bytes} (h : CleanKnows tr pk) : CleanKnows tr (X25519.x25519Key pk) := by
  unfold X25519.x25519Key X25519.normalizeX25519Key; have hp := Bytes.pack_view? X25519.Variant.SubF pk
  cases hv : pk.view? X25519.Variant.SubF <;> [exact h; (rw [hv] at hp; rw [← hp] at h; exact CleanKnows.inv_variant h)]
theorem CleanKnows.attackerKnowledge_implies {tr : ExecTrace} : SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (CleanKnows tr) := by
  change SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (CleanKnows tr); dsimp [DY.Libsignal.Composed.attackerKnowledge]; apply SubAttackerKnowledge.combine.implies
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hlt⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
    intro b hb; rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hb; exact hb.elim
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, hlt'⟩
    · intro b hb; dsimp [Literal.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hb
      rcases hb with ⟨bs, rfl⟩; exact .opaqueAtom (isOpaqueAtom_literal bs)
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | n, hlt'⟩ <;> try omega
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hb
      rcases hb with ⟨lhs, rhs, rfl, hlhs, hrhs⟩; exact .cat hlhs hrhs
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, rhs, i, hsplit, hinp⟩; exact (CleanKnows.inv_cat (Concat.concat_split inp i b rhs hsplit.symm ▸ hinp)).1
    · intro b hb; dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, hinp⟩; exact (CleanKnows.inv_cat (Concat.concat_split inp i lhs b hsplit.symm ▸ hinp)).2
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩ <;> try omega
    · intro b hb; dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .opaqueAtom (isOpaqueAtom_dhPk sk)
    · intro b hb; dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, sk, rfl, _, hsk⟩; exact .dh pk sk hsk
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, hlt'⟩
    · intro b hb; dsimp [KdfExtract.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hb
      rcases hb with ⟨salt, ikm, rfl, hsalt, hikm⟩; exact .kdf hsalt hikm
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩ <;> try omega
    · intro b hb; dsimp [SymEnc.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.symEnc_attackerKnowledge_pred] at hb
      rcases hb with ⟨k, iv, msg, rfl, _, _, hmsg⟩; exact .enc hmsg
    · intro b hb; dsimp [SymEnc.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.symDec_attackerKnowledge_pred] at hb
      rcases hb with ⟨key, iv, ct, hdec, _, _, hct⟩
      dsimp [SymEnc.symDec, SymEnc.CanSymEnc.symDec] at hdec; have hp := Bytes.pack_view? SymEnc.Enc.SubF ct
      cases hv : ct.view? SymEnc.Enc.SubF with
      | none => rw [hv] at hdec; cases hdec
      | some x =>
        rw [hv] at hdec hp; rcases x with ⟨k', iv', msg'⟩; dsimp only at hdec hp
        split at hdec <;> [injection hdec with hdec'; cases hdec]; subst hdec'; rw [← hp] at hct; exact CleanKnows.inv_enc hct
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, hlt'⟩
    · intro b hb; dsimp [Trunc.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.trunc8_attackerKnowledge_pred] at hb
      rcases hb with ⟨m, rfl, hm⟩; exact .trunc hm
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩ <;> try omega
    · intro b hb; dsimp [X25519.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.x25519Variant_attackerKnowledge_pred] at hb
      rcases hb with ⟨key, v, t, rfl, hkey⟩; dsimp [X25519.x25519TorsionVariant]; split <;> [exact CleanKnows.x25519Key hkey; exact .var v (CleanKnows.x25519Key hkey)]
    · intro b hb; dsimp [X25519.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.x25519VariantKey_attackerKnowledge_pred] at hb
      rcases hb with ⟨x, hpack, rfl⟩; exact CleanKnows.inv_variant hpack
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | n, hlt'⟩ <;> try omega
    · intro b hb; dsimp [PQKem.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.kemPk_attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .opaqueAtom (isOpaqueAtom_kemPk sk)
    · intro b hb; dsimp [PQKem.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.kemEncapCipher_attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, e, rhs, heq, _, _⟩; have h1 := congrArg Prod.fst heq; dsimp only at h1; rw [h1]; exact .opaqueAtom (isOpaqueAtom_kemEncap_fst pk e)
    · intro b hb; dsimp [PQKem.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.kemEncapSS_attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, e, lhs, heq, _, _⟩; have h1 := congrArg Prod.snd heq; dsimp only at h1; rw [h1]; exact .opaqueAtom (isOpaqueAtom_kemEncap_snd pk e)
    · intro b hb; dsimp [PQKem.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.kemDecap_attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, ct, hdec, _, _⟩
      obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp hdec.symm; exact .opaqueAtom (isOpaqueAtom_kemEncap_snd (PQKem.kemPk sk) e)
    · intro b hb; dsimp [PQKem.attackerKnowledge.internal] at hb
      rw [kemRejKey_attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, ct, rfl, _, _⟩; exact .opaqueAtom (isOpaqueAtom_kemRejKey sk ct)
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩ <;> try omega
    · intro b hb; dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .opaqueAtom (isOpaqueAtom_vk sk)
    · intro b hb; dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, _, _, _⟩; exact .opaqueAtom (isOpaqueAtom_sign sk nonce msg)
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hlt'⟩ <;> try omega
    · intro b hb; dsimp [Spqr.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.spqrInit_attackerKnowledge_pred] at hb
      rcases hb with ⟨authKey, params, rfl, hk, hp⟩; exact .spqrInit hk hp
    · intro b hb; dsimp [Spqr.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.spqrChainKey_attackerKnowledge_pred] at hb
      rcases hb with ⟨authKey, params, idx, rfl, _, _, _⟩; exact .opaqueAtom (isOpaqueAtom_spqrChainKey authKey params idx)
    · intro b hb; dsimp [Spqr.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.spqrSendState_attackerKnowledge_pred] at hb
      rcases hb with ⟨st, coins, rfl, hst, hc⟩; exact .spqrSendState hst hc
    · intro b hb; dsimp [Spqr.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.spqrSendKey_attackerKnowledge_pred] at hb
      rcases hb with ⟨st, coins, rfl, _, _⟩; exact .opaqueAtom (isOpaqueAtom_spqrSendKey st coins)
    · intro b hb; dsimp [Spqr.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.spqrSendMsg_attackerKnowledge_pred] at hb
      rcases hb with ⟨st, coins, rfl, _, _⟩; exact .opaqueAtom (isOpaqueAtom_spqrSendMsg st coins)
    · intro b hb; dsimp [Spqr.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.spqrRecvState_attackerKnowledge_pred] at hb
      rcases hb with ⟨st, msg, idx, r, hrecv, rfl, hst, hm⟩; rw [Spqr.spqrRecv_state st msg idx r hrecv]; exact .spqrRecvState hst hm
    · intro b hb; dsimp [Spqr.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.spqrRecvKey_attackerKnowledge_pred] at hb
      rcases hb with ⟨st, msg, idx, r, hrecv, rfl, _, _⟩; exact .opaqueAtom (isOpaqueAtom_spqrRecvKey hrecv)
    · intro b hb; dsimp [Spqr.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.spqrStateArg_attackerKnowledge_pred] at hb
      rcases hb with (⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩)
      exacts [(CleanKnows.inv_spqrInitPack hpack).1, (CleanKnows.inv_spqrInitPack hpack).2, (CleanKnows.inv_spqrSendStatePack hpack).1, (CleanKnows.inv_spqrSendStatePack hpack).2, (CleanKnows.inv_spqrRecvStatePack hpack).1, (CleanKnows.inv_spqrRecvStatePack hpack).2]
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩ <;> try omega
    · intro b hb; dsimp [TrWire.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.trWireMsg_attackerKnowledge_pred] at hb
      rcases hb with ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, hrk, hct, hpq⟩; exact .trWire hrk hct hpq
    · intro b hb; dsimp [TrWire.attackerKnowledge.internal] at hb
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.trWireMsgArg_attackerKnowledge_pred] at hb
      rcases hb with ⟨⟨v, rk, c, pc, ct, pq, ev⟩, hw, hmem⟩
      obtain ⟨hrk, hct, hpq⟩ := CleanKnows.inv_trWire hw; rcases hmem with rfl | rfl | rfl <;> assumption
  · omega
theorem CleanKnows.of_attackerKnows {tr : ExecTrace}
    (hbase : ∀ x, Trace.BaseAttackerKnows tr x → CleanKnows tr x) {x : Bytes} (hk : x.AttackerKnows tr) : CleanKnows tr x :=
  Bytes.AttackerKnows.is_least_fixpoint (CleanKnows tr) x tr CleanKnows.attackerKnowledge_implies
    (fun y hy => hbase y (by simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hy; exact hy)) hk
def CleanBase (tr : ExecTrace) : Prop := ∀ x, Trace.BaseAttackerKnows tr x → CleanKnows tr x
theorem CleanBase.nil : CleanBase Trace.nil := fun x hx => False.elim ((Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1 x).mp hx)
def NewNetNonSubterm (tr₀ tr : ExecTrace) : Prop := ∀ x, Trace.BaseAttackerKnows tr x → Trace.BaseAttackerKnows tr₀ x ∨ IsNonSubterm x
theorem newNetNonSubterm_refl (tr₀ : ExecTrace) : NewNetNonSubterm tr₀ tr₀ := fun _ hx => .inl hx
theorem newNetNonSubterm_append_net {tr₀ tr : ExecTrace} (h : NewNetNonSubterm tr₀ tr) {msg : Bytes} (hm : IsNonSubterm msg) : NewNetNonSubterm tr₀ (tr.append (CompTrace.NetE msg)) := by intro x hx; rcases (CompTrace.baseAttackerKnows_append_net tr msg x).mp hx with rfl | hx' <;> [exact .inr hm; exact h x hx']
theorem newNetNonSubterm_append_rnd {tr₀ tr : ExecTrace} (h : NewNetNonSubterm tr₀ tr) (n : Nat) : NewNetNonSubterm tr₀ (tr.append (CompTrace.RndE n)) := fun x hx => h x ((CompTrace.baseAttackerKnows_append_rnd tr n x).mp hx)
theorem newNetNonSubterm_append_trEv {tr₀ tr : ExecTrace} (h : NewNetNonSubterm tr₀ tr) (ev : TREvent) : NewNetNonSubterm tr₀ (tr.append (CompTrace.TREvE ev)) := fun x hx => h x ((CompTrace.baseAttackerKnows_append_trEv tr ev x).mp hx)
theorem newNetNonSubterm_append_pqEv {tr₀ tr : ExecTrace} (h : NewNetNonSubterm tr₀ tr) (ev : PQXDHEvent) : NewNetNonSubterm tr₀ (tr.append (CompTrace.PQEvE ev)) := fun x hx => h x ((CompTrace.baseAttackerKnows_append_pqEv tr ev x).mp hx)
theorem newNetNonSubterm_append_cEv {tr₀ tr : ExecTrace} (h : NewNetNonSubterm tr₀ tr) (ev : CEvent) : NewNetNonSubterm tr₀ (tr.append (CompTrace.CEvE ev)) := fun x hx => h x ((CompTrace.baseAttackerKnows_append_cEv tr ev x).mp hx)
theorem newNetNonSubterm_append_trSt {tr₀ tr : ExecTrace} (h : NewNetNonSubterm tr₀ tr) (p : Participant) (st : TRState) : NewNetNonSubterm tr₀ (tr.append (CompTrace.TRStE p st)) := fun x hx => h x ((CompTrace.baseAttackerKnows_append_trSt tr p st x).mp hx)
theorem newNetNonSubterm_append_pqSt {tr₀ tr : ExecTrace} (h : NewNetNonSubterm tr₀ tr) (p : Participant) (st : PQXDHState) : NewNetNonSubterm tr₀ (tr.append (CompTrace.PQStE p st)) := fun x hx => h x ((CompTrace.baseAttackerKnows_append_pqSt tr p st x).mp hx)
theorem cleanBase_of_newNetNonSubterm {tr₀ tr : ExecTrace} (hle : tr₀ ≤ tr) (hinv : SpqrInv tr) (h0 : CleanBase tr₀) (hnew : NewNetNonSubterm tr₀ tr) : CleanBase tr := by intro x hx; rcases hnew x hx with hx0 | hview <;> [exact (h0 x hx0).mono hle; exact .atom (hinv.netPub x hx) hview]
theorem CleanKnows.inv_chainKeyAt {tr : ExecTrace} {ck0 : Bytes} : ∀ {n : Nat}, CleanKnows tr (chainKeyAt ck0 n) → CleanKnows tr ck0
  | 0, h => h
  | _ + 1, h => CleanKnows.inv_chainKeyAt (CleanKnows.inv_kdf (chainKeyAt_succ_eq_kdfCk_fst _ _ ▸ h)).1
theorem CleanKnows.ck_d1_of_bobStart_mac {tr : ExecTrace} {d1 d2 d3 : Bytes} {d4 : Option Bytes} {ss pk sk pqSalt msg : Bytes} {counter : Nat} (hk : CleanKnows tr (hmac (trMsgKeys pqSalt (kdfCk (chainKeyAt (createChain (pqxdhKdf (pqxdhIkm d1 d2 d3 d4 ss)).rk pk sk).2 counter)).2).macKey msg)) : CleanKnows tr d1 := by
  have h4 := CleanKnows.inv_chainKeyAt (CleanKnows.inv_kdf (CleanKnows.inv_kdf (CleanKnows.inv_kdf (CleanKnows.inv_kdf hk).1).1).2).1; have h6 := (CleanKnows.inv_kdf (CleanKnows.inv_kdf (CleanKnows.inv_kdf (CleanKnows.inv_kdf h4).1).1).1).2
  cases d4 <;> exact (CleanKnows.inv_cat (CleanKnows.inv_cat h6).2).1
private theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type}
    (p : α × β) (f : α → β → Traceful γ) (hf : ∀ a b, CompTrace.Preserves Inv (f a b)) :
    CompTrace.Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b
private theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β)
    (hn : CompTrace.Preserves Inv noneCase) (hs : ∀ a, CompTrace.Preserves Inv (someCase a)) :
    CompTrace.Preserves Inv (Option.casesOn o noneCase someCase) := by rcases o with _ | a; exact hn; exact hs a
private theorem preserves_spqrRecv_optionCasesOn {Inv : ExecTrace → Prop} {α : Type} (st msg : Bytes) (idx : UInt32) (noneCase : Traceful α) (someCase : Bytes × Bytes → Traceful α) (hn : CompTrace.Preserves Inv noneCase) (hs : ∀ spqr' key, Spqr.spqrRecv st msg idx = some (spqr', key) → CompTrace.Preserves Inv (someCase (spqr', key))) : CompTrace.Preserves Inv (Option.casesOn (Spqr.spqrRecv st msg idx) noneCase someCase) := by rcases h : Spqr.spqrRecv st msg idx with _ | ⟨spqr', key⟩; exact hn; exact hs spqr' key h
private theorem preserves_genRand_newNet {tr₀ : ExecTrace} (n : Nat) : CompTrace.Preserves (NewNetNonSubterm tr₀) (Random.genRand n : Traceful Bytes) := fun tr h => (TR.Runs.genRand tr n).2.symm ▸ newNetNonSubterm_append_rnd h n
private theorem preserves_sendMessage_newNet {tr₀ : ExecTrace} {m : Bytes} (hm : IsNonSubterm m) : CompTrace.Preserves (NewNetNonSubterm tr₀) (Network.sendMessage m) := fun tr h => (TR.Runs.sendMessage tr m).2.symm ▸ newNetNonSubterm_append_net h hm
private theorem preserves_storeLocalState_tr_newNet {tr₀ : ExecTrace} (p : Participant) (st : TRState) : CompTrace.Preserves (NewNetNonSubterm tr₀) (PersistentLocalState.storeLocalState p st) := fun _ h => by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.storeLocalState_tr_snd_eq]; exact newNetNonSubterm_append_trSt h p st
private theorem preserves_storeLocalState_pq_newNet {tr₀ : ExecTrace} (p : Participant) (st : PQXDHState) : CompTrace.Preserves (NewNetNonSubterm tr₀) (PersistentLocalState.storeLocalState p st) := fun tr h => (TR.Runs.storeLocalState tr p st).2.symm ▸ newNetNonSubterm_append_pqSt h p st
private theorem preserves_logEventPQ_newNet {tr₀ : ExecTrace} (ev : PQXDHEvent) : CompTrace.Preserves (NewNetNonSubterm tr₀) (ProtocolEvent.logEvent ev) := fun tr h => (TR.Runs.logEvent tr ev).2.symm ▸ newNetNonSubterm_append_pqEv h ev
private theorem preserves_logEventTR_newNet {tr₀ : ExecTrace} (ev : TREvent) : CompTrace.Preserves (NewNetNonSubterm tr₀) (ProtocolEvent.logEvent ev) := fun _ h => by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.logEvent_snd_eq]; exact newNetNonSubterm_append_trEv h ev
private theorem preserves_logEventC_newNet {tr₀ : ExecTrace} (ev : CEvent) : CompTrace.Preserves (NewNetNonSubterm tr₀) (ProtocolEvent.logEvent ev) := fun _ h => by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.logEvent_snd_eq]; exact newNetNonSubterm_append_cEv h ev
private theorem preserves_getKey_newNet {tr₀ : ExecTrace} (p : Participant) (h : Nat) (kind : KeyKind) : CompTrace.Preserves (NewNetNonSubterm tr₀) (getKey p h kind) := CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p h) fun _ => CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
private theorem preserves_lookupIdentity_newNet {tr₀ : ExecTrace} (p : Participant) (h : Nat) : CompTrace.Preserves (NewNetNonSubterm tr₀) (lookupIdentity p h) := by
  unfold lookupIdentity; refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry h) fun _ => ?_
  split <;> [exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _; exact CompTrace.Preserves.failure]
private theorem preserves_logMessageKeyAndStore_newNet {tr₀ : ExecTrace} (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : Bytes) (n : UInt32) (r par : Nat) (st : TRState) : CompTrace.Preserves (NewNetNonSubterm tr₀) (logMessageKeyAndStore me s dir seed pqSalt n r par st) := CompTrace.Preserves.bind (preserves_logEventTR_newNet _) fun _ => preserves_storeLocalState_tr_newNet _ _
private theorem preserves_dhRatchetStep_newNet {tr₀ : ExecTrace} (st : TRState) (pk : Bytes) : CompTrace.Preserves (NewNetNonSubterm tr₀) (dhRatchetStep st pk) := by simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.bind (preserves_genRand_newNet 32) fun _ => CompTrace.Preserves.pure _
private theorem preserves_ensureReceiverChain_newNet {tr₀ : ExecTrace} (st : TRState) (pk : Bytes) : CompTrace.Preserves (NewNetNonSubterm tr₀) (ensureReceiverChain st pk) := by simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split <;> [exact CompTrace.Preserves.pure _; exact CompTrace.Preserves.bind (preserves_dhRatchetStep_newNet st pk) fun _ => CompTrace.Preserves.pure _; exact CompTrace.Preserves.failure]
private theorem preserves_logSkippedKeys_newNet {tr₀ : ExecTrace} (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) (ck : Bytes) (n : UInt32) (k : Nat) : CompTrace.Preserves (NewNetNonSubterm tr₀) (logSkippedKeys s pk rIdx src ck n k) := by induction k generalizing ck n with | zero => unfold logSkippedKeys; exact CompTrace.Preserves.pure _ | succ _ ih => unfold logSkippedKeys; exact CompTrace.Preserves.bind (preserves_logEventTR_newNet _) fun _ => ih _ _
local macro "newNet_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply CompTrace.Preserves.bind | with_reducible apply preserves_spqrRecv_optionCasesOn
  | with_reducible apply preserves_prodCasesOn | with_reducible apply preserves_optionCasesOn
  | with_reducible apply CompTrace.Preserves.pure | with_reducible apply CompTrace.Preserves.failure
  | with_reducible apply preserves_genRand_newNet | with_reducible apply preserves_storeLocalState_tr_newNet
  | with_reducible apply preserves_storeLocalState_pq_newNet | with_reducible apply preserves_sendMessage_newNet (isNonSubterm_dhPk _)
  | with_reducible apply preserves_sendMessage_newNet (isNonSubterm_vk _) | with_reducible apply preserves_sendMessage_newNet (isNonSubterm_sign _ _ _)
  | with_reducible apply preserves_sendMessage_newNet (isNonSubterm_kemPk _) | with_reducible apply preserves_sendMessage_newNet (isNonSubterm_kemEncap_fst _ _)
  | with_reducible apply preserves_sendMessage_newNet (isNonSubterm_spqrRecvKey ‹_›) | with_reducible apply CompTrace.Preserves.getLocalState_tr
  | with_reducible apply CompTrace.Preserves.getLocalState_pq | with_reducible apply preserves_getKey_newNet
  | with_reducible apply preserves_lookupIdentity_newNet | with_reducible apply CompTrace.Preserves.receiveMessage
  | with_reducible apply CompTrace.Preserves.getEntry | with_reducible apply CompTrace.Preserves.receiveSignalMsg
  | with_reducible apply CompTrace.Preserves.verifyMacAndDecrypt | with_reducible apply preserves_dhRatchetStep_newNet
  | with_reducible apply preserves_ensureReceiverChain_newNet | with_reducible apply preserves_logSkippedKeys_newNet
  | with_reducible apply CompTrace.Preserves.guardP | with_reducible apply CompTrace.Preserves.monadLiftErr
  | with_reducible apply CompTrace.Preserves.guardTrace | with_reducible apply CompTrace.Preserves.guardOnTrace
  | with_reducible apply CompTrace.Preserves.requireTracePredicate
  | with_reducible apply CompTrace.Preserves.traceLength | with_reducible apply preserves_logMessageKeyAndStore_newNet
  | with_reducible apply preserves_logEventPQ_newNet | with_reducible apply preserves_logEventTR_newNet
  | with_reducible apply preserves_logEventC_newNet | apply CompTrace.Preserves.failure | split | with_reducible intro))
theorem preserves_bobStart_newNet {tr₀ : ExecTrace} (b a : Participant) (kh : BobKeyHandles) (regA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) : CompTrace.Preserves (NewNetNonSubterm tr₀) (DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]; exact CompTrace.Preserves.bind (by unfold bobHandshake; newNet_tac) fun _ => by newNet_tac
theorem newNetNonSubterm_aliceStart (a b : Participant) (idS regB : Nat) (bh : BundleHandles) (tr : ExecTrace) : NewNetNonSubterm tr ((DY.Libsignal.Composed.aliceStart a b idS regB bh).run tr).2.val := by
  have hmove : ((DY.Libsignal.Composed.aliceStart a b idS regB bh).run tr).2.val =
      (Move.aliceStart a b idS regB bh 0).next tr := by unfold Move.next Move.act; exact (xrun_bind_unit _ tr).symm
  rw [hmove]
  rcases aliceStart_next_cases a b idS regB bh 0 tr with h | h | ⟨ikA, ikB, _, spk, _, pqpk, _, opk, _, _, _, _, _, _, _, _, _, _, h⟩ <;> rw [h]
  · exact newNetNonSubterm_refl tr
  · exact newNetNonSubterm_append_rnd (newNetNonSubterm_refl tr) 32
  · dsimp only [aliceStartTrOfOut, aliceOut]
    exact newNetNonSubterm_append_trSt (newNetNonSubterm_append_cEv (newNetNonSubterm_append_trEv (newNetNonSubterm_append_pqEv (newNetNonSubterm_append_net (newNetNonSubterm_append_net (newNetNonSubterm_append_rnd (newNetNonSubterm_append_rnd (newNetNonSubterm_append_rnd (newNetNonSubterm_refl tr) 32) 32) 32) (isNonSubterm_dhPk _)) (isNonSubterm_kemEncap_fst _ _)) _) _) _) _ _
theorem cleanBase_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) (tr : ExecTrace) (hinv : SpqrInv tr) (hbase : CleanBase tr) : CleanBase ((messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val := by
  unfold messageEncrypt; apply CompTrace.bind_getLocalState_tr_at me stateIdx tr hbase; intro st hst; obtain ⟨j, keys, hj, hkeys, _, hdhs, _, _, hcks, _⟩ := hinv.trStOK me st stateIdx hst; apply CompTrace.bind_guardP_at _ tr hbase; intro _; rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd]; dsimp only; rw [CompPresTRExp.run_sendMessage_bind_snd]
  let m := rnd tr.length 32; let tr1 := tr.append (CompTrace.RndE 32)
  let coins := rnd tr1.length coinsLen; let tr2 := tr1.append (CompTrace.RndE coinsLen)
  let key := (Spqr.spqrSend st.spqr coins).2.1; let tr3 := tr2.append (CompTrace.NetE key)
  have hinv3 : SpqrInv tr3 := CompPresTRExp.append_net_of_pub (CompPresTRExp.append_rnd coinsLen (CompPresTRExp.append_rnd 32 hinv)) (Pub.spqrSendKey_of st.spqr coins); have hle01 : tr ≤ tr1 := Trace.append_le tr _; have hle12 : tr1 ≤ tr2 := Trace.append_le tr1 _; have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 _; have hle13 : tr1 ≤ tr3 := Trace.le_trans tr1 tr2 tr3 hle12 hle23; have hle03 : tr ≤ tr3 := Trace.le_trans tr tr2 tr3 (Trace.le_trans tr tr1 tr2 hle01 hle12) hle23
  have hbase3 : CleanBase tr3 := cleanBase_of_newNetNonSubterm hle03 hinv3 hbase (newNetNonSubterm_append_net (newNetNonSubterm_append_rnd (newNetNonSubterm_append_rnd (newNetNonSubterm_refl tr) 32) coinsLen) (isNonSubterm_spqrSendKey st.spqr coins)); apply CompTrace.bind_receiveMessage_at pqIdx tr3 hbase3; intro pqSalt _ _; rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent), CompPresTRExp.run_logMessageKeyAndStore_bind_snd, CompPresTRExp.run_sendMessage_snd]
  let tr4 := tr3.append (CompTrace.TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m))
  let st' : TRState := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
  let tr5 := tr4.append (CompTrace.TREvE (TREvent.MessageKey (st.sinfo me) .sender (kdfCk st.cks).2 pqSalt st.ns st.rIdx stateIdx))
  let tr6 := tr5.append (CompTrace.TRStE me st'); let mk := trMsgKeys pqSalt (kdfCk st.cks).2
  let wire := trHonestWireMsg (DiffieHellman.dhPk st.dhs) st.ns st.pn (SymEnc.symEnc mk.cipherKey mk.iv m) (Spqr.spqrSend st.spqr coins).2.2
  let mac := computeMac mk.macKey st.myIk st.peerIk wire; let tr7 := tr6.append (CompTrace.NetE (Concat.concat wire mac))
  have hle34 : tr3 ≤ tr4 := Trace.append_le tr3 _; have hle46 : tr4 ≤ tr6 := Trace.le_trans tr4 tr5 tr6 (Trace.append_le tr4 _) (Trace.append_le tr5 _); have hle47 : tr4 ≤ tr7 := Trace.le_trans tr4 tr6 tr7 hle46 (Trace.append_le tr6 _); have hle37 : tr3 ≤ tr7 := Trace.le_trans tr3 tr6 tr7 (Trace.le_trans tr3 tr4 tr6 hle34 hle46) (Trace.append_le tr6 _)
  have hle24 : tr2 ≤ tr4 := Trace.le_trans tr2 tr3 tr4 hle23 hle34; have hle14 : tr1 ≤ tr4 := Trace.le_trans tr1 tr3 tr4 hle13 hle34; have hle04 : tr ≤ tr4 := Trace.le_trans tr tr3 tr4 hle03 hle34; have hle07 : tr ≤ tr7 := Trace.le_trans tr tr4 tr7 hle04 hle47; have hr_m : CompInv.RandAt tr4 tr.length 32 := CompInv.RandAt.mono hle14 (CompTrace.randAt_here tr 32)
  have hlen1 : tr1.length = tr.length + 1 := length_append_entry tr _
  have hlen2 : tr2.length = tr.length + 2 := by dsimp [tr2]; rw [length_append_entry, hlen1]
  have hlen3 : tr3.length = tr.length + 3 := by dsimp [tr3]; rw [length_append_entry, hlen2]
  have hlen6 : tr6.length = tr.length + 6 := by dsimp [tr6, tr5, tr4]; simp only [length_append_entry, hlen3]
  have hlen7 : tr7.length = (tr.length + 6).succ := by dsimp [tr7]; rw [length_append_entry, hlen6]
  have hr_c : CompInv.RandAt tr4 (tr.length + 1) coinsLen := hlen1 ▸ CompInv.RandAt.mono hle24 (CompTrace.randAt_here tr1 coinsLen)
  have hn_k : NetAt tr4 key (tr.length + 2) := hlen2 ▸ NetAt.mono hle34 (CompTrace.at?_append_here tr2 (CompTrace.NetE key))
  have hev_sent : tr4.EventLoggedAt (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m) (tr.length + 3) :=
    (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at? TREvent _ _ _).mpr
      (hlen3 ▸ CompTrace.at?_append_here tr3 (CompTrace.TREvE (TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m)))
  have hm_pub4 : Pub tr4 m := .rand (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨tr.length, coinsLen, key, rfl, hr_m, hr_c, hn_k, _, hev_sent⟩))))))))
  have hdh_pub4 : Pub tr4 (DiffieHellman.dhPk st.dhs) := by
    rcases hdhs with h | h <;> [exact .dhPub (.inr (.inr (.inr (.inr (.inl (h.mono hle04))))));
      exact .dhPub (.inr (.inr (.inr (.inr (.inr (h.mono hle04))))))]
  have hwire4 : CleanKnows tr4 wire := .trWire (.atom hdh_pub4 (isNonSubterm_dhPk st.dhs)) (.enc (.atom hm_pub4 (isNonSubterm_rnd tr.length 32))) (.atom (.spqrSendMsg st.spqr coins) (isNonSubterm_spqrSendMsg st.spqr coins)); obtain ⟨rkChain, pk_c, sk_c, n_c, hrk_c, hcks_eq⟩ := hcks
  have hsent7 : SentMac tr7 (hmac mk.macKey (Concat.concat st.myIk (Concat.concat st.peerIk wire))) := by
    refine ⟨tr.length, j, keys, rkChain, pk_c, sk_c, n_c, pqSalt, st.myIk, st.peerIk, wire, me, st.peer, DiffieHellman.dhPk st.dhs, st.ns, m, hj, hlen7 ▸ Nat.lt_succ_self (tr.length + 6), handshakeKeysAt_mono hle07 hkeys, evAt_mono hle47 hev_sent, hlen6 ▸ CompTrace.at?_append_here tr6 (CompTrace.NetE (Concat.concat wire mac)), hrk_c, ?_⟩
    dsimp only [mk]; rw [hcks_eq]
  intro x hx
  rcases (CompTrace.baseAttackerKnows_append_net tr6 (Concat.concat wire mac) x).mp hx with rfl | hx6
  · exact .cat (hwire4.mono hle47) (.truncSent hsent7)
  · exact (hbase3 x ((CompTrace.baseAttackerKnows_append_trEv _ _ x).mp
      ((CompTrace.baseAttackerKnows_append_trEv _ _ x).mp ((CompTrace.baseAttackerKnows_append_trSt _ _ _ x).mp hx6)))).mono hle37
def NoLeakOrBreak (tr : ExecTrace) : Prop := (∀ ev j, XplSteps.xplPqLeakEv ev = true → ¬ tr.EventLoggedAt ev j) ∧ (∀ ev j, XplSteps.xplTrLeakEv ev = true → ¬ tr.EventLoggedAt ev j) ∧ ¬ tr.EventLogged PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged PQXDHEvent.BrokenKEM
theorem NoLeakOrBreak.anti {tr tr' : ExecTrace} (hle : tr ≤ tr') (h : NoLeakOrBreak tr') : NoLeakOrBreak tr := ⟨fun ev j hp hev => h.1 ev j hp (evAt_mono hle hev), fun ev j hp hev => h.2.1 ev j hp (evAt_mono hle hev), fun hev => h.2.2.1 (ev_mono hle hev), fun hev => h.2.2.2 (ev_mono hle hev)⟩
theorem cleanBase_of_leakKind {α : Type} {c : Traceful α} {m : Move} {tr : ExecTrace}
    (hc : (do let _ ← c; pure ()) = m.act) (hk : LeakKind m)
    (hno : NoLeakOrBreak (c.run tr).2.val) (hbase : CleanBase tr) : CleanBase (c.run tr).2.val := by
  have heq : (c.run tr).2.val = m.next tr := by unfold Move.next; rw [← hc, xrun_bind_unit]
  rw [heq] at hno ⊢
  rcases xpl_leak_shape hk tr with h | ⟨e, he, hl⟩ | ⟨e, he, hl⟩
  · rw [h]; exact hbase
  · exact False.elim (hno.1 e.ev tr.length hl ((Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at? PQXDHEvent _ _ _).mpr he))
  · exact False.elim (hno.2.1 e.ev tr.length hl ((Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at? TREvent _ _ _).mpr he))
theorem cleanBase_of_reachable (tr : ExecTrace) (hreach : tr.Reachable DY.Libsignal.Composed.reachability) : NoLeakOrBreak tr → CleanBase tr := by
  induction hreach with
  | Base => intro _; exact CleanBase.nil
  | @Step trPre input hPre hReachPre ih =>
    intro hno; have hle : trPre ≤ (((DY.Libsignal.Composed.reachability.step input).snd).run trPre).2.val := xrun_le ((DY.Libsignal.Composed.reachability.step input).snd) trPre; have hbase : CleanBase trPre := ih (hno.anti hle); have hinv : SpqrInv trPre := spqrInv_of_reachable trPre hReachPre; have hinv_next : SpqrInv (((DY.Libsignal.Composed.reachability.step input).snd).run trPre).2.val := spqrInv_of_reachable _ (Trace.Reachable.Step input hPre hReachPre)
    rcases input with ⟨⟨i, hi⟩, inp⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · have hmsg : CleanKnows trPre inp := CleanKnows.of_attackerKnows hbase hPre
      intro x hx
      have hrun_eq : (((DY.Libsignal.Composed.reachability.step ⟨⟨0, hi⟩, inp⟩).snd).run trPre).2.val = trPre.append (CompTrace.NetE inp) := (TR.Runs.sendMessage trPre inp).2
      rw [hrun_eq] at hx
      rcases (CompTrace.baseAttackerKnows_append_net trPre inp x).mp hx with rfl | hx'
      · exact hmsg.mono hle
      · exact (hbase x hx').mono hle
    · change Participant at inp; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase ((by unfold registerIdentity; newNet_tac : CompTrace.Preserves _ (registerIdentity inp)) trPre (newNetNonSubterm_refl _))
    · rcases inp with ⟨p, skIdx⟩; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase ((by unfold registerCorruptIdentity; newNet_tac : CompTrace.Preserves _ (registerCorruptIdentity p skIdx)) trPre (newNetNonSubterm_refl _))
    · rcases inp with ⟨b, idS⟩; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase ((by unfold genSignedPrekey; newNet_tac : CompTrace.Preserves _ (genSignedPrekey b idS)) trPre (newNetNonSubterm_refl _))
    · rcases inp with ⟨b, idS⟩; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase ((by unfold genPQPrekey; newNet_tac : CompTrace.Preserves _ (genPQPrekey b idS)) trPre (newNetNonSubterm_refl _))
    · change Participant at inp; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase ((by unfold genOneTimePrekey; newNet_tac : CompTrace.Preserves _ (genOneTimePrekey inp)) trPre (newNetNonSubterm_refl _))
    · rcases inp with ⟨a, b, idS, regB, bh⟩; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase (newNetNonSubterm_aliceStart a b idS regB bh trPre)
    · rcases inp with ⟨b, a, kh, regA, mh, pqIdx, spqrMsgIdx⟩; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase (preserves_bobStart_newNet b a kh regA mh pqIdx spqrMsgIdx trPre (newNetNonSubterm_refl _))
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact cleanBase_messageEncrypt me stateIdx coinsLen pqIdx trPre hinv hbase
    · rcases inp with ⟨me, stateIdx⟩; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase ((by unfold messageEncryptAbort; newNet_tac : CompTrace.Preserves _ (messageEncryptAbort me stateIdx)) trPre (newNetNonSubterm_refl _))
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase ((by simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; newNet_tac : CompTrace.Preserves _ (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx)) trPre (newNetNonSubterm_refl _))
    · rcases inp with ⟨me, stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx⟩; exact cleanBase_of_newNetNonSubterm hle hinv_next hbase ((by unfold messageDecryptSkipped; newNet_tac : CompTrace.Preserves _ (messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx)) trPre (newNetNonSubterm_refl _))
    · rcases inp with ⟨me, si, k⟩; exact cleanBase_of_leakKind (m := .exposeKey me si k) rfl trivial hno hbase
    · rcases inp with ⟨me, si⟩; exact cleanBase_of_leakKind (m := .exposeSpqr me si) rfl trivial hno hbase
    · exact cleanBase_of_leakKind (m := .exposeSkipped inp) rfl trivial hno hbase
    · rcases inp with ⟨p, si⟩; exact cleanBase_of_leakKind (m := .compromiseIK p si) rfl trivial hno hbase
    · rcases inp with ⟨b, si⟩; exact cleanBase_of_leakKind (m := .compromiseSPK b si) rfl trivial hno hbase
    · rcases inp with ⟨b, si⟩; exact cleanBase_of_leakKind (m := .compromisePQSPK b si) rfl trivial hno hbase
    · rcases inp with ⟨b, si⟩; exact cleanBase_of_leakKind (m := .compromiseOPK b si) rfl trivial hno hbase
    · exact cleanBase_of_newNetNonSubterm hle hinv_next hbase (preserves_logEventPQ_newNet _ trPre (newNetNonSubterm_refl _))
    · exact cleanBase_of_newNetNonSubterm hle hinv_next hbase (preserves_logEventPQ_newNet _ trPre (newNetNonSubterm_refl _))
    · exact CompPresPQXDH.bind_guardOnTrace_at brokenDHB trPre hbase fun hbrok =>
        False.elim ((hno.anti hle).2.2.1 (CompPresPQXDH.eventLogged_of_brokenDHB hbrok))
    · exact CompPresPQXDH.bind_guardOnTrace_at brokenKEMB trPre hbase fun hbrok =>
        False.elim ((hno.anti hle).2.2.2 (CompPresPQXDH.eventLogged_of_brokenKEMB hbrok))
    · omega
def NoNewLeakTREv (tr₀ tr : ExecTrace) : Prop := ∀ (ev : TREvent) (j : Nat), XplSteps.xplTrLeakEv ev = true → tr.EventLoggedAt ev j → tr₀.EventLoggedAt ev j
theorem noNewLeakTREv_move {tr₀ tr : ExecTrace} {m : Move} (htr : NoNewLeakTREv tr₀ tr) (hnoleak : ∀ v ∈ m.vis tr, v.kind ≠ .leak) : NoNewLeakTREv tr₀ (m.next tr) := by
  intro ev j hp hev
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := TREvent)] at hev
  have hle : tr ≤ m.next tr := XplSteps.xrun_le (Move.act m) tr
  have hj_next : j < (m.next tr).length := XplSteps.xlt_of_at?_some hev
  by_cases hj : j < tr.length
  · apply htr ev j hp
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := TREvent)]
    rwa [← CompSetupSecrecy.at?_eq_of_le_of_lt hle hj]
  · exfalso
    have hmem : j ∈ newIndices tr (m.next tr) := by simp only [newIndices, List.mem_range']; exact ⟨j - tr.length, by omega, by omega⟩
    have hget : (m.next tr).getEventAt TREvent j = some ev := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at? TREvent, hev]
    obtain ⟨v, hv⟩ : ∃ v, trExposureAt (m.next tr) j = some v := by
      unfold trExposureAt; rw [hget]; revert hp; cases ev <;> simp [XplSteps.xplTrLeakEv]
    have hexp : v ∈ exposures tr (m.next tr) := List.mem_append_right _ (List.mem_filterMap.2 ⟨j, hmem, hv⟩)
    have hvis : v ∈ m.vis tr := by rw [xpl_vis_eq]; exact List.mem_append_right _ hexp
    exact hnoleak v hvis (xpl_exposures_kind hexp)
theorem noNewLeakTREv_runMoves {tr₀ : ExecTrace} :
    ∀ (ms : List Move) (tr : ExecTrace), (∀ v ∈ (runMoves ms tr).2, v.kind ≠ .leak) → NoNewLeakTREv tr₀ tr → NoNewLeakTREv tr₀ (runMoves ms tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hnoleak, htr => by
    simp only [runMoves] at hnoleak ⊢
    exact noNewLeakTREv_runMoves ms (m.next tr) (fun v hv => hnoleak v (List.mem_append_right _ hv))
      (noNewLeakTREv_move htr (fun v hv => hnoleak v (List.mem_append_left _ hv)))
theorem cleanBase_runTrace {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) (hnb : CompSetupSecrecy.NoBrk r ms) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) : CleanBase (runTraceMoves r ms) := by
  have hpq := CompSetupSecrecy.noNewLeakPQEv_runMoves (r.setupMove :: ms) Trace.nil hnoleak (CompSetupSecrecy.noNewPQEv_refl _ Trace.nil)
  have htr := noNewLeakTREv_runMoves (r.setupMove :: ms) Trace.nil hnoleak (fun _ _ _ h => h)
  have hno := CompSetupSecrecy.not_compromised_or_brokenDH_of_no_leak hNe hns hnoleak hnb
  exact cleanBase_of_reachable (runTraceMoves r ms) hreach
    ⟨fun ev j hp hev => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.not_eventLoggedAt_nil (hpq ev j hp hev),
     fun ev j hp hev => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.not_eventLoggedAt_nil (htr ev j hp hev), hno.2.2.2.2.1, hno.2.2.2.2.2⟩
theorem BobStartOk.sentMac_of_no_leak {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) (hnb : CompSetupSecrecy.NoBrk r ms) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : CompSetupSecrecy.BobStartOk (runTraceMoves r ms) b a kh regA mh pqIdx spqrMsgIdx) : ∃ t me peer dhs ns m_pt, t + 6 < (runTraceMoves r ms).length ∧ (runTraceMoves r ms).EventLoggedAt (TREvent.Sent me peer dhs ns m_pt) (t + 3) ∧ NetAt (runTraceMoves r ms) w.raw (t + 6) ∧ AliceMatch (runTraceMoves r ms) w.ikAPk (DiffieHellman.dhPk w.ikB) (PQKem.kemPk w.pqsk) w.ek w.ct w.keys t := by
  have hinv := spqrInv_of_reachable (runTraceMoves r ms) hreach; have hcik := cikOK_of_reachable hreach hinv; have hno := CompSetupSecrecy.not_compromised_or_brokenDH_of_no_leak hNe hns hnoleak hnb; have hbase := cleanBase_runTrace hNe hns hreach hnb hnoleak; have hB : IKAt (runTraceMoves r ms) b w.ikB := hinv.stOK b { kind := .identity, sk := w.ikB } kh.ik w.hik
  have hS : SPKAt (runTraceMoves r ms) b w.spk := hinv.stOK b { kind := .signedPrekey, sk := w.spk } kh.spk w.hspk; have hQ : PQAt (runTraceMoves r ms) b w.pqsk := hinv.stOK b { kind := .pqPrekey, sk := w.pqsk } kh.pqspk w.hpq; obtain ⟨e, hdec, hkeys⟩ := CompPresBob.kemDecap_of_bobAgreement w.hagree; have hmac_ak : w.msg.mac.AttackerKnows (runTraceMoves r ms) := (CompPresBob.attackerKnows_of_parseTrSignalMsg hinv (CompTrace.NetMsgAt.attackerKnows w.hmsg) w.hparse).1
  have hmac_ck : CleanKnows (runTraceMoves r ms) w.msg.mac := CleanKnows.of_attackerKnows hbase hmac_ak; have hseed : w.seed = (kdfCk (chainKeyAt (createChain w.keys.rk w.msg.ratchetKey w.spk).2 w.msg.counter.toNat)).2 := (CompPresBob.consumeMessageKey_out w.hcons).1
  have hreg_ev : (runTraceMoves r ms).EventLoggedAt (PQXDHEvent.IdentityRegistered a w.ikAPk w.vkA w.honest) regA :=
    (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at? PQXDHEvent _ _ _).mpr w.hreg
  cases hhon : w.honest with
  | false => exact absurd ⟨regA + 1, hinv.irCorrupt a w.ikAPk w.vkA regA (hhon ▸ hreg_ev)⟩ (hno.1 a w.ikAPk)
  | true =>
    obtain ⟨sA, hA, hikA, _⟩ := hinv.irHonest a w.ikAPk w.vkA regA (hhon ▸ hreg_ev); have hmac_eq : w.msg.mac = Trunc.trunc8 (hmac (trMsgKeys w.pqSalt w.seed).macKey (Concat.concat (serializedIk w.ikAPk) (Concat.concat (serializedIk (DiffieHellman.dhPk w.ikB)) w.msg.wire))) := w.hmac; rw [hmac_eq] at hmac_ck
    rcases CleanKnows.inv_trunc hmac_ck with hck_hmac | hsent
    · rw [hseed, hkeys] at hck_hmac
      have hck_d1 := CleanKnows.ck_d1_of_bobStart_mac hck_hmac; rw [hikA] at hck_d1
      have ⟨tA, hsA_eq, _⟩ := hA; have ⟨tS, hsS_eq, _⟩ := hS
      rw [hsA_eq, hsS_eq] at hck_d1
      rcases CleanKnows.inv_agree_dhPk hinv hck_d1 with hsA | hsS
      · rw [← hsA_eq] at hsA
        rcases pub_IK hinv hA hsA with hcik_ev | hbdh
        · rw [← hikA] at hcik_ev; exact absurd hcik_ev (hno.1 a w.ikAPk)
        · exact absurd hbdh hno.2.2.2.2.1
      · rw [← hsS_eq] at hsS
        rcases pub_SPK hinv hS hsS with hcspk | hbdh
        · exact absurd hcspk (hno.2.1 b (DiffieHellman.dhPk w.spk))
        · exact absurd hbdh hno.2.2.2.2.1
    · obtain ⟨t, j, keys₀, rkChain, pk, sk, counter, pqSalt', ikA', ikB', wire', me, peer, dhs, ns, m_pt,
        hjt, ht, hkeys₀, hsent_ev, hnet, hrkChain, hhmac_eq⟩ := hsent
      have hwire_eq : w.msg.wire = wire' := (concat_inj (concat_inj (hmac_inj hhmac_eq).2).2).2; have hck_at := kdfCk_snd_inj (hseed.symm.trans (trMsgKeys_macKey_inj (hmac_inj hhmac_eq).1).2); obtain ⟨hrk_eq, _⟩ := createChain_snd_inj (chainKeyAt_createChain_snd_inj hck_at).1
      rcases hrkChain with rfl | ⟨r₀, p₀, s₀, rfl⟩
      · have hrk_eq' := hrk_eq; rw [hkeys, hikA] at hrk_eq'
        rcases CompPresBob.origin_of_handshakeKeysAt_rk_eq hinv hcik hB hS hQ hA w.hcan hdec hjt hkeys₀ hrk_eq' with
          hmatch | hcik_ev | hcspk | hbdh
        · rw [← hikA, ← hkeys] at hmatch
          have hraw_eq : Concat.concat wire' (Trunc.trunc8 (hmac (trMsgKeys w.pqSalt w.seed).macKey (Concat.concat (serializedIk w.ikAPk) (Concat.concat (serializedIk (DiffieHellman.dhPk w.ikB)) w.msg.wire)))) = w.raw := by
            rw [← hwire_eq, ← hmac_eq]; have hp := w.hparse; unfold parseTrSignalMsg at hp; simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hp
            rcases hp with ⟨⟨_, _⟩, hsplit, ⟨_, _, _, _, _, _, _⟩, _, hmsg_eq⟩; rw [← hmsg_eq]
            exact Concat.concat_split w.raw (w.raw.length - Trunc.trunc8Length) _ _ hsplit
          rw [hraw_eq] at hnet; exact ⟨t, me, peer, dhs, ns, m_pt, ht, hsent_ev, hnet, hmatch⟩
        · rw [← hikA] at hcik_ev; exact absurd hcik_ev (hno.1 a w.ikAPk)
        · exact absurd hcspk (hno.2.1 b (DiffieHellman.dhPk w.spk))
        · exact absurd hbdh hno.2.2.2.2.1
      · rw [hkeys] at hrk_eq; exact False.elim (pqxdhKdf_rk_ne_createChain_fst _ _ _ _ hrk_eq)
end CleanKnowsSection
def AllAliceDone (P : DY.Bytes → Prop) (tr : ExecTrace) : Prop := ∀ a b ikA ikB spk pqpk opk ek ct keys j, tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j → P ek
theorem allAliceDone_of_noNewPQEv {P : DY.Bytes → Prop} {tr₀ tr : ExecTrace} (h : CompSetupSecrecy.NoNewPQEv isAliceDone tr₀ tr) (h0 : AllAliceDone P tr₀) : AllAliceDone P tr := fun a b ikA ikB spk pqpk opk ek ct keys j hev => h0 a b ikA ikB spk pqpk opk ek ct keys j (h _ j rfl hev)
theorem allAliceDone_of_noSessionEffect {P : DY.Bytes → Prop} {tr : ExecTrace} {m : Move} (hm : NoSessionEffect tr m) (htr : AllAliceDone P tr) : AllAliceDone P (m.next tr) := fun a b ikA ikB spk pqpk opk ek ct keys j hev => htr a b ikA ikB spk pqpk opk ek ct keys j ((eventLoggedAt_of_noSessionEffect hm).mp hev)
theorem allAliceDone_of_movesFrom_invisible {P : DY.Bytes → Prop} {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom InvisibleNoEffect tr δ) (htr : AllAliceDone P tr) : AllAliceDone P (runMoves δ tr).1 := fun a b ikA ikB spk pqpk opk ek ct keys j hev => htr a b ikA ikB spk pqpk opk ek ct keys j ((eventLoggedAt_of_movesFrom_invisibleNoEffect hδ).mp hev)
theorem allAliceDone_setupTrace {r : Records} (hNe : r.alice ≠ r.bob) (P : DY.Bytes → Prop) : AllAliceDone P (setupTrace r) := by
  intro a b ikA ikB spk pqpk opk ek ct keys j hev
  rcases setupTrace_eventLoggedAt_cases hNe hev with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
theorem allAliceDone_aliceStart {tr : ExecTrace} (a b : Participant) (idS regB : Nat) (hb : PQXDH.BundleHandles) (shown : Nat) (h0 : AllAliceDone (fun _ => False) tr) : AllAliceDone (· = DY.DiffieHellman.dhPk (randTerm tr.length 32)) ((Move.aliceStart a b idS regB hb shown).next tr) := by
  rcases aliceStart_next_cases a b idS regB hb shown tr with h | h | ⟨ikA, ikB, _, spk, _, pqpk, _, opk, _, _, _, _, _, _, _, _, _, _, h⟩ <;> rw [h]
  · exact fun a' b' ikA' ikB' spk' pqpk' opk' ek ct keys j hev => False.elim (h0 a' b' ikA' ikB' spk' pqpk' opk' ek ct keys j hev)
  · exact fun a' b' ikA' ikB' spk' pqpk' opk' ek ct keys j hev =>
      False.elim (h0 a' b' ikA' ikB' spk' pqpk' opk' ek ct keys j (CompTrace.eventLoggedAt_append_other rfl hev))
  · intro a' b' ikA' ikB' spk' pqpk' opk' ek ct keys j hev; dsimp only [aliceStartTrOfOut] at hev
    have hev := CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl hev))
    rcases CompTrace.eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨_, heq⟩
    · have hev := CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl
        (CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl hev))))
      exact False.elim (h0 a' b' ikA' ikB' spk' pqpk' opk' ek ct keys j hev)
    · injection heq with _ _ _ _ _ _ _ hek; exact hek.symm
private theorem preserves_genRand_noAliceDone {tr₀ : ExecTrace} (n : Nat) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.Random.genRand n : Traceful DY.Bytes) := fun tr h => (TR.Runs.genRand tr n).2.symm ▸ CompSetupSecrecy.noNewPQEv_append_other h (CompTrace.RndE n) rfl
private theorem preserves_sendMessage_noAliceDone {tr₀ : ExecTrace} (m : DY.Bytes) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.Network.sendMessage m) := fun tr h => (TR.Runs.sendMessage tr m).2.symm ▸ CompSetupSecrecy.noNewPQEv_append_other h (CompTrace.NetE m) rfl
private theorem preserves_storeLocalState_tr_noAliceDone {tr₀ : ExecTrace} (p : Participant) (st : TRState) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.PersistentLocalState.storeLocalState p st) := fun _ h => by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.storeLocalState_tr_snd_eq]; exact CompSetupSecrecy.noNewPQEv_append_other h (CompTrace.TRStE p st) rfl
private theorem preserves_storeLocalState_pq_noAliceDone {tr₀ : ExecTrace} (p : Participant) (st : PQXDH.PQXDHState) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.PersistentLocalState.storeLocalState p st) := fun tr h => (TR.Runs.storeLocalState tr p st).2.symm ▸ CompSetupSecrecy.noNewPQEv_append_other h (CompTrace.PQStE p st) rfl
private theorem preserves_logEventPQ_opk_noAliceDone {tr₀ : ExecTrace} (b : Participant) (opk : DY.Bytes) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.ProtocolEvent.logEvent (PQXDHEvent.OPKUsed b opk)) := fun tr h => (TR.Runs.logEvent tr _).2.symm ▸ CompSetupSecrecy.noNewPQEv_append_pq h _ rfl
private theorem preserves_logEventPQ_bobDone_noAliceDone {tr₀ : ExecTrace} (b a : Participant) (ikA ikB spk pqpk : DY.Bytes) (opk : Option DY.Bytes) (ek ct : DY.Bytes) (keys : PQXDH.HandshakeKeys) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.ProtocolEvent.logEvent (PQXDHEvent.BobDone b a ikA ikB spk pqpk opk ek ct keys)) := fun tr h => (TR.Runs.logEvent tr _).2.symm ▸ CompSetupSecrecy.noNewPQEv_append_pq h _ rfl
private theorem preserves_logEventC_noAliceDone {tr₀ : ExecTrace} (ev : CEvent) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.ProtocolEvent.logEvent ev) := fun _ h => by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.logEvent_snd_eq]; exact CompSetupSecrecy.noNewPQEv_append_other h (CompTrace.CEvE ev) rfl
private theorem preserves_logEventTR_noAliceDone {tr₀ : ExecTrace} (ev : TREvent) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.ProtocolEvent.logEvent ev) := fun _ h => by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.logEvent_snd_eq]; exact CompSetupSecrecy.noNewPQEv_append_other h (CompTrace.TREvE ev) rfl
private theorem preserves_getKey_noAliceDone {tr₀ : ExecTrace} (p : Participant) (h : Nat) (kind : PQXDH.KeyKind) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.Libsignal.PQXDH.getKey p h kind) := CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p h) fun _ => CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
private theorem preserves_lookupIdentity_noAliceDone {tr₀ : ExecTrace} (p : Participant) (h : Nat) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity; refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry h) fun _ => ?_
  split <;> [exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _; exact CompTrace.Preserves.failure]
private theorem preserves_logMessageKeyAndStore_noAliceDone {tr₀ : ExecTrace} (me : Participant) (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r par : Nat) (st : TRState) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) := CompTrace.Preserves.bind (preserves_logEventTR_noAliceDone _) fun _ => preserves_storeLocalState_tr_noAliceDone _ _
private theorem preserves_logSkippedKeys_noAliceDone {tr₀ : ExecTrace} (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by induction k generalizing ck n with | zero => unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact CompTrace.Preserves.pure _ | succ _ ih => unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact CompTrace.Preserves.bind (preserves_logEventTR_noAliceDone _) fun _ => ih _ _
private theorem preserves_dhRatchetStep_noAliceDone {tr₀ : ExecTrace} (st : TRState) (pk : DY.Bytes) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.bind (preserves_genRand_noAliceDone 32) fun _ => CompTrace.Preserves.pure _
private theorem preserves_ensureReceiverChain_noAliceDone {tr₀ : ExecTrace} (st : TRState) (pk : DY.Bytes) : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr₀) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split <;> [exact CompTrace.Preserves.pure _; exact CompTrace.Preserves.bind (preserves_dhRatchetStep_noAliceDone st pk) fun _ => CompTrace.Preserves.pure _; exact CompTrace.Preserves.failure]
local macro "noAliceDone_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply CompTrace.Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply CompTrace.Preserves.pure
  | with_reducible apply CompTrace.Preserves.failure | with_reducible apply preserves_genRand_noAliceDone
  | with_reducible apply preserves_storeLocalState_tr_noAliceDone | with_reducible apply preserves_storeLocalState_pq_noAliceDone
  | with_reducible apply preserves_sendMessage_noAliceDone | with_reducible apply CompTrace.Preserves.getLocalState_tr
  | with_reducible apply CompTrace.Preserves.getLocalState_pq | with_reducible apply preserves_getKey_noAliceDone
  | with_reducible apply preserves_lookupIdentity_noAliceDone | with_reducible apply CompTrace.Preserves.receiveMessage
  | with_reducible apply CompTrace.Preserves.getEntry | with_reducible apply CompTrace.Preserves.receiveSignalMsg
  | with_reducible apply CompTrace.Preserves.verifyMacAndDecrypt | with_reducible apply preserves_dhRatchetStep_noAliceDone
  | with_reducible apply preserves_ensureReceiverChain_noAliceDone | with_reducible apply preserves_logSkippedKeys_noAliceDone
  | with_reducible apply CompTrace.Preserves.guardP | with_reducible apply CompTrace.Preserves.monadLiftErr
  | with_reducible apply CompTrace.Preserves.guardTrace | with_reducible apply CompTrace.Preserves.guardOnTrace
  | with_reducible apply CompTrace.Preserves.requireTracePredicate
  | with_reducible apply CompTrace.Preserves.traceLength | with_reducible apply preserves_logMessageKeyAndStore_noAliceDone
  | with_reducible apply preserves_logEventPQ_opk_noAliceDone | with_reducible apply preserves_logEventPQ_bobDone_noAliceDone
  | with_reducible apply preserves_logEventC_noAliceDone | with_reducible apply preserves_logEventTR_noAliceDone
  | split | with_reducible intro))
theorem allAliceDone_sendBy {P : DY.Bytes → Prop} {p : Participant} {m : Move} {tr : ExecTrace} (hsnd : SendBy p m) (htr : AllAliceDone P tr) : AllAliceDone P (m.next tr) := by
  have hp : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr) (Move.act m) := by
    cases m <;> try exact False.elim hsnd
    · unfold Move.act DY.Libsignal.TripleRatchet.messageEncrypt; noAliceDone_tac
    · unfold Move.act DY.Libsignal.TripleRatchet.messageEncryptAbort; noAliceDone_tac
    · unfold Move.act DY.Libsignal.TripleRatchet.messageEncrypt; noAliceDone_tac
  exact allAliceDone_of_noNewPQEv (hp tr (CompSetupSecrecy.noNewPQEv_refl _ tr)) htr
theorem noNewPQEv_bobStart {tr : ExecTrace} (b a : Participant) (kh : PQXDH.BobKeyHandles) (regA : Nat) (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat) : CompSetupSecrecy.NoNewPQEv isAliceDone tr ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr) := by
  have hp : CompTrace.Preserves (CompSetupSecrecy.NoNewPQEv isAliceDone tr) (Move.act (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown)) := by
    unfold Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
    exact CompTrace.Preserves.bind (CompTrace.Preserves.bind (by unfold DY.Libsignal.PQXDH.bobHandshake; noAliceDone_tac) fun _ => by noAliceDone_tac) fun _ => CompTrace.Preserves.pure _
  exact hp tr (CompSetupSecrecy.noNewPQEv_refl _ tr)
theorem allAliceDone_bobStart {P : DY.Bytes → Prop} {tr : ExecTrace} (b a : Participant) (kh : PQXDH.BobKeyHandles) (regA : Nat) (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat) (htr : AllAliceDone P tr) : AllAliceDone P ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr) :=
  allAliceDone_of_noNewPQEv (noNewPQEv_bobStart b a kh regA mh pqIdx spqrMsgIdx shown) htr
theorem allAliceDone_xplBlock_ini {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ δ : List Move} {acc : List MachineEvent} {bun : HwBytes} {rs : List MachineEvent} (hB : XplBlock6 i r S g ms₀ δ acc (.recv bun :: rs)) (hrs : ∀ e ∈ rs, eventKind e = .rng) (htr : AllAliceDone (fun _ => False) (runTraceMoves r ms₀)) : ∃ ek₀, AllAliceDone (· = ek₀) (runTraceMoves r (ms₀ ++ δ)) := by
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨hs, ha, hm⟩, hpost_inv⟩ :=
    xpl6_oneMove hB (by intro e he; simp at he; subst he; exact Or.inl rfl) (by simp) (by intro e he; rw [hrs e he]; decide)
  have hact : ActorIn ((moveActor m).getD r.alice) m := by unfold ActorIn; cases moveActor m <;> simp
  have hstep := xplStep_ini hs ha hm ⟨⟨bun, rfl⟩, hrs⟩ hact
  let tr_pre := (runMoves pre (runTraceMoves r ms₀)).1
  have htr_pre : AllAliceDone (fun _ => False) tr_pre := allAliceDone_of_movesFrom_invisible hpre_inv htr
  refine ⟨DY.DiffieHellman.dhPk (randTerm tr_pre.length 32), ?_⟩
  rw [CompPrefixInvStruct.runTrace_append, runMoves_append_fst, runMoves_cons_fst]
  refine allAliceDone_of_movesFrom_invisible hpost_inv ?_; rcases hstep.2 with hini | hneff
  · unfold IniKind at hini; cases m <;> try exact False.elim hini
    case aliceStart a b idS regB hb shown => exact allAliceDone_aliceStart a b idS regB hb shown htr_pre
    case reject draws =>
      have hnext : (Move.reject draws).next tr_pre = tr_pre := by
        unfold Move.next Move.act; simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_pure_snd]
      rw [hnext]; exact fun a' b' ikA ikB spk pqpk opk ek ct keys j hev => False.elim (htr_pre a' b' ikA ikB spk pqpk opk ek ct keys j hev)
    case attackerSend msg =>
      unfold Move.next Move.act; rw [xrun_bind_unit, (TR.Runs.sendMessage tr_pre msg).2]
      exact fun a' b' ikA ikB spk pqpk opk ek ct keys j hev =>
        False.elim (htr_pre a' b' ikA ikB spk pqpk opk ek ct keys j (CompTrace.eventLoggedAt_append_other rfl hev))
  · exact allAliceDone_of_noSessionEffect hneff fun a' b' ikA ikB spk pqpk opk ek ct keys j hev =>
      False.elim (htr_pre a' b' ikA ikB spk pqpk opk ek ct keys j hev)
theorem allAliceDone_xplBlock_send {P : DY.Bytes → Prop} {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms₀ δ : List Move} {acc : List MachineEvent} {b_pt : HwBytes} {tail : List MachineEvent} (hB : XplBlock6 i r S g ms₀ δ acc (.pt b_pt :: tail)) (htail : ∀ e ∈ tail, eventKind e = .rng ∨ eventKind e = .send) (htr : AllAliceDone P (runTraceMoves r ms₀)) : AllAliceDone P (runTraceMoves r (ms₀ ++ δ)) := by
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨hs, _, hm⟩, hpost_inv⟩ :=
    xpl6_oneMove hB (by intro e he; simp at he; subst he; exact Or.inr rfl)
      (by simp) (by intro e he; rcases htail e he with h | h <;> rw [h] <;> decide)
  have hact : ActorIn ((moveActor m).getD r.alice) m := by unfold ActorIn; cases moveActor m <;> simp
  have hstep := xplStep_send hs hm ⟨⟨b_pt, rfl⟩, htail⟩ hact; rw [CompPrefixInvStruct.runTrace_append, runMoves_append_fst, runMoves_cons_fst]; exact allAliceDone_of_movesFrom_invisible hpost_inv (allAliceDone_sendBy hstep.1 (allAliceDone_of_movesFrom_invisible hpre_inv htr))
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
