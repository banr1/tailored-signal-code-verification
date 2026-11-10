/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Sanitize
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptHypsPure
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Opk
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.ReadFaithful
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRelPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.Fail
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Faithfulness, Rejected-Call `Clean`, and `COpkRelC` Lemmas for Pre-Key Receive

Discharges `DeltaFaithful`, `RoleSnapshots`, `preKeyRepresentations`, and `¬ KyberMismatch` on an
accepting `bobStart` block, and proves `rpk_clean_reject` and `rpk_accept_cOpk`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure.RpkCli
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement (opkRemovedIdx)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)

theorem rpkRel_invisible_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ →
      (runMoves δ tr).2 = [] ∧ visActorsFrom δ tr = []
  | [], _, _ => ⟨rfl, rfl⟩
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    obtain ⟨h1, h2⟩ := rpkRel_invisible_nil δ (m.next tr) hδ
    exact ⟨by simp only [runMoves, hv, h1, List.nil_append],
      by simp only [visActorsFrom, hv, h2, List.length_nil, List.replicate_zero, List.nil_append]⟩

theorem rpkRel_moveActor_eq_party {m : Move} (h : RecvHeadKind m) : moveActor m = m.party? := by
  cases m <;> first | rfl | exact False.elim h

theorem rpk_deltaFaithful_of_roleFaithful {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {caller : Option Participant} {acc : List MachineEvent} {b d pt : HwBytes}
    (hc : caller = some r.bob) {who : List Participant} {g : Ghost} {ms₀ δ : List Move}
    (hB : XplBlock interpretation r S who g ms₀ δ acc [.recv b, .rng d, .accept pt])
    (hrf : RoleFaithful r who (ms₀ ++ δ)) (hwho : who[(callStarts acc).length]? = caller) :
    DeltaFaithful r.bob (runTraceMoves r ms₀) δ := by
  have htail : ∀ e ∈ ([.recv b, .rng d, .accept pt] : List MachineEvent).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h
  obtain ⟨pre, m, post, rfl, hpre, ⟨_, _, hm⟩, hpost⟩ :=
    xpl_oneMove hB (rpkA2_blockHead b d pt) (List.cons_ne_nil _ _) htail
  obtain ⟨hpreV, hpreA⟩ := rpkRel_invisible_nil pre (runTraceMoves r ms₀) hpre
  obtain ⟨_, hpostA⟩ := rpkRel_invisible_nil post _ hpost
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm (e := .recv b) rfl
  have hrk := xpl_recvHeadKind m _ hv hvk
  have hagree : ActorAgrees (moveActor m) (some r.bob) := by
    rw [rpkRel_moveActor_eq_party hrk]
    rcases hp : m.party? with _ | p
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ?_)
      have hrf' := hrf (ms₀.length + pre.length) m p
        (by rw [← List.append_assoc, List.getElem?_append_right (by simp)]; simp) hp
      have htake : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
        rw [← List.append_assoc]; exact List.take_left' (by simp)
      rw [htake, TR.runVis_append, hpreV, List.append_nil,
        Sanitize.callCount_of_forall₂ hB.pre.2.2.2.2.2, hwho, hc] at hrf'
      exact hrf'.symm
  unfold DeltaFaithful; intro a ha
  rw [visActorsFrom_append, hpreA, List.nil_append] at ha
  simp only [visActorsFrom, hpostA, List.append_nil] at ha
  rw [List.eq_of_mem_replicate ha]; exact hagree

theorem rpk_peer_eq_of_peerFaithful {r : ProtocolSetup} {ms₀ pre post : List Move}
    {a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    (hpeer : PeerFaithful r
      (ms₀ ++ (pre ++ Move.bobStart r.bob a kh regA mh pqIdx spqrMsgIdx shown :: post))) :
    a = r.alice := by
  have h := hpeer _ (List.mem_append_right ms₀ (List.mem_append_right pre (List.mem_cons_self ..)))
  simpa [Move.MatchesSetupPeer] using h

theorem rpkRel_decVis_absurd {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr tr' : ExecTrace} {si msgIdx : Nat} {b d pt : HwBytes}
    {pf : PreKeyFields} (hparse : parsePreKeyWire b = some pf)
    {v : VisEntry} (hv : v ∈ decVis tr tr' si msgIdx false ++ exposures tr tr') (hvk : v.kind = .recv)
    (hvis : List.Forall₂ (EventMatchesEntry interpretation r S g)
      [.recv b, .rng d, .accept pt] (decVis tr tr' si msgIdx false ++ exposures tr tr')) : False := by
  rcases hmsg : tr.getMessageSentAt msgIdx with _ | raw
  · rcases List.mem_append.1 hv with hv | hv
    · simp only [decVis, hmsg, Option.map_none, Option.toList_none, List.nil_append,
        List.mem_append, List.mem_map] at hv
      rcases hv with ⟨_, _, rfl⟩ | hv
      · simp [rngEntry] at hvk
      · cases hp : receivedPlaintext tr tr' <;> simp [hp] at hv
        subst hv; simp at hvk
    · rw [xpl_exposures_kind hv] at hvk; simp at hvk
  · simp only [decVis, hmsg, Option.map_some, Option.toList_some, List.cons_append] at hvis
    cases hvis with
    | cons hme _ =>
      obtain ⟨t, _, hb⟩ := hme.2
      change b = TripleRatchet.Refinement.wireWhisperTag :: gamma interpretation S g t at hb
      rw [hb] at hparse
      simp [parsePreKeyWire, TripleRatchet.Refinement.wireWhisperTag,
        PQXDH.Refinement.wirePrekeyTag] at hparse

theorem rpk_noDecrypt_of_pathFaithful {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {sent accepted : List HwBytes}
    {acc : List MachineEvent} {b d pt : HwBytes} {pf : PreKeyFields}
    (hparse : parsePreKeyWire b = some pf)
    (hfresh : ∀ q, parsePreKeyWire b = some q → q.baseKey.take 33 ∉ accepted)
    {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hpath : PathFaithful interpretation r S g (ms₀ ++ (pre ++ m :: post))
      (acc ++ [.recv b, .rng d, .accept pt]))
    (hbook : CBook interpretation r S g ms₀ sent accepted acc) :
    ¬ DecryptBy r.bob m := by
  intro hdec
  have hi : (ms₀ ++ (pre ++ m :: post))[ms₀.length + pre.length]? = some m := by
    rw [← List.append_assoc, List.getElem?_append_right (by simp)]; simp
  have htake : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
    rw [← List.append_assoc]; exact List.take_left' (by simp)
  obtain ⟨hpreV, _⟩ := rpkRel_invisible_nil pre (runTraceMoves r ms₀) hpre
  obtain ⟨hpostV, _⟩ := rpkRel_invisible_nil post (m.next (runMoves pre (runTraceMoves r ms₀)).1) hpost
  have htr_pre : runTraceMoves r (ms₀ ++ pre) = (runMoves pre (runTraceMoves r ms₀)).1 :=
    TR.runTrace_append r ms₀ pre
  have hvis : List.Forall₂ (EventMatchesEntry interpretation r S g)
      [.recv b, .rng d, .accept pt] (m.vis (runTraceMoves r (ms₀ ++ pre))) := by
    have hm := hB.matched
    rw [b5_runMoves_append_snd, hpreV, List.nil_append, runMoves_cons_snd, hpostV,
      List.append_nil, ← htr_pre] at hm
    exact hm
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hvis (e := .recv b) rfl
  have hcc : callCount (runVis r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length))) =
      (callStarts acc).length := by
    rw [htake, TR.runVis_append, hpreV, List.append_nil]
    exact Sanitize.callCount_of_forall₂ hB.pre.2.2.2.2.2
  have hcall : (callStarts (acc ++ [.recv b, .rng d, .accept pt]))[
      callCount (runVis r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length)))]? =
      some (.recv b) := by
    rw [hcc, show callStarts (acc ++ [.recv b, .rng d, .accept pt]) = callStarts acc ++ [.recv b]
      by simp [callStarts, List.filter_append, eventKind], List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  have hbook_done : ∀ ek ∈ bobDoneBaseKeys
      (runTraceMoves r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length))),
      ecKey (gamma interpretation S g ek) ∈ accepted := by
    rw [htake, XplQuiet.quiet_bobDoneBaseKeys (b2_quietPre hpre)]; exact hbook.2.2.2
  have hnot_true : m.prekeyPath? ≠ some true := by
    intro hpath_m
    obtain ⟨ek, hek, heq⟩ := (hpath (ms₀.length + pre.length) m true b pf
      hi hpath_m hcall hparse).1 rfl
    exact hfresh pf hparse (heq ▸ hbook_done ek hek)
  cases m with
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    cases wrapped
    · rw [xpl_vis_eq] at hv hvis; exact rpkRel_decVis_absurd hparse hv hvk hvis
    · exact hnot_true rfl
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    cases wrapped
    · rw [xpl_vis_eq] at hv hvis; exact rpkRel_decVis_absurd hparse hv hvk hvis
    · exact hnot_true rfl
  | _ => exact False.elim hdec

theorem rpk_roleSnapshots_accept {interpretation : ExternInterpretation} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms₀ δ : List Move}
    {acc : List MachineEvent} {b d pt : HwBytes}
    (hB : XplBlock interpretation r S who g ms₀ δ acc [.recv b, .rng d, .accept pt])
    (hdf : DeltaFaithful r.bob (runTraceMoves r ms₀) δ)
    (hrole₀ : RoleSnapshots r (runTraceMoves r ms₀)) :
    RoleSnapshots r (runTraceMoves r (ms₀ ++ δ)) := by
  rw [TR.runTrace_append]
  exact roleSnapshots_of_oneMove
    (fun _ _ ⟨hact, hkind, _⟩ => roleSnapshots_of_rpkMove hwf.1 hact hkind)
    (xplInv_rpk hB hdf (rpkA2_blockShape b d pt)) hrole₀

theorem rpkRel_attackerKnows_of_at? {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : tr.at? i = some (Symbolic.Swarm.CREF.TR.NetE b)) : b.AttackerKnows tr := by
  have hs : tr.getMessageSentAt i = some b := by simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; rw [h]
  exact DY.Trace.MessageSentAt_implies_AttackerKnows tr b i
    ((DY.Trace.MessageSentAt_eq_getMessageSentAt b i tr).mpr hs)

theorem rpkRel_getMessageSentAt_of_at? {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : tr.at? i = some (Symbolic.Swarm.CREF.TR.NetE b)) : tr.getMessageSentAt i = some b := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; rw [h]

theorem rpk_rep_of_readFaithful {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx shown :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx shown).next
        (runMoves pre (runTraceMoves r ms₀)).1) post)
    (w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) r.bob r.alice kh regA mh pqIdx spqrMsgIdx)
    (hrf : ReadFaithful interpretation r S g
      (ms₀ ++ (pre ++ Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx shown :: post))
      (acc ++ [.recv b, .rng d, .accept pt])) :
    ⟨w.ek, w.ct, w.raw⟩ ∈ preKeyRepresentations interpretation r S g (ms₀ ++ pre) b := by
  let m := Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx shown
  obtain ⟨hpreV, _⟩ := rpkRel_invisible_nil pre (runTraceMoves r ms₀) hpre
  obtain ⟨hpostV, _⟩ := rpkRel_invisible_nil post (m.next (runMoves pre (runTraceMoves r ms₀)).1) hpost
  have htr_pre : runTraceMoves r (ms₀ ++ pre) = (runMoves pre (runTraceMoves r ms₀)).1 :=
    TR.runTrace_append r ms₀ pre
  have hm_vis : List.Forall₂ (EventMatchesEntry interpretation r S g)
      [.recv b, .rng d, .accept pt] (m.vis (runTraceMoves r (ms₀ ++ pre))) := by
    have hm := hB.matched
    rw [b5_runMoves_append_snd, hpreV, List.nil_append, runMoves_cons_snd, hpostV,
      List.append_nil, ← htr_pre] at hm
    exact hm
  obtain ⟨v₀, vrng, hhead_match, _, hvis_eq⟩ := List.forall₂_cons_left_iff.mp hm_vis
  have hshown : 0 < shown := by
    by_contra h0
    have h0' : shown = 0 := by omega
    have hexp : ∀ u ∈ exposures (runTraceMoves r (ms₀ ++ pre))
        ((Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx 0).next (runTraceMoves r (ms₀ ++ pre))),
        u.kind ≠ .recv := by
      intro u hu; rw [xpl_exposures_kind hu]; simp
    have hv₀_mem : v₀ ∈ (Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx 0).vis
        (runTraceMoves r (ms₀ ++ pre)) := by
      have : (Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx 0).vis
          (runTraceMoves r (ms₀ ++ pre)) = v₀ :: vrng := by simpa [m, h0'] using hvis_eq
      rw [this]; exact List.mem_cons_self
    rw [xpl_vis_eq] at hv₀_mem
    exact hexp v₀ hv₀_mem hhead_match.1.symm
  obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
  have hv₀_eq : v₀ = ⟨.recv, [w.ek, w.ct, w.raw] ++
      (bobOpkPk r.bob kh (runTraceMoves r (ms₀ ++ pre))).toList, .preKeyRecv, none⟩ := by
    have hv : (Move.bobStart r.bob r.alice kh regA mh pqIdx spqrMsgIdx (k + 1)).vis
        (runTraceMoves r (ms₀ ++ pre)) = v₀ :: vrng := hvis_eq
    rw [xpl_vis_eq] at hv
    simp only [xpl_ownVis, bobVis, received, List.filterMap_cons, List.filterMap_nil,
      rpkRel_getMessageSentAt_of_at? w.hek, rpkRel_getMessageSentAt_of_at? w.hct,
      rpkRel_getMessageSentAt_of_at? w.hmsg, List.cons_append] at hv
    exact (List.cons.inj hv).1.symm
  have hrunVis : runVis r (ms₀ ++ (pre ++ m :: post)) =
      runVis r ms₀ ++ m.vis (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runVis_append, b5_runMoves_append_snd, hpreV, List.nil_append, runMoves_cons_snd,
      hpostV, List.append_nil, ← htr_pre]
  have hzip_mem : (MachineEvent.recv b, v₀) ∈
      (acc ++ [MachineEvent.recv b, .rng d, .accept pt]).zip (runVis r (ms₀ ++ (pre ++ m :: post))) := by
    rw [hrunVis, List.zip_append hB.pre.2.2.2.2.2.length_eq, hvis_eq]
    exact List.mem_append_right _ List.mem_cons_self
  have hok_read := readFaithful_iff.mp hrf (MachineEvent.recv b, v₀) hzip_mem (by rw [hv₀_eq])
  rw [hv₀_eq] at hok_read
  dsimp only [ReadOKWith, eventBytes, List.cons_append] at hok_read
  exact ⟨rpkRel_attackerKnows_of_at? w.hek, rpkRel_attackerKnows_of_at? w.hct,
    rpkRel_attackerKnows_of_at? w.hmsg, hok_read.2.2.2⟩

theorem rpk_not_kyberMismatch_of_not_collisionAt {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {sent accepted : List HwBytes} {g₀ : Ghost} {ms₀ pre δ' : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {pf : PreKeyFields} {x : PreKeyRep}
    (hexpl : ExplainsMoves interpretation r S who ok g₀ (ms₀ ++ (pre ++ δ'))
      (acc ++ [.recv b, .rng d, .accept pt]))
    (hB : XplBlock interpretation r S who g₀ ms₀ (pre ++ δ') acc [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hparse : parsePreKeyWire b = some pf)
    (hfresh : ∀ q, parsePreKeyWire b = some q → q.baseKey.take 33 ∉ accepted)
    (hbook₀ : CBook interpretation r S g₀ ms₀ sent accepted acc)
    (hrep : x ∈ preKeyRepresentations interpretation r S g₀ (ms₀ ++ pre) b)
    (hcol : ¬ CollisionAt interpretation r S who ok (acc ++ [.recv b, .rng d, .accept pt])) :
    ¬ KyberMismatch interpretation r pf := by
  intro hkm
  have hpre_f2 : List.Forall₂ (EventMatchesEntry interpretation r S g₀) acc
      (runVis r (ms₀ ++ pre)) := by
    rw [TR.runVis_append, (rpkRel_invisible_nil pre (runTraceMoves r ms₀) hpre).1, List.append_nil]
    exact hB.pre.2.2.2.2.2
  have hexpl_pre : ExplainsMoves interpretation r S who ok g₀ (ms₀ ++ pre) acc := by
    have hexpl' : ExplainsMoves interpretation r S who ok g₀ ((ms₀ ++ pre) ++ δ')
        (acc ++ [.recv b, .rng d, .accept pt]) := by
      simpa only [List.append_assoc] using hexpl
    exact explains_prefix hpre_f2.length_eq hexpl'
  have hnkb : ¬ KnownBaseKey interpretation r S g₀ (ms₀ ++ pre) pf := by
    rintro ⟨ek, hek, heq⟩
    rw [XplQuiet.quiet_bobDoneBaseKeys (b2_quietPre hpre)] at hek
    exact hfresh pf hparse (heq ▸ hbook₀.2.2.2 ek hek)
  apply hcol
  rcases b with _ | ⟨tag, body⟩
  · cases hparse
  · exact ⟨acc, .recv (tag :: body), [.rng d, .accept pt], g₀, ms₀ ++ pre, rfl, hexpl_pre,
      ⟨pt, rfl⟩, .inr ⟨pf, hparse, by simp [hnkb]; exact ⟨⟨x, hrep⟩, .inl hkm⟩⟩⟩

theorem rpkRel_clearStuckWrap_prekeyPath?_imp {tr : ExecTrace} {m : Move} {promote : Bool}
    (hp : (Sanitize.clearStuckWrap tr m).prekeyPath? = some promote) :
    m.prekeyPath? = some promote := by
  cases m <;> simp only [Sanitize.clearStuckWrap, Move.prekeyPath?] at hp ⊢
  case bobStart => exact hp
  case decrypt me si mi pq sp w => revert hp; cases (tr.getMessageSentAt mi).isSome <;> simp
  case decryptSkipped me si mi k pq sp w => revert hp; cases (tr.getMessageSentAt mi).isSome <;> simp
  all_goals cases hp

theorem rpkRel_sanitize_clean {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} (hc : Clean interpretation r S who ok g ms acc) :
    Clean interpretation r S who ok g (Sanitize.sanitizeMoves (setupTrace r) ms) acc := by
  let ms_s := Sanitize.sanitizeMoves (setupTrace r) ms
  have hpath_s : PathFaithful interpretation r S g ms_s acc := by
    intro i m' promote b' p hi hpath hcall hparse
    rw [Sanitize.getElem?_sanitizeMoves] at hi
    rcases hmi : ms[i]? with _ | m
    · simp [hmi] at hi
    · simp only [hmi, Option.map_some, Option.some.injEq] at hi
      subst hi
      simp only [ms_s, Sanitize.sanitizeMoves_take, Sanitize.runVis_sanitizeMoves,
        Sanitize.runTrace_sanitizeMoves] at hcall ⊢
      exact hc.matched.2.2.2.1 i m promote b' p hmi
        (rpkRel_clearStuckWrap_prekeyPath?_imp hpath) hcall hparse
  exact ⟨⟨⟨hc.matched.1, Sanitize.modelRun_sanitizeMoves hc.matched.2.1,
    Sanitize.roleFaithful_sanitizeMoves hc.matched.2.2.1, hpath_s,
    Sanitize.readFaithful_sanitizeMoves hc.matched.2.2.2.2.1,
    by simpa [ms_s] using hc.matched.2.2.2.2.2⟩,
    Sanitize.outcomeFaithful_sanitizeMoves hc.1.2⟩,
    mt Sanitize.readCollision_sanitizeMoves_iff.mp hc.2⟩

theorem rpkRel_sanitize_path_fail {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} (b : HwBytes) (ds : List HwBytes)
    (hc : Clean interpretation r S who ok g ms acc) :
    PathFaithful interpretation r S g (Sanitize.sanitizeMoves (setupTrace r) ms)
      (acc ++ (.recv b :: ds.map MachineEvent.rng)) := by
  have hc_s := rpkRel_sanitize_clean hc
  intro i m' promote b' p hi hpath hcall hparse
  have hk := Sanitize.callCount_take_lt_of_sanitizeMoves_prekeyPath? hc.matched hi hpath
  have hcs_app : callStarts (acc ++ (.recv b :: ds.map MachineEvent.rng)) =
      callStarts acc ++ [.recv b] := by
    unfold callStarts; rw [List.filter_append]
    exact congrArg (callStarts acc ++ ·)
      (show MachineEvent.recv b :: callStarts (ds.map MachineEvent.rng) = [.recv b]
        by rw [rpk_callStarts_map_rng])
  rw [hcs_app, List.getElem?_append_left hk] at hcall
  exact hc_s.matched.2.2.2.1 i m' promote b' p hi hpath hcall hparse

theorem rpk_clean_reject {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} (b : HwBytes) (ds : List HwBytes)
    (hc : Clean interpretation r S who ok g ms acc)
    (hok : ok (callStarts acc).length = false) :
    Clean interpretation r S who ok g
      (Sanitize.sanitizeMoves (setupTrace r) ms ++ [.reject (ds.map List.length)])
      (acc ++ (.recv b :: ds.map MachineEvent.rng)) :=
  clean_snoc_reject b ds (rpkRel_sanitize_clean hc) (rpkRel_sanitize_path_fail b ds hc) hok

theorem rpk_accept_cOpk {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc : List MachineEvent}
    {b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields} {d ct_wire pt : HwBytes}
    (hA : RpkAcceptHypsPure interpretation r S who ok records sent accepted opkUsed acc b sm pf d ct_wire pt) :
    COpkRelC interpretation r S who ok
      (opkUsed || (sm.message[opkRemovedIdx]?).any (· != 0#8))
      (acc ++ [.recv b, .rng d, .accept pt]) := by
  cases hu : (opkUsed || (sm.message[opkRemovedIdx]?).any (· != 0#8)) with
  | true => intro _ h; exact Bool.noConfusion h
  | false =>
    have hu' := Bool.or_eq_false_iff.mp hu
    have hk : pf.preKeyId = none := by
      cases hk : pf.preKeyId with
      | none => rfl
      | some k =>
        exfalso
        have h1 := hA.contract.opk_removed (by rw [hk]; rfl)
        rw [hu] at h1
        exact Bool.noConfusion h1
    exact cOpkRelC_of_exists (used := opkUsed) hA.ready.2.2 (fun _ => hu'.1)
      rpk_prefix_reachable (Or.inl (not_opkNamed_true_of_preKeyId_isNone hA.contract.parse hk))

end Symbolic.Swarm.CREF.CliPure
