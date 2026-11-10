/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (SendMatchesMoves)
theorem sendMatches_of_encVis {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr tr' : ExecTrace} {e c' : Nat} {o : DY.Bytes} {pt c w : HwBytes} (hls : lastSent tr tr' = some o) (hm : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr tr' (some (e, c')) true)) : SendMatchesMoves i r S g w (received tr [e, c'] ++ [o]) := by
  have hmem : MachineEvent.send w ∈ ([.pt pt, .rng c, .send w] : List MachineEvent) := by simp
  obtain ⟨v, hv, hev⟩ := xpl_forall₂_mem_left hm (.send w) hmem; have hvk : v.kind = .send := xpl_kind_of_matches hev; unfold encVis at hv; simp only [↓reduceIte, List.mem_append] at hv
  rcases hv with hd | hsnd
  · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk] at hk; cases hk)
  · unfold encSend at hsnd; rw [hls, List.mem_singleton] at hsnd; subst hsnd; exact hev.2
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice in
theorem pia_x0_decomp_legacy {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} {pt c w : HwBytes} (hNe : r.alice ≠ r.bob) (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms ((.recv bun :: rs) ++ [.pt pt, .rng c, .send w])) (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) (hbun4 : bun[4]? ≠ some 1#8) (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) : ∃ (pre : List Move) (a : Participant) (idS : Nat) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) (mid : List Move) (cl e c' : Nat) (post : List Move) (ikA : DY.Bytes) (tr₁ tr₂ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (stA : DY.Libsignal.TripleRatchet.TRState), tr₁ = (runMoves pre (setupTrace r)).1 ∧ o = aliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none ∧ stA = aliceStartState tr₁ r.bob o ∧ tr₂ = (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁)).1 ∧ ms = pre ++ .aliceStart a r.bob idS 6 hb shown :: mid ++ .encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧ ((idS = 4 ∧ a = r.alice ∧ ikA = setupSecret r 0) ∨ (idS = 9 ∧ a = r.bob ∧ ikA = setupSecret r 1)) ∧ NetMsgAt o.ek (tr₁.length + 3) tr₂ ∧ NetMsgAt o.ct (tr₁.length + 4) tr₂ ∧ o.ek.AttackerKnows (runTraceMoves r ms) ∧ o.ct.AttackerKnows (runTraceMoves r ms) ∧ (encOut tr₂ stA cl (tr₂.length + 2)).AttackerKnows (runTraceMoves r ms) ∧ bobDoneBaseKeys (runTraceMoves r ms) = [] ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) hb) ∧ SendMatchesMoves compI0 r S g w (received tr₂ [e, c'] ++ [encOut tr₂ stA cl (tr₂.length + 2)]) ∧ (Move.aliceStart a r.bob idS 6 hb shown).next tr₁ = aliceStartTrOfOut tr₁ a r.bob o ∧ MovesFrom InvisibleNoEffect (setupTrace r) pre ∧ MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) mid ∧ MovesFrom InvisibleNoEffect ((Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post := by
  obtain ⟨pre, a, idS, hb, shown, mid, me, sIdx, cl, pq, wr, post, ikA, spkSig, pqpkSig, hms, hrest⟩ := matchedPrefix_ini_send_bundle_legacy hNe hnb hmp hrs_len hrs_kind hbun4 hw; dsimp only at hrest; obtain ⟨hpre, hmid, hpost, _hshown, _hopk, _hbun0, hdisj, _hspk, _hspkSig, _hpqpk, _hpqpkSig, _hcore, hm₀, hls, hvis₀, hvis₁⟩ := hrest
  rcases wr with ⟨e, c'⟩
  have hown : ownSaltsFrom (setupTrace r) ms = true := hmp.2.1.2.2.2.2.1; have hntr : NoTRState (runMoves pre (setupTrace r)).1 := noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre
  have hek₁ : NetMsgAt (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek ((runMoves pre (setupTrace r)).1.length + 3)
      ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) := by
    rw [hm₀]; exact netMsgAt_ek_iniAliceStartTr _ _ _ _
  have hct₁ : NetMsgAt (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct ((runMoves pre (setupTrace r)).1.length + 4)
      ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) := by
    rw [hm₀]; exact netMsgAt_ct_iniAliceStartTr _ _ _ _
  have hst₁ : ∀ j : Nat,
      (((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1).at? j : Option TRStEntry) =
      if j = (runMoves pre (setupTrace r)).1.length + 8 then
        some (TRStE a (aliceStartState (runMoves pre (setupTrace r)).1 r.bob (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)))
      else none := by
    rw [hm₀]; exact at?_trSt_iniAliceStartTr_of_noTRState hntr _ _ _
  obtain ⟨_hE1, hme, hsIdx, hpq, _hns, _hnext, hlastSent, hek₂, hct₂, _hekr, _hctr, _hencr, hekK, hctK, hencK, hnil⟩ := pia_enc_inv (stA := aliceStartState (runMoves pre (setupTrace r)).1 r.bob (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hms hpre hmid hpost hown hek₁ hct₁ hst₁ hls; have hsm := sendMatches_of_encVis hlastSent hvis₁; subst hme hsIdx hpq
  exact ⟨pre, me, idS, hb, shown, mid, cl, e, c', post, ikA, (runMoves pre (setupTrace r)).1,
    (runMoves mid ((Move.aliceStart me r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1,
    _, _, rfl, rfl, rfl, rfl, hms, hdisj, hek₂, hct₂, hekK, hctK, hencK, hnil, hvis₀, hsm, hm₀, hpre, hmid, hpost⟩
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice in
theorem pia_x0_decomp {r : Records} {S : Sem} {who : List Participant} {g : Ghost} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} {pt c w : HwBytes} (hNe : r.alice ≠ r.bob) (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who g ms ((.recv bun :: rs) ++ [.pt pt, .rng c, .send w])) (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) (hbun4 : bun[4]? ≠ some 1#8) (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) : ∃ (pre : List Move) (a : Participant) (idS : Nat) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) (mid : List Move) (cl e c' : Nat) (post : List Move) (ikA : DY.Bytes) (tr₁ tr₂ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (stA : DY.Libsignal.TripleRatchet.TRState), tr₁ = (runMoves pre (setupTrace r)).1 ∧ o = aliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none ∧ stA = aliceStartState tr₁ r.bob o ∧ tr₂ = (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁)).1 ∧ ms = pre ++ .aliceStart a r.bob idS 6 hb shown :: mid ++ .encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧ ((idS = 4 ∧ a = r.alice ∧ ikA = setupSecret r 0) ∨ (idS = 9 ∧ a = r.bob ∧ ikA = setupSecret r 1)) ∧ NetMsgAt o.ek (tr₁.length + 3) tr₂ ∧ NetMsgAt o.ct (tr₁.length + 4) tr₂ ∧ o.ek.AttackerKnows (runTraceMoves r ms) ∧ o.ct.AttackerKnows (runTraceMoves r ms) ∧ (encOut tr₂ stA cl (tr₂.length + 2)).AttackerKnows (runTraceMoves r ms) ∧ bobDoneBaseKeys (runTraceMoves r ms) = [] ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) hb) ∧ SendMatchesMoves compI0 r S g w (received tr₂ [e, c'] ++ [encOut tr₂ stA cl (tr₂.length + 2)]) ∧ (Move.aliceStart a r.bob idS 6 hb shown).next tr₁ = aliceStartTrOfOut tr₁ a r.bob o ∧ MovesFrom InvisibleNoEffect (setupTrace r) pre ∧ MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) mid ∧ MovesFrom InvisibleNoEffect ((Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post := pia_x0_decomp_legacy hNe hnb (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp) hrs_len hrs_kind hbun4 hw
end Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp
