/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.StepBranchOKPure
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.CBadReady
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptCollisionPickPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.Fail
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TRView

/-!
# Promote `Clean` Explanation Step Assembly

Assembles `PromExplainOK` (`prom_explainOK_of_rawKnBranches`) from `PromNoDrawOK`,
`PromRawCtxSupply`, and the three `PromRawKnBranchOK` obligations (`Skipped`, `NoRatchet`, and
`RatchetDH`).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSessionRepr
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement

private theorem promXpl_hmid_no_recv {mid : List MachineEvent}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32) :
    ∀ e ∈ mid, ∀ x, e ≠ .recv x := by
  rcases hmid with rfl | ⟨rb, rfl, -⟩ <;> simp

private theorem promXpl_hmid_filter_head {mid : List MachineEvent} {pt : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32) :
    ((mid ++ [MachineEvent.accept pt]).filter fun e => eventKind e != .rng).head? =
      some (.accept pt) := by
  rcases hmid with rfl | ⟨rb, rfl, -⟩ <;> rfl

private theorem promXpl_tag_ne_whisper {tag : BitVec 8} {body : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire (tag :: body) = some pf) :
    tag ≠ wireWhisperTag := by
  rintro rfl
  unfold parsePreKeyWire wireWhisperTag DY.Libsignal.PQXDH.Refinement.wirePrekeyTag at hpf
  simp at hpf

theorem promXpl_mid_cases_of_acceptCallBy₂
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt) :
    mid = [] ∨ ∃ d : HwBytes, mid = [.rng d] := by
  rcases hC.hmid with rfl | ⟨rb, rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨rb, rfl⟩

theorem promXpl_hbka_of_acceptCallBy₂
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf
      sess sess' coins expected pt)
    {g : Ghost} {ms : List Move}
    (hc : CleanBy interpretation r S who ok g ms acc) :
    ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms),
      ecKey (gamma interpretation S g ek) = pf.baseKey.take 33 := by
  have hbk_acc : pf.baseKey.take 33 ∈ e'.accepted :=
    prom_baseKey_in_accepted hC.entry hC.out.hpf
  obtain ⟨ek, hek, heq⟩ := ((hC.entry.ready.2.1.clean g ms hc).1).2.1.2.2.1 _ hbk_acc
  exact ⟨ek, hek, heq.symm⟩

theorem promXpl_knownBaseKey_of_acceptCallBy₂
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf
      sess sess' coins expected pt)
    {g : Ghost} {ms : List Move}
    (hc : CleanBy interpretation r S who ok g ms acc) :
    KnownBaseKey interpretation r S g ms pf := by
  obtain ⟨ek, hek, heq⟩ := promXpl_hbka_of_acceptCallBy₂ hC hc
  exact ⟨ek, hek, heq.symm⟩

private theorem promXpl_explains_pin_ok_end
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms : List Move} {acc : List MachineEvent}
    (hf : ExplainsMoves interpretation r S who ok g ms acc) :
    ExplainsMoves interpretation r S who
      (fun k => if k = (callStarts acc).length then true else ok k) g ms acc := by
  refine ⟨hf.1, fun i m hi => ?_⟩
  have hlt : i < ms.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hi
    cases hi
  have hcc_ms : callCount (runVis r ms) = (callStarts acc).length :=
    prom_callCount_of_forall₂ hf.1.2.2.2.2.2
  by_cases hk : callCount (runVis r (ms.take i)) = (callStarts acc).length
  · refine ⟨fun ds hrej => ?_, fun _ => by simp only [hk, ↓reduceIte]⟩
    subst hrej
    have hsplit : ms = ms.take i ++ Move.reject ds :: ms.drop (i + 1) := by
      conv_lhs => rw [← List.take_append_drop i ms, ← List.cons_getElem_drop_succ (h := hlt)]
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hi
      rw [hi]
    have hvis : runVis r ms =
        runVis r (ms.take i) ++
          (runMoves (Move.reject ds :: ms.drop (i + 1)) (runTraceMoves r (ms.take i))).2 := by
      conv_lhs => rw [hsplit]
      exact runVis_append r (ms.take i) _
    have hcc_pos : 1 ≤
        callCount (runMoves (Move.reject ds :: ms.drop (i + 1)) (runTraceMoves r (ms.take i))).2 := by
      rw [runMoves_cons_snd, callCount_append]
      have h1 : 1 ≤ callCount ((Move.reject ds).vis (runTraceMoves r (ms.take i))) := by
        simp [Move.vis, callCount]
      omega
    have htot := congrArg callCount hvis
    rw [callCount_append, hcc_ms, hk] at htot
    omega
  · obtain ⟨h1, h2⟩ := hf.2 i m hi
    refine ⟨fun ds hrej => ?_, fun hal => ?_⟩
    · simp only [hk, ↓reduceIte]; exact h1 ds hrej
    · simp only [hk, ↓reduceIte]; exact h2 hal

theorem prom_decSel_cases_of_noDraw
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hNoDraw : PromNoDrawOK interpretation r S who ok) :
    PromDecSelCases interpretation r S who ok :=
  fun j e' _mid acc rec b sm pf sess sess' coins expected pt hC =>
    prom_decSel_cases_out hC.out fun hnil =>
      hNoDraw j e' acc rec b sm pf sess sess' coins expected pt (hnil ▸ hC)

/-- Raw-decrypt and attacker-known-salt witness tuple consumed by `cBadG2_of_rawWitness` and
`explains_append_decrypt_step`. -/
def PromXplRawKnWitness (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (acc mid : List MachineEvent)
    (p : Participant) (tag : BitVec 8) (body b pt : HwBytes) : Prop :=
  ∃ (g₁ : Ghost) (stateIdx : Nat) (spqrMsgIdx : UInt32) (pqSalt t_m : DY.Bytes) (m : Move),
    CBadSigmaFrame g g₁ (runTraceMoves r ms).length ∧
    t_m ∈ recvRepresentations interpretation r S g ms b ∧
    pqSalt.AttackerKnows (runTraceMoves r ms) ∧
    DY.Libsignal.TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
    (m = Move.decrypt p stateIdx ((runTraceMoves r ms).length + 1) (runTraceMoves r ms).length
          spqrMsgIdx (decide (tag ≠ wireWhisperTag)) ∨
      ∃ skIdx, m = Move.decryptSkipped p stateIdx ((runTraceMoves r ms).length + 1) skIdx
        (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag))) ∧
    RawDecryptMatched interpretation r S g₁
      (ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m]))
      (acc ++ .recv (tag :: body) :: (mid ++ [.accept pt]))

/-- Produces `CBadG2Hyp` when `ok j = true` from `PromXplRawKnWitness` via `cBadG2_of_rawWitness`. -/
theorem promXpl_cBadG2_of_acceptCallBy₂_of_rawKn
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf
      sess sess' coins expected pt)
    (hok : ok j = true)
    (hw : ∀ g ms t',
      CleanBy interpretation r S who ok g ms acc →
      t' ∈ recvRepresentations interpretation r S g ms pf.message →
      ¬ RecvCollision interpretation r S g ms t' →
      RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) pf.message t' →
      PromXplRawKnWitness interpretation r S g ms acc mid r.bob tag body pf.message pt) :
    CBadG2Hyp interpretation r S who ok acc mid pt tag body pf.message := by
  have hwho_cs : who[(callStarts acc).length]? = some r.bob := by rw [hC.hj]; exact hC.entry.who_at
  have hok_cs : ok (callStarts acc).length = true := by rw [hC.hj]; exact hok
  have htag : tag ≠ wireWhisperTag := promXpl_tag_ne_whisper hC.out.hpf
  have hmid : mid = [] ∨ ∃ d : HwBytes, mid = [.rng d] := promXpl_mid_cases_of_acceptCallBy₂ hC
  intro _hmid_nr g ms t' hc ht' hncol hEF
  obtain ⟨g₁, _stateIdx, _spqrMsgIdx, pqSalt, t_m, m, hfr, ht_m, hpq_kn, _hcur, hm, hraw⟩ :=
    hw g ms t' hc ht' hncol hEF
  have hc₁ := cbadG2_cleanBy_transfer hfr hc
  obtain ⟨g₂, hfr₂, hc₂, hbr⟩ := cBadG2_of_rawWitness hc hEF.2 hfr ht_m hpq_kn hwho_cs hok_cs
    hm hmid (Or.inr ⟨htag, pf, hC.out.hpf, rfl, promXpl_hbka_of_acceptCallBy₂ hC hc₁⟩) hraw
  exact ⟨g₂, hfr₂.1, hc₂, hbr⟩

/-- Produces a `MatchedPrefix` on `acc ++ promAccBlk (tag :: body) mid pt` from
`PromXplRawKnWitness`. -/
theorem promXpl_matchedPrefix_of_acceptCallBy₂_of_rawKn
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf
      sess sess' coins expected pt)
    (hncol : ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk (tag :: body) mid pt))
    (hw : ∀ g ms t',
      CleanBy interpretation r S who ok g ms acc →
      t' ∈ recvRepresentations interpretation r S g ms pf.message →
      ¬ RecvCollision interpretation r S g ms t' →
      RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) pf.message t' →
      PromXplRawKnWitness interpretation r S g ms acc mid r.bob tag body pf.message pt) :
    ∃ g ms, MatchedPrefix interpretation r S who g ms (acc ++ promAccBlk (tag :: body) mid pt) := by
  obtain ⟨g₀, ms₀, hc₀⟩ := hC.entry.ready.1
  obtain ⟨t₀, ht₀⟩ :=
    prom_recvRepresentations_nonempty_of_parsePreKeyWire interpretation r S g₀ ms₀ hC.out.hpf
  rcases cBadStep_promote_before_c13 interpretation hc₀ ht₀
      (promXpl_hmid_filter_head hC.hmid) hC.out.hpf
      (promXpl_knownBaseKey_of_acceptCallBy₂ hC hc₀) with
    ⟨g', ms', t', hc', ht', hnc', hEF'⟩ | hcol
  · obtain ⟨g₁, _stateIdx, _spqrMsgIdx, pqSalt, t_m, m, hfr, ht_m, _hpq_kn, _hcur, hm, hraw⟩ :=
      hw g' ms' t' hc' ht' hnc' hEF'
    have hc₁ := cbadG2_cleanBy_transfer hfr hc'
    have ht₁ := cbadG2_recvRep_of_sigmaFrame hfr hc'.matched ht_m
    have hwho_cs : who[(callStarts acc).length]? = some r.bob := by rw [hC.hj]; exact hC.entry.who_at
    have htag : tag ≠ wireWhisperTag := promXpl_tag_ne_whisper hC.out.hpf
    have hmid : mid = [] ∨ ∃ d : HwBytes, mid = [.rng d] := promXpl_mid_cases_of_acceptCallBy₂ hC
    have hok_pin : (fun k => if k = (callStarts acc).length then true else ok k)
        (callStarts acc).length = true := by simp only [↓reduceIte]
    have hExpl := explains_append_decrypt_step
      (promXpl_explains_pin_ok_end hc₁.explains) ht₁ hwho_cs hok_pin hm hmid
      (Or.inr ⟨htag, pf, hC.out.hpf, rfl, promXpl_hbka_of_acceptCallBy₂ hC hc₁⟩) hraw
    exact ⟨g₁, ms' ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m]), hExpl.1⟩
  · exact False.elim (hncol hcol)

/-- Proves `PromExplainOK` from a `PromXplRawKnWitness` provider. -/
theorem promXpl_explainOK_of_rawKn
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hRawKn : ∀ j e' mid acc rec tag body sm pf sess sess' coins expected pt,
      PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf
        sess sess' coins expected pt →
      ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk (tag :: body) mid pt) →
      ∀ g ms t',
        CleanBy interpretation r S who ok g ms acc →
        t' ∈ recvRepresentations interpretation r S g ms pf.message →
        ¬ RecvCollision interpretation r S g ms t' →
        RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) pf.message t' →
        PromXplRawKnWitness interpretation r S g ms acc mid r.bob tag body pf.message pt) :
    PromExplainOK interpretation r S who ok := by
  intro j e' mid acc rec b sm pf sess sess' coins expected pt hC hncol
  cases b with
  | nil => cases hC.out.hpf
  | cons tag body =>
    have hw := hRawKn j e' mid acc rec tag body sm pf sess sess' coins expected pt hC hncol
    refine ⟨promXpl_matchedPrefix_of_acceptCallBy₂_of_rawKn hC hncol hw, fun hok => ?_⟩
    obtain ⟨g₀, ms₀, hc₀⟩ := hC.entry.ready.1
    obtain ⟨t₀, ht₀⟩ :=
      prom_recvRepresentations_nonempty_of_parsePreKeyWire interpretation r S g₀ ms₀ hC.out.hpf
    rcases cBadStep_promote_c13 interpretation hc₀ ht₀
        (promXpl_hmid_no_recv hC.hmid)
        (promXpl_hmid_filter_head hC.hmid)
        hC.out.hpf
        (promXpl_knownBaseKey_of_acceptCallBy₂ hC hc₀)
        (promXpl_cBadG2_of_acceptCallBy₂_of_rawKn hC hok hw) with
      ⟨g_c, ms_c, hc_c⟩ | hcol
    · exact ⟨g_c, ms_c, hc_c⟩
    · exact False.elim (hncol hcol)

/-- Proves `PromExplainOK` from `PromNoDrawOK`, `PromRawCtxSupply`, and the three
`PromRawKnBranchOK` obligations (`Skipped`, `NoRatchet`, and `RatchetDH`). -/
theorem prom_explainOK_of_rawKnBranches
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hNoDraw : PromNoDrawOK interpretation r S who ok)
    (hCtx : PromRawCtxSupply interpretation r S who ok)
    (hSk : PromRawKnBranchOK interpretation r S who ok PromDecSelSkipped)
    (hNR : PromRawKnBranchOK interpretation r S who ok PromDecSelNoRatchet)
    (hDH : PromRawKnBranchOK interpretation r S who ok PromDecSelRatchetDH) :
    PromExplainOK interpretation r S who ok :=
  promXpl_explainOK_of_rawKn
    (prom_hRawKn_of_rawKnBranches (prom_decSel_cases_of_noDraw hNoDraw) hCtx hSk hNR hDH)

end Symbolic.Swarm.CREF.CliPure
