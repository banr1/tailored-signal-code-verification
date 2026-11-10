/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPinRun
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PreKeyRep
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin
namespace SP
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins (schedBCall1SendBytes schedBCall2SendBytes schedBCall1SendBytes_eq wireMacChainOk wireMacChainOk_b1 saltAndSeedPin_s1_1 wsSaltA msgMac8 schedBCall1Send_head_eq schedBCall2Send_head_eq eventBytes_send)
end SP
open ByteSpecs CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPinRun
def sendsE (τ : List MachineEvent) : List MachineEvent := τ.filter fun e => decide (eventKind e = .send)
def sendsV (L : List VisEntry) : List VisEntry := L.filter fun v => decide (v.kind = .send)
theorem forall₂_filter_send {R : MachineEvent → VisEntry → Prop}
    (hk : ∀ e v, R e v → v.kind = eventKind e) :
    ∀ {τ : List MachineEvent} {L : List VisEntry}, List.Forall₂ R τ L → List.Forall₂ R (sendsE τ) (sendsV L)
  | [], [], .nil => .nil
  | e :: _, v :: _, .cons h t => by
    have ih := forall₂_filter_send hk t
    unfold sendsE sendsV at ih ⊢
    simp only [List.filter_cons, hk e v h]; split <;> [exact .cons h ih; exact ih]
theorem forall₂_two_head {α β : Type} {R : α → β → Prop} {a₁ a₂ : α} {A M X C Rst : List β} {b : β} (hC : C ≠ []) (h : List.Forall₂ R [a₁, a₂] (A ++ ((b :: M) ++ X) ++ (C ++ Rst))) : R a₁ b := by
  have hlen := h.length_eq; have hCpos := List.length_pos_of_ne_nil hC; simp only [List.length_cons, List.length_nil, List.length_append] at hlen
  have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hA; simp only [List.nil_append, List.cons_append] at h; exact (List.forall₂_cons.1 h).1
open Symbolic.Swarm.CREF in
theorem runVis_split (r : Records) {ms : List Move} {k : Nat} {m : Move} (hms : ms[k]? = some m) : runVis r ms = runVis r (ms.take k) ++ (m.vis (runTraceMoves r (ms.take k)) ++ (runMoves (ms.drop (k + 1)) (m.next (runTraceMoves r (ms.take k)))).2) := by
  obtain ⟨hlt, hm⟩ := List.getElem?_eq_some_iff.1 hms
  have hsplit : ms = ms.take k ++ m :: ms.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k ms, List.drop_eq_getElem_cons hlt, hm]
  conv_lhs => rw [hsplit]
  change (runMoves (r.setupMove :: (ms.take k ++ m :: ms.drop (k + 1))) Trace.nil).2 = _
  rw [← List.cons_append, CompPrefixInvStruct.runMoves_append_snd]; rfl
section EncVis
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem sendsV_encrypt_vis (tr : ExecTrace) (me : Participant) (sIdx cl pq : Nat) (wrap : Option (Nat × Nat)) : sendsV ((Move.encrypt me sIdx cl pq wrap).vis tr) = encSend tr ((Move.encrypt me sIdx cl pq wrap).next tr) wrap := by
  have hex : exposures tr ((Move.encrypt me sIdx cl pq wrap).next tr) = [] :=
    exposures_nil_of_not_leakKind rfl (fun h => nomatch h)
  have hvis : (Move.encrypt me sIdx cl pq wrap).vis tr =
      encVis tr ((Move.encrypt me sIdx cl pq wrap).next tr) wrap true := by
    rw [xpl_vis_eq, hex, List.append_nil]; rfl
  rw [hvis]; unfold sendsV encVis; rw [List.filter_append]
  have hd : (encDraws (newRandoms tr ((Move.encrypt me sIdx cl pq wrap).next tr))).filter
      (fun v => decide (v.kind = .send)) = [] := by
    rw [List.filter_eq_nil_iff]; intro v hv; rcases encDraws_kind _ hv with hk | hk <;> simp [hk]
  simp only [hd, List.nil_append, ↓reduceIte]; unfold encSend; split <;> [split <;> rfl; rfl]
theorem lastSent_encNextTr' (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : lastSent tr₂ (encNextTr tr₂ me sIdx stA cl pq) = some (encOut tr₂ stA cl pq) := CompPrefixInvEnc.lastSent_encNextTr tr₂ me sIdx stA cl pq
end EncVis
theorem sendsV_append (A B : List VisEntry) : sendsV (A ++ B) = sendsV A ++ sendsV B := List.filter_append ..
theorem sendsE_append (A B : List MachineEvent) : sendsE (A ++ B) = sendsE A ++ sendsE B := List.filter_append ..
theorem sendsE_map_rng (ps : List HwBytes) : sendsE (ps.map MachineEvent.rng) = [] := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => exact ih
theorem sendsE_coinSplit : ∀ {σ τ : List MachineEvent},
    DY.Libsignal.Composed.Refinement.Cli.CoinSplit σ τ → sendsE τ = sendsE σ
  | _, _, .nil => rfl
  | e :: _, _, .keep _ hrest => by
    unfold sendsE
    simp only [List.filter_cons]
    split <;> [exact congrArg (e :: ·) (sendsE_coinSplit hrest); exact sendsE_coinSplit hrest]
  | .rng _ :: tail, _, .split _ _ hrest => by
    rw [sendsE_append, sendsE_map_rng, List.nil_append]
    change _ = sendsE tail
    exact sendsE_coinSplit hrest
theorem encSend_ne_nil {tr tr' : ExecTrace} {o : DY.Bytes} (wrap : Option (Nat × Nat)) (hls : lastSent tr tr' = some o) : encSend tr tr' wrap ≠ [] := by unfold encSend; rw [hls]; cases wrap <;> simp
attribute [local irreducible] Symbolic.BugInjection.hexBytes in theorem sendsE_take40 : sendsE (wsIdx1Trace.take 40) = [.send SP.schedBCall1SendBytes, .send SP.schedBCall2SendBytes] := by unfold SP.schedBCall1SendBytes SP.schedBCall2SendBytes; rw [SP.schedBCall1Send_head_eq, SP.schedBCall2Send_head_eq, SP.eventBytes_send, SP.eventBytes_send]; rfl
theorem take40_split_eq :
    wsIdx1Trace.take 40 =
      (wsIdx1Trace.take 35 ++ (wsIdx1Trace.drop 35 |>.take 3)) ++ (wsIdx1Trace.drop 38 |>.take 2) := rfl
theorem sendsE_seg38SplitSrc_eq : sendsE seg38SplitSrc = sendsE (wsIdx1Trace.drop 38 |>.take 2) := rfl
theorem sendsE_take40_split {b1 b2 : List MachineEvent}
    (hcs1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 35 |>.take 3) b1)
    (hcs2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc b2) :
    sendsE ((wsIdx1Trace.take 35 ++ b1) ++ b2) =
      [.send SP.schedBCall1SendBytes, .send SP.schedBCall2SendBytes] := by
  rw [← sendsE_take40, take40_split_eq]
  simp only [sendsE_append, sendsE_coinSplit hcs1, sendsE_coinSplit hcs2, sendsE_seg38SplitSrc_eq]
set_option maxRecDepth 200000 in theorem schedB1_head : SP.schedBCall1SendBytes.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by rw [SP.schedBCall1SendBytes_eq]; decide +kernel
set_option maxRecDepth 200000 in theorem schedB1_len : SP.schedBCall1SendBytes.length < 2 ^ 63 := by rw [SP.schedBCall1SendBytes_eq]; decide +kernel
theorem parse_of_wireMacChainOk {k P w : HwBytes} (h : SP.wireMacChainOk k P w = true) : ∃ p, parsePreKeyWire w = some p := by
  unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.wireMacChainOk at h
  split at h <;> [exact ⟨_, ‹_›⟩; cases h]
theorem parse_b1 : ∃ p, parsePreKeyWire SP.schedBCall1SendBytes = some p := parse_of_wireMacChainOk SP.wireMacChainOk_b1
theorem wsSaltA_eq : SP.wsSaltA = WsIdx1O4Tag.wsSalt1 := by decide
theorem encMac_of_matched_encSend {r : Records} {S : Sem} {g : Ghost} {tr₂ tr' : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wrap : Option (Nat × Nat)} {b : HwBytes} {p : PreKeyFields} {v : VisEntry} {M : List VisEntry} (hls : lastSent tr₂ tr' = some (encOut tr₂ stA cl pq)) (hv : encSend tr₂ tr' wrap = v :: M) (hE : EventMatchesEntry compI0 r S g (.send b) v) (hhead : b.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hlen : b.length < 2 ^ 63) (hp : parsePreKeyWire b = some p) : gamma compI0 S g (encMac tr₂ stA cl pq) = SP.msgMac8 p := by
  unfold encSend at hv; rw [hls] at hv
  rcases wrap with _ | ⟨e, c⟩ <;> injection hv with hv _ <;> subst hv
  · obtain ⟨_, t, _, hb⟩ := hE; change b = _ at hb; rw [hb] at hhead; exact absurd rfl hhead
  · obtain ⟨_, _, _, _, _, hmsg⟩ := WsIdx1PreKeyRep.sendMatches_append_inv hE.2 hlen hp
    have hsplit : gamma compI0 S g (encWire tr₂ stA cl pq) ++ gamma compI0 S g (encMac tr₂ stA cl pq) = p.message := by rw [hmsg]; exact (CompFreshDistinct.gamma_concat_eq compI0 S g _ _).symm
    have hmac_len := WsIdx1PreKeyRep.gamma_encMac_length compI0 S g tr₂ stA cl pq
    have hlen' : p.message.length - 8 = (gamma compI0 S g (encWire tr₂ stA cl pq)).length := by rw [← hsplit, List.length_append, hmac_len]; omega
    show _ = p.message.drop (p.message.length - 8); rw [hlen', ← hsplit, List.drop_left]
theorem encMac_msg1 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {p₁ : PreKeyFields} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hp₁ : parsePreKeyWire SP.schedBCall1SendBytes = some p₁) : gamma compI0 S g (encMac tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2)) = SP.msgMac8 p₁ := by
  obtain ⟨k₁, k₂, k₃, hb₁, sh₁, s₁, s₂, pq₁, pq₂, w₁, w₂, _hk₁₂, hk₂₃, _htr₁, _hms₁, htr₂, hms₂,
    htr₃, hms₃, _hnext₁, _hpq₁, _hpq₂, hnext₂, hnext₃⟩ := hinv.links
  obtain ⟨b1, b2, hcs1, hcs2, hmp⟩ := hinv.mp.2.2.2.2.2
  have hF := hmp.2.2.2.2.2
  have hms₂' : (ms'.take k₃)[k₂]? = some (.encrypt r.alice s₁ cl₁ pq₁ w₁) := by
    rw [List.getElem?_take_of_lt hk₂₃]; exact hms₂
  have htt : (ms'.take k₃).take k₂ = ms'.take k₂ := by rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk₂₃)]
  rw [runVis_split r hms₃, runVis_split r hms₂', htt, htr₂, htr₃] at hF
  have hS := forall₂_filter_send (fun _ _ h => Symbolic.Swarm.CREF.xpl_kind_of_matches h) hF
  rw [sendsE_take40_split hcs1 hcs2] at hS; simp only [sendsV_append, sendsV_encrypt_vis] at hS; rw [hnext₂] at hS; have hls₂ := lastSent_encNextTr' tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2)
  have hne₃ : encSend tr₃ ((Move.encrypt r.alice s₂ cl₂ pq₂ w₂).next tr₃) w₂ ≠ [] := by rw [hnext₃]; exact encSend_ne_nil w₂ (lastSent_encNextTr' _ _ _ _ _ _)
  obtain ⟨v, M, hv⟩ : ∃ v M, encSend tr₂ (encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2)) w₁ = v :: M := by
    unfold encSend; rw [hls₂]; cases w₁ <;> exact ⟨_, _, rfl⟩
  rw [hv] at hS; exact encMac_of_matched_encSend hls₂ hv (forall₂_two_head hne₃ hS) schedB1_head schedB1_len hp₁
theorem split40Ck1Pin : Split40Ck1Pin := by intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ _hfits _hp hinv; obtain ⟨p₁, hp₁⟩ := parse_b1; obtain ⟨_, _, hSalt, _⟩ := SP.saltAndSeedPin_s1_1 S g tr₂ _ cl₁ (Or.inl hp₁) (encMac_msg1 hinv hp₁); rw [CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ r.bob _ cl₁] at hSalt; exact hSalt.trans wsSaltA_eq
theorem split40ZPins : Split40ZPins := split40ZPins_of split40Ck1Pin
theorem split40ZTagInj : Split40ZTagInj := split40ZTagInj_of_ck1 split40Ck1Pin
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin
