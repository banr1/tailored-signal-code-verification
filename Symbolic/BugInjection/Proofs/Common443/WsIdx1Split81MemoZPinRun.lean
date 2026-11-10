/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPin
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PreKeyRep
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun
namespace SP
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins (schedBCall1SendBytes schedBCall2SendBytes schedBCall5SendBytes schedBCall1SendBytes_eq schedBCall2SendBytes_eq schedBCall5SendBytes_eq schedBCall1Send_head_eq schedBCall2Send_head_eq schedBCall5Send_head_eq wireMacChainOk wireMacChainOk_b1 wireMacChainOk_b2 wireMacChainOk_b5 saltAndSeedPin_s1_1 saltAndSeedPin_s1_2 saltAndSeedPin_s2_1 wsSaltA wsSaltB wsSaltC msgMac8 eventBytes_send)
end SP
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4)
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPin
theorem forall₂_three_all {α β : Type} {R : α → β → Prop} {a₁ a₂ a₃ : α} {A₁ M₁ A₂ M₂ A₃ M₃ X₃ : List β} {b₁ b₂ b₃ : β} (h : List.Forall₂ R [a₁, a₂, a₃] ((A₁ ++ ((b₁ :: M₁) ++ A₂)) ++ ((b₂ :: M₂) ++ A₃) ++ ((b₃ :: M₃) ++ X₃))) : R a₁ b₁ ∧ R a₂ b₂ ∧ R a₃ b₃ := by
  have hlen := h.length_eq; simp only [List.length_cons, List.length_nil, List.length_append] at hlen
  rcases List.eq_nil_of_length_eq_zero (by omega : A₁.length = 0) with rfl
  rcases List.eq_nil_of_length_eq_zero (by omega : M₁.length = 0) with rfl
  rcases List.eq_nil_of_length_eq_zero (by omega : A₂.length = 0) with rfl
  rcases List.eq_nil_of_length_eq_zero (by omega : M₂.length = 0) with rfl
  rcases List.eq_nil_of_length_eq_zero (by omega : A₃.length = 0) with rfl
  rcases List.eq_nil_of_length_eq_zero (by omega : M₃.length = 0) with rfl
  rcases List.eq_nil_of_length_eq_zero (by omega : X₃.length = 0) with rfl
  simp only [List.nil_append, List.append_nil, List.cons_append] at h; obtain ⟨h1, h⟩ := List.forall₂_cons.1 h; obtain ⟨h2, h⟩ := List.forall₂_cons.1 h; exact ⟨h1, h2, (List.forall₂_cons.1 h).1⟩
theorem encWire_and_encMac_of_matched_encSend {r : Records} {S : Sem} {g : Ghost} {tr₂ tr' : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wrap : Option (Nat × Nat)} {b : HwBytes} {p : PreKeyFields} {v : VisEntry} {M : List VisEntry} (hls : lastSent tr₂ tr' = some (encOut tr₂ stA cl pq)) (hv : encSend tr₂ tr' wrap = v :: M) (hE : EventMatchesEntry compI0 r S g (.send b) v) (hhead : b.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hlen : b.length < 2 ^ 63) (hp : parsePreKeyWire b = some p) : gamma compI0 S g (encWire tr₂ stA cl pq) = p.message.take (p.message.length - 8) ∧ gamma compI0 S g (encMac tr₂ stA cl pq) = SP.msgMac8 p := by
  refine ⟨?_, encMac_of_matched_encSend hls hv hE hhead hlen hp⟩
  unfold encSend at hv; rw [hls] at hv
  rcases wrap with _ | ⟨e, c⟩
  · injection hv with hv _; subst hv; obtain ⟨_, t, _, hb⟩ := hE
    change b = _ at hb; rw [hb] at hhead; exact absurd rfl hhead
  · injection hv with hv _; subst hv
    obtain ⟨_, _, _, _, _, hmsg⟩ := WsIdx1PreKeyRep.sendMatches_append_inv hE.2 hlen hp
    have hsplit : gamma compI0 S g (encWire tr₂ stA cl pq) ++ gamma compI0 S g (encMac tr₂ stA cl pq) = p.message := by rw [hmsg]; exact (CompFreshDistinct.gamma_concat_eq compI0 S g _ _).symm
    have hmac_len := WsIdx1PreKeyRep.gamma_encMac_length compI0 S g tr₂ stA cl pq
    have hlen' : p.message.length - 8 = (gamma compI0 S g (encWire tr₂ stA cl pq)).length := by rw [← hsplit, List.length_append, hmac_len]; omega
    rw [hlen', ← hsplit, List.take_left]
attribute [local irreducible] Symbolic.BugInjection.hexBytes in theorem sendsE_take81 : sendsE (wsIdx1Trace.take 81) = [.send SP.schedBCall1SendBytes, .send SP.schedBCall2SendBytes, .send SP.schedBCall5SendBytes] := by unfold SP.schedBCall1SendBytes SP.schedBCall2SendBytes SP.schedBCall5SendBytes; rw [SP.schedBCall1Send_head_eq, SP.schedBCall2Send_head_eq, SP.schedBCall5Send_head_eq, SP.eventBytes_send, SP.eventBytes_send, SP.eventBytes_send]; rfl
theorem take81_split_eq :
    wsIdx1Trace.take 81 =
      (((((wsIdx1Trace.take 35 ++ (wsIdx1Trace.drop 35 |>.take 3)) ++ (wsIdx1Trace.drop 38 |>.take 2)) ++
        (wsIdx1Trace.drop 40 |>.take 3)) ++ (wsIdx1Trace.drop 43 |>.take 35)) ++
        (wsIdx1Trace.drop 78 |>.take 3)) := rfl
theorem sendsE_take81_split {b1 b2 b5 : List MachineEvent}
    (hcs1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 35 |>.take 3) b1)
    (hcs2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc b2)
    (hcs5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 78 |>.take 3) b5) :
    sendsE (((((wsIdx1Trace.take 35 ++ b1) ++ b2) ++
      (wsIdx1Trace.drop 40 |>.take 3)) ++ (wsIdx1Trace.drop 43 |>.take 35)) ++ b5) =
      [.send SP.schedBCall1SendBytes, .send SP.schedBCall2SendBytes, .send SP.schedBCall5SendBytes] := by
  rw [← sendsE_take81, take81_split_eq]
  simp only [sendsE_append, sendsE_coinSplit hcs1, sendsE_coinSplit hcs2, sendsE_seg38SplitSrc_eq, sendsE_coinSplit hcs5]
set_option maxRecDepth 200000 in theorem schedB2_head : SP.schedBCall2SendBytes.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by rw [SP.schedBCall2SendBytes_eq]; decide +kernel
set_option maxRecDepth 200000 in theorem schedB2_len : SP.schedBCall2SendBytes.length < 2 ^ 63 := by rw [SP.schedBCall2SendBytes_eq]; decide +kernel
set_option maxRecDepth 200000 in theorem schedB5_head : SP.schedBCall5SendBytes.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by rw [SP.schedBCall5SendBytes_eq]; decide +kernel
set_option maxRecDepth 200000 in theorem schedB5_len : SP.schedBCall5SendBytes.length < 2 ^ 63 := by rw [SP.schedBCall5SendBytes_eq]; decide +kernel
theorem parse_b2 : ∃ p, parsePreKeyWire SP.schedBCall2SendBytes = some p := parse_of_wireMacChainOk SP.wireMacChainOk_b2
theorem parse_b5 : ∃ p, parsePreKeyWire SP.schedBCall5SendBytes = some p := parse_of_wireMacChainOk SP.wireMacChainOk_b5
theorem wsSaltB_eq : SP.wsSaltB = wsSalt2 := by decide
theorem wsSaltC_eq : SP.wsSaltC = wsSalt5 := by decide
abbrev stA₂81 (r : Records) (tr₄ : ExecTrace) : DY.Libsignal.TripleRatchet.TRState :=
  let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  iniAliceStartState tr₄ r.bob o₂
theorem encWire_and_encMac_msgs_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p₁ p₂ p₅ : PreKeyFields} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hp₁ : parsePreKeyWire SP.schedBCall1SendBytes = some p₁) (hp₂ : parsePreKeyWire SP.schedBCall2SendBytes = some p₂) (hp₅ : parsePreKeyWire SP.schedBCall5SendBytes = some p₅) : (gamma compI0 S g (encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2)) = p₁.message.take (p₁.message.length - 8) ∧ gamma compI0 S g (encMac tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2)) = SP.msgMac8 p₁) ∧ (gamma compI0 S g (encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) = p₂.message.take (p₂.message.length - 8) ∧ gamma compI0 S g (encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) = SP.msgMac8 p₂) ∧ (gamma compI0 S g (encWire tr₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2)) = p₅.message.take (p₅.message.length - 8) ∧ gamma compI0 S g (encMac tr₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2)) = SP.msgMac8 p₅) := by
  obtain ⟨k₁, k₂, k₃, k₄, k₅, hb₁, hb₄, sh₁, sh₄, s₁, s₂, s₅, pq₁, pq₂, pq₅, w₁, w₂, w₅, _hk₁₂, hk₂₃, hk₃₄, hk₄₅, _htr₁, _hms₁, htr₂, hms₂, htr₃, hms₃, _htr₄, _hms₄, htr₅, hms₅,
    _hnext₁, _hnext₄, rfl, rfl, rfl, hnext₂, hnext₃, hnext₅⟩ := hinv.links
  have hk₃₅ : k₃ < k₅ := Nat.lt_trans hk₃₄ hk₄₅
  obtain ⟨b1, b2, b5, hcs1, hcs2, hcs5, hmp⟩ := hinv.mp.2.2.2.2.2
  have hF := hmp.2.2.2.2.2
  have hms₃' : (ms'.take k₅)[k₃]? = some (.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂) := by
    rw [List.getElem?_take_of_lt hk₃₅]; exact hms₃
  have htt₃₅ : (ms'.take k₅).take k₃ = ms'.take k₃ := by rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk₃₅)]
  have hms₂' : (ms'.take k₃)[k₂]? = some (.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁) := by
    rw [List.getElem?_take_of_lt hk₂₃]; exact hms₂
  have htt₂₃ : (ms'.take k₃).take k₂ = ms'.take k₂ := by rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk₂₃)]
  rw [runVis_split r hms₅, runVis_split r hms₃', htt₃₅, runVis_split r hms₂', htt₂₃, htr₂, htr₃, htr₅] at hF
  have hS := forall₂_filter_send (fun _ _ h => Symbolic.Swarm.CREF.xpl_kind_of_matches h) hF
  rw [sendsE_take81_split hcs1 hcs2 hcs5] at hS; simp only [sendsV_append, sendsV_encrypt_vis] at hS
  change (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂ =
    encNextTr tr₂ r.alice s₁ (stA81 r tr₁) cl₁ (tr₂.length + 2) at hnext₂
  change (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃ =
    encNextTr tr₃ r.alice s₂ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2) at hnext₃
  change (Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₅).next tr₅ =
    encNextTr tr₅ r.alice s₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2) at hnext₅
  rw [hnext₂, hnext₃, hnext₅] at hS; have hls₂ := lastSent_encNextTr' tr₂ r.alice s₁ (stA81 r tr₁) cl₁ (tr₂.length + 2); have hls₃ := lastSent_encNextTr' tr₃ r.alice s₂ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2); have hls₅ := lastSent_encNextTr' tr₅ r.alice s₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2)
  obtain ⟨v₁, M₁, hv₁⟩ : ∃ v M, encSend tr₂ (encNextTr tr₂ r.alice s₁ (stA81 r tr₁) cl₁ (tr₂.length + 2)) w₁ = v :: M := by
    unfold encSend; rw [hls₂]; cases w₁ <;> exact ⟨_, _, rfl⟩
  obtain ⟨v₂, M₂, hv₂⟩ : ∃ v M, encSend tr₃ (encNextTr tr₃ r.alice s₂ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) w₂ = v :: M := by
    unfold encSend; rw [hls₃]; cases w₂ <;> exact ⟨_, _, rfl⟩
  obtain ⟨v₅, M₅, hv₅⟩ : ∃ v M, encSend tr₅ (encNextTr tr₅ r.alice s₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2)) w₅ = v :: M := by
    unfold encSend; rw [hls₅]; cases w₅ <;> exact ⟨_, _, rfl⟩
  rw [hv₁, hv₂, hv₅] at hS; obtain ⟨hE₁, hE₂, hE₅⟩ := forall₂_three_all hS; exact ⟨encWire_and_encMac_of_matched_encSend hls₂ hv₁ hE₁ schedB1_head schedB1_len hp₁, encWire_and_encMac_of_matched_encSend hls₃ hv₂ hE₂ schedB2_head schedB2_len hp₂, encWire_and_encMac_of_matched_encSend hls₅ hv₅ hE₅ schedB5_head schedB5_len hp₅⟩
theorem encMac_msg2_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p₂ : PreKeyFields} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hp₂ : parsePreKeyWire SP.schedBCall2SendBytes = some p₂) : gamma compI0 S g (encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) = SP.msgMac8 p₂ := by obtain ⟨p₁, hp₁⟩ := parse_b1; obtain ⟨p₅, hp₅⟩ := parse_b5; exact (encWire_and_encMac_msgs_81 hinv hp₁ hp₂ hp₅).2.1.2
theorem encMac_msg5_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p₅ : PreKeyFields} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hp₅ : parsePreKeyWire SP.schedBCall5SendBytes = some p₅) : gamma compI0 S g (encMac tr₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2)) = SP.msgMac8 p₅ := by obtain ⟨p₁, hp₁⟩ := parse_b1; obtain ⟨p₂, hp₂⟩ := parse_b2; exact (encWire_and_encMac_msgs_81 hinv hp₁ hp₂ hp₅).2.2.2
theorem split81ZPins : Split81ZPins := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ _hfits _hp hinv; obtain ⟨p₂, hp₂⟩ := parse_b2; obtain ⟨p₅, hp₅⟩ := parse_b5; obtain ⟨_, _, hSalt₂, _⟩ := SP.saltAndSeedPin_s1_2 S g tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ hp₂ (encMac_msg2_81 hinv hp₂); obtain ⟨_, _, hSalt₅, _⟩ := SP.saltAndSeedPin_s2_1 S g tr₅ _ cl₅ hp₅ (encMac_msg5_81 hinv hp₅); rw [CompRSchedBSalts.encSalt_self tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂] at hSalt₂
  rw [CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₄ tr₅ r.bob _ cl₅] at hSalt₅; exact ⟨hSalt₂.trans wsSaltB_eq, hSalt₅.trans wsSaltC_eq⟩
theorem split81ZTagInj : Split81ZTagInj := split81ZTagInj_of_pins split81ZPins
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun
