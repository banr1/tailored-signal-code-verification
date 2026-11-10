/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnWire
section Msg1Wire
open ByteSpecs CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin
theorem encWire_of_matched_encSend {r : Records} {S : Sem} {g : Ghost} {tr₂ tr' : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wrap : Option (Nat × Nat)} {b : HwBytes} {p : PreKeyFields} {v : VisEntry} {M : List VisEntry} (hls : lastSent tr₂ tr' = some (encOut tr₂ stA cl pq)) (hv : encSend tr₂ tr' wrap = v :: M) (hE : EventMatchesEntry compI0 r S g (.send b) v) (hhead : b.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hlen : b.length < 2 ^ 63) (hp : parsePreKeyWire b = some p) : gamma compI0 S g (encWire tr₂ stA cl pq) = p.message.take (p.message.length - 8) := by
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
theorem encWire_msg1 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {p₁ : PreKeyFields} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hp₁ : parsePreKeyWire SP.schedBCall1SendBytes = some p₁) : gamma compI0 S g (encWire tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2)) = p₁.message.take (p₁.message.length - 8) := by
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
  rw [hv] at hS; exact encWire_of_matched_encSend hls₂ hv (forall₂_two_head hne₃ hS) schedB1_head schedB1_len hp₁
set_option maxRecDepth 200000 in
theorem schedB1Fast_msg_bounds :
    (parsePreKeyWire Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall1SendFast).map
      (fun p => decide (77 ≤ p.message.length ∧ p.message.length ≤ 1408)) = some true := by decide +kernel
theorem schedB1_msg_bounds {p : PreKeyFields} (hp : parsePreKeyWire SP.schedBCall1SendBytes = some p) : 77 ≤ p.message.length ∧ p.message.length ≤ 1408 := by
  have h := schedB1Fast_msg_bounds; unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall1SendFast at h; rw [← SP.schedBCall1SendBytes_eq, hp] at h; exact of_decide_eq_true (Option.some.inj h)
set_option maxRecDepth 200000 in
theorem wire3Fast_msg_bounds :
    (parsePreKeyWire WsIdx1Split40OwnSalt.wire3Idx1Fast).map
      (fun p => decide (77 ≤ p.message.length ∧ p.message.length ≤ 1408)) = some true := by decide +kernel
theorem wire3_msg_bounds {p : PreKeyFields} (hp : parsePreKeyWire wire3Idx1Bytes = some p) : 77 ≤ p.message.length ∧ p.message.length ≤ 1408 := by
  have h := wire3Fast_msg_bounds; unfold WsIdx1Split40OwnSalt.wire3Idx1Fast at h; rw [← WsIdx1Split40OwnSalt.wire3Idx1Bytes_eq_fast, hp] at h; exact of_decide_eq_true (Option.some.inj h)
end Msg1Wire
section Run
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80 (sendAt)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop (ptAt)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem split40_wire_bounds {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) : 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length ∧ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length ≤ 1400 ∧ 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ∧ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ≤ 1400 := by
  obtain ⟨p₁, hp₁⟩ := WsIdx1Split40MemoCk1Pin.parse_b1; have hw₁ := encWire_msg1 hinv hp₁
  have hw₂ : gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) =
      p.message.take (p.message.length - 8) := (hinv.hwire₂ p hp).1
  have hb₁ := schedB1_msg_bounds hp₁; have hb₂ := wire3_msg_bounds hp; rw [hw₁, hw₂, List.length_take, List.length_take]; omega
end Run
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnWire
