/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc
public import Symbolic.BugInjection.Proofs.Common443.CompPlant
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Mem

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
export Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT ( MemoPairCollides not_memoCollisionOn_of_no_pair_collides gamma_encMac_length gamma_encWire_mac_of_encOut Split38MemoClass
)
theorem forall2_append_inv {α β : Type} {R : α → β → Prop} : ∀ {l₁ l₂ : List α} {r₁ r₂ : List β}, l₁.length = r₁.length → List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂) → List.Forall₂ R l₁ r₁ ∧ List.Forall₂ R l₂ r₂
  | [], _, [], _, _, h => ⟨List.Forall₂.nil, h⟩
  | _ :: _, _, [], _, hlen, _ => by simp at hlen
  | [], _, _ :: _, _, hlen, _ => by simp at hlen
  | a :: l₁, l₂, b :: r₁, r₂, hlen, List.Forall₂.cons hab hrest => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen; obtain ⟨h1, h2⟩ := forall2_append_inv hlen hrest; exact ⟨List.Forall₂.cons hab h1, h2⟩
theorem encVis_encNextTr_length_le_three (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (wrap : Option (Nat × Nat)) : (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) wrap true).length ≤ 3 := by
  unfold encVis encDraws encSend; rw [CompPrefixInvFresh.newRandoms_encNextTr, lastSent_encNextTr]
  cases wrap <;> by_cases hcl : (cl != 0) = true <;> simp [hcl]
theorem split38_forall2_vis_inv {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) {bun b₀ pt c w : HwBytes} {rs' : List MachineEvent} (hrs' : rs'.length = 33) (hvis : List.Forall₂ (EventMatchesEntry i r S g) ((.recv bun :: .rng b₀ :: rs') ++ [.pt pt, .rng c, .send w]) (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post))) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: .rng b₀ :: rs') (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb) ∧ List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w]
      (encVis tr₂ (encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2)) (some (e, c')) true) := by
  let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')); change List.Forall₂ (EventMatchesEntry i r S g) ((.recv bun :: .rng b₀ :: rs') ++ [.pt pt, .rng c, .send w]) (runVis r (pre ++ m₀ :: mid ++ m₁ :: post)) at hvis
  have henc : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) := (by subst ho; exact encrypt_next_split38_eq (some (e, c')) hm₀ hmid rfl)
  have halice : m₀.vis tr₁ = (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).take shown := by rw [aliceStart_vis_eq, hm₀]
  rw [runVis_split38_eq hNe hpre hmid hpost, halice, encrypt_vis_eq, henc] at hvis
  have halice_len : (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).length = 35 := by rw [aliceVis_iniAliceStartTr]; simp [kyberCoinEntries]
  have htake_le : ((aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).take shown).length ≤ 35 := (by rw [List.length_take, halice_len]; exact Nat.min_le_right shown 35); have henc_le : (encVis tr₂ (encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2)) (some (e, c')) true).length ≤ 3 := encVis_encNextTr_length_le_three tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) (some (e, c')); have htot := hvis.length_eq; rw [List.length_append, List.length_append] at htot
  have hlhs_len : (.recv bun :: .rng b₀ :: rs' : List MachineEvent).length = 35 := by simp [hrs']
  have hrhs_len : ([.pt pt, .rng c, .send w] : List MachineEvent).length = 3 := rfl; rw [hlhs_len, hrhs_len] at htot; have htake_len : ((aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).take shown).length = 35 := (by dsimp only [tr₂, m₀, tr₁] at henc_le htake_le htot ⊢; omega)
  have hshown : 35 ≤ shown := by rw [List.length_take, halice_len] at htake_len; omega
  have htake_eq : (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).take shown = aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb :=
    List.take_of_length_le (by omega)
  rw [htake_eq] at hvis; exact forall2_append_inv (by rw [hlhs_len, halice_len]) hvis
open Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma (coinHeads)
open Symbolic.BugInjection.Proofs.Common443.CompRX0Mem (sendMatches_append_inv)
theorem aliceVis_dhs_coin {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {a b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {hb : DY.Libsignal.PQXDH.BundleHandles} {bun b₀ dhsBytes : HwBytes} {rs' : List MachineEvent} (hrs_len : rs'.length = 33) (hdhs : rs'.drop 32 = [.rng dhsBytes]) (hvis₀ : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: .rng b₀ :: rs') (aliceVis tr₁ (iniAliceStartTr tr₁ a b o) hb)) : [gamma i S g (randTerm tr₁.length 32)] = [b₀] ∧ List.Forall₂ (EventMatchesEntry i r S g) (rs'.take 32) (kyberCoinEntries (randTerm (tr₁.length + 1) 32)) ∧ [gamma i S g (randTerm (tr₁.length + 2) 32)] = [dhsBytes] := by
  rw [aliceVis_iniAliceStartTr] at hvis₀; obtain ⟨_, hvis₁⟩ := List.forall₂_cons.mp hvis₀; obtain ⟨hek, hcoins⟩ := List.forall₂_cons.mp hvis₁
  have hrs_split : rs' = rs'.take 32 ++ [.rng dhsBytes] := by rw [← hdhs, List.take_append_drop]
  rw [hrs_split] at hcoins
  have hlen32 : (rs'.take 32).length = (kyberCoinEntries (randTerm (tr₁.length + 1) 32)).length := by simp [kyberCoinEntries, hrs_len]
  obtain ⟨hcoins_take, hdhs_vis⟩ := forall2_append_inv hlen32 hcoins; obtain ⟨hmatch, _⟩ := List.forall₂_cons.mp hdhs_vis; exact ⟨hek.2, hcoins_take, hmatch.2⟩
theorem encVis_split38_pins {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c' : Nat} {pt c w : HwBytes} {q₀ : PreKeyFields} (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀) (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some (e, c')) true)) : cl ≠ 0 ∧ [gamma i S g (randTerm tr₂.length 32)] = [pt] ∧ [gamma i S g (randTerm (tr₂.length + 1) cl)] = [c] ∧ gamma i S g (encOut tr₂ stA cl pq) = q₀.message := by
  have hsm := CompRX0Decomp.sendMatches_of_encVis (lastSent_encNextTr tr₂ me sIdx stA cl pq) hm₁; obtain ⟨_, _, _, _, _, hmsg⟩ := sendMatches_append_inv hsm hlen hq₀; unfold encVis encDraws encSend at hm₁; rw [CompPrefixInvFresh.newRandoms_encNextTr, lastSent_encNextTr] at hm₁
  by_cases hcl : (cl != 0) = true
  · simp only [List.filter_cons, hcl, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hm₁; obtain ⟨hpt, hm₂⟩ := List.forall₂_cons.mp hm₁; obtain ⟨hc, _⟩ := List.forall₂_cons.mp hm₂; exact ⟨bne_iff_ne.mp hcl, hpt.2, hc.2, hmsg.symm⟩
  · have hcl' : (cl != 0) = false := Bool.eq_false_iff.mpr hcl; have hlen_eq := hm₁.length_eq; simp [hcl'] at hlen_eq
theorem single_eq_inv {α : Type _} {x y : α} (h : [x] = [y]) : x = y := (List.cons.inj h).1
end Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire
