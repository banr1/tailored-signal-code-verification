/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81CoreAux
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Aux
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open DY.Libsignal (HwBytes) open CryptoProofLib.Refinement (ExternInterpretation)
theorem runMoves_cons_fst₀ (m : Move) (ms : List Move) (tr : ExecTrace) : (runMoves (m :: ms) tr).1 = (runMoves ms (m.next tr)).1 := rfl
theorem explains_swap3 {i : ExternInterpretation} {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {τ : List MachineEvent} {P₁ mid₂ P₂ post₅ : List Move} {me : Participant} {s₁ cl₁ pq₁ e₁ c₁ s₂ cl₂ pq₂ e₂ c₂ s₅ cl₅ pq₅ e₅ c₅ e₁' c₁' e₂' c₂' : Nat} {ek₁ ct₁ ek₂ ct₂ : DY.Bytes} (hek₁ : NetMsgAt ek₁ e₁' (runTraceMoves r P₁)) (hct₁ : NetMsgAt ct₁ c₁' (runTraceMoves r P₁)) (hγ₁ : (received (runTraceMoves r P₁) [e₁, c₁]).map (gamma i S g) = [gamma i S g ek₁, gamma i S g ct₁]) (hγ₂ : (received (runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂)) [e₂, c₂]).map (gamma i S g) = [gamma i S g ek₁, gamma i S g ct₁]) (hek₂ : NetMsgAt ek₂ e₂' (runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: P₂))) (hct₂ : NetMsgAt ct₂ c₂' (runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: P₂))) (hγ₅ : (received (runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: P₂)) [e₅, c₅]).map (gamma i S g) = [gamma i S g ek₂, gamma i S g ct₂]) (hex : ExplainsMoves i r S who ok g (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: P₂ ++ .encrypt me s₅ cl₅ pq₅ (some (e₅, c₅)) :: post₅) τ) : ExplainsMoves i r S who ok g (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁', c₁')) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₁', c₁')) :: P₂ ++ .encrypt me s₅ cl₅ pq₅ (some (e₂', c₂')) :: post₅) τ ∧ runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁', c₁')) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₁', c₁')) :: P₂ ++ .encrypt me s₅ cl₅ pq₅ (some (e₂', c₂')) :: post₅) = runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: P₂ ++ .encrypt me s₅ cl₅ pq₅ (some (e₅, c₅)) :: post₅) ∧ preKeyRepresentations i r S g (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁', c₁')) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₁', c₁')) :: P₂ ++ .encrypt me s₅ cl₅ pq₅ (some (e₂', c₂')) :: post₅) = preKeyRepresentations i r S g (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: P₂ ++ .encrypt me s₅ cl₅ pq₅ (some (e₅, c₅)) :: post₅) := by
  have hAssoc : ∀ (w₁ w₂ w₅ : Option (Nat × Nat)), P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅ = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: (P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅) := by intros; simp only [List.append_assoc, List.cons_append]
  rw [hAssoc] at hex; obtain ⟨hex₁₂, htr₁₂, hrep₁₂⟩ := WsIdx1Decomp40.explains_swap2 hek₁ hct₁ hγ₁ hγ₂ hex; rw [← hAssoc] at hex₁₂ htr₁₂ hrep₁₂; rw [← hAssoc (some (e₁, c₁))] at htr₁₂ hrep₁₂
  have htrP₂ : runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁', c₁')) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₁', c₁')) :: P₂) = runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ (some (e₂, c₂)) :: P₂) := by
    have htrP₁ : runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁', c₁')) :: mid₂) = runTraceMoves r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂) := by rw [WsIdx1DecompSwap.runTrace_append, WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, runMoves_cons_fst₀, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ (some (e₁', c₁')) (some (e₁, c₁))]
    rw [WsIdx1DecompSwap.runTrace_append r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁', c₁')) :: mid₂), WsIdx1DecompSwap.runTrace_append r (P₁ ++ .encrypt me s₁ cl₁ pq₁ (some (e₁, c₁)) :: mid₂), runMoves_cons_fst₀, runMoves_cons_fst₀, htrP₁, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ (some (e₁', c₁')) (some (e₂, c₂))]
  obtain ⟨hex₅, htr₅, hrep₅⟩ := WsIdx1DecompSwap.explains_swap_append (by rw [htrP₂]; exact hek₂)
    (by rw [htrP₂]; exact hct₂) (by rw [htrP₂]; exact hγ₅) hex₁₂
  exact ⟨hex₅, htr₅.trans htr₁₂, hrep₅.trans hrep₁₂⟩
theorem decryptNoop_split81 {r : Records} {pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move} {A₁ E₁ E₂ m₃ A₂ E₅ : Move} (hA₁ : A₁.decryptMsgIdx? = none) (hE₁ : E₁.decryptMsgIdx? = none) (hE₂ : E₂.decryptMsgIdx? = none) (hm₃ : m₃.decryptMsgIdx? = none) (hA₂ : A₂.decryptMsgIdx? = none) (hE₅ : E₅.decryptMsgIdx? = none) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect (A₁.next (runTraceMoves r pre₀)) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect (E₁.next (runTraceMoves r (pre₀ ++ A₁ :: mid₁))) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect (E₂.next (runTraceMoves r (pre₀ ++ A₁ :: mid₁ ++ E₁ :: mid₂))) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect (m₃.next (runTraceMoves r (pre₀ ++ A₁ :: mid₁ ++ E₁ :: mid₂ ++ E₂ :: mid₃))) mid₄) (hmid₅ : MovesFrom InvisibleNoEffect (A₂.next (runTraceMoves r (pre₀ ++ A₁ :: mid₁ ++ E₁ :: mid₂ ++ E₂ :: mid₃ ++ m₃ :: mid₄))) mid₅) (hpost₅ : MovesFrom InvisibleNoEffect (E₅.next (runTraceMoves r (pre₀ ++ A₁ :: mid₁ ++ E₁ :: mid₂ ++ E₂ :: mid₃ ++ m₃ :: mid₄ ++ A₂ :: mid₅))) post₅) : WsIdx1DecryptNoop.DecryptNoop r (pre₀ ++ A₁ :: mid₁ ++ E₁ :: mid₂ ++ E₂ :: mid₃ ++ m₃ :: mid₄ ++ A₂ :: mid₅ ++ E₅ :: post₅) := by
  have h40 := WsIdx1Decomp40.decryptNoop_split40 hA₁ hE₁ hE₂ hpre₀ hmid₁ hmid₂ hmid₃
  have h1 := WsIdx1Decomp40.decryptNoop_snoc h40 (fun hd => absurd hm₃ hd)
  have h2 := WsIdx1Decomp40.decryptNoop_append_movesFrom h1 (by rw [WsIdx1Decomp40.runTrace_snoc]; exact hmid₄)
  have h2' : WsIdx1DecryptNoop.DecryptNoop r (pre₀ ++ A₁ :: mid₁ ++ E₁ :: mid₂ ++ E₂ :: mid₃ ++ m₃ :: mid₄) := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h2
  have h3 := WsIdx1Decomp40.decryptNoop_snoc h2' (fun hd => absurd hA₂ hd)
  have h4 := WsIdx1Decomp40.decryptNoop_append_movesFrom h3 (by rw [WsIdx1Decomp40.runTrace_snoc]; exact hmid₅)
  have h4' : WsIdx1DecryptNoop.DecryptNoop r (pre₀ ++ A₁ :: mid₁ ++ E₁ :: mid₂ ++ E₂ :: mid₃ ++ m₃ :: mid₄ ++ A₂ :: mid₅) := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h4
  have h5 := WsIdx1Decomp40.decryptNoop_snoc h4' (fun hd => absurd hE₅ hd)
  have h6 := WsIdx1Decomp40.decryptNoop_append_movesFrom h5 (by rw [WsIdx1Decomp40.runTrace_snoc]; exact hpost₅)
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h6
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol) in
theorem gamma_facts81_s2 {r : Records} {S : Sem} {g : Ghost} {tr₄ : ExecTrace} {hb : DY.Libsignal.PQXDH.BundleHandles} (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 43) :: rs4) (aliceVis tr₄ (iniAliceStartTr tr₄ r.alice r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb)) : gamma compI0 S g (randTerm (tr₄.length + 1) 32) = compKyberE2 ∧ gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₄.length 32)) = WsIdx1CensusDefs.ek2PubKey ∧ gamma compI0 S g (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct = compKyberCt2 := by
  rw [rs4_eq_cons] at hvis; obtain ⟨hγek, hγe⟩ := CompRX0Gamma.aliceVis_rng_coins hvis; rw [rs4_coinHeads_eq] at hγe; have hek := CompRX0Gamma.gamma_iniAliceOut_ek_compI0 (S := S) (g := g) (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none hγek; rw [clamp_rng44_lookup] at hek
  have hct := CompRX0Gamma.gamma_iniAliceOut_ct (i := compI0) (S := S) (g := g)
    (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none (by rw [hγe]; decide)
  rw [hγe] at hct
  refine ⟨hγe, hek, ?_⟩
  rw [hct]
  have h0 : compI0 kyberEncapsSymbol [gamma compI0 S g (setupPublic r 6), compKyberE2] =
      some (compKyberEncaps compKyberE2) := rfl
  rw [h0, Option.getD_some, compKyberEncaps_e2_take1568]
attribute [local irreducible] setupPublic setupSecret
theorem split5_take_get {α : Type _} (P : List α) (a : α) (M₁ : List α) (b : α) (M₂ : List α)
    (c : α) (M₃ : List α) (d : α) (M₄ : List α) (e : α) (Q : List α) :
    let L := P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄ ++ e :: Q
    L.take P.length = P ∧ L[P.length]? = some a ∧
    L.take (P ++ a :: M₁).length = P ++ a :: M₁ ∧ L[(P ++ a :: M₁).length]? = some b ∧
    L.take (P ++ a :: M₁ ++ b :: M₂).length = P ++ a :: M₁ ++ b :: M₂ ∧
    L[(P ++ a :: M₁ ++ b :: M₂).length]? = some c ∧
    L.take (P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃).length = P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ∧
    L[(P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃).length]? = some d ∧
    L.take (P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄).length = P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄ ∧
    L[(P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄).length]? = some e := by
  dsimp only
  have h₁ : P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄ ++ e :: Q =
      P ++ a :: (M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄ ++ e :: Q) := by simp only [List.append_assoc, List.cons_append]
  have h₂ : P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄ ++ e :: Q =
      (P ++ a :: M₁) ++ b :: (M₂ ++ c :: M₃ ++ d :: M₄ ++ e :: Q) := by simp only [List.append_assoc, List.cons_append]
  have h₃ : P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄ ++ e :: Q =
      (P ++ a :: M₁ ++ b :: M₂) ++ c :: (M₃ ++ d :: M₄ ++ e :: Q) := by simp only [List.append_assoc, List.cons_append]
  have h₄ : P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃ ++ d :: M₄ ++ e :: Q =
      (P ++ a :: M₁ ++ b :: M₂ ++ c :: M₃) ++ d :: (M₄ ++ e :: Q) := by simp only [List.append_assoc, List.cons_append]
  refine ⟨by rw [h₁]; exact List.take_left, by rw [h₁]; simp, by rw [h₂]; exact List.take_left, by rw [h₂]; simp,
    by rw [h₃]; exact List.take_left, by rw [h₃]; simp, by rw [h₄]; exact List.take_left, by rw [h₄]; simp,
    List.take_left, by simp⟩
theorem links81Own_of {r : Records} {pre₀ mid₁ mid₂ mid₃₄ mid₅ post₅ : List Move} {hb₁ hb₄ : DY.Libsignal.PQXDH.BundleHandles} {sh₁ sh₄ s₁ s₂ s₅ cl₁ cl₂ cl₅ : Nat} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {o₁ o₂ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ stA₂ : DY.Libsignal.TripleRatchet.TRState} (hnb : CompSetupSecrecy.NoBrk r (pre₀ ++ .aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ .encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ .encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₃₄ ++ .aliceStart r.alice r.bob 4 6 hb₄ sh₄ :: mid₅ ++ .encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4)) :: post₅)) (ho₁ : o₁ = aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hstA₁ : stA₁ = aliceStartState tr₁ r.bob o₁) (ho₂ : o₂ = aliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hstA₂ : stA₂ = aliceStartState tr₄ r.bob o₂) (htr₁ : runTraceMoves r pre₀ = tr₁) (htr₂ : runTraceMoves r (pre₀ ++ .aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁) = tr₂) (htr₃ : runTraceMoves r (pre₀ ++ .aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ .encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂) = tr₃) (htr₄ : runTraceMoves r (pre₀ ++ .aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ .encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ .encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₃₄) = tr₄) (htr₅ : runTraceMoves r (pre₀ ++ .aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ .encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ .encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₃₄ ++ .aliceStart r.alice r.bob 4 6 hb₄ sh₄ :: mid₅) = tr₅) (hA₁ : (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o₁) (hA₂ : (Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄ = aliceStartTrOfOut tr₄ r.alice r.bob o₂) (hE₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2)) (hE₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ = encNextTr tr₃ r.alice s₂ (encSt tr₂ stA₁ cl₁) cl₂ (tr₃.length + 2)) (hE₅ : (Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))).next tr₅ = encNextTr tr₅ r.alice s₅ stA₂ cl₅ (tr₅.length + 2)) : WsIdx1PrefDefs.Links81Own r (pre₀ ++ .aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ .encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ .encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₃₄ ++ .aliceStart r.alice r.bob 4 6 hb₄ sh₄ :: mid₅ ++ .encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4)) :: post₅) tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := by
  obtain ⟨t₁, g₁, t₂, g₂, t₃, g₃, t₄, g₄, t₅, g₅⟩ := split5_take_get pre₀ (.aliceStart r.alice r.bob 4 6 hb₁ sh₁) mid₁ (.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))) mid₂ (.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))) mid₃₄ (.aliceStart r.alice r.bob 4 6 hb₄ sh₄) mid₅ (.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))) post₅
  refine ⟨hnb, _, _, _, _, _, hb₁, hb₄, sh₁, sh₄, s₁, s₂, s₅, WsIdx1Decomp40.split3_lt₁ pre₀ mid₁, WsIdx1Decomp40.split3_lt₂ (pre₀ ++ _ :: mid₁) mid₂, WsIdx1Decomp40.split3_lt₂ (pre₀ ++ _ :: mid₁ ++ _ :: mid₂) mid₃₄, WsIdx1Decomp40.split3_lt₂ (pre₀ ++ _ :: mid₁ ++ _ :: mid₂ ++ _ :: mid₃₄) mid₅,
    by rw [t₁, htr₁], g₁, by rw [t₂, htr₂], g₂, by rw [t₃, htr₃], g₃, by rw [t₄, htr₄], g₄, by rw [t₅, htr₅], g₅,
    by rw [WsIdx1Decomp40.c_tr_eq, WsIdx1Decomp40.c_out_eq, ← ho₁]; exact hA₁,
    by rw [WsIdx1Decomp40.c_tr_eq, WsIdx1Decomp40.c_out_eq, ← ho₂]; exact hA₂,
    by rw [WsIdx1Decomp40.census_encNextTr_eq, WsIdx1Decomp40.c_st_eq, WsIdx1Decomp40.c_out_eq, ← ho₁, ← hstA₁]; exact hE₁,
    by rw [WsIdx1Decomp40.census_encNextTr_eq, WsIdx1Decomp40.census_encSt_eq, WsIdx1Decomp40.c_st_eq, WsIdx1Decomp40.c_out_eq, ← ho₁, ← hstA₁]; exact hE₂,
    by rw [WsIdx1Decomp40.census_encNextTr_eq, WsIdx1Decomp40.c_st_eq, WsIdx1Decomp40.c_out_eq, ← ho₂, ← hstA₂]; exact hE₅⟩
theorem honestKeysFrom_bob_seg {tr : ExecTrace} {mid₃ mid₄ : List Move} {m₃ : Move} (hm₃ : ∀ me sIdx cl pq wr, m₃ ≠ Move.encrypt me sIdx cl pq wr) (hmid₃ : Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect tr mid₃) (hmid₄ : Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect (m₃.next (runMoves mid₃ tr).1) mid₄) : honestKeysFrom tr (mid₃ ++ m₃ :: mid₄) = [] := by
  have hM₃ : honestKeysFrom (runMoves mid₃ tr).1 [m₃] = [] :=
    CompRSchedBSalts.honestKeysFrom_noEncrypt (fun m hm => by simp at hm; subst hm; exact hm₃)
  rw [CompRSchedBSalts.honestKeysFrom_append mid₃ (m₃ :: mid₄), CompRSchedBSalts.honestKeysFrom_movesFrom_invisibleNoEffect hmid₃, List.nil_append,
    show m₃ :: mid₄ = [m₃] ++ mid₄ from rfl,
    CompRSchedBSalts.honestKeysFrom_append [m₃] mid₄, hM₃, List.nil_append]
  exact CompRSchedBSalts.honestKeysFrom_movesFrom_invisibleNoEffect hmid₄
theorem honestSalts_schedB81_bob_mem {r : Records} {s₀ s₁ s₂ mid₃ mid₄ s₄ s₅ : List Move} {A₁ A₂ E₁ E₂ m₃ E₅ : Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {o₁ o₂ : DY.Libsignal.PQXDH.AliceHandshakeOut} {b me₁ me₂ me₅ : Participant} {i₁ i₂ i₅ cl₁ cl₂ cl₅ pq₁ pq₂ pq₅ : Nat} (hE₁ : ∃ wr, E₁ = Move.encrypt me₁ i₁ cl₁ pq₁ wr) (hE₂ : ∃ wr, E₂ = Move.encrypt me₂ i₂ cl₂ pq₂ wr) (hE₅ : ∃ wr, E₅ = Move.encrypt me₅ i₅ cl₅ pq₅ wr) (hA₁ : ∀ me sIdx cl pq wr, A₁ ≠ Move.encrypt me sIdx cl pq wr) (hm₃ : ∀ me sIdx cl pq wr, m₃ ≠ Move.encrypt me sIdx cl pq wr) (hA₂ : ∀ me sIdx cl pq wr, A₂ ≠ Move.encrypt me sIdx cl pq wr) (htr₁ : tr₁ = (runMoves s₀ (setupTrace r)).1) (htr₂ : tr₂ = (runMoves s₁ (A₁.next tr₁)).1) (htr₃ : tr₃ = (runMoves s₂ (E₁.next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ (E₂.next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ (m₃.next tr_bob)).1) (htr₅ : tr₅ = (runMoves s₄ (A₂.next tr₄)).1) (hs₀ : CompRSchedBSalts.SaltFree (setupTrace r) s₀) (hs₁ : CompRSchedBSalts.SaltFree (A₁.next tr₁) s₁) (hs₂ : CompRSchedBSalts.SaltFree (E₁.next tr₂) s₂) (hmid₃ : Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect (E₂.next tr₃) mid₃) (hmid₄ : Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect (m₃.next tr_bob) mid₄) (hs₄ : CompRSchedBSalts.SaltFree (A₂.next tr₄) s₄) (hs₅ : CompRSchedBSalts.SaltFree (E₅.next tr₅) s₅) (henc₁ : E₁.next tr₂ = Census443Defs.encNextTr tr₂ me₁ i₁ (Census443Defs.iniAliceStartState tr₁ b o₁) cl₁ pq₁) (henc₂ : E₂.next tr₃ = Census443Defs.encNextTr tr₃ me₂ i₂ (Census443Defs.encSt tr₂ (Census443Defs.iniAliceStartState tr₁ b o₁) cl₁) cl₂ pq₂) (henc₅ : E₅.next tr₅ = Census443Defs.encNextTr tr₅ me₅ i₅ (Census443Defs.iniAliceStartState tr₄ b o₂) cl₅ pq₅) {s : DY.Bytes} (hs : s ∈ honestSalts r (s₀ ++ A₁ :: s₁ ++ E₁ :: s₂ ++ E₂ :: mid₃ ++ m₃ :: mid₄ ++ A₂ :: s₄ ++ E₅ :: s₅)) : s = DY.Spqr.zeroKey ∨ s = DY.Spqr.spqrChainKey o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) ∨ s = (DY.Spqr.spqrSend (Census443Defs.encSt tr₂ (Census443Defs.iniAliceStartState tr₁ b o₁) cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.1 ∨ s = DY.Spqr.spqrChainKey o₂.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) := by
  obtain ⟨wr₁, rfl⟩ := hE₁; obtain ⟨wr₂, rfl⟩ := hE₂; obtain ⟨wr₅, rfl⟩ := hE₅
  have hA₁_keys : honestKeysFrom tr₁ [A₁] = [] :=
    CompRSchedBSalts.honestKeysFrom_noEncrypt (fun m hm => by simp at hm; subst hm; exact hA₁)
  have hA₂_keys : honestKeysFrom tr₄ [A₂] = [] :=
    CompRSchedBSalts.honestKeysFrom_noEncrypt (fun m hm => by simp at hm; subst hm; exact hA₂)
  have htr₄_seg : tr₄ = (runMoves (mid₃ ++ m₃ :: mid₄) ((Move.encrypt me₂ i₂ cl₂ pq₂ wr₂).next tr₃)).1 := by rw [runMoves_append_fst, ← htr_bob, runMoves_cons_fst₀, ← htr₄]
  have hbob_keys : honestKeysFrom ((Move.encrypt me₂ i₂ cl₂ pq₂ wr₂).next tr₃) (mid₃ ++ m₃ :: mid₄) = [] := by
    refine honestKeysFrom_bob_seg hm₃ hmid₃ ?_; rw [← htr_bob]; exact hmid₄
  have heq : honestSalts r (s₀ ++ A₁ :: s₁ ++ Move.encrypt me₁ i₁ cl₁ pq₁ wr₁ :: s₂ ++ Move.encrypt me₂ i₂ cl₂ pq₂ wr₂ :: mid₃ ++ m₃ :: mid₄ ++ A₂ :: s₄ ++ Move.encrypt me₅ i₅ cl₅ pq₅ wr₅ :: s₅) = [DY.Spqr.zeroKey, DY.Spqr.spqrChainKey o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1),
       ({ st := (DY.Spqr.spqrSend (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B) (randTerm (tr₂.length + 1) cl₁)).1,
          coins := randTerm (tr₃.length + 1) cl₂ } : DY.Spqr.SendKey.SubF DY.Bytes).pack,
       DY.Spqr.spqrChainKey o₂.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)] := by
    unfold honestSalts; congr 1
    have hassoc : s₀ ++ A₁ :: s₁ ++ Move.encrypt me₁ i₁ cl₁ pq₁ wr₁ :: s₂ ++ Move.encrypt me₂ i₂ cl₂ pq₂ wr₂ :: mid₃ ++ m₃ :: mid₄ ++ A₂ :: s₄ ++ Move.encrypt me₅ i₅ cl₅ pq₅ wr₅ :: s₅ = s₀ ++ ([A₁] ++ (s₁ ++ (Move.encrypt me₁ i₁ cl₁ pq₁ wr₁ :: s₂ ++ (Move.encrypt me₂ i₂ cl₂ pq₂ wr₂ :: (mid₃ ++ m₃ :: mid₄) ++ ([A₂] ++ (s₄ ++ Move.encrypt me₅ i₅ cl₅ pq₅ wr₅ :: s₅)))))) := by simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hassoc, CompRSchedBSalts.honestKeysFrom_append s₀, CompRSchedBSalts.honestKeysFrom_saltFree hs₀, List.nil_append, ← htr₁, CompRSchedBSalts.honestKeysFrom_append [A₁], hA₁_keys, List.nil_append]; dsimp only [runMoves]
    rw [CompRSchedBSalts.honestKeysFrom_append s₁, CompRSchedBSalts.honestKeysFrom_saltFree hs₁, List.nil_append, ← htr₂, List.cons_append, CompRSchedBSalts.honestKeysFrom_encrypt_cons henc₁, ← henc₁, CompRSchedBSalts.honestKeysFrom_append s₂, CompRSchedBSalts.honestKeysFrom_saltFree hs₂, List.nil_append, ← htr₃, List.cons_append, CompRSchedBSalts.honestKeysFrom_encrypt_cons henc₂, ← henc₂, CompRSchedBSalts.honestKeysFrom_append (mid₃ ++ m₃ :: mid₄), hbob_keys, List.nil_append, ← htr₄_seg, CompRSchedBSalts.honestKeysFrom_append [A₂], hA₂_keys, List.nil_append]
    dsimp only [runMoves]; rw [CompRSchedBSalts.honestKeysFrom_append s₄, CompRSchedBSalts.honestKeysFrom_saltFree hs₄, List.nil_append, ← htr₅, CompRSchedBSalts.honestKeysFrom_encrypt_cons henc₅, ← henc₅, CompRSchedBSalts.honestKeysFrom_saltFree hs₅]
    change [(DY.Spqr.spqrSend (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B) (randTerm (tr₂.length + 1) cl₁)).2.1, (DY.Spqr.spqrSend (DY.Spqr.spqrSend (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B) (randTerm (tr₂.length + 1) cl₁)).1 (randTerm (tr₃.length + 1) cl₂)).2.1, (DY.Spqr.spqrSend (DY.Spqr.spqrInit o₂.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B) (randTerm (tr₅.length + 1) cl₅)).2.1] = _
    rw [CompRSchedBSalts.spqrSend_spqrInit_key, CompRSchedBSalts.spqrSend_after_send_key, CompRSchedBSalts.spqrSend_spqrInit_key]
  rw [heq] at hs
  have h2 : ({ st := (DY.Spqr.spqrSend (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B) (randTerm (tr₂.length + 1) cl₁)).1,
               coins := randTerm (tr₃.length + 1) cl₂ } : DY.Spqr.SendKey.SubF DY.Bytes).pack =
      (DY.Spqr.spqrSend (Census443Defs.encSt tr₂ (Census443Defs.iniAliceStartState tr₁ b o₁) cl₁).spqr
        (randTerm (tr₃.length + 1) cl₂)).2.1 :=
    (CompRSchedBSalts.spqrSend_after_send_key (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B) (randTerm (tr₂.length + 1) cl₁) (randTerm (tr₃.length + 1) cl₂)).symm
  rw [h2] at hs; simpa using hs
theorem x81_eq (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : WsIdx1CensusDefs.x81Idx1 r tr₁ tr₂ tr₄ cl₁ = ⟨(aliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek, (aliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct, encOut tr₂ (aliceStartState tr₁ r.bob (aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2)⟩ := rfl
theorem prk_x81_eq : @WsIdx1PreKeyRep.x81Idx1 = @WsIdx1CensusDefs.x81Idx1 := rfl
theorem prk_wire6_eq : WsIdx1PreKeyRep.wire6Idx1Bytes = WsIdx1CensusDefs.wire6Idx1Bytes := by
  show WsIdx1PreKeyRep.recvAt 81 = WsIdx1CensusDefs.recvAt 81; rw [WsIdx1Decomp40.prk_recvAt_eq]
theorem census_wire6_eq : WsIdx1CensusDefs.wire6Idx1Bytes = wireAt 81 := by
  show WsIdx1CensusDefs.recvAt 81 = wireAt 81; rw [WsIdx1Decomp40.census_recvAt_eq]
theorem ek2PubKey_eq : Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts.ek2PubKey = WsIdx1CensusDefs.ek2PubKey := rfl
set_option maxRecDepth 200000 in theorem checkOuter_wire81Fast : CompFitsNames.checkPreKeyOuter Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 wire81Fast = true := by decide +kernel
theorem wireAt81_outer {r : Records} {p : PreKeyFields} (hf : Symbolic.BugInjection.compFits Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r) (hp : parsePreKeyWire (wireAt 81) = some p) : CompRPreKeyWire.PreKeyOuterMatches compI0 r (wireAt 81) p := by rw [wireAt81_eq_fast] at hp ⊢; exact CompFitsNames.preKeyOuterMatches_of_check hf hp checkOuter_wire81Fast
theorem split81_pre_of_parts {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} {b1 b2 b5 : List MachineEvent} (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r) (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (WsIdx1CensusDefs.wsIdx1Trace.drop 35 |>.take 3) b1) (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2) (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (WsIdx1CensusDefs.wsIdx1Trace.drop 78 |>.take 3) b5) (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms (((((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 40 |>.take 3)) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 43 |>.take 35)) ++ b5)) (hnb : CompSetupSecrecy.NoBrk r ms) (hp : parsePreKeyWire WsIdx1CensusDefs.wire6Idx1Bytes = some p) {pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move} {hb₀ hb₄ : DY.Libsignal.PQXDH.BundleHandles} {sh₀ sh₄ : Nat} {cl₁ e₁ c₁ cl₂ e₂ c₂ cl₅ e₅ c₅ : Nat} {m₃ : Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {o₁ o₂ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ stA₂ : DY.Libsignal.TripleRatchet.TRState} (hm₃_dec : m₃.decryptMsgIdx? = none) (hm₃_enc : ∀ me sIdx cl pq wr, m₃ ≠ Move.encrypt me sIdx cl pq wr) (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (ho₁ : o₁ = aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hstA₁ : stA₁ = aliceStartState tr₁ r.bob o₁) (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀).next tr₁)).1) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))).next tr₂)).1) (htr_bob : tr_bob = (runMoves mid₃ ((Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))).next tr₃)).1) (htr₄ : tr₄ = (runMoves mid₄ (m₃.next tr_bob)).1) (ho₂ : o₂ = aliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hstA₂ : stA₂ = aliceStartState tr₄ r.bob o₂) (htr₅ : tr₅ = (runMoves mid₅ ((Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄)).1) (hms : ms = pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀ :: mid₁ ++ Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁)) :: mid₂ ++ Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂)) :: mid₃ ++ m₃ :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄ :: mid₅ ++ Move.encrypt r.alice (tr₄.length + 8) cl₅ (tr₅.length + 2) (some (e₅, c₅)) :: post₅) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀).next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o₁) (hE₁ : (Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))).next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA₁ cl₁ (tr₂.length + 2)) (hE₂ : (Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))).next tr₃ = encNextTr tr₃ r.alice (tr₂.length + 5) (encSt tr₂ stA₁ cl₁) cl₂ (tr₃.length + 2)) (hm₄ : (Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄ = aliceStartTrOfOut tr₄ r.alice r.bob o₂) (hE₅ : (Move.encrypt r.alice (tr₄.length + 8) cl₅ (tr₅.length + 2) (some (e₅, c₅))).next tr₅ = encNextTr tr₅ r.alice (tr₄.length + 8) stA₂ cl₅ (tr₅.length + 2)) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀).next tr₁) mid₁) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))).next tr₂) mid₂) (hmid₃ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))).next tr₃) mid₃) (hmid₄ : MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄) (hmid₅ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄) mid₅) (hpost₅ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₄.length + 8) cl₅ (tr₅.length + 2) (some (e₅, c₅))).next tr₅) post₅) (hek₁ : NetMsgAt o₁.ek (tr₁.length + 3) tr₂) (hct₁ : NetMsgAt o₁.ct (tr₁.length + 4) tr₂) (hek₂ : NetMsgAt o₂.ek (tr₄.length + 3) tr₅) (hct₂ : NetMsgAt o₂.ct (tr₄.length + 4) tr₅) (hvis₀ : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 0) :: rs0) (aliceVis tr₁ ((Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀).next tr₁) hb₀)) (hvis₄ : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 43) :: rs4) (aliceVis tr₄ ((Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄) hb₄)) (hsm₁ : CompRPreKeyWire.SendMatchesMoves compI0 r S g (sendAt 37) (received tr₂ [e₁, c₁] ++ [encOut tr₂ stA₁ cl₁ (tr₂.length + 2)])) (hsm₂ : CompRPreKeyWire.SendMatchesMoves compI0 r S g (wireAt 40) (received tr₃ [e₂, c₂] ++ [encOut tr₃ (encSt tr₂ stA₁ cl₁) cl₂ (tr₃.length + 2)])) (hsm₅ : CompRPreKeyWire.SendMatchesMoves compI0 r S g (sendAt 80) (received tr₅ [e₅, c₅] ++ [encOut tr₅ stA₂ cl₅ (tr₅.length + 2)])) : ∃ (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms' (((((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 40 |>.take 3)) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 43 |>.take 35)) ++ b5) ∧ (∃ P₁ mid₂ P₂ post₅ me s₁ pq₁ s₂ pq₂ s₅ pq₅ w₁ w₂ w₅ w₁' w₂' w₅', ms = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅ ∧ ms' = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁' :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂' :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅' :: post₅) ∧ WsIdx1PrefDefs.WS81Idx1Pre r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧ WsIdx1CensusDefs.x81Idx1 r tr₁ tr₂ tr₄ cl₁ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire6Idx1Bytes := by
  have hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms
      (((((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 40 |>.take 3)) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 43 |>.take 35)) ++ b5) :=
    Symbolic.Swarm.CREF.MatchedPrefix.of_composed hex.1
  have hvis₀' := hvis₀; rw [hm₀, ← WsIdx1Decomp40.a_tr_eq, ho₁, ← WsIdx1Decomp40.a_out_eq] at hvis₀'; obtain ⟨hent₁, hek1, hct₁γ⟩ := WsIdx1Decomp40.gamma_facts40 hvis₀'; rw [WsIdx1Decomp40.a_out_eq, ← ho₁] at hct₁γ
  have hek₁γ : gamma compI0 S g o₁.ek = WsIdx1CensusDefs.ek1PubKey := by rw [ho₁, WsIdx1Decomp40.aliceOut_ek_eq]; exact hek1
  have hvis₄' := hvis₄; rw [hm₄, ← WsIdx1Decomp40.a_tr_eq, ho₂, ← WsIdx1Decomp40.a_out_eq] at hvis₄'; obtain ⟨hent₂, hek2, hct₂γ⟩ := gamma_facts81_s2 hvis₄'; rw [WsIdx1Decomp40.a_out_eq, ← ho₂] at hct₂γ
  have hek₂γ : gamma compI0 S g o₂.ek = WsIdx1CensusDefs.ek2PubKey := by rw [ho₂, WsIdx1Decomp40.aliceOut_ek_eq]; exact hek2
  let m₀ := Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀
  let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (e₁, c₁))
  let m₂ := Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (e₂, c₂))
  let m₄ := Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄
  let m₅ := Move.encrypt r.alice (tr₄.length + 8) cl₅ (tr₅.length + 2) (some (e₅, c₅))
  let m₁' := Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))
  let m₂' := Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))
  let m₅' := Move.encrypt r.alice (tr₄.length + 8) cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))
  have hrt₁ : runTraceMoves r pre₀ = tr₁ := by rw [xpl_runTrace_eq, htr₁]
  have hrt₂ : runTraceMoves r (pre₀ ++ m₀ :: mid₁) = tr₂ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₁, htr₂]
  have hrt₃ : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂) = tr₃ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₂, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁)), htr₃]
  have hrt₃o : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂) = tr₃ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₂, htr₃]
  have hrt_bob : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃) = tr_bob := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₃, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂)), htr_bob]
  have hrt_bobo : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃) = tr_bob := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₃o, htr_bob]
  have hrt₄ : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄) = tr₄ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt_bob, htr₄]
  have hrt₄o : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄) = tr₄ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt_bobo, htr₄]
  have hrt₅ : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅) = tr₅ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₄, htr₅]
  have hrt₅o : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅) = tr₅ := by rw [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₄o, htr₅]
  obtain ⟨q₁, hq₁⟩ := sendAt37_parses
  have hγ₁ := CompRX0Mem.hγ_of_sendMatches (ek := o₁.ek) (ct := o₁.ct) hsm₁ sendAt37_len hq₁
    (by rw [sendAt37_baseKey hq₁, hek₁γ]) (by rw [sendAt37_kyberCiphertext hq₁, hct₁γ])
  obtain ⟨q₂, hq₂⟩ := wireAt40_parses
  have hlen₂ : (wireAt 40).length < 2 ^ 63 := by rw [← sendAt39_eq_wireAt40]; exact sendAt39_len
  have hγ₂ := CompRX0Mem.hγ_of_sendMatches (ek := o₁.ek) (ct := o₁.ct) hsm₂ hlen₂ hq₂
    (by rw [wireAt40_baseKey_full hq₂, hek₁γ]) (by rw [wireAt40_kyberCiphertext hq₂, hct₁γ])
  obtain ⟨q₅, hq₅⟩ := sendAt80_parses
  have hγ₅ := CompRX0Mem.hγ_of_sendMatches (ek := o₂.ek) (ct := o₂.ct) hsm₅ sendAt80_len hq₅
    (by rw [sendAt80_baseKey_full hq₅, hek₂γ]) (by rw [sendAt80_kyberCiphertext hq₅, hct₂γ])
  have hP₂_eq : ∀ (w₁ w₂ w₅ : Option (Nat × Nat)), pre₀ ++ m₀ :: mid₁ ++ Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) w₂ :: (mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅) ++ Move.encrypt r.alice (tr₄.length + 8) cl₅ (tr₅.length + 2) w₅ :: post₅ = pre₀ ++ m₀ :: mid₁ ++ Move.encrypt r.alice (tr₁.length + 8) cl₁ (tr₂.length + 2) w₁ :: mid₂ ++ Move.encrypt r.alice (tr₂.length + 5) cl₂ (tr₃.length + 2) w₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ Move.encrypt r.alice (tr₄.length + 8) cl₅ (tr₅.length + 2) w₅ :: post₅ := by intros; simp only [List.append_assoc, List.cons_append]
  have hrt₅o' : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: (mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅)) = tr₅ := by
    have h : pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: (mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅) = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ := by simp only [List.append_assoc, List.cons_append]
    rw [h, hrt₅o]
  subst hms
  have hex_grouped : DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g (pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: (mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅) ++ m₅ :: post₅)
      (((((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 40 |>.take 3)) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 43 |>.take 35)) ++ b5) := by rw [hP₂_eq]; exact hex
  obtain ⟨hex'_grouped, hrteq_grouped, -⟩ := explains_swap3
    (by rw [hrt₂]; exact hek₁) (by rw [hrt₂]; exact hct₁) (by rw [hrt₂]; exact hγ₁) (by rw [hrt₃o]; exact hγ₂)
    (by rw [hrt₅o']; exact hek₂) (by rw [hrt₅o']; exact hct₂) (by rw [hrt₅o']; exact hγ₅) hex_grouped
  rw [hP₂_eq] at hex'_grouped hrteq_grouped; rw [hP₂_eq (some (e₁, c₁))] at hrteq_grouped
  obtain ⟨MS', hMS'⟩ : ∃ MS', MS' =
      pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅' :: post₅ := ⟨_, rfl⟩
  obtain ⟨_, _, -, -, -, hmsg₁⟩ := CompRX0Mem.sendMatches_append_inv hsm₁ sendAt37_len hq₁
  have hp81 : parsePreKeyWire (wireAt 81) = some p := by rw [← census_wire6_eq]; exact hp
  have hmsg81 : gamma compI0 S g (encOut tr₂ stA₁ cl₁ (tr₂.length + 2)) = p.message := hmsg₁.symm.trans (wireAt81_message_eq_sendAt37 hp81 hq₁).symm
  have hle₅ : m₅'.next tr₅ ≤ runTraceMoves r MS' := by rw [hMS', WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₅]; exact CompPrefixInvEnc.runMoves_le _ _
  have hle_tr₅ : tr₅ ≤ runTraceMoves r MS' := Trace.le_trans _ _ _ (Move.le_next m₅' tr₅) hle₅
  have hle_m₁' : m₁'.next tr₂ ≤ runTraceMoves r MS' := by
    have hsplit : MS' = (pre₀ ++ m₀ :: mid₁) ++ (m₁' :: (mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅' :: post₅)) := by rw [hMS']; simp only [List.append_assoc, List.cons_append]
    rw [hsplit, WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₂]; exact CompPrefixInvEnc.runMoves_le _ _
  have hkmsgN := netMsgAt_encOut_encNextTr tr₂ r.alice (tr₁.length + 8) stA₁ cl₁ (tr₂.length + 2); rw [← hE₁, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (tr₁.length + 3, tr₁.length + 4))] at hkmsgN; have hkmsg := (NetMsgAt.mono hle_m₁' hkmsgN).attackerKnows; have hkek := (NetMsgAt.mono hle_tr₅ hek₂).attackerKnows; have hkct := (NetMsgAt.mono hle_tr₅ hct₂).attackerKnows
  have hbk81 : p.baseKey.take 33 = ecKey WsIdx1CensusDefs.ek2PubKey := by rw [← ek2PubKey_eq]; exact baseKey_of_map wireAt81_baseKey hp81
  have hall := WsIdx1PreKeyRep.x81Idx1_mem_preKeyRepresentations (ms' := MS')
    (tr₁ := tr₁) (tr₂ := tr₂) (tr₄ := tr₄) (cl₁ := cl₁) (p := p)
    (by rw [prk_x81_eq, x81_eq, ← ho₂]; dsimp only; exact hkek)
    (by rw [prk_x81_eq, x81_eq, ← ho₂]; dsimp only; exact hkct)
    (by rw [prk_x81_eq, x81_eq, ← ho₁, ← hstA₁]; dsimp only; exact hkmsg)
    (by rw [prk_wire6_eq]; exact hp)
    (by rw [prk_x81_eq, x81_eq, ← ho₂]; dsimp only; rw [hek₂γ, hbk81])
    (by rw [prk_x81_eq, x81_eq, ← ho₂]; dsimp only; rw [hct₂γ, wireAt81_kyberCiphertext hp81])
    (by rw [prk_x81_eq, x81_eq, ← ho₁, ← hstA₁]; dsimp only; exact hmsg81) (wireAt81_canon hp81)
    (by rw [prk_wire6_eq, census_wire6_eq]; exact wireAt81_outer hfits.1 hp81)
  dsimp only at hall; rw [prk_x81_eq, prk_wire6_eq] at hall; obtain ⟨hmem, hw⟩ := hall; subst hMS'
  have hrt₄_grouped : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: (mid₃ ++ m₃ :: mid₄)) = tr₄ := by
    have h : pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: (mid₃ ++ m₃ :: mid₄) =
        pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ := by simp only [List.append_assoc, List.cons_append]
    rw [h, hrt₄]
  have hrt₅_grouped : runTraceMoves r (pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: (mid₃ ++ m₃ :: mid₄) ++ m₄ :: mid₅) = tr₅ := by
    have h : pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: (mid₃ ++ m₃ :: mid₄) ++ m₄ :: mid₅ = pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ := by simp only [List.append_assoc, List.cons_append]
    rw [h, hrt₅]
  have hnb' : CompSetupSecrecy.NoBrk r (pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅' :: post₅) :=
    CompSetupSecrecy.noBrk_of_eq hrteq_grouped hnb
  have hlinks_grouped := links81Own_of (mid₃₄ := mid₃ ++ m₃ :: mid₄) (post₅ := post₅) (by simpa only [List.append_assoc, List.cons_append] using hnb') ho₁ hstA₁ ho₂ hstA₂ hrt₁ hrt₂ hrt₃ hrt₄_grouped hrt₅_grouped hm₀ hm₄
    (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact hE₁)
    (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact hE₂)
    (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₅, c₅))]; exact hE₅)
  have hlinks : WsIdx1PrefDefs.Links81Own r (pre₀ ++ m₀ :: mid₁ ++ m₁' :: mid₂ ++ m₂' :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅' :: post₅) tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := by
    simpa only [List.append_assoc, List.cons_append] using hlinks_grouped
  refine ⟨_, tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex'_grouped,
    ⟨pre₀ ++ m₀ :: mid₁, mid₂, mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅, post₅, r.alice,
      tr₁.length + 8, tr₂.length + 2, tr₂.length + 5, tr₃.length + 2, tr₄.length + 8, tr₅.length + 2,
      some (e₁, c₁), some (e₂, c₂), some (e₅, c₅),
      some (tr₁.length + 3, tr₁.length + 4), some (tr₁.length + 3, tr₁.length + 4), some (tr₄.length + 3, tr₄.length + 4),
      (hP₂_eq _ _ _).symm, (hP₂_eq _ _ _).symm⟩,
    { fits := hfits, ex := CompSetupSecrecy.noBrk_of_eq hrteq_grouped hnb, dn := ?_, mp := WsIdx1CensusDefs.matchedPrefix81_of_split3 hc1 hc2 hc5 hex'_grouped.1, links := hlinks,
      compat := hex.1.1, reach := ?_, hent₁ := hent₁, hek₁ := hek1, hek₂ := hek2,
      hent₂ := hent₂, hwire₁ := ?_, hsalts := ?_ }, hmem⟩
  · exact decryptNoop_split81 (by rfl) (by rfl) (by rfl) hm₃_dec (by rfl) (by rfl)
      hpre₀ (by rw [hrt₁]; exact hmid₁)
      (by rw [hrt₂, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact hmid₂)
      (by rw [hrt₃, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact hmid₃)
      (by rw [hrt_bob]; exact hmid₄) (by rw [hrt₄]; exact hmid₅)
      (by rw [hrt₅, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₅, c₅))]; exact hpost₅)
  · rw [hrteq_grouped]; exact CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp _ [] (List.append_nil _).symm
  · dsimp only; intro p' hp'; obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp); exact hw
  · dsimp only
    have hnb_post₅ : CompRX0Top.NoBrkTr (runMoves post₅ (m₅.next tr₅)).1 := by
      have h := CompRX0Top.noBrkTr_of_noBrk hnb
      rwa [WsIdx1DecompSwap.runTrace_append, runMoves_cons_fst₀, hrt₅o] at h
    have hnb_tr₅ : CompRX0Top.NoBrkTr tr₅ :=
      CompRX0Top.noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next _ _) (CompPrefixInvEnc.runMoves_le _ _)) hnb_post₅
    have hnb_tr₄ : CompRX0Top.NoBrkTr tr₄ :=
      CompRX0Top.noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next _ _) (by rw [htr₅]; exact CompPrefixInvEnc.runMoves_le _ _)) hnb_tr₅
    have hnb_tr_bob : CompRX0Top.NoBrkTr tr_bob :=
      CompRX0Top.noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next _ _) (by rw [htr₄]; exact CompPrefixInvEnc.runMoves_le _ _)) hnb_tr₄
    have hnb_tr₃ : CompRX0Top.NoBrkTr tr₃ :=
      CompRX0Top.noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next _ _) (by rw [htr_bob]; exact CompPrefixInvEnc.runMoves_le _ _)) hnb_tr_bob
    have hnb_tr₂ : CompRX0Top.NoBrkTr tr₂ :=
      CompRX0Top.noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next _ _) (by rw [htr₃]; exact CompPrefixInvEnc.runMoves_le _ _)) hnb_tr₃
    have hnb_tr₁ : CompRX0Top.NoBrkTr tr₁ :=
      CompRX0Top.noBrkTr_of_le (Trace.le_trans _ _ _ (Move.le_next _ _) (by rw [htr₂]; exact CompPrefixInvEnc.runMoves_le _ _)) hnb_tr₂
    rw [WsIdx1Decomp40.c_out_eq, WsIdx1Decomp40.c_st_eq, WsIdx1Decomp40.census_encSt_eq, ← ho₁, ← hstA₁, ← ho₂]; intro s hs
    have h := honestSalts_schedB81_bob_mem (r := r)
      (s₀ := pre₀) (s₁ := mid₁) (s₂ := mid₂) (mid₃ := mid₃) (mid₄ := mid₄) (s₄ := mid₅)
      (s₅ := post₅) (A₁ := m₀) (A₂ := m₄) (E₁ := m₁') (E₂ := m₂') (m₃ := m₃) (E₅ := m₅')
      (tr₁ := tr₁) (tr₂ := tr₂) (tr₃ := tr₃) (tr_bob := tr_bob) (tr₄ := tr₄) (tr₅ := tr₅)
      (o₁ := o₁) (o₂ := o₂) (b := r.bob) ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩
      (fun _ _ _ _ _ h => nomatch h) hm₃_enc (fun _ _ _ _ _ h => nomatch h) htr₁ htr₂
      (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact htr₃)
      (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact htr_bob)
      htr₄ htr₅
      (Or.inl (WsIdx1Decomp40.movesFrom_census (by rw [← htr₁]; exact hnb_tr₁) hpre₀))
      (Or.inl (WsIdx1Decomp40.movesFrom_census (by rw [← htr₂]; exact hnb_tr₂) hmid₁))
      (Or.inl (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact WsIdx1Decomp40.movesFrom_census (by rw [← htr₃]; exact hnb_tr₃) hmid₂))
      (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact WsIdx1Decomp40.movesFrom_census (by rw [← htr_bob]; exact hnb_tr_bob) hmid₃)
      (WsIdx1Decomp40.movesFrom_census (by rw [← htr₄]; exact hnb_tr₄) hmid₄)
      (Or.inl (WsIdx1Decomp40.movesFrom_census (by rw [← htr₅]; exact hnb_tr₅) hmid₅))
      (Or.inl (by rw [WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₅, c₅))]; exact WsIdx1Decomp40.movesFrom_census hnb_post₅ hpost₅))
      (by rw [WsIdx1Decomp40.census_encNextTr_eq, WsIdx1Decomp40.c_st_eq, ← hstA₁, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₁, c₁))]; exact hE₁)
      (by rw [WsIdx1Decomp40.census_encNextTr_eq, WsIdx1Decomp40.census_encSt_eq, WsIdx1Decomp40.c_st_eq, ← hstA₁, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₂, c₂))]; exact hE₂)
      (by rw [WsIdx1Decomp40.census_encNextTr_eq, WsIdx1Decomp40.c_st_eq, ← hstA₂, WsIdx1DecompSwap.encrypt_next_eq_wrap _ _ _ _ _ _ (some (e₅, c₅))]; exact hE₅)
      hs
    rw [WsIdx1Decomp40.census_encSt_eq, WsIdx1Decomp40.c_st_eq, ← hstA₁] at h; exact h
theorem split81DecompSwapRep_split_of_pre {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ : List MachineEvent} (hpref : WsIdx1PrefDefs.Pref81Idx1Hyp) (hpre : ∃ (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms' τ ∧ (∃ P₁ mid₂ P₂ post₅ me s₁ pq₁ s₂ pq₂ s₅ pq₅ w₁ w₂ w₅ w₁' w₂' w₅', ms = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅ ∧ ms' = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁' :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂' :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅' :: post₅) ∧ WsIdx1PrefDefs.WS81Idx1Pre r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧ WsIdx1CensusDefs.x81Idx1 r tr₁ tr₂ tr₄ cl₁ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire6Idx1Bytes) : ∃ (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms' τ ∧ (∃ P₁ mid₂ P₂ post₅ me s₁ pq₁ s₂ pq₂ s₅ pq₅ w₁ w₂ w₅ w₁' w₂' w₅', ms = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅ ∧ ms' = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁' :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂' :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅' :: post₅) ∧ WsIdx1DecryptNoop.DecryptNoop r ms' ∧ WsIdx1CensusDefs.WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧ WsIdx1PrefDefs.Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧ WsIdx1CensusDefs.x81Idx1 r tr₁ tr₂ tr₄ cl₁ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire6Idx1Bytes := by
  obtain ⟨ms', tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex', hswap, hP, hmem⟩ := hpre; have hF := hpref r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hP
  obtain ⟨_, k₁, k₂, k₃, k₄, k₅, hb₁, hb₄, sh₁, sh₄, s₁, s₂, s₅, hl1, hl2, hl3, hl4, ht1, hg1, ht2, hg2, ht3, hg3, ht4, hg4, ht5, hg5,
    hn1, hn4, he1, he2, he5⟩ := hP.links
  exact ⟨ms', tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex', hswap, hP.dn,
    { mp := hP.mp
      links := ⟨k₁, k₂, k₃, k₄, k₅, hb₁, hb₄, sh₁, sh₄, s₁, s₂, s₅, _, _, _, _, _, _, hl1, hl2, hl3, hl4, ht1, hg1, ht2, hg2, ht3, hg3, ht4, hg4, ht5, hg5, hn1, hn4, rfl, rfl, rfl, he1, he2, he5⟩
      compat := hP.compat, reach := hP.reach, hent₁ := hP.hent₁, hek₁ := hP.hek₁, hdhs₁ := hF.hdhs₁,
      hm₁ := hF.hm₁, hm₁_len := hF.hm₁_len, hcoins₁ := hF.hcoins₁, hm₂ := hF.hm₂, hm₂_len := hF.hm₂_len,
      hcoins₂ := hF.hcoins₂, hek₂_safe := hF.hek₂_safe, hek₂ := hP.hek₂, hent₂_safe := hF.hent₂_safe,
      hent₂ := hP.hent₂, hwire₁ := hP.hwire₁, hsalts := hP.hsalts, hpref_safe := hF.hpref_safe },
    hP.links, hmem⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Aux
