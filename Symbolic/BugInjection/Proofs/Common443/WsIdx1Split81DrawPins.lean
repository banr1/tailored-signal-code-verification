/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumAux
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead78

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
open DY DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus Symbolic.BugInjection.Proofs.Common443.CompC2RestR38 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj (KdfFree)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead78 (call4Rng rng44Chars rngAt44_eq_hex rng44Str_eq rng77Chars rngAt77_eq_hex rng77Str_eq call4Rng_take_1_eq call4Rng_drop_33_eq)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 (call0Rng_length)
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem rngAt44_eq_fast : rngAt 44 = hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng44Chars := by rw [rngAt44_eq_hex, rng44Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
theorem rngAt77_eq_fast : rngAt 77 = hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng77Chars := by rw [rngAt77_eq_hex, rng77Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
theorem rVal_rngAt44 : RVal (rngAt 44) := by rw [rngAt44_eq_fast]; unfold RVal NonInjOff KdfFree; decide +kernel
theorem rVal_rngAt77 : RVal (rngAt 77) := by rw [rngAt77_eq_fast]; unfold RVal NonInjOff KdfFree; decide +kernel
def rng79Chars : List Char := chars_of_hex (rngAt 79)
theorem rngAt79_eq_hex : rngAt 79 = hexBytes (str_of_hex (rngAt 79)) := rfl
theorem rng79Str_eq : (str_of_hex (rngAt 79)) = String.ofList rng79Chars := rfl
theorem rngAt79_eq_fast : rngAt 79 = hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng79Chars := by rw [rngAt79_eq_hex, rng79Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
theorem rngAt79_length : (rngAt 79).length = 64 := by
  rw [rngAt79_eq_fast]; rfl
theorem rVal_rngAt79 : RVal (rngAt 79) :=
  rVal_of_len (by rw [rngAt79_length]; decide) (by rw [rngAt79_length]; decide)
theorem rVal_rngAt79_inits : ∀ c ∈ (rngAt 79).inits, RVal c := by
  rw [rngAt79_eq_fast]; unfold RVal NonInjOff KdfFree; decide +kernel
theorem call4Rng_length : call4Rng.length = 34 := rfl
theorem seg43_35_eq : seg 43 35 = .recv (wireAt 43) :: call4Rng := rfl
theorem seg78_3_eq : seg 78 3 = [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] := rfl
theorem call4Rng_take_1_bytes : ∀ ev ∈ call4Rng.take 1, DY.Libsignal.Composed.Refinement.eventBytes ev = rngAt 44 := by intro ev hev; rw [call4Rng_take_1_eq, List.mem_singleton] at hev; subst hev; rfl
theorem call4Rng_drop_33_bytes : ∀ ev ∈ call4Rng.drop 33, DY.Libsignal.Composed.Refinement.eventBytes ev = rngAt 77 := by intro ev hev; rw [call4Rng_drop_33_eq, List.mem_singleton] at hev; subst hev; rfl
attribute [local irreducible] bundle0 call0Rng call4Rng rngAt sendAt wireAt setupPublic setupSecret
theorem matchedPrefix_split_seg_gen {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ₁ blk : List MachineEvent} {k₀ : Kind} {ks : List Kind} (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms (τ₁ ++ blk)) (hmap : blk.map eventKind = k₀ :: ks) (hk₀ : k₀ = .recv ∨ k₀ = .pt) (hks : ∀ k ∈ ks, k = .rng ∨ k = .send ∨ k = .accept) : ∃ (ms₁ pre post : List Move) (m : Move), ms = ms₁ ++ pre ++ m :: post ∧ Symbolic.Swarm.CREF.MatchedPrefix i r S g ms₁ τ₁ ∧ MovesFrom InvisibleNoEffect (runTraceMoves r ms₁) pre ∧ List.Forall₂ (EventMatchesEntry i r S g) blk (m.vis (runTraceMoves r (ms₁ ++ pre))) ∧ MovesFrom InvisibleNoEffect (m.next (runTraceMoves r (ms₁ ++ pre))) post := by
  have hne : blk ≠ [] := fun hnil => by rw [hnil] at hmap; cases hmap
  have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    cases blk with
    | nil => contradiction
    | cons hd tl =>
      intro e he; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he; subst he
      simp only [List.map_cons, List.cons.injEq] at hmap; rw [hmap.1]; exact hk₀
  have htail : ∀ e ∈ blk.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    cases blk with
    | nil => contradiction
    | cons hd tl =>
      intro e he; simp only [List.tail_cons] at he; simp only [List.map_cons, List.cons.injEq] at hmap
      rcases hks (eventKind e) (hmap.2 ▸ List.mem_map_of_mem he) with hk | hk | hk <;> (rw [hk]; decide)
  obtain ⟨ms₁, δ, hms, hmp₁, hfor⟩ := matchedPrefix6_split hmp hhead (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp); have hB : XplBlock6 i r S g ms₁ δ τ₁ blk := ⟨hmp₁, hms ▸ hmp.2.1, hfor⟩; obtain ⟨pre, m, post, rfl, hpre, ⟨-, -, hm⟩, hpost⟩ := xpl6_oneMove hB hhead hne htail
  refine ⟨ms₁, pre, post, m, by rw [hms]; simp only [List.append_assoc], hmp₁, hpre, ?_, ?_⟩ <;>
    rwa [CompPrefixInvStruct.runTrace_append]
theorem decomp81_moves {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {b1 b2 b5 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 35 3) b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc b2)
    (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 78 3) b5)
    (hmp81 : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms' (((((seg 0 35 ++ b1) ++ b2) ++ seg 40 3) ++ seg 43 35) ++ b5)) :
    ∃ (pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move) (m₀ m₁ m₂ m₃ m₄ m₅ : Move), ms' = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅ ∧
      let tr₁ := (runMoves pre₀ (setupTrace r)).1
      let tr₂ := (runMoves mid₁ (m₀.next tr₁)).1
      let tr₃ := (runMoves mid₂ (m₁.next tr₂)).1
      let tr_bob := (runMoves mid₃ (m₂.next tr₃)).1
      let tr₄ := (runMoves mid₄ (m₃.next tr_bob)).1
      let tr₅ := (runMoves mid₅ (m₄.next tr₄)).1
      MovesFrom InvisibleNoEffect (setupTrace r) pre₀ ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid₁ ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂ ∧
      MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃ ∧
      MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄ ∧
      MovesFrom InvisibleNoEffect (m₄.next tr₄) mid₅ ∧
      MovesFrom InvisibleNoEffect (m₅.next tr₅) post₅ ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 0 35) (m₀.vis tr₁) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b1 (m₁.vis tr₂) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b2 (m₂.vis tr₃) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 40 3) (m₃.vis tr_bob) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 43 35) (m₄.vis tr₄) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b5 (m₅.vis tr₅) := by
  obtain ⟨ks5, hks5_eq, hks5⟩ := coinSplit_kinds (show DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt _, .rng _, .send _] b5 from seg78_3_eq ▸ hc5)
  obtain ⟨ms₇₈, pre₅, post₅, m₅, hms', hmp78, hpre₅, hm₅, hpost₅⟩ := matchedPrefix_split_seg_gen hmp81 hks5_eq (Or.inr rfl)
      (fun k hk => (hks5 k hk).elim Or.inl (Or.inr ∘ Or.inl))
  obtain ⟨ms₄₃, pre₄, post₄, m₄, hms₇₈, hmp43, hpre₄, hm₄, hpost₄⟩ :=
    matchedPrefix_split_seg_gen hmp78 seg43_kinds (Or.inl rfl) (fun k hk => Or.inl (replicate_rng 34 k hk))
  obtain ⟨ms₄₀, pre₃, post₃, m₃, hms₄₃, hmp40, hpre₃, hm₃, hpost₃⟩ := matchedPrefix_split_seg_gen hmp43 seg40_kinds (Or.inl rfl)
      (fun k hk => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; exact hk.elim Or.inl (Or.inr ∘ Or.inr))
  obtain ⟨pre₀, mid₁, mid₂, post₂, m₀, m₁, m₂, hms₄₀, hpre₀, hmid₁, hmid₂, hpost₂, hm₀, hm₁, hm₂⟩ := decomp40_moves hc1 hc2 hmp40
  let tr₁ := (runMoves pre₀ (setupTrace r)).1
  let tr₂ := (runMoves mid₁ (m₀.next tr₁)).1
  let tr₃ := (runMoves mid₂ (m₁.next tr₂)).1
  let mid₃ := post₂ ++ pre₃
  let tr_bob := (runMoves mid₃ (m₂.next tr₃)).1
  have htr_ms₄₀ : runTraceMoves r ms₄₀ = (runMoves post₂ (m₂.next tr₃)).1 := by
    rw [hms₄₀, xpl_runTrace_eq]; simp only [List.append_assoc, List.cons_append, runMoves_append_fst, runMoves]; rfl
  have htr_bob : runTraceMoves r (ms₄₀ ++ pre₃) = tr_bob := by
    rw [CompPrefixInvStruct.runTrace_append, htr_ms₄₀]; dsimp [tr_bob, mid₃]; rw [runMoves_append_fst]
  rw [htr_bob] at hm₃ hpost₃
  have hmid₃ : MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃ := by
    dsimp [mid₃]; rw [movesFrom_append, ← htr_ms₄₀]; exact ⟨hpost₂, hpre₃⟩
  let mid₄ := post₃ ++ pre₄
  let tr₄ := (runMoves mid₄ (m₃.next tr_bob)).1
  have hms₄₃_eq : ms₄₃ = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: post₃ := by
    dsimp [mid₃]; rw [hms₄₃, hms₄₀]; simp only [List.append_assoc, List.cons_append]
  have htr_ms₄₃ : runTraceMoves r ms₄₃ = (runMoves post₃ (m₃.next tr_bob)).1 := by
    rw [hms₄₃_eq, xpl_runTrace_eq]; simp only [List.append_assoc, List.cons_append, runMoves_append_fst, runMoves]; rfl
  have htr₄ : runTraceMoves r (ms₄₃ ++ pre₄) = tr₄ := by
    rw [CompPrefixInvStruct.runTrace_append, htr_ms₄₃]; dsimp [tr₄, mid₄]; rw [runMoves_append_fst]
  rw [htr₄] at hm₄ hpost₄
  have hmid₄ : MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄ := by
    dsimp [mid₄]; rw [movesFrom_append, ← htr_ms₄₃]; exact ⟨hpost₃, hpre₄⟩
  let mid₅ := post₄ ++ pre₅
  let tr₅ := (runMoves mid₅ (m₄.next tr₄)).1
  have hms₇₈_eq : ms₇₈ = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: post₄ := by
    dsimp [mid₄]; rw [hms₇₈, hms₄₃_eq]; simp only [List.append_assoc, List.cons_append]
  have htr_ms₇₈ : runTraceMoves r ms₇₈ = (runMoves post₄ (m₄.next tr₄)).1 := by
    rw [hms₇₈_eq, xpl_runTrace_eq]; simp only [List.append_assoc, List.cons_append, runMoves_append_fst, runMoves]; rfl
  have htr₅ : runTraceMoves r (ms₇₈ ++ pre₅) = tr₅ := by
    rw [CompPrefixInvStruct.runTrace_append, htr_ms₇₈]; dsimp [tr₅, mid₅]; rw [runMoves_append_fst]
  rw [htr₅] at hm₅ hpost₅
  have hmid₅ : MovesFrom InvisibleNoEffect (m₄.next tr₄) mid₅ := by
    dsimp [mid₅]; rw [movesFrom_append, ← htr_ms₇₈]; exact ⟨hpost₄, hpre₅⟩
  have hms'_eq : ms' = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅ := by
    dsimp [mid₅]; rw [hms', hms₇₈_eq]; simp only [List.append_assoc, List.cons_append]
  exact ⟨pre₀, mid₁, mid₂, mid₃, mid₄, mid₅, post₅, m₀, m₁, m₂, m₃, m₄, m₅, hms'_eq, hpre₀, hmid₁, hmid₂, hmid₃, hmid₄, hmid₅, hpost₅, hm₀, hm₁, hm₂, hm₃, hm₄, hm₅⟩
theorem not_aliceStart_of_vis_seg40 {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {a b : Participant} {idS regB : Nat} {hb : DY.Libsignal.PQXDH.BundleHandles} {sh : Nat} (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 40 3) ((Move.aliceStart a b idS regB hb sh).vis tr)) : False := by
  obtain ⟨b_rng, b_pt, hseg⟩ := seg40_eq; rw [hseg, aliceStart_vis_eq] at hvis
  rcases List.forall₂_cons_left_iff.mp hvis with ⟨v₀, vs₁, _, hvis₁, hvs⟩
  rcases List.forall₂_cons_left_iff.mp hvis₁ with ⟨v₁, vs₂, _, hvis₂, rfl⟩
  rcases List.forall₂_cons_left_iff.mp hvis₂ with ⟨v₂, vs₃, hev, _, rfl⟩
  have hmem : v₂ ∈ (aliceVis tr ((Move.aliceStart a b idS regB hb sh).next tr) hb).take sh := by rw [hvs]; simp
  have hk : v₂.kind = .accept := xpl_kind_of_matches hev
  rcases xpl_aliceVis_kind (List.mem_of_mem_take hmem) with h | h <;> (rw [hk] at h; cases h)
theorem not_encrypt_of_vis_seg40 {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {me : Participant} {sIdx cl pq : Nat} {wrap : Option (Nat × Nat)} (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 40 3) ((Move.encrypt me sIdx cl pq wrap).vis tr)) : False := by
  obtain ⟨b_rng, b_pt, hseg⟩ := seg40_eq; rw [hseg, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38.encrypt_vis_eq] at hvis
  rcases List.forall₂_cons_left_iff.mp hvis with ⟨v₀, vs₁, hev, _, hvs⟩
  have hmem : v₀ ∈ encVis tr ((Move.encrypt me sIdx cl pq wrap).next tr) wrap true := by rw [hvs]; simp
  have hk : v₀.kind = .recv := xpl_kind_of_matches hev
  rcases xpl_encVis_kind hmem with h | h | ⟨_, h⟩ <;> (rw [hk] at h; cases h)
theorem decomp81_of_mp_links {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {b1 b2 b5 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 35 3) b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc b2)
    (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 78 3) b5)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms' (((((seg 0 35 ++ b1) ++ b2) ++ seg 40 3) ++ seg 43 35) ++ b5))
    (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    ∃ (pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move) (m₃ : Move) (hb₁ hb₄ : DY.Libsignal.PQXDH.BundleHandles) (sh₁ sh₄ s₁ s₂ s₅ : Nat),
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁
      let w₁ := some (tr₁.length + 3, tr₁.length + 4)
      let m₁ := Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁
      let m₂ := Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₁
      let m₄ := Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄
      let w₄ := some (tr₄.length + 3, tr₄.length + 4)
      let m₅ := Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) w₄
      let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let stA₁ := iniAliceStartState tr₁ r.bob o₁
      let stA₁' := encSt tr₂ stA₁ cl₁
      let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let stA₂ := iniAliceStartState tr₄ r.bob o₂
      let tr_bob := (runMoves mid₃ (m₂.next tr₃)).1
      ms' = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅ ∧
      tr₁ = (runMoves pre₀ (setupTrace r)).1 ∧
      tr₂ = (runMoves mid₁ (m₀.next tr₁)).1 ∧
      tr₃ = (runMoves mid₂ (m₁.next tr₂)).1 ∧
      tr₄ = (runMoves mid₄ (m₃.next tr_bob)).1 ∧
      tr₅ = (runMoves mid₅ (m₄.next tr₄)).1 ∧
      MovesFrom InvisibleNoEffect (setupTrace r) pre₀ ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid₁ ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂ ∧
      MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃ ∧
      MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄ ∧
      MovesFrom InvisibleNoEffect (m₄.next tr₄) mid₅ ∧
      MovesFrom InvisibleNoEffect (m₅.next tr₅) post₅ ∧
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o₁ ∧
      m₁.next tr₂ = encNextTr tr₂ r.alice s₁ stA₁ cl₁ (tr₂.length + 2) ∧
      m₂.next tr₃ = encNextTr tr₃ r.alice s₂ stA₁' cl₂ (tr₃.length + 2) ∧
      m₄.next tr₄ = iniAliceStartTr tr₄ r.alice r.bob o₂ ∧
      m₅.next tr₅ = encNextTr tr₅ r.alice s₅ stA₂ cl₅ (tr₅.length + 2) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 0 35) (m₀.vis tr₁) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b1 (m₁.vis tr₂) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b2 (m₂.vis tr₃) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 40 3) (m₃.vis tr_bob) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (seg 43 35) (m₄.vis tr₄) ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) b5 (m₅.vis tr₅) := by
  obtain ⟨pre₀, mid₁, mid₂, mid₃, mid₄, mid₅, post₅, m₀, m₁, m₂, m₃, m₄, m₅, hms', hpre₀, hmid₁, hmid₂, hmid₃, hmid₄, hmid₅, hpost₅,
    hvis₀, hvis₁, hvis₂, hvis₃, hvis₄, hvis₅⟩ := decomp81_moves hc1 hc2 hc5 hmp
  obtain ⟨hb₁, hb₄, sh₁, sh₄, s₁, s₂, s₅, rfl, rfl, rfl, rfl, rfl,
    htr₁_eq, htr₂_eq, htr₃_eq, htr₄_eq, htr₅_eq, hnext₀, hnext₁, hnext₂, hnext₄, hnext₅⟩ :=
    WsIdx1Prefix81Enum.decomp81_links_pin hms' hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅
      (fun _ _ _ _ _ _ h => not_aliceStart_of_vis_seg40 (h ▸ hvis₃))
      (fun _ _ _ _ _ h => not_encrypt_of_vis_seg40 (h ▸ hvis₃)) hlinks
  rw [← htr₁_eq] at hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hvis₀ hvis₁ hvis₂ hvis₃ hvis₄ hvis₅
  rw [← htr₂_eq] at hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hvis₁ hvis₂ hvis₃ hvis₄ hvis₅
  rw [← htr₃_eq] at hmid₃ hmid₄ hmid₅ hpost₅ hvis₂ hvis₃ hvis₄ hvis₅
  rw [← htr₄_eq] at hmid₅ hpost₅ hvis₄ hvis₅
  rw [← htr₅_eq] at hpost₅ hvis₅
  exact ⟨pre₀, mid₁, mid₂, mid₃, mid₄, mid₅, post₅, m₃, hb₁, hb₄, sh₁, sh₄, s₁, s₂, s₅, hms', htr₁_eq, htr₂_eq, htr₃_eq, htr₄_eq, htr₅_eq, hpre₀, hmid₁, hmid₂, hmid₃, hmid₄, hmid₅, hpost₅, hnext₀, hnext₁, hnext₂, hnext₄, hnext₅, hvis₀, hvis₁, hvis₂, hvis₃, hvis₄, hvis₅⟩
theorem split81_draw_pins_raw {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : gamma compI0 S g (randTerm tr₁.length 32) = rngAt 1 ∧ gamma compI0 S g (randTerm (tr₁.length + 2) 32) = rngAt 34 ∧ gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1 ∧ gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (rngAt 36).inits ∧ (cl₁ ≠ 0 → gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (rngAt 36).inits.tail) ∧ gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2 ∧ gamma compI0 S g (randTerm (tr₃.length + 1) cl₂) ∈ cliCoins2Fast.inits ∧ (cl₂ ≠ 0 → gamma compI0 S g (randTerm (tr₃.length + 1) cl₂) ∈ cliCoins2Fast.inits.tail) ∧ gamma compI0 S g (randTerm tr₄.length 32) = rngAt 44 ∧ gamma compI0 S g (randTerm (tr₄.length + 2) 32) = rngAt 77 ∧ gamma compI0 S g (randTerm tr₅.length 32) = compAesPt3 ∧ gamma compI0 S g (randTerm (tr₅.length + 1) cl₅) ∈ (rngAt 79).inits ∧ (cl₅ ≠ 0 → gamma compI0 S g (randTerm (tr₅.length + 1) cl₅) ∈ (rngAt 79).inits.tail) := by
  obtain ⟨b1, b2, b5, hc1, hc2, hc5, hmp_comp⟩ := hinv.mp.2.2.2.2.2
  have hmp := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp_comp
  obtain ⟨pre₀, mid₁, mid₂, mid₃, mid₄, mid₅, post₅, m₃, hb₁, hb₄, sh₁, sh₄, s₁, s₂, s₅, _hms', _htr₁, _htr₂, _htr₃, _htr₄, _htr₅, _hpre₀, _hmid₁, _hmid₂, _hmid₃, _hmid₄, _hmid₅, _hpost₅,
    hm₀, hm₁, hm₂, hm₄, hm₅, hvis₀, hvis₁, hvis₂, _hvis₃, hvis₄, hvis₅⟩ := decomp81_of_mp_links hc1 hc2 hc5 hmp hlinks
  let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let o₂ := CompPrefixInvAlice.iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  have hvis₀' : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bundle0 :: call0Rng) (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ r.alice r.bob o₁) hb₁) := by
    rw [seg0_35_eq, aliceStart_vis_eq, hm₀] at hvis₀
    have halice_len : (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ r.alice r.bob o₁) hb₁).length = 35 := by rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr]; simp [kyberCoinEntries]
    have htot := hvis₀.length_eq
    have hlhs : (.recv bundle0 :: call0Rng : List MachineEvent).length = 35 := by simp [call0Rng_length]
    rw [hlhs, List.length_take, halice_len] at htot
    rwa [List.take_of_length_le (by rw [halice_len]; omega)] at hvis₀
  obtain ⟨hek₁_pin, hdhs₁_pin⟩ := aliceVis_draws_pin_gen hvis₀' call0Rng_take_1_bytes call0Rng_drop_33_bytes; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38.encrypt_vis_eq, hm₁] at hvis₁; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38.encrypt_vis_eq, hm₂] at hvis₂
  have hvis₄' : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv (wireAt 43) :: call4Rng) (aliceVis tr₄ (CompPrefixInvAlice.iniAliceStartTr tr₄ r.alice r.bob o₂) hb₄) := by
    rw [seg43_35_eq, aliceStart_vis_eq, hm₄] at hvis₄
    have halice_len : (aliceVis tr₄ (CompPrefixInvAlice.iniAliceStartTr tr₄ r.alice r.bob o₂) hb₄).length = 35 := by rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr]; simp [kyberCoinEntries]
    have htot := hvis₄.length_eq
    have hlhs : (.recv (wireAt 43) :: call4Rng : List MachineEvent).length = 35 := by simp [call4Rng_length]
    rw [hlhs, List.length_take, halice_len] at htot
    rwa [List.take_of_length_le (by rw [halice_len]; omega)] at hvis₄
  obtain ⟨hek₂_pin, hdhs₂_pin⟩ := aliceVis_draws_pin_gen hvis₄' call4Rng_take_1_bytes call4Rng_drop_33_bytes; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38.encrypt_vis_eq, hm₅] at hvis₅
  have hc1' : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1 := seg35_3_eq ▸ hc1
  have hc5' : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] b5 := seg78_3_eq ▸ hc5
  obtain ⟨hpt₁_raw, hc₁_mem, hc₁_ne⟩ := encVis_coinSplit_pins hc1' hvis₁
  obtain ⟨hpt₂_raw, hc₂_mem, hc₂_ne⟩ := encVis_coinSplit_pins hc2 hvis₂
  obtain ⟨hpt₅_raw, hc₅_mem, hc₅_ne⟩ := encVis_coinSplit_pins hc5' hvis₅
  exact ⟨hek₁_pin, hdhs₁_pin, hpt₁_raw.trans ptAt35_eq_compAesPt1, hc₁_mem, hc₁_ne, hpt₂_raw.trans ptAt38_eq_compAesPt2, hc₂_mem, hc₂_ne, hek₂_pin, hdhs₂_pin, hpt₅_raw.trans ptAt78_eq_compAesPt3, hc₅_mem, hc₅_ne⟩
theorem split81DrawPinsOwn' : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → RVal (gamma compI0 S g (randTerm tr₁.length 32)) ∧ RVal (gamma compI0 S g (randTerm (tr₁.length + 2) 32)) ∧ gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1 ∧ RVal (gamma compI0 S g (randTerm (tr₂.length + 1) cl₁)) ∧ gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2 ∧ RVal (gamma compI0 S g (randTerm (tr₃.length + 1) cl₂)) ∧ RVal (gamma compI0 S g (randTerm tr₄.length 32)) ∧ RVal (gamma compI0 S g (randTerm (tr₄.length + 2) 32)) ∧ gamma compI0 S g (randTerm tr₅.length 32) = compAesPt3 ∧ RVal (gamma compI0 S g (randTerm (tr₅.length + 1) cl₅)) := by intro r S g _p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ _hfits _hp hinv hlinks; obtain ⟨hek₁, hdhs₁, hpt₁, hc₁, _, hpt₂, hc₂, _, hek₂, hdhs₂, hpt₅, hc₅, _⟩ := split81_draw_pins_raw hinv hlinks; exact ⟨hek₁ ▸ rVal_rngAt1, hdhs₁ ▸ rVal_rngAt34, hpt₁, rVal_rngAt36_inits _ hc₁, hpt₂, rVal_cliCoins2Fast_inits _ hc₂, hek₂ ▸ rVal_rngAt44, hdhs₂ ▸ rVal_rngAt77, hpt₅, rVal_rngAt79_inits _ hc₅⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
