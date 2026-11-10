/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
import Computational.Proofs.CryptoGames.FSAEAD.HybridLazy
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Final
public import Computational.Proofs.CryptoGames.AEAD.PrimitivesProofDefs
public import Computational.Proofs.CryptoGames.FSAEAD.HybridProofDefs
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs

/-!
# Initial Hybrid Equivalence for ACD19 Theorem 5

**Checked by Lean.**

Relates the real `fromAEADPRG` FS-AEAD game to the initial main-chain and lookahead-chain hybrids
`hybridA … 0 false A` and `hybridA … 0 true A` via deterministic PRG key-schedule evaluation and
two- and three-way state bisimulations.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.FSAEAD.Thm5.Ends

variable {CK MK AD M C : Type}

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C
local notation "SP" => StateT (HSt CK MK AD M C) ProbComp
local notation "RState" => FSAEAD.State (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)
local notation "GameM" => StateT RState ProbComp

/-! ## Deterministic PRG chain schedule -/

section ChainHelpers

variable (G : ℕ → PRGScheme CK (CK × MK))

/-- Message key generated at 0-based chain position `p` from initial seed `k`. -/
def keyAt (k : CK) (p : ℕ) : MK := ((G p).gen (chainFrom G 0 k p)).2

/-- First `n` message keys generated from initial seed `k`. -/
def keysUpTo (k : CK) (n : ℕ) : List MK := (List.range n).map (keyAt G k)

/-- Skipped `(index, key)` pairs for 1-based message indices `sk`. -/
def skippedPairs (k : CK) (sk : List ℕ) : List (ℕ × MK) :=
  sk.map fun i => (i, keyAt G k (i - 1))

@[simp] theorem chainFrom_zero (p : ℕ) (w : CK) : chainFrom G p w 0 = w := rfl

@[simp] theorem chainFrom_succ (p : ℕ) (w : CK) (n : ℕ) :
    chainFrom G p w (n + 1) = ((G (p + n)).gen (chainFrom G p w n)).1 := rfl

theorem chainFrom_add (w : CK) (a b : ℕ) :
    chainFrom G 0 w (a + b) = chainFrom G a (chainFrom G 0 w a) b := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [Nat.add_succ, chainFrom_succ, Nat.zero_add, ih]

@[simp] theorem keysUpTo_zero (k : CK) : keysUpTo G k 0 = [] := rfl

theorem keysUpTo_succ (k : CK) (n : ℕ) :
    keysUpTo G k (n + 1) = keysUpTo G k n ++ [keyAt G k n] := by
  simp [keysUpTo, List.range_succ]

@[simp] theorem keysUpTo_length (k : CK) (n : ℕ) : (keysUpTo G k n).length = n := by
  simp [keysUpTo]

theorem keysUpTo_getElem? (k : CK) (n p : ℕ) (hp : p < n) :
    (keysUpTo G k n)[p]? = some (keyAt G k p) := by
  simp [keysUpTo, hp]

@[simp] theorem skippedPairs_nil (k : CK) : skippedPairs G k [] = [] := rfl

@[simp] theorem skippedPairs_cons (k : CK) (i : ℕ) (sk : List ℕ) :
    skippedPairs G k (i :: sk) = (i, keyAt G k (i - 1)) :: skippedPairs G k sk := rfl

@[simp] theorem skippedPairs_append (k : CK) (sk₁ sk₂ : List ℕ) :
    skippedPairs G k (sk₁ ++ sk₂) = skippedPairs G k sk₁ ++ skippedPairs G k sk₂ := by
  simp [skippedPairs]

theorem lookup_skippedPairs (k : CK) (sk : List ℕ) (i : ℕ) :
    (skippedPairs G k sk).lookup i =
      if sk.contains i then some (keyAt G k (i - 1)) else none := by
  induction sk with
  | nil => rfl
  | cons j sk ih =>
    simp only [skippedPairs_cons, List.lookup_cons, List.contains_cons]
    cases h : (i == j)
    · simpa using ih
    · have hij : i = j := beq_iff_eq.mp h
      subst hij
      simp

theorem filter_skippedPairs (k : CK) (sk : List ℕ) (i : ℕ) :
    (skippedPairs G k sk).filter (·.1 != i) = skippedPairs G k (sk.filter (· != i)) := by
  induction sk with
  | nil => rfl
  | cons j sk ih =>
    simp only [skippedPairs_cons, List.filter_cons]
    split <;> simp [ih]

theorem skipKeys_skippedPairs (k : CK) :
    ∀ (n j : ℕ) (sk : List ℕ),
      skipKeys G n (chainFrom G 0 k j) j (skippedPairs G k sk) =
        (chainFrom G 0 k (j + n), skippedPairs G k ((List.range' (j + 1) n).reverse ++ sk))
  | 0, j, sk => by simp [skipKeys]
  | n + 1, j, sk => by
    simp only [skipKeys]
    have h1 : ((G j).gen (chainFrom G 0 k j)).1 = chainFrom G 0 k (j + 1) := by
      simp [chainFrom]
    have h2 : ((j + 1, ((G j).gen (chainFrom G 0 k j)).2) :: skippedPairs G k sk) =
        skippedPairs G k ((j + 1) :: sk) := by
      simp [skippedPairs, keyAt]
    rw [h1, h2, skipKeys_skippedPairs k n (j + 1) ((j + 1) :: sk)]
    have hj : j + 1 + n = j + (n + 1) := by omega
    rw [hj, List.range'_succ, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem skipKeys_eq_newSkipped (k : CK) (iB i : ℕ) (sk : List ℕ) (hlt : iB < i) :
    skipKeys G (i - iB - 1) (chainFrom G 0 k iB) iB (skippedPairs G k sk) =
      (chainFrom G 0 k (i - 1), skippedPairs G k (newSkipped iB i ++ sk)) := by
  rw [skipKeys_skippedPairs]
  have h : iB + (i - iB - 1) = i - 1 := by omega
  rw [h, newSkipped]

theorem filterMap_skippedPairs (k : CK) (n : ℕ) (p : ℕ → Bool) (sk : List ℕ)
    (hsk : ∀ i ∈ sk, p i = true ∧ 1 ≤ i ∧ i ≤ n) :
    (sk.filter p).filterMap (fun i => ((keysUpTo G k n)[i - 1]?).map (i, ·)) =
      skippedPairs G k sk := by
  induction sk with
  | nil => rfl
  | cons i sk ih =>
    rcases hsk i (by simp) with ⟨hp, h1, hn⟩
    have hlt : i - 1 < n := by omega
    simp only [List.filter_cons_of_pos hp, List.filterMap_cons,
      keysUpTo_getElem? G k n (i - 1) hlt, Option.map_some, skippedPairs_cons]
    congr 1
    exact ih fun j hj => hsk j (by simp [hj])

end ChainHelpers

/-! ## Deterministic evaluation from `.seed` -/

section SeedEval

variable (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- Well-formedness of a hybrid state whose keys and slot come deterministically from seed `k`. -/
structure WFSeed (k : CK) (s : St) : Prop where
  keys_eq : s.1.keys = keysUpTo G k s.1.keys.length
  slot_eq : s.2 = .seed (chainFrom G 0 k s.1.keys.length)

theorem wfSeed_hInit (k : CK) (b : Bool) :
    WFSeed G k (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b (.seed k)) :=
  ⟨rfl, rfl⟩

theorem wfSeed_modifyH {k : CK} {s : St} (hs : WFSeed G k s) {st' : HS}
    (hf : st'.keys = s.1.keys) : WFSeed G k (st', s.2) := by
  refine ⟨?_, ?_⟩
  · dsimp only; rw [hf]; exact hs.keys_eq
  · dsimp only; rw [hf, hs.slot_eq]

theorem wfSeed_of_keys_slot {k : CK} {st : HS} {n : ℕ}
    (hk : st.keys = keysUpTo G k n) :
    WFSeed G k (st, .seed (chainFrom G 0 k n)) := by
  refine ⟨?_, ?_⟩ <;> simp [hk]

variable [SampleableType MK] [SampleableType CK]

omit [SampleableType CK] in
theorem genStep_run_of_wfSeed {P : Params} {D : ℕ → ProbComp (CK × MK)} {k : CK} {s : St}
    (hs : WFSeed G k s) :
    (genStep G P D : SP Unit).run s =
      pure ((), ({ s.1 with keys := keysUpTo G k (s.1.keys.length + 1) },
        .seed (chainFrom G 0 k (s.1.keys.length + 1)))) := by
  rcases s with ⟨st, sl⟩
  rcases hs with ⟨hkeys, hsl⟩
  dsimp only at hkeys hsl ⊢
  subst hsl
  simp only [genStep, StateT.run_mk, keysUpTo_succ, chainFrom_succ, Nat.zero_add, keyAt]
  rw [← hkeys]

omit [SampleableType CK] in
theorem genN_run_of_wfSeed {P : Params} {D : ℕ → ProbComp (CK × MK)} {k : CK} :
    ∀ (n : ℕ) {s : St}, WFSeed G k s →
      (genN G P D n : SP Unit).run s =
        pure ((), ({ s.1 with keys := keysUpTo G k (s.1.keys.length + n) },
          .seed (chainFrom G 0 k (s.1.keys.length + n))))
  | 0, s, hs => by
    simp only [genN, StateT.run_pure, Nat.add_zero]
    congr 2
    rcases s with ⟨⟨⟩, sl⟩
    rcases hs with ⟨hkeys, hsl⟩
    dsimp only at hkeys hsl
    subst hsl
    rw [← hkeys]
  | n + 1, s, hs => by
    simp only [genN, StateT.run_bind, genStep_run_of_wfSeed G hs, pure_bind]
    have hs' : WFSeed G k
        ({ s.1 with keys := keysUpTo G k (s.1.keys.length + 1) },
          .seed (chainFrom G 0 k (s.1.keys.length + 1))) := by
      refine ⟨?_, ?_⟩ <;> simp
    rw [genN_run_of_wfSeed n hs']
    simp only [keysUpTo_length, Nat.add_right_comm _ 1 n, Nat.add_assoc]

omit [SampleableType CK] in
theorem genUpTo_run_of_wfSeed {P : Params} {D : ℕ → ProbComp (CK × MK)} {k : CK} {s : St}
    (hs : WFSeed G k s) (i : ℕ) :
    (genUpTo G P D i : SP Unit).run s =
      pure ((), ({ s.1 with keys := keysUpTo G k (max s.1.keys.length i) },
        .seed (chainFrom G 0 k (max s.1.keys.length i)))) := by
  simp only [genUpTo, StateT.run_bind, getH_run, pure_bind, genN_run_of_wfSeed G _ hs]
  have hmax : s.1.keys.length + (i - s.1.keys.length) = max s.1.keys.length i := by omega
  rw [hmax]

omit [SampleableType CK] in
theorem genUpTo_run_of_le {P : Params} {D : ℕ → ProbComp (CK × MK)} {k : CK} {s : St}
    (hs : WFSeed G k s) {i : ℕ} (hi : i ≤ s.1.keys.length) :
    (genUpTo G P D i : SP Unit).run s = pure ((), s) := by
  rw [genUpTo_run_of_wfSeed G hs i, Nat.max_eq_left hi, ← hs.keys_eq, ← hs.slot_eq,
    hstate_self_keys]

omit [SampleableType MK] [SampleableType CK] in
theorem wfSeed_after_genUpTo {k : CK} {s : St} (i : ℕ) :
    WFSeed G k ({ s.1 with keys := keysUpTo G k (max s.1.keys.length i) },
      .seed (chainFrom G 0 k (max s.1.keys.length i))) := by
  refine ⟨?_, ?_⟩ <;> simp

omit [SampleableType MK] in
theorem reveal_run_of_wfSeed {k : CK} {s : St} (hs : WFSeed G k s) :
    (reveal : SP CK).run s = pure (chainFrom G 0 k s.1.keys.length, s) := by
  rcases s with ⟨st, sl⟩
  rcases hs with ⟨_, hsl⟩
  dsimp only at hsl ⊢
  subst hsl
  rfl

omit [SampleableType MK] in
theorem senderKey_run_of_wfSeed {k : CK} {s : St} (hs : WFSeed G k s)
    (huncorr : s.1.senderCorruptedAt = none → s.1.keys.length = s.1.lastSentIdx)
    (hcorr : (s.1.senderCorruptedAt = none ∧ s.1.corrKey = none) ∨
      ∃ c, s.1.senderCorruptedAt = some c ∧ c ≤ s.1.lastSentIdx ∧
        s.1.corrKey = some (chainFrom G 0 k c)) :
    (senderKey G : SP CK).run s = pure (chainFrom G 0 k s.1.lastSentIdx, s) := by
  unfold senderKey
  simp only [StateT.run_bind, getH_run, pure_bind]
  rcases hcorr with ⟨hca, hck⟩ | ⟨c, hca, hle, hck⟩
  · simp only [hca, hck, reveal_run_of_wfSeed G hs, huncorr hca]
  · simp only [hca, hck, StateT.run_pure, ← chainFrom_add G k c (s.1.lastSentIdx - c),
      Nat.add_sub_of_le hle]

omit [SampleableType MK] [SampleableType CK] in
theorem kind_hp_zero_of_pos (la : Bool) (st : HS) {i : ℕ} (hi : 1 ≤ i) :
    kind (hp 0 0 la) (none : Option (SpecialOps AD M C ProbComp)) st i = .real := by
  simp [kind, hp]
  omega

omit [SampleableType MK] [SampleableType CK] in
theorem encIdx_run_of_wfSeed (la : Bool) {k : CK} {s : St} (hs : WFSeed G k s)
    {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ s.1.keys.length) (a : AD) (msg : M) :
    (encIdxWith ideal ae (hp 0 0 la) (none : Option (SpecialOps AD M C ProbComp)) i a msg).run s =
      pure (ae.enc (keyAt G k (i - 1)) (i, a) msg, s) := by
  have hlt : i - 1 < s.1.keys.length := by omega
  have hk : s.1.keys[i - 1]? = some (keyAt G k (i - 1)) := by
    rw [hs.keys_eq, keysUpTo_getElem? G k s.1.keys.length (i - 1) hlt]
  unfold encIdxWith
  simp [kind_hp_zero_of_pos la s.1 hi1, hk]

omit [SampleableType MK] [SampleableType CK] in
theorem decIdx_none_run_of_wfSeed (la : Bool) {k : CK} {s : St} (hs : WFSeed G k s)
    {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ s.1.keys.length) (a : AD) (e : C) :
    (decIdx ae (hp 0 0 la) (none : Option (SpecialOps AD M C ProbComp)) none i a e).run s =
      pure (ae.dec (keyAt G k (i - 1)) (i, a) e, s) := by
  have hlt : i - 1 < s.1.keys.length := by omega
  have hk : s.1.keys[i - 1]? = some (keyAt G k (i - 1)) := by
    rw [hs.keys_eq, keysUpTo_getElem? G k s.1.keys.length (i - 1) hlt]
  unfold decIdx
  simp [kind_hp_zero_of_pos la s.1 hi1, hk]

omit [SampleableType MK] [SampleableType CK] in
theorem decIdx_some_run (P : Params) (msg : M) (i : ℕ) (a : AD) (e : C) (s : St) :
    (decIdx ae P (none : Option (SpecialOps AD M C ProbComp)) (some msg) i a e).run s =
      pure (some msg, s) := rfl

end SeedEval

/-! ## Post-lookahead-forgery regime -/

section Regime2

variable [SampleableType MK] [SampleableType CK] (ideal : ℕ × AD → ProbComp C)
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

theorem ended_lf_simulateQ (P : Params) (D : ℕ → ProbComp (CK × MK))
    {α : Type} (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α) :
    ∀ {sL : St} {z : α × St},
      sL.1.ended = true → sL.1.lf = true →
      z ∈ support ((simulateQ (implWith ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp))) oa).run sL) →
      z.2.1.ended = true ∧ z.2.1.lf = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sL z hend hlf hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact ⟨hend, hlf⟩
  | query_bind t k ih =>
    intro sL z hend hlf hz
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, s₁⟩, h₁, h₂⟩
    rcases t with n | (((((q | q) | q) | q) | q) | q)
    · have hs₁ : s₁ = sL := mem_support_sampleH h₁
      subst hs₁; exact ih u hend hlf h₂
    · change (u, s₁) ∈ support ((transmitHWith ideal ae G P D none q).run sL) at h₁
      simp [transmitHWith, hend] at h₁
      rcases h₁ with ⟨_, rfl⟩; exact ih _ hend hlf h₂
    · change (u, s₁) ∈ support ((challengeHWith ideal ae G P D none q).run sL) at h₁
      simp [challengeHWith, hend] at h₁
      rcases h₁ with ⟨_, rfl⟩; exact ih _ hend hlf h₂
    · change (u, s₁) ∈ support ((corruptSenderH G P q).run sL) at h₁
      simp [corruptSenderH, hend] at h₁
      rcases h₁ with ⟨_, rfl⟩; exact ih _ hend hlf h₂
    · change (u, s₁) ∈ support ((corruptReceiverH G P q).run sL) at h₁
      simp [corruptReceiverH, hend] at h₁
      rcases h₁ with ⟨_, rfl⟩; exact ih _ hend hlf h₂
    · rcases q with ⟨a, e⟩
      change (u, s₁) ∈ support ((deliverH ae G maxSkip P D none (a, e)).run sL) at h₁
      simp [deliverH, hend] at h₁
      rcases h₁ with ⟨_, rfl⟩; exact ih _ hend hlf h₂
    · rcases q with ⟨a, e⟩
      change (u, s₁) ∈ support ((injectH ae G maxSkip P D none (a, e)).run sL) at h₁
      simp [injectH, hend] at h₁
      rcases h₁ with ⟨_, rfl⟩; exact ih _ hend hlf h₂

theorem evalDist_runL_eq_one_of_ended_lf (P : Params) (D : ℕ → ProbComp (CK × MK))
    {α : Type} (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α)
    (f : α × St → ProbComp Bool) (hf : ∀ z : α × St, z.2.1.lf = true → 𝒟[f z] = 𝒟[(pure true : ProbComp Bool)])
    {sL : St} (hend : sL.1.ended = true) (hlf : sL.1.lf = true) :
    𝒟[(simulateQ (implWith ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp))) oa).run sL >>= f]
      {true} = 1 := by
  have heq : 𝒟[(simulateQ (implWith ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp))) oa).run sL >>= f] =
      𝒟[(pure true : ProbComp Bool)] := by
    rw [evalDist_bind_congr_of_support _ _ (fun _ => pure true)]
    · exact OracleComp.evalDist_bind_const _ _
    · intro z hz
      exact hf z (ended_lf_simulateQ ideal ae G maxSkip P D oa hend hlf hz).2
  rw [heq]
  simp

end Regime2

/-! ## Deterministic receive step equations -/

section ReceiveSteps

variable [SampleableType MK] [SampleableType CK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

omit [SampleableType MK] [SampleableType CK] in
theorem receive_real_of_contains (k : CK) (rcv : ℕ) (sk : List ℕ) (a : AD) (i : ℕ) (e : C)
    (hcont : i ∈ sk) :
    (fromAEADPRG ae G maxSkip).receive ⟨chainFrom G 0 k rcv, rcv, skippedPairs G k sk⟩ a (i, e) =
      (ae.dec (keyAt G k (i - 1)) (i, a) e).map fun m =>
        (⟨chainFrom G 0 k rcv, rcv, skippedPairs G k (sk.filter (· != i))⟩, i, m) := by
  simp [fromAEADPRG, lookup_skippedPairs, hcont, filter_skippedPairs]

omit [SampleableType MK] [SampleableType CK] in
theorem receive_real_of_out_of_window (k : CK) (rcv : ℕ) (sk : List ℕ) (a : AD) (i : ℕ) (e : C)
    (hcont : i ∉ sk) (hout : i ≤ rcv ∨ maxSkip < i - rcv - 1) :
    (fromAEADPRG ae G maxSkip).receive ⟨chainFrom G 0 k rcv, rcv, skippedPairs G k sk⟩ a (i, e) =
      none := by
  simp [fromAEADPRG, lookup_skippedPairs, hcont, hout]

omit [SampleableType MK] [SampleableType CK] in
theorem receive_real_of_in_window (k : CK) (rcv : ℕ) (sk : List ℕ) (a : AD) (i : ℕ) (e : C)
    (hcont : i ∉ sk) (hin : ¬ (i ≤ rcv ∨ maxSkip < i - rcv - 1)) :
    (fromAEADPRG ae G maxSkip).receive ⟨chainFrom G 0 k rcv, rcv, skippedPairs G k sk⟩ a (i, e) =
      (ae.dec (keyAt G k (i - 1)) (i, a) e).map fun m =>
        (⟨chainFrom G 0 k i, i, skippedPairs G k (newSkipped rcv i ++ sk)⟩, i, m) := by
  have hlt : rcv < i := by omega
  have hgen : (G (i - 1)).gen (chainFrom G 0 k (i - 1)) = (chainFrom G 0 k i, keyAt G k (i - 1)) := by
    have hi : (i - 1) + 1 = i := by omega
    ext
    · rw [← hi, chainFrom_succ, Nat.zero_add]; rfl
    · rfl
  simp [fromAEADPRG, lookup_skippedPairs, hcont, hin, skipKeys_eq_newSkipped G k rcv i sk hlt, hgen]

omit [SampleableType CK] in
theorem receiveH_some_run_of_contains (P : Params) (D : ℕ → ProbComp (CK × MK))
    (msg : M) (a : AD) (i : ℕ) (e : C) {s : St} (hcont : i ∈ s.1.skipped) :
    (receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) (some msg) a (i, e)).run s =
      pure (some (i, msg), ({ s.1 with skipped := s.1.skipped.filter (· != i) }, s.2)) := by
  unfold receiveH decIdx
  simp [hcont]

omit [SampleableType CK] in
theorem receiveH_some_run_of_out_of_window (P : Params) (D : ℕ → ProbComp (CK × MK))
    (msg : M) (a : AD) (i : ℕ) (e : C) {s : St}
    (hcont : i ∉ s.1.skipped)
    (hout : i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1) :
    (receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) (some msg) a (i, e)).run s =
      pure (none, s) := by
  unfold receiveH
  simp [hcont, hout]

omit [SampleableType CK] in
theorem receiveH_some_run_of_in_window (P : Params) (D : ℕ → ProbComp (CK × MK))
    {k : CK} {s : St} (hs : WFSeed G k s) (msg : M) (a : AD) {i : ℕ} (e : C)
    (hcont : i ∉ s.1.skipped)
    (hin : ¬ (i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1))
    (hisent : i ≤ s.1.lastSentIdx) (hkeys : s.1.lastSentIdx ≤ s.1.keys.length) :
    (receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) (some msg) a (i, e)).run s =
      pure (some (i, msg), ({ s.1 with skipped := newSkipped s.1.receiverIdx i ++ s.1.skipped }, s.2)) := by
  have hlt : ¬ s.1.lastSentIdx < i := by omega
  have hle : i ≤ s.1.keys.length := by omega
  have hcontF : s.1.skipped.contains i = false := by simpa using hcont
  have hcondF : (!P.la && decide (s.1.lastSentIdx < i) && !s.1.isCompromised i) = false := by
    simp [hlt]
  unfold receiveH
  simp only [StateT.run_bind, getH_run, pure_bind, hcontF, Bool.false_eq_true, ↓reduceIte, hin,
    hcondF, genUpTo_run_of_le G hs hle]
  change (do
    let msg? ← decIdx ae P (none : Option (SpecialOps AD M C ProbComp)) (some msg) i a e
    match msg? with
    | some msg =>
      modifyH fun st' => { st' with skipped := newSkipped s.1.receiverIdx i ++ st'.skipped }
      return some (i, msg)
    | none => return none).run s = _
  rw [StateT.run_bind, decIdx_some_run, pure_bind]
  simp

theorem receiveH_none_run_of_contains (la : Bool) {k : CK} {s : St} (hs : WFSeed G k s)
    (a : AD) {i : ℕ} (e : C) (hcont : i ∈ s.1.skipped)
    (hi1 : 1 ≤ i) (hi2 : i ≤ s.1.keys.length) :
    (receiveH ae G maxSkip (hp 0 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) none a (i, e)).run s =
      match ae.dec (keyAt G k (i - 1)) (i, a) e with
      | none => pure (none, s)
      | some msg =>
        pure (some (i, msg), ({ s.1 with skipped := s.1.skipped.filter (· != i) }, s.2)) := by
  have hcontT : s.1.skipped.contains i = true := List.contains_iff_mem.mpr hcont
  unfold receiveH
  simp only [StateT.run_bind, getH_run, pure_bind, hcontT, ↓reduceIte,
    decIdx_none_run_of_wfSeed ae G la hs hi1 hi2]
  cases ae.dec (keyAt G k (i - 1)) (i, a) e <;> simp

omit [SampleableType CK] in
theorem receiveH_none_run_of_out_of_window (P : Params) (D : ℕ → ProbComp (CK × MK))
    (a : AD) (i : ℕ) (e : C) {s : St}
    (hcont : i ∉ s.1.skipped)
    (hout : i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1) :
    (receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) none a (i, e)).run s =
      pure (none, s) := by
  unfold receiveH
  simp [hcont, hout]

omit [SampleableType CK] in
theorem receiveH_none_run_of_lookahead_reject (P : Params) (D : ℕ → ProbComp (CK × MK))
    (a : AD) (i : ℕ) (e : C) {s : St}
    (hcont : i ∉ s.1.skipped)
    (hin : ¬ (i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1))
    (hlarej : (P.la = false ∧ s.1.lastSentIdx < i) ∧ s.1.isCompromised i = false) :
    (receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) none a (i, e)).run s =
      pure (none, s) := by
  unfold receiveH
  simp [hcont, hin, hlarej.1.1, hlarej.1.2, hlarej.2]

theorem receiveH_none_run_of_in_window (la : Bool) {k : CK} {s : St} (hs : WFSeed G k s)
    (a : AD) {i : ℕ} (e : C)
    (hcont : i ∉ s.1.skipped)
    (hin : ¬ (i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1))
    (hlarej : ¬ ((la = false ∧ s.1.lastSentIdx < i) ∧ s.1.isCompromised i = false)) :
    (receiveH ae G maxSkip (hp 0 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) none a (i, e)).run s =
      let s₁ : St := ({ s.1 with keys := keysUpTo G k (max s.1.keys.length i) },
        .seed (chainFrom G 0 k (max s.1.keys.length i)))
      match ae.dec (keyAt G k (i - 1)) (i, a) e with
      | none => pure (none, s₁)
      | some msg =>
        pure (some (i, msg), ({ s₁.1 with skipped := newSkipped s.1.receiverIdx i ++ s.1.skipped }, s₁.2)) := by
  have hi1 : 1 ≤ i := by omega
  have hcontF : s.1.skipped.contains i = false := by simpa using hcont
  let s₁ : St := ({ s.1 with keys := keysUpTo G k (max s.1.keys.length i) },
    .seed (chainFrom G 0 k (max s.1.keys.length i)))
  have hs₁ : WFSeed G k s₁ := wfSeed_after_genUpTo G i
  have hi2 : i ≤ s₁.1.keys.length := by simp [s₁]
  have hcond : ((!la && decide (s.1.lastSentIdx < i) && !s.1.isCompromised i) = true) ↔
      ((la = false ∧ s.1.lastSentIdx < i) ∧ s.1.isCompromised i = false) := by
    simp
  have hcondF : (!la && decide (s.1.lastSentIdx < i) && !s.1.isCompromised i) = false :=
    Bool.eq_false_iff.mpr (mt hcond.mp hlarej)
  unfold receiveH
  simp only [StateT.run_bind, getH_run, pure_bind, hcontF, Bool.false_eq_true, ↓reduceIte, hin,
    hp_la, hcondF, genUpTo_run_of_wfSeed G hs i]
  change (do
    let msg? ← decIdx ae (hp 0 0 la) (none : Option (SpecialOps AD M C ProbComp)) none i a e
    match msg? with
    | some msg =>
      modifyH fun st' => { st' with skipped := newSkipped s.1.receiverIdx i ++ st'.skipped }
      return some (i, msg)
    | none => return none).run s₁ = _
  rw [StateT.run_bind, decIdx_none_run_of_wfSeed ae G la hs₁ hi1 hi2, pure_bind]
  cases ae.dec (keyAt G k (i - 1)) (i, a) e <;> simp [s₁]

end ReceiveSteps

/-! ## Post-corruption two-way bisimulation -/

section Regime1b

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

abbrev implR :
    QueryImpl (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      GameM :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget GameM +
    oracleImpl (fromAEADPRG ae G maxSkip)

abbrev implH (la : Bool) :
    QueryImpl (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      SP :=
  implWith ideal ae G maxSkip (hp 0 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp))

def mkRState (k : CK) (st : HS) : RState :=
  { b := st.b
    senderState := ⟨chainFrom G 0 k st.lastSentIdx, st.lastSentIdx⟩
    receiverState := ⟨chainFrom G 0 k st.receiverIdx, st.receiverIdx, skippedPairs G k st.skipped⟩
    lastSentIdx := st.lastSentIdx
    senderCorruptedAt := st.senderCorruptedAt
    receiverIdx := st.receiverIdx
    ended := st.ended
    win := st.win
    inTransit := st.inTransit
    challengesInTransit := st.challengesInTransit }

def uncompBound (st : HS) : ℕ :=
  st.senderCorruptedAt.getD st.lastSentIdx

structure WFState (k : CK) (st : HS) : Prop where
  sent_le_keys : st.lastSentIdx ≤ st.keys.length
  rcv_le_keys : st.receiverIdx ≤ st.keys.length
  keys_eq_sent_of_uncorr : st.senderCorruptedAt = none → st.keys.length = st.lastSentIdx
  rcv_le_sent_of_uncorr : st.senderCorruptedAt = none → st.receiverIdx ≤ st.lastSentIdx
  corr_inv :
    (st.senderCorruptedAt = none ∧ st.corrKey = none) ∨
    ∃ c, st.senderCorruptedAt = some c ∧ c ≤ st.lastSentIdx ∧
      st.corrKey = some (chainFrom G 0 k c)
  skipped_bounds : ∀ i ∈ st.skipped, 1 ≤ i ∧ i < st.receiverIdx
  inTransit_valid : ∀ r ∈ st.inTransit,
    1 ≤ r.idx ∧ r.idx ≤ st.lastSentIdx ∧
    r.ct = (r.idx, ae.enc (keyAt G k (r.idx - 1)) (r.idx, r.ad) r.msg)
  pending_inTransit : ∀ i, 1 ≤ i → i ≤ uncompBound st →
    (i ∈ st.skipped ∨ st.receiverIdx < i) → ∃ r ∈ st.inTransit, r.idx = i

structure SyncRM (k : CK) (stR : RState) (sM : St) : Prop where
  wf_seed : WFSeed G k sM
  wf_state : WFState ae G k sM.1
  stR_eq : stR = mkRState G k sM.1

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem wfState_hInit (k : CK) (b : Bool) :
    WFState ae G k (hInit b (.seed k : Slot CK MK)).1 := by
  refine ⟨by simp [hInit], by simp [hInit], fun _ => rfl, fun _ => le_rfl,
    Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro i hi; simp [hInit] at hi
  · intro r hr; simp [hInit] at hr
  · intro i hi1 hi0 _; simp [uncompBound, hInit] at hi0; omega

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem syncRM_init (k : CK) (b : Bool) :
    SyncRM ae G k (initState (fromAEADPRG ae G maxSkip) k b) (hInit b (.seed k)) :=
  ⟨wfSeed_hInit G k b, wfState_hInit ae G k b, rfl⟩

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem wfState_send {k : CK} {st : HS} (hwf : WFState ae G k st)
    (a : AD) (msg : M) (challs : List ℕ) :
    let i := st.lastSentIdx + 1
    let e := ae.enc (keyAt G k st.lastSentIdx) (i, a) msg
    WFState ae G k
      { st with
        lastSentIdx := i
        inTransit := ⟨i, a, msg, (i, e)⟩ :: st.inTransit
        challengesInTransit := challs
        keys := keysUpTo G k (max st.keys.length i) } := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, hwf.skipped_bounds, ?_, ?_⟩
  · simp
  · have := hwf.rcv_le_keys; simp; omega
  · intro huncorr
    have hk := hwf.keys_eq_sent_of_uncorr huncorr
    simp [hk]
  · intro huncorr
    have hr := hwf.rcv_le_sent_of_uncorr huncorr
    simp; omega
  · rcases hwf.corr_inv with ⟨h1, h2⟩ | ⟨c, h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨c, h1, by simp; omega, h3⟩
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨by simp, le_rfl, rfl⟩
    · rcases hwf.inTransit_valid r hr with ⟨h1, h2, h3⟩
      exact ⟨h1, by simp; omega, h3⟩
  · intro j hj1 hj2 horsk
    simp only [List.mem_cons]
    cases h : st.senderCorruptedAt with
    | none =>
      simp only [uncompBound, h, Option.getD_none] at hj2
      by_cases hjeq : j = st.lastSentIdx + 1
      · exact ⟨⟨st.lastSentIdx + 1, a, msg, (st.lastSentIdx + 1, _)⟩, Or.inl rfl, hjeq.symm⟩
      · have hjle : j ≤ uncompBound st := by simp [uncompBound, h]; omega
        rcases hwf.pending_inTransit j hj1 hjle horsk with ⟨r, hr, hidx⟩
        exact ⟨r, Or.inr hr, hidx⟩
    | some c =>
      have hjle : j ≤ uncompBound st := by simpa [uncompBound, h] using hj2
      rcases hwf.pending_inTransit j hj1 hjle horsk with ⟨r, hr, hidx⟩
      exact ⟨r, Or.inr hr, hidx⟩

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem wfState_corruptSender {k : CK} {st : HS} (hwf : WFState ae G k st)
    (w : CK) (hw : w = chainFrom G 0 k st.lastSentIdx) :
    WFState ae G k
      { st with
        senderCorruptedAt := some (st.senderCorruptedAt.getD st.lastSentIdx)
        corrKey := some (st.corrKey.getD w) } := by
  refine ⟨hwf.sent_le_keys, hwf.rcv_le_keys, by simp, by simp, ?_, hwf.skipped_bounds,
    hwf.inTransit_valid, ?_⟩
  · rcases hwf.corr_inv with ⟨h1, h2⟩ | ⟨c, h1, h2, h3⟩
    · right
      refine ⟨st.lastSentIdx, by simp [h1], le_rfl, by simp [h2, hw]⟩
    · right
      refine ⟨c, by simp [h1], h2, by simp [h3]⟩
  · intro i hi1 hi2 horsk
    have hi2' : i ≤ uncompBound st := by
      cases h : st.senderCorruptedAt <;> simpa [uncompBound, h] using hi2
    exact hwf.pending_inTransit i hi1 hi2' horsk

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem wfState_accept_contains {k : CK} {st : HS} (hwf : WFState ae G k st)
    {i : ℕ} (hcont : i ∈ st.skipped) (win' ended' lf' : Bool) :
    WFState ae G k
      (HState.removeFromTransit
        { st with
          skipped := st.skipped.filter (· != i)
          receiverIdx := max st.receiverIdx i
          win := win'
          ended := ended'
          lf := lf' } i) := by
  have hi_bounds := hwf.skipped_bounds i hcont
  have hmax : max st.receiverIdx i = st.receiverIdx := Nat.max_eq_left (le_of_lt hi_bounds.2)
  refine ⟨hwf.sent_le_keys, ?_, hwf.keys_eq_sent_of_uncorr, ?_, hwf.corr_inv, ?_, ?_, ?_⟩
  · simp [HState.removeFromTransit, hmax, hwf.rcv_le_keys]
  · intro huncorr
    simp [HState.removeFromTransit, hmax, hwf.rcv_le_sent_of_uncorr huncorr]
  · intro j hj
    simp only [HState.removeFromTransit, List.mem_filter] at hj
    simpa [HState.removeFromTransit, hmax] using hwf.skipped_bounds j hj.1
  · intro r hr
    simp only [HState.removeFromTransit, List.mem_filter] at hr
    exact hwf.inTransit_valid r hr.1
  · intro j hj1 hj2 horsk
    simp only [HState.removeFromTransit, hmax, List.mem_filter,
      bne_iff_ne, ne_eq] at horsk ⊢
    have hjne : j ≠ i := by
      rcases horsk with ⟨_, hjne⟩ | hlt
      · exact hjne
      · omega
    have horsk' : j ∈ st.skipped ∨ st.receiverIdx < j := by
      rcases horsk with ⟨hmem, _⟩ | hlt
      · exact Or.inl hmem
      · exact Or.inr hlt
    rcases hwf.pending_inTransit j hj1 hj2 horsk' with ⟨r, hr, hidx⟩
    exact ⟨r, ⟨hr, by omega⟩, hidx⟩

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem wfState_accept_in_window {k : CK} {st : HS} (hwf : WFState ae G k st)
    {i n : ℕ} (hlt : st.receiverIdx < i) (hn1 : st.keys.length ≤ n) (hn2 : i ≤ n)
    (hnh : st.senderCorruptedAt = none → n = st.lastSentIdx ∧ i ≤ st.lastSentIdx)
    (win' ended' lf' : Bool) :
    WFState ae G k
      (HState.removeFromTransit
        { st with
          keys := keysUpTo G k n
          skipped := newSkipped st.receiverIdx i ++ st.skipped
          receiverIdx := max st.receiverIdx i
          win := win'
          ended := ended'
          lf := lf' } i) := by
  have hmax : max st.receiverIdx i = i := Nat.max_eq_right (le_of_lt hlt)
  have hsent := hwf.sent_le_keys
  refine ⟨?_, ?_, ?_, ?_, hwf.corr_inv, ?_, ?_, ?_⟩
  · simp [HState.removeFromTransit]; omega
  · simp [HState.removeFromTransit, hmax, hn2]
  · intro huncorr
    simp [HState.removeFromTransit, (hnh huncorr).1]
  · intro huncorr
    simp [HState.removeFromTransit, hmax, (hnh huncorr).2]
  · intro j hj
    simp only [HState.removeFromTransit, hmax, List.mem_append,
      mem_newSkipped_iff] at hj ⊢
    rcases hj with ⟨h1, h2⟩ | hj
    · exact ⟨by omega, h2⟩
    · have := hwf.skipped_bounds j hj
      exact ⟨this.1, by omega⟩
  · intro r hr
    simp only [HState.removeFromTransit, List.mem_filter] at hr
    exact hwf.inTransit_valid r hr.1
  · intro j hj1 hj2 horsk
    simp only [HState.removeFromTransit, hmax, List.mem_append,
      mem_newSkipped_iff, List.mem_filter, bne_iff_ne, ne_eq] at horsk ⊢
    have hjne : j ≠ i := by
      rcases horsk with (⟨_, h2⟩ | hj) | h2
      · omega
      · have := (hwf.skipped_bounds j hj).2; omega
      · omega
    have horsk' : j ∈ st.skipped ∨ st.receiverIdx < j := by
      rcases horsk with (⟨h1, _⟩ | hj) | h2
      · exact Or.inr h1
      · exact Or.inl hj
      · exact Or.inr (by omega)
    rcases hwf.pending_inTransit j hj1 hj2 horsk' with ⟨r, hr, hidx⟩
    exact ⟨r, ⟨hr, by omega⟩, hidx⟩

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem transmitH_run_of_wfSeed (la : Bool) {k : CK} {s : St} (hs : WFSeed G k s) (q : AD × M) :
    (transmitHWith ideal ae G (hp 0 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s =
      if s.1.ended then pure (none, s)
      else
        let i := s.1.lastSentIdx + 1
        let e := ae.enc (keyAt G k s.1.lastSentIdx) (i, q.1) q.2
        pure (some (i, e),
          ({ s.1 with
             lastSentIdx := i
             inTransit := ⟨i, q.1, q.2, (i, e)⟩ :: s.1.inTransit
             keys := keysUpTo G k (max s.1.keys.length i) },
           Slot.seed (chainFrom G 0 k (max s.1.keys.length i)))) := by
  unfold transmitHWith
  simp only [StateT.run_bind, getH_run, pure_bind]
  cases hend : s.1.ended
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let i := s.1.lastSentIdx + 1
    let s₁ : St := ({ s.1 with keys := keysUpTo G k (max s.1.keys.length i) },
      Slot.seed (chainFrom G 0 k (max s.1.keys.length i)))
    have hs₁ : WFSeed G k s₁ := wfSeed_after_genUpTo G i
    have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ s₁.1.keys.length := by simp [s₁, i]
    rw [StateT.run_bind, genUpTo_run_of_wfSeed G hs i, pure_bind, StateT.run_bind,
      encIdx_run_of_wfSeed ideal ae G la hs₁ hi1 hi2 q.1 q.2, pure_bind]
    simp [s₁, i, hend]
  · simp

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem challengeH_run_of_wfSeed (la : Bool) {k : CK} {s : St} (hs : WFSeed G k s)
    (q : AD × M × M) :
    (challengeHWith ideal ae G (hp 0 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s =
      if s.1.ended || s.1.senderCorruptedAt.isSome then pure (none, s)
      else
        let i := s.1.lastSentIdx + 1
        let msg := if s.1.b then q.2.2 else q.2.1
        let e := ae.enc (keyAt G k s.1.lastSentIdx) (i, q.1) msg
        pure (some (i, e),
          ({ s.1 with
             lastSentIdx := i
             inTransit := ⟨i, q.1, msg, (i, e)⟩ :: s.1.inTransit
             challengesInTransit := i :: s.1.challengesInTransit
             keys := keysUpTo G k (max s.1.keys.length i) },
           Slot.seed (chainFrom G 0 k (max s.1.keys.length i)))) := by
  unfold challengeHWith
  simp only [StateT.run_bind, getH_run, pure_bind]
  cases hcond : (s.1.ended || s.1.senderCorruptedAt.isSome)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let i := s.1.lastSentIdx + 1
    let msg := if s.1.b then q.2.2 else q.2.1
    let s₁ : St := ({ s.1 with keys := keysUpTo G k (max s.1.keys.length i) },
      Slot.seed (chainFrom G 0 k (max s.1.keys.length i)))
    have hs₁ : WFSeed G k s₁ := wfSeed_after_genUpTo G i
    have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ s₁.1.keys.length := by simp [s₁, i]
    rw [StateT.run_bind, genUpTo_run_of_wfSeed G hs i, pure_bind, StateT.run_bind,
      encIdx_run_of_wfSeed ideal ae G la hs₁ hi1 hi2 q.1 msg, pure_bind]
    simp [s₁, i, msg]
  · simp

@[simp] theorem modifyGet_run {σ α : Type} {m : Type → Type} [Monad m] (f : σ → α × σ) (s : σ) :
    (modifyGet f : StateT σ m α).run s = pure (f s) := rfl

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem transmit_syncRM {k : CK} {stR : RState} {sM : St}
    (hsync : SyncRM ae G k stR sM) (q : AD × M) :
    ∃ u stR' sM',
      (transmitImpl (fromAEADPRG ae G maxSkip) q).run stR = pure (u, stR') ∧
      (transmitHWith ideal ae G (hp 0 0 false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run sM =
        pure (u, sM') ∧
      SyncRM ae G k stR' sM' ∧
      sM'.1.senderCorruptedAt = sM.1.senderCorruptedAt ∧
      sM'.1.ended = sM.1.ended := by
  rw [transmitH_run_of_wfSeed ideal ae G false hsync.wf_seed q]
  have hstR := hsync.stR_eq; subst hstR
  cases hend : sM.1.ended
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_of_keys_slot G rfl,
      wfState_send ae G hsync.wf_state q.1 q.2 sM.1.challengesInTransit, rfl⟩, rfl, hend⟩
    simp [transmitImpl, FSAEAD.transmit, mkRState, hend, fromAEADPRG, keyAt]
  · simp only [↓reduceIte]
    refine ⟨none, mkRState G k sM.1, sM, ?_, rfl, hsync, rfl, hend⟩
    simp [transmitImpl, FSAEAD.transmit, mkRState, hend]

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem challenge_syncRM {k : CK} {stR : RState} {sM : St}
    (hsync : SyncRM ae G k stR sM) (q : AD × M × M) :
    ∃ u stR' sM',
      (challengeImpl (fromAEADPRG ae G maxSkip) q).run stR = pure (u, stR') ∧
      (challengeHWith ideal ae G (hp 0 0 false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run sM =
        pure (u, sM') ∧
      SyncRM ae G k stR' sM' ∧
      sM'.1.senderCorruptedAt = sM.1.senderCorruptedAt ∧
      sM'.1.ended = sM.1.ended := by
  rw [challengeH_run_of_wfSeed ideal ae G false hsync.wf_seed q]
  have hstR := hsync.stR_eq; subst hstR
  cases hcond : (sM.1.ended || sM.1.senderCorruptedAt.isSome)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_of_keys_slot G rfl,
      wfState_send ae G hsync.wf_state q.1 (if sM.1.b then q.2.2 else q.2.1)
        ((sM.1.lastSentIdx + 1) :: sM.1.challengesInTransit), rfl⟩, rfl, rfl⟩
    have hend : sM.1.ended = false := by revert hcond; cases sM.1.ended <;> simp
    have hcorr : sM.1.senderCorruptedAt.isSome = false := by
      revert hcond; cases sM.1.ended <;> cases sM.1.senderCorruptedAt.isSome <;> simp
    simp [challengeImpl, FSAEAD.challenge, mkRState, hend, hcorr, fromAEADPRG, keyAt]
  · simp only [↓reduceIte]
    refine ⟨none, mkRState G k sM.1, sM, ?_, rfl, hsync, rfl, rfl⟩
    simp only [challengeImpl, modifyGet_run, FSAEAD.challenge]
    have hcondR : ((mkRState G k sM.1).ended || (mkRState G k sM.1).senderCorruptedAt.isSome) = true :=
      hcond
    simp [hcondR]

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem corruptSender_syncRM {k : CK} {stR : RState} {sM : St}
    (hsync : SyncRM ae G k stR sM) (q : Unit) :
    ∃ u stR' sM',
      (corruptSenderImpl q : GameM _).run stR = pure (u, stR') ∧
      (corruptSenderH G (hp 0 0 false) q : SP _).run sM = pure (u, sM') ∧
      SyncRM ae G k stR' sM' ∧
      (sM'.1.senderCorruptedAt.isSome = true ∨ sM'.1.ended = true) := by
  have hstR := hsync.stR_eq; subst hstR
  have hrun : (corruptSenderH G (hp 0 0 false) q : SP _).run sM =
      if sM.1.ended then pure (none, sM)
      else
        let w := chainFrom G 0 k sM.1.lastSentIdx
        pure (some ⟨w, sM.1.lastSentIdx⟩,
          ({ sM.1 with
             senderCorruptedAt := some (sM.1.senderCorruptedAt.getD sM.1.lastSentIdx)
             corrKey := some (sM.1.corrKey.getD w) }, sM.2)) := by
    unfold corruptSenderH
    simp only [StateT.run_bind, getH_run, pure_bind, hp_la, Bool.false_eq_true, ↓reduceIte]
    cases hend : sM.1.ended
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        senderKey_run_of_wfSeed G hsync.wf_seed hsync.wf_state.keys_eq_sent_of_uncorr
          hsync.wf_state.corr_inv,
        pure_bind]
      simp [hend]
    · simp
  rw [hrun]
  cases hend : sM.1.ended
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_modifyH G hsync.wf_seed rfl,
      wfState_corruptSender ae G hsync.wf_state _ rfl, rfl⟩, Or.inl (by simp)⟩
    simp [corruptSenderImpl, FSAEAD.corruptSender, mkRState, hend]
  · simp only [↓reduceIte]
    refine ⟨none, mkRState G k sM.1, sM, ?_, rfl, hsync, Or.inr hend⟩
    simp [corruptSenderImpl, FSAEAD.corruptSender, mkRState, hend]

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem corruptReceiver_guard_lemma {k : CK} {st : HS} (hwf : WFState ae G k st)
    (hall : ∀ r ∈ st.inTransit, st.isCompromised r.idx = true) :
    uncompBound st ≤ st.receiverIdx ∧ ∀ i ∈ st.skipped, st.isCompromised i = true := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have hlt' : st.receiverIdx < uncompBound st := by omega
    have h1 : 1 ≤ uncompBound st := by omega
    rcases hwf.pending_inTransit (uncompBound st) h1 le_rfl (Or.inr hlt') with ⟨r, hr, hidx⟩
    have hcomp := hall r hr
    rw [hidx] at hcomp
    cases h : st.senderCorruptedAt with
    | none => simp [HState.isCompromised, h] at hcomp
    | some c => simp [HState.isCompromised, uncompBound, h] at hcomp
  · intro i hi
    by_contra hcompF
    have hF : st.isCompromised i = false := Bool.eq_false_iff.mpr hcompF
    have hbounds := hwf.skipped_bounds i hi
    have hle : i ≤ uncompBound st := by
      cases h : st.senderCorruptedAt with
      | none =>
        have := hwf.rcv_le_sent_of_uncorr h
        simp [uncompBound, h]; omega
      | some c =>
        simp [HState.isCompromised, h] at hF
        simpa [uncompBound, h] using hF
    rcases hwf.pending_inTransit i hbounds.1 hle (Or.inl hi) with ⟨r, hr, hidx⟩
    have hcomp := hall r hr
    rw [hidx, hF] at hcomp
    exact Bool.false_ne_true hcomp

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem corruptReceiver_syncRM {k : CK} {stR : RState} {sM : St}
    (hsync : SyncRM ae G k stR sM) (q : Unit) :
    ∃ u stR' sM',
      (corruptReceiverImpl q : GameM _).run stR = pure (u, stR') ∧
      (corruptReceiverH G (hp 0 0 false) q : SP _).run sM = pure (u, sM') ∧
      SyncRM ae G k stR' sM' ∧
      (sM.1.senderCorruptedAt.isSome = true ∨ sM.1.ended = true →
        sM'.1.senderCorruptedAt.isSome = true ∨ sM'.1.ended = true) ∧
      ((sM.1.ended || !sM.1.challengesInTransit.isEmpty ||
          sM.1.inTransit.any (fun r => !sM.1.isCompromised r.idx)) = false →
        sM'.1.ended = true) := by
  have hstR := hsync.stR_eq; subst hstR
  have hguard_eq :
      ((mkRState G k sM.1).ended || !(mkRState G k sM.1).challengesInTransit.isEmpty ||
        (mkRState G k sM.1).inTransit.any (fun r => !(mkRState G k sM.1).isCompromised r.idx)) =
      (sM.1.ended || !sM.1.challengesInTransit.isEmpty ||
        sM.1.inTransit.any (fun r => !sM.1.isCompromised r.idx)) := rfl
  cases hguard : (sM.1.ended || !sM.1.challengesInTransit.isEmpty ||
      sM.1.inTransit.any (fun r => !sM.1.isCompromised r.idx))
  · have hall : ∀ r ∈ sM.1.inTransit, sM.1.isCompromised r.idx = true := by
      intro r hr
      have hany : sM.1.inTransit.any (fun r => !sM.1.isCompromised r.idx) = false := by
        revert hguard
        cases sM.1.ended <;> cases sM.1.challengesInTransit.isEmpty <;>
          cases sM.1.inTransit.any (fun r => !sM.1.isCompromised r.idx) <;> simp
      simpa using List.any_eq_false.mp hany r hr
    rcases corruptReceiver_guard_lemma ae G hsync.wf_state hall with ⟨hub, hsk_comp⟩
    have hwB : (match sM.1.senderCorruptedAt, sM.1.corrKey with
        | some c, some w => chainFrom G c w (sM.1.receiverIdx - c)
        | _, _ => chainFrom G 0 k sM.1.lastSentIdx) = chainFrom G 0 k sM.1.receiverIdx := by
      rcases hsync.wf_state.corr_inv with ⟨h1, h2⟩ | ⟨c, h1, h2, h3⟩
      · have hle := hsync.wf_state.rcv_le_sent_of_uncorr h1
        have hge : sM.1.lastSentIdx ≤ sM.1.receiverIdx := by simpa [uncompBound, h1] using hub
        have heq : sM.1.lastSentIdx = sM.1.receiverIdx := by omega
        simp [h1, h2, heq]
      · have hge : c ≤ sM.1.receiverIdx := by simpa [uncompBound, h1] using hub
        simp [h1, h3, ← chainFrom_add G k c (sM.1.receiverIdx - c), Nat.add_sub_of_le hge]
    have hD : (sM.1.skipped.filter sM.1.isCompromised).filterMap
        (fun i => (sM.1.keys[i - 1]?).map (i, ·)) = skippedPairs G k sM.1.skipped := by
      rw [hsync.wf_seed.keys_eq]
      apply filterMap_skippedPairs G k sM.1.keys.length sM.1.isCompromised sM.1.skipped
      intro i hi
      have hb := hsync.wf_state.skipped_bounds i hi
      have hrcv := hsync.wf_state.rcv_le_keys
      exact ⟨hsk_comp i hi, hb.1, by omega⟩
    have hrun : (corruptReceiverH G (hp 0 0 false) q : SP _).run sM =
        pure (some (⟨chainFrom G 0 k sM.1.lastSentIdx, sM.1.lastSentIdx⟩,
          ⟨chainFrom G 0 k sM.1.receiverIdx, sM.1.receiverIdx, skippedPairs G k sM.1.skipped⟩),
          ({ sM.1 with ended := true }, sM.2)) := by
      unfold corruptReceiverH
      simp only [StateT.run_bind, getH_run, pure_bind, hguard, Bool.false_eq_true, ↓reduceIte,
        hp_la]
      rw [senderKey_run_of_wfSeed G hsync.wf_seed hsync.wf_state.keys_eq_sent_of_uncorr
        hsync.wf_state.corr_inv, pure_bind]
      simp [hD]
      exact hwB
    rw [hrun]
    refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_modifyH G hsync.wf_seed rfl, ?_, rfl⟩,
      fun _ => Or.inr rfl, fun _ => rfl⟩
    · simp only [corruptReceiverImpl, modifyGet_run, FSAEAD.corruptReceiver]
      rw [hguard_eq, hguard]
      rfl
    · exact ⟨hsync.wf_state.sent_le_keys, hsync.wf_state.rcv_le_keys,
        hsync.wf_state.keys_eq_sent_of_uncorr, hsync.wf_state.rcv_le_sent_of_uncorr,
        hsync.wf_state.corr_inv, hsync.wf_state.skipped_bounds,
        hsync.wf_state.inTransit_valid, hsync.wf_state.pending_inTransit⟩
  · have hrun : (corruptReceiverH G (hp 0 0 false) q : SP _).run sM = pure (none, sM) := by
      unfold corruptReceiverH
      simp only [StateT.run_bind, getH_run, pure_bind, hguard, ↓reduceIte, StateT.run_pure]
    rw [hrun]
    refine ⟨none, mkRState G k sM.1, sM, ?_, rfl, hsync, id, fun h => Bool.noConfusion h⟩
    simp only [corruptReceiverImpl, modifyGet_run, FSAEAD.corruptReceiver]
    rw [hguard_eq, hguard]
    rfl

@[simp] theorem beq_nat_prod_eq (x y : ℕ × C) :
    (@BEq.beq (ℕ × C) instBEqOfDecidableEq x y) = (@BEq.beq (ℕ × C) instBEqProd x y) := by
  rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
  simp [BEq.beq]

omit [SampleableType CK] in
theorem deliverH_run_of_wfSeed (P : Params) (D : ℕ → ProbComp (CK × MK))
    {k : CK} {s : St} (hs : WFSeed G k s)
    (hvalid : ∀ r ∈ s.1.inTransit,
      1 ≤ r.idx ∧ r.idx ≤ s.1.lastSentIdx ∧
      r.ct = (r.idx, ae.enc (keyAt G k (r.idx - 1)) (r.idx, r.ad) r.msg))
    (hkeys : s.1.lastSentIdx ≤ s.1.keys.length) (a : AD) (i : ℕ) (e : C) :
    (deliverH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) (a, (i, e))).run s =
      if s.1.ended then pure (none, s)
      else
        match s.1.inTransit.find? (fun r => r.ad == a && r.ct == (i, e)) with
        | none => pure (none, s)
        | some r =>
          let inWindow := decide (r.idx ≤ s.1.receiverIdx + maxSkip + 1)
          let mustBeCorrect := !s.1.isCompromised r.idx && inWindow
          let out := if s.1.challengesInTransit.contains r.idx then none else some r.msg
          if i ∈ s.1.skipped then
            pure (some (.accepted i out),
              (HState.removeFromTransit
                { s.1 with
                  skipped := s.1.skipped.filter (· != i)
                  receiverIdx := max s.1.receiverIdx i
                  win := s.1.win || false } r.idx, s.2))
          else if i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1 then
            pure (some .rejected, ({ s.1 with win := s.1.win || mustBeCorrect }, s.2))
          else
            pure (some (.accepted i out),
              (HState.removeFromTransit
                { s.1 with
                  skipped := newSkipped s.1.receiverIdx i ++ s.1.skipped
                  receiverIdx := max s.1.receiverIdx i
                  win := s.1.win || false } r.idx, s.2)) := by
  unfold deliverH
  simp only [StateT.run_bind, getH_run, pure_bind]
  cases hend : s.1.ended
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hfind : s.1.inTransit.find? (fun r => r.ad == a && r.ct == (i, e)) with
    | none => simp
    | some r =>
      have hr_mem : r ∈ s.1.inTransit := List.mem_of_find?_eq_some hfind
      have hr_pred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hr_pred
      rcases hvalid r hr_mem with ⟨hi1, hisent, hct⟩
      have hidx : r.idx = i := by
        have := congrArg Prod.fst (hr_pred.2.symm.trans hct)
        exact this.symm
      subst hidx
      by_cases hcont : r.idx ∈ s.1.skipped
      · simp only [hcont, ↓reduceIte, StateT.run_bind,
          receiveH_some_run_of_contains ae G maxSkip P D r.msg a r.idx e hcont, pure_bind]
        simp [HState.removeFromTransit, hend]
      · simp only [hcont, ↓reduceIte]
        by_cases hout : r.idx ≤ s.1.receiverIdx ∨ maxSkip < r.idx - s.1.receiverIdx - 1
        · simp only [hout, ↓reduceIte, StateT.run_bind,
            receiveH_some_run_of_out_of_window ae G maxSkip P D r.msg a r.idx e hcont hout,
            pure_bind]
          simp [hend]
        · simp only [hout, ↓reduceIte, StateT.run_bind,
            receiveH_some_run_of_in_window ae G maxSkip P D hs r.msg a e hcont hout hisent hkeys,
            pure_bind]
          simp [HState.removeFromTransit, hend]
  · simp

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem wfState_extend_keys {k : CK} {st : HS} (hwf : WFState ae G k st)
    {n : ℕ} (hn1 : st.keys.length ≤ n)
    (hnh : st.senderCorruptedAt = none → n = st.lastSentIdx) :
    WFState ae G k { st with keys := keysUpTo G k n } := by
  have hsent := hwf.sent_le_keys
  have hrcv := hwf.rcv_le_keys
  refine ⟨by simp; omega, by simp; omega, fun h => by simp [hnh h],
    hwf.rcv_le_sent_of_uncorr, hwf.corr_inv, hwf.skipped_bounds,
    hwf.inTransit_valid, hwf.pending_inTransit⟩

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem isCompromised_of_corr_lt_sent {k : CK} {st : HS}
    (hwf : WFState ae G k st) {i : ℕ} (hlt : st.lastSentIdx < i)
    (hcorr : st.senderCorruptedAt.isSome = true) :
    st.isCompromised i = true := by
  rcases hwf.corr_inv with ⟨hnone, _⟩ | ⟨c, hc, hcle, _⟩
  · simp [hnone] at hcorr
  · simp [HState.isCompromised, hc]; omega

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem isCompromised_of_wfState_lt {k : CK} {st : HS} (hwf : WFState ae G k st)
    {j : ℕ} (hj : j ≤ st.receiverIdx) (hlt : st.lastSentIdx < j) :
    st.isCompromised j = true := by
  cases h : st.senderCorruptedAt with
  | none =>
    have := hwf.rcv_le_sent_of_uncorr h
    omega
  | some c =>
    exact isCompromised_of_corr_lt_sent ae G hwf hlt (by rw [h]; rfl)

omit [DecidableEq M] in
theorem injectH_run_of_wfSeed_not_lookahead (la : Bool) {k : CK} {s : St} (hs : WFSeed G k s)
    (hsk : ∀ j ∈ s.1.skipped, 1 ≤ j ∧ j < s.1.receiverIdx)
    (hrcv : s.1.receiverIdx ≤ s.1.keys.length)
    (hsk_comp : ∀ j ∈ s.1.skipped, s.1.lastSentIdx < j → s.1.isCompromised j = true)
    (a : AD) (i : ℕ) (e : C)
    (hcomp : s.1.ended = false →
      (s.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false →
      i ∉ s.1.skipped →
      ¬ (i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1) →
      s.1.lastSentIdx < i → s.1.isCompromised i = true) :
    (injectH ae G maxSkip (hp 0 0 la) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) (a, (i, e))).run s =
      if s.1.ended || s.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e)) then
        pure (none, s)
      else if i ∈ s.1.skipped then
        match ae.dec (keyAt G k (i - 1)) (i, a) e with
        | none => pure (some .rejected, s)
        | some msg =>
          let forged := !s.1.isCompromised i
          pure (some (.accepted i (some msg)),
            (HState.removeFromTransit
              { s.1 with
                skipped := s.1.skipped.filter (· != i)
                receiverIdx := max s.1.receiverIdx i
                win := s.1.win || forged
                lf := s.1.lf
                ended := s.1.ended } i, s.2))
      else if i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1 then
        pure (some .rejected, s)
      else
        let s₁ : St := ({ s.1 with keys := keysUpTo G k (max s.1.keys.length i) },
          .seed (chainFrom G 0 k (max s.1.keys.length i)))
        match ae.dec (keyAt G k (i - 1)) (i, a) e with
        | none => pure (some .rejected, s₁)
        | some msg =>
          let forged := !s.1.isCompromised i
          pure (some (.accepted i (some msg)),
            (HState.removeFromTransit
              { s₁.1 with
                skipped := newSkipped s.1.receiverIdx i ++ s.1.skipped
                receiverIdx := max s.1.receiverIdx i
                win := s.1.win || forged
                lf := s.1.lf
                ended := s.1.ended } i, s₁.2)) := by
  unfold injectH
  simp only [StateT.run_bind, getH_run, pure_bind]
  cases hguard : (s.1.ended || s.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e)))
  · have hend : s.1.ended = false := by revert hguard; cases s.1.ended <;> simp
    have hany : (s.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false := by
      revert hguard; cases s.1.ended <;> simp
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hcont : i ∈ s.1.skipped
    · have hb := hsk i hcont
      have hlfNow : (!s.1.isCompromised i && decide (s.1.lastSentIdx < i)) = false := by
        by_cases hlt : s.1.lastSentIdx < i
        · simp [hsk_comp i hcont hlt]
        · simp [hlt]
      simp only [hcont, ↓reduceIte, StateT.run_bind,
        receiveH_none_run_of_contains ae G maxSkip la hs a e hcont hb.1 (by omega)]
      cases ae.dec (keyAt G k (i - 1)) (i, a) e <;>
        simp [HState.removeFromTransit, hlfNow]
    · simp only [hcont, ↓reduceIte]
      by_cases hout : i ≤ s.1.receiverIdx ∨ maxSkip < i - s.1.receiverIdx - 1
      · simp only [hout, ↓reduceIte, StateT.run_bind,
          receiveH_none_run_of_out_of_window ae G maxSkip (hp 0 0 la) (DG G) a i e hcont hout,
          pure_bind, StateT.run_pure]
      · have hcomp' := hcomp hend hany hcont hout
        have hlarej : ¬ ((la = false ∧ s.1.lastSentIdx < i) ∧ s.1.isCompromised i = false) := by
          rintro ⟨⟨_, hlt⟩, hF⟩; rw [hcomp' hlt] at hF; exact Bool.false_ne_true hF.symm
        have hlfNow : (!s.1.isCompromised i && decide (s.1.lastSentIdx < i)) = false := by
          by_cases hlt : s.1.lastSentIdx < i
          · simp [hcomp' hlt]
          · simp [hlt]
        simp only [hout, ↓reduceIte, StateT.run_bind,
          receiveH_none_run_of_in_window ae G maxSkip la hs a e hcont hout hlarej]
        cases ae.dec (keyAt G k (i - 1)) (i, a) e <;>
          simp [HState.removeFromTransit, hlfNow]
  · simp

omit [DecidableEq M] in
theorem inject_syncRM_of_not_lookahead {k : CK} {stR : RState} {sM : St}
    (hsync : SyncRM ae G k stR sM) (q : AD × (ℕ × C))
    (hlook : sM.1.ended = false →
      (sM.1.inTransit.any (fun r => r.ad == q.1 && r.ct == q.2)) = false →
      q.2.1 ∉ sM.1.skipped →
      ¬ (q.2.1 ≤ sM.1.receiverIdx ∨ maxSkip < q.2.1 - sM.1.receiverIdx - 1) →
      sM.1.senderCorruptedAt = none → q.2.1 ≤ sM.1.lastSentIdx) :
    ∃ u stR' sM',
      (injectImpl (fromAEADPRG ae G maxSkip) q).run stR = pure (u, stR') ∧
      (injectH ae G maxSkip (hp 0 0 false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sM = pure (u, sM') ∧
      SyncRM ae G k stR' sM' ∧
      sM'.1.senderCorruptedAt = sM.1.senderCorruptedAt ∧
      sM'.1.ended = sM.1.ended ∧
      sM'.1.lf = sM.1.lf ∧
      (sM.1.senderCorruptedAt = none → sM'.1.keys = sM.1.keys ∧ sM'.2 = sM.2) := by
  rcases q with ⟨a, i, e⟩
  have hcomp : sM.1.ended = false →
      (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false →
      i ∉ sM.1.skipped →
      ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1) →
      sM.1.lastSentIdx < i → sM.1.isCompromised i = true := by
    intro hend hany hcont hout hlt
    have hcorr : sM.1.senderCorruptedAt.isSome = true := by
      cases h : sM.1.senderCorruptedAt with
      | none =>
        have := hlook hend hany hcont hout h
        dsimp only at this
        omega
      | some c => rfl
    exact isCompromised_of_corr_lt_sent ae G hsync.wf_state hlt hcorr
  have hsk_comp : ∀ j ∈ sM.1.skipped, sM.1.lastSentIdx < j → sM.1.isCompromised j = true := by
    intro j hj hlt
    exact isCompromised_of_wfState_lt ae G hsync.wf_state
      (le_of_lt (hsync.wf_state.skipped_bounds j hj).2) hlt
  rw [injectH_run_of_wfSeed_not_lookahead ae G maxSkip false hsync.wf_seed
    hsync.wf_state.skipped_bounds hsync.wf_state.rcv_le_keys hsk_comp a i e hcomp]
  have hstR := hsync.stR_eq; subst hstR
  have hguard_eq :
      ((mkRState G k sM.1).ended ||
        (mkRState G k sM.1).inTransit.any (fun r => r.ad == a && r.ct == (i, e))) =
      (sM.1.ended || sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) := rfl
  cases hguard : (sM.1.ended || sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e)))
  · have hend : sM.1.ended = false := by revert hguard; cases sM.1.ended <;> simp
    have hany : (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false := by
      revert hguard; cases sM.1.ended <;> simp
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hcont : i ∈ sM.1.skipped
    · simp only [hcont, ↓reduceIte]
      cases hdec : ae.dec (keyAt G k (i - 1)) (i, a) e with
      | none =>
        refine ⟨some .rejected, mkRState G k sM.1, sM, ?_, rfl, hsync, rfl, rfl, rfl,
          fun _ => ⟨rfl, rfl⟩⟩
        simp only [injectImpl, modifyGet_run, FSAEAD.inject, beq_nat_prod_eq]
        rw [hguard_eq, hguard]
        simp [mkRState, receive_real_of_contains ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont, hdec]
      | some msg =>
        have hmax : max sM.1.receiverIdx i = sM.1.receiverIdx :=
          Nat.max_eq_left (le_of_lt (hsync.wf_state.skipped_bounds i hcont).2)
        refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_modifyH G hsync.wf_seed rfl,
          wfState_accept_contains ae G hsync.wf_state hcont (sM.1.win || !sM.1.isCompromised i)
            sM.1.ended sM.1.lf, rfl⟩, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
        simp only [injectImpl, modifyGet_run, FSAEAD.inject, beq_nat_prod_eq]
        rw [hguard_eq, hguard]
        simp [mkRState, receive_real_of_contains ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont,
          hdec, HState.removeFromTransit, State.removeFromTransit, hmax]; rfl
    · simp only [hcont, ↓reduceIte]
      by_cases hout : i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1
      · simp only [hout, ↓reduceIte]
        refine ⟨some .rejected, mkRState G k sM.1, sM, ?_, rfl, hsync, rfl, rfl, rfl,
          fun _ => ⟨rfl, rfl⟩⟩
        simp only [injectImpl, modifyGet_run, FSAEAD.inject, beq_nat_prod_eq]
        rw [hguard_eq, hguard]
        simp [mkRState, receive_real_of_out_of_window ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont hout]
      · simp only [hout, ↓reduceIte]
        have hlt : sM.1.receiverIdx < i := by omega
        have hmax : max sM.1.receiverIdx i = i := Nat.max_eq_right (le_of_lt hlt)
        have hnh : sM.1.senderCorruptedAt = none →
            max sM.1.keys.length i = sM.1.lastSentIdx ∧ i ≤ sM.1.lastSentIdx := by
          intro huncorr
          have h1 := hsync.wf_state.keys_eq_sent_of_uncorr huncorr
          have h2 := hlook hend hany hcont hout huncorr
          dsimp only at h2
          exact ⟨by omega, h2⟩
        cases hdec : ae.dec (keyAt G k (i - 1)) (i, a) e with
        | none =>
          refine ⟨some .rejected, _, _, ?_, rfl, ⟨wfSeed_of_keys_slot G rfl,
            wfState_extend_keys ae G hsync.wf_state (le_max_left _ _) (fun h => (hnh h).1), rfl⟩,
            rfl, rfl, rfl, ?_⟩
          · simp only [injectImpl, modifyGet_run, FSAEAD.inject, beq_nat_prod_eq]
            rw [hguard_eq, hguard]
            simp [mkRState, receive_real_of_in_window ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont hout, hdec]
          · intro huncorr
            have h1 := hsync.wf_state.keys_eq_sent_of_uncorr huncorr
            have h2 := (hnh huncorr).2
            have hmax_k : max sM.1.keys.length i = sM.1.keys.length := by omega
            simp [hmax_k, ← hsync.wf_seed.keys_eq, ← hsync.wf_seed.slot_eq]
        | some msg =>
          refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_of_keys_slot G rfl,
            wfState_accept_in_window ae G hsync.wf_state hlt (le_max_left _ _) (le_max_right _ _)
              hnh (sM.1.win || !sM.1.isCompromised i) sM.1.ended sM.1.lf, rfl⟩,
            rfl, rfl, rfl, ?_⟩
          · simp only [injectImpl, modifyGet_run, FSAEAD.inject, beq_nat_prod_eq]
            rw [hguard_eq, hguard]
            simp [mkRState, receive_real_of_in_window ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont hout,
              hdec, HState.removeFromTransit, State.removeFromTransit, hmax]; rfl
          · intro huncorr
            have h1 := hsync.wf_state.keys_eq_sent_of_uncorr huncorr
            have h2 := (hnh huncorr).2
            have hmax_k : max sM.1.keys.length i = sM.1.keys.length := by omega
            simp [HState.removeFromTransit, hmax_k, ← hsync.wf_seed.keys_eq, ← hsync.wf_seed.slot_eq]
  · simp only [↓reduceIte]
    refine ⟨none, mkRState G k sM.1, sM, ?_, rfl, hsync, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
    simp only [injectImpl, modifyGet_run, FSAEAD.inject, beq_nat_prod_eq]
    rw [hguard_eq, hguard]
    simp

theorem state_bind_eq_of_pure {σ₁ σ₂ α β γ : Type}
    {m₁ : StateT σ₁ ProbComp α} {m₂ : StateT σ₂ ProbComp α}
    {s₁ : σ₁} {s₂ : σ₂} {u : α} {s₁' : σ₁} {s₂' : σ₂}
    {k₁ : α → StateT σ₁ ProbComp β} {k₂ : α → StateT σ₂ ProbComp β}
    {f₁ : β × σ₁ → ProbComp γ} {f₂ : β × σ₂ → ProbComp γ}
    (h₁ : m₁.run s₁ = pure (u, s₁')) (h₂ : m₂.run s₂ = pure (u, s₂'))
    (hk : (k₁ u).run s₁' >>= f₁ = (k₂ u).run s₂' >>= f₂) :
    (m₁ >>= k₁).run s₁ >>= f₁ = (m₂ >>= k₂).run s₂ >>= f₂ := by
  simp only [StateT.run_bind, h₁, h₂, pure_bind, hk]

theorem state_bind_eq_of_liftM {σ₁ σ₂ α β γ : Type} (c : ProbComp α)
    {s₁ : σ₁} {s₂ : σ₂}
    {k₁ : α → StateT σ₁ ProbComp β} {k₂ : α → StateT σ₂ ProbComp β}
    {f₁ : β × σ₁ → ProbComp γ} {f₂ : β × σ₂ → ProbComp γ}
    (hk : ∀ u, (k₁ u).run s₁ >>= f₁ = (k₂ u).run s₂ >>= f₂) :
    ((liftM c : StateT σ₁ ProbComp α) >>= k₁).run s₁ >>= f₁ =
      ((liftM c : StateT σ₂ ProbComp α) >>= k₂).run s₂ >>= f₂ := by
  simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
  congr 1; funext u; exact hk u

end Regime1b

/-! ## Pre-corruption three-way simulation -/

section Regime1a

variable [SampleableType MK] [SampleableType CK] (ideal : ℕ × AD → ProbComp C)
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

def CloseBy (cR cM cL : ProbComp Bool) : Prop :=
  ∀ s : Set Bool,
    𝒟[cR] s ≤ 𝒟[cM] s + 𝒟[cL] {true} ∧
    𝒟[cM] s ≤ 𝒟[cR] s + 𝒟[cL] {true}

theorem closeBy_of_eq {cR cM cL : ProbComp Bool} (h : cR = cM) :
    CloseBy cR cM cL := by
  intro s
  rw [h]
  exact ⟨le_self_add, le_self_add⟩

theorem closeBy_of_evalDist_eq_one {cR cM cL : ProbComp Bool}
    (h : 𝒟[cL] {true} = 1) :
    CloseBy cR cM cL := by
  intro s
  rw [h]
  exact ⟨(prob_le_one).trans le_add_self, (prob_le_one).trans le_add_self⟩

theorem closeBy_bind {α : Type}
    (oa : ProbComp α) {fR fM fL : α → ProbComp Bool}
    (h : ∀ a, CloseBy (fR a) (fM a) (fL a)) :
    CloseBy (oa >>= fR) (oa >>= fM) (oa >>= fL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a
  | query_bind t k ih =>
    intro s
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool, ∀ ev : Set Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] ev =
          ∫⁻ u, 𝒟[g u] ev ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      intro g ev
      rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    rw [h1 (fun u => k u >>= fR) s, h1 (fun u => k u >>= fM) s, h1 (fun u => k u >>= fL) {true}]
    rw [← lintegral_add_left Measurable.of_discrete,
        ← lintegral_add_left Measurable.of_discrete]
    exact ⟨lintegral_mono fun u => (ih u s).1, lintegral_mono fun u => (ih u s).2⟩

theorem closeBy_state_bind_of_pure {σ₁ σ₂ σ₃ α β : Type}
    {m₁ : StateT σ₁ ProbComp α} {m₂ : StateT σ₂ ProbComp α} {m₃ : StateT σ₃ ProbComp α}
    {s₁ : σ₁} {s₂ : σ₂} {s₃ : σ₃} {u : α} {s₁' : σ₁} {s₂' : σ₂} {s₃' : σ₃}
    {k₁ : α → StateT σ₁ ProbComp β} {k₂ : α → StateT σ₂ ProbComp β} {k₃ : α → StateT σ₃ ProbComp β}
    {f₁ : β × σ₁ → ProbComp Bool} {f₂ : β × σ₂ → ProbComp Bool} {f₃ : β × σ₃ → ProbComp Bool}
    (h₁ : m₁.run s₁ = pure (u, s₁')) (h₂ : m₂.run s₂ = pure (u, s₂')) (h₃ : m₃.run s₃ = pure (u, s₃'))
    (hk : CloseBy ((k₁ u).run s₁' >>= f₁) ((k₂ u).run s₂' >>= f₂) ((k₃ u).run s₃' >>= f₃)) :
    CloseBy ((m₁ >>= k₁).run s₁ >>= f₁) ((m₂ >>= k₂).run s₂ >>= f₂) ((m₃ >>= k₃).run s₃ >>= f₃) := by
  simp only [StateT.run_bind, h₁, h₂, h₃, pure_bind]
  exact hk

theorem closeBy_state_bind_of_liftM {σ₁ σ₂ σ₃ α β : Type}
    (c : ProbComp α) {s₁ : σ₁} {s₂ : σ₂} {s₃ : σ₃}
    {k₁ : α → StateT σ₁ ProbComp β} {k₂ : α → StateT σ₂ ProbComp β} {k₃ : α → StateT σ₃ ProbComp β}
    {f₁ : β × σ₁ → ProbComp Bool} {f₂ : β × σ₂ → ProbComp Bool} {f₃ : β × σ₃ → ProbComp Bool}
    (hk : ∀ u, CloseBy ((k₁ u).run s₁ >>= f₁) ((k₂ u).run s₂ >>= f₂) ((k₃ u).run s₃ >>= f₃)) :
    CloseBy (((liftM c : StateT σ₁ ProbComp α) >>= k₁).run s₁ >>= f₁)
      (((liftM c : StateT σ₂ ProbComp α) >>= k₂).run s₂ >>= f₂)
      (((liftM c : StateT σ₃ ProbComp α) >>= k₃).run s₃ >>= f₃) := by
  simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
  exact closeBy_bind c hk

structure SyncRML (k : CK) (stR : RState) (sM sL : St) : Prop where
  syncRM : SyncRM ae G k stR sM
  wf_seedL : WFSeed G k sL
  sL_eq : sL.1 = { sM.1 with keys := sL.1.keys }
  keys_le : sM.1.keys.length ≤ sL.1.keys.length
  uncorr : sM.1.senderCorruptedAt = none
  not_ended : sM.1.ended = false

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem syncRML_init (k : CK) (b : Bool) :
    SyncRML ae G k (initState (fromAEADPRG ae G maxSkip) k b)
      (hInit b (.seed k)) (hInit b (.seed k)) :=
  ⟨syncRM_init ae G maxSkip k b, wfSeed_hInit G k b, rfl, le_rfl, rfl, rfl⟩

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem transmit_syncRML {k : CK} {stR : RState} {sM sL : St}
    (hsync : SyncRML ae G k stR sM sL) (q : AD × M) :
    ∃ u stR' sM' sL',
      (transmitImpl (fromAEADPRG ae G maxSkip) q).run stR = pure (u, stR') ∧
      (transmitHWith ideal ae G (hp 0 0 false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sM = pure (u, sM') ∧
      (transmitHWith ideal ae G (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sL = pure (u, sL') ∧
      SyncRML ae G k stR' sM' sL' := by
  have hendL : sL.1.ended = false := by rw [hsync.sL_eq]; exact hsync.not_ended
  have hsentL : sL.1.lastSentIdx = sM.1.lastSentIdx := by rw [hsync.sL_eq]
  rw [transmitH_run_of_wfSeed ideal ae G false hsync.syncRM.wf_seed q,
      transmitH_run_of_wfSeed ideal ae G true hsync.wf_seedL q]
  have hstR := hsync.syncRM.stR_eq; subst hstR
  simp only [hsync.not_ended, hendL, hsentL, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, _, _, _, ?_, rfl, rfl, ⟨⟨wfSeed_of_keys_slot G rfl,
    ?_, rfl⟩,
    wfSeed_of_keys_slot G rfl, ?_, ?_, hsync.uncorr, rfl⟩⟩
  · simp [transmitImpl, FSAEAD.transmit, mkRState, hsync.not_ended, fromAEADPRG, keyAt]
  · simpa [hsync.not_ended] using
      wfState_send ae G hsync.syncRM.wf_state q.1 q.2 sM.1.challengesInTransit
  · rw [hsync.sL_eq]
  · have := hsync.keys_le; simp; omega

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem challenge_syncRML {k : CK} {stR : RState} {sM sL : St}
    (hsync : SyncRML ae G k stR sM sL) (q : AD × M × M) :
    ∃ u stR' sM' sL',
      (challengeImpl (fromAEADPRG ae G maxSkip) q).run stR = pure (u, stR') ∧
      (challengeHWith ideal ae G (hp 0 0 false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sM = pure (u, sM') ∧
      (challengeHWith ideal ae G (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sL = pure (u, sL') ∧
      SyncRML ae G k stR' sM' sL' := by
  have hcondM : (sM.1.ended || sM.1.senderCorruptedAt.isSome) = false := by
    simp [hsync.not_ended, hsync.uncorr]
  have hcondL : (sL.1.ended || sL.1.senderCorruptedAt.isSome) = false := by
    rw [hsync.sL_eq]; exact hcondM
  have hsentL : sL.1.lastSentIdx = sM.1.lastSentIdx := by rw [hsync.sL_eq]
  have hbL : sL.1.b = sM.1.b := by rw [hsync.sL_eq]
  rw [challengeH_run_of_wfSeed ideal ae G false hsync.syncRM.wf_seed q,
      challengeH_run_of_wfSeed ideal ae G true hsync.wf_seedL q]
  have hstR := hsync.syncRM.stR_eq; subst hstR
  simp only [hcondM, hcondL, hsentL, hbL, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, _, _, _, ?_, rfl, rfl, ⟨⟨wfSeed_of_keys_slot G rfl,
    wfState_send ae G hsync.syncRM.wf_state q.1 (if sM.1.b then q.2.2 else q.2.1)
      ((sM.1.lastSentIdx + 1) :: sM.1.challengesInTransit), rfl⟩,
    wfSeed_of_keys_slot G rfl, ?_, ?_, hsync.uncorr, hsync.not_ended⟩⟩
  · simp [challengeImpl, FSAEAD.challenge, mkRState, hsync.not_ended, hsync.uncorr,
      fromAEADPRG, keyAt]
  · rw [hsync.sL_eq]
  · have := hsync.keys_le; simp; omega

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem corruptReceiver_syncRML {k : CK} {stR : RState} {sM sL : St}
    (hsync : SyncRML ae G k stR sM sL) (q : Unit) :
    (∃ u stR' sM' sL',
      (corruptReceiverImpl q : GameM _).run stR = pure (u, stR') ∧
      (corruptReceiverH G (hp 0 0 false) q : SP _).run sM = pure (u, sM') ∧
      (corruptReceiverH G (hp 0 0 true) q : SP _).run sL = pure (u, sL') ∧
      SyncRML ae G k stR' sM' sL') ∨
    (∃ u stR' sM',
      (corruptReceiverImpl q : GameM _).run stR = pure (u, stR') ∧
      (corruptReceiverH G (hp 0 0 false) q : SP _).run sM = pure (u, sM') ∧
      SyncRM ae G k stR' sM' ∧
      (sM'.1.senderCorruptedAt.isSome = true ∨ sM'.1.ended = true)) := by
  by_cases hguard : (sM.1.ended || !sM.1.challengesInTransit.isEmpty ||
      sM.1.inTransit.any (fun r => !sM.1.isCompromised r.idx)) = true
  · left
    have hguardL : (sL.1.ended || !sL.1.challengesInTransit.isEmpty ||
        sL.1.inTransit.any (fun r => !sL.1.isCompromised r.idx)) = true := by
      rw [hsync.sL_eq]; exact hguard
    have hR : (corruptReceiverImpl q : GameM _).run stR = pure (none, stR) := by
      rw [hsync.syncRM.stR_eq]
      simp only [corruptReceiverImpl, modifyGet_run, FSAEAD.corruptReceiver]
      change pure (if (sM.1.ended || !sM.1.challengesInTransit.isEmpty ||
        sM.1.inTransit.any (fun r => !sM.1.isCompromised r.idx)) then _ else _) = _
      rw [hguard]; rfl
    have hM : (corruptReceiverH G (hp 0 0 false) q : SP _).run sM = pure (none, sM) := by
      unfold corruptReceiverH
      simp only [StateT.run_bind, getH_run, pure_bind, hguard, ↓reduceIte, StateT.run_pure]
    have hL : (corruptReceiverH G (hp 0 0 true) q : SP _).run sL = pure (none, sL) := by
      unfold corruptReceiverH
      simp only [StateT.run_bind, getH_run, pure_bind, hguardL, ↓reduceIte, StateT.run_pure]
    exact ⟨none, stR, sM, sL, hR, hM, hL, hsync⟩
  · right
    have hguardF := Bool.eq_false_iff.mpr hguard
    rcases corruptReceiver_syncRM ae G hsync.syncRM q with
      ⟨u, stR', sM', hR, hM, hsyncRM', _, hend'⟩
    exact ⟨u, stR', sM', hR, hM, hsyncRM', Or.inr (hend' hguardF)⟩

omit [DecidableEq M] in
theorem inject_syncRML_of_not_lookahead {k : CK} {stR : RState} {sM sL : St}
    (hsync : SyncRML ae G k stR sM sL) (q : AD × (ℕ × C))
    (hlook : sM.1.ended = false →
      (sM.1.inTransit.any (fun r => r.ad == q.1 && r.ct == q.2)) = false →
      q.2.1 ∉ sM.1.skipped →
      ¬ (q.2.1 ≤ sM.1.receiverIdx ∨ maxSkip < q.2.1 - sM.1.receiverIdx - 1) →
      sM.1.senderCorruptedAt = none → q.2.1 ≤ sM.1.lastSentIdx) :
    ∃ u stR' sM' sL',
      (injectImpl (fromAEADPRG ae G maxSkip) q).run stR = pure (u, stR') ∧
      (injectH ae G maxSkip (hp 0 0 false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sM = pure (u, sM') ∧
      (injectH ae G maxSkip (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sL = pure (u, sL') ∧
      SyncRML ae G k stR' sM' sL' := by
  rcases inject_syncRM_of_not_lookahead ae G maxSkip hsync.syncRM q hlook with
    ⟨u, stR', sM', hR, hM, hsyncRM', hca, hend, _, hkeysM⟩
  have hkeysM' := hkeysM hsync.uncorr
  have hL :
      (injectH ae G maxSkip (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sL =
        pure (u, ({ sM'.1 with keys := sL.1.keys }, sL.2)) := by
    rcases q with ⟨a, i, e⟩
    let K := sL.1.keys
    have hsL1 : sL.1 = { sM.1 with keys := K } := hsync.sL_eq
    have hskL : ∀ j ∈ sL.1.skipped, 1 ≤ j ∧ j < sL.1.receiverIdx := by
      rw [hsL1]; exact hsync.syncRM.wf_state.skipped_bounds
    have hrcvL : sL.1.receiverIdx ≤ sL.1.keys.length := by
      have := hsync.syncRM.wf_state.rcv_le_keys.trans hsync.keys_le
      rw [hsL1]; exact this
    have hsk_compM : ∀ j ∈ sM.1.skipped, sM.1.lastSentIdx < j → sM.1.isCompromised j = true := by
      intro j hj hlt
      exact isCompromised_of_wfState_lt ae G hsync.syncRM.wf_state
        (le_of_lt (hsync.syncRM.wf_state.skipped_bounds j hj).2) hlt
    have hsk_compL : ∀ j ∈ sL.1.skipped, sL.1.lastSentIdx < j → sL.1.isCompromised j = true := by
      rw [hsL1]; exact hsk_compM
    have hcompM : sM.1.ended = false →
        (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false →
        i ∉ sM.1.skipped →
        ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1) →
        sM.1.lastSentIdx < i → sM.1.isCompromised i = true := by
      intro he ha hc ho hlt
      have := hlook he ha hc ho hsync.uncorr
      dsimp only at this; omega
    have hcompL : sL.1.ended = false →
        (sL.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false →
        i ∉ sL.1.skipped →
        ¬ (i ≤ sL.1.receiverIdx ∨ maxSkip < i - sL.1.receiverIdx - 1) →
        sL.1.lastSentIdx < i → sL.1.isCompromised i = true := by
      rw [hsL1]; exact hcompM
    have hM' := hM
    rw [injectH_run_of_wfSeed_not_lookahead ae G maxSkip false hsync.syncRM.wf_seed
      hsync.syncRM.wf_state.skipped_bounds hsync.syncRM.wf_state.rcv_le_keys hsk_compM a i e hcompM] at hM'
    rw [injectH_run_of_wfSeed_not_lookahead ae G maxSkip true hsync.wf_seedL
      hskL hrcvL hsk_compL a i e hcompL]
    have hcomp_eq : ∀ idx, ({ sM.1 with keys := K } : HS).isCompromised idx =
        sM.1.isCompromised idx := fun _ => rfl
    have hsL_pair : sL = ({ sM.1 with keys := K }, sL.2) := Prod.ext hsL1 rfl
    simp only [hsL1, hcomp_eq]
    by_cases hguard : (sM.1.ended || sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = true
    · simp only [hguard, ↓reduceIte] at hM' ⊢
      injection hM' with hM'; injection hM' with hu hsM'; subst hu hsM'
      rw [← hsL_pair]
    · have hend0 : sM.1.ended = false := by revert hguard; cases sM.1.ended <;> simp
      have hany0 : (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false := by
        revert hguard; cases sM.1.ended <;> simp
      by_cases hcont : i ∈ sM.1.skipped
      · simp only [hguard, hcont, Bool.false_eq_true, ↓reduceIte] at hM' ⊢
        cases hdec : ae.dec (keyAt G k (i - 1)) (i, a) e <;>
          (simp only [hdec] at hM' ⊢; injection hM' with hM'; injection hM' with hu hsM';
           subst hu hsM'; first | rw [← hsL_pair] | simp [HState.removeFromTransit])
      · by_cases hout : i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1
        · simp only [hguard, hcont, hout, Bool.false_eq_true, ↓reduceIte] at hM' ⊢
          injection hM' with hM'; injection hM' with hu hsM'; subst hu hsM'
          rw [← hsL_pair]
        · have hi_le : i ≤ sM.1.lastSentIdx := hlook hend0 hany0 hcont hout hsync.uncorr
          have h1 := hsync.syncRM.wf_state.keys_eq_sent_of_uncorr hsync.uncorr
          have hleL := hsync.keys_le
          have hmaxM : max sM.1.keys.length i = sM.1.keys.length := by omega
          have hmaxL : max K.length i = K.length := by
            change max sL.1.keys.length i = sL.1.keys.length; omega
          have hslM : Slot.seed (chainFrom G 0 k sM.1.keys.length) = sM.2 :=
            hsync.syncRM.wf_seed.slot_eq.symm
          have hkeys_eqM : keysUpTo G k sM.1.keys.length = sM.1.keys :=
            hsync.syncRM.wf_seed.keys_eq.symm
          have hslL : Slot.seed (chainFrom G 0 k K.length) = sL.2 := by
            simpa [K] using hsync.wf_seedL.slot_eq.symm
          have hkeys_eqL : keysUpTo G k K.length = K := by
            simpa [K] using hsync.wf_seedL.keys_eq.symm
          simp only [hguard, hcont, hout, Bool.false_eq_true, ↓reduceIte,
            hmaxM, hslM, hkeys_eqM] at hM'
          simp only [hguard, hcont, hout, Bool.false_eq_true, ↓reduceIte,
            hmaxL, hslL, hkeys_eqL]
          cases hdec : ae.dec (keyAt G k (i - 1)) (i, a) e <;>
            (simp only [hdec] at hM' ⊢; injection hM' with hM'; injection hM' with hu hsM';
             subst hu hsM'; first | rw [← hsL_pair] | simp [HState.removeFromTransit])
  refine ⟨u, stR', sM', ({ sM'.1 with keys := sL.1.keys }, sL.2), hR, hM, hL,
    ⟨hsyncRM', wfSeed_modifyH G hsync.wf_seedL rfl, rfl, ?_, ?_, ?_⟩⟩
  · rw [hkeysM'.1]; exact hsync.keys_le
  · rw [hca]; exact hsync.uncorr
  · rw [hend]; exact hsync.not_ended

omit [DecidableEq M] in
theorem inject_syncRML_of_lookahead_none {k : CK} {stR : RState} {sM sL : St}
    (hsync : SyncRML ae G k stR sM sL) (a : AD) (i : ℕ) (e : C)
    (hend : sM.1.ended = false)
    (hany : (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false)
    (hcont : i ∉ sM.1.skipped)
    (hout : ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1))
    (hlt : sM.1.lastSentIdx < i)
    (hdec : ae.dec (keyAt G k (i - 1)) (i, a) e = none) :
    ∃ u stR' sM' sL',
      (injectImpl (fromAEADPRG ae G maxSkip) (a, i, e)).run stR = pure (u, stR') ∧
      (injectH ae G maxSkip (hp 0 0 false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (a, i, e)).run sM = pure (u, sM') ∧
      (injectH ae G maxSkip (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (a, i, e)).run sL = pure (u, sL') ∧
      SyncRML ae G k stR' sM' sL' := by
  have huncompM : sM.1.isCompromised i = false := by
    simp [HState.isCompromised, hsync.uncorr]
  have hsL1 : sL.1 = { sM.1 with keys := sL.1.keys } := hsync.sL_eq
  have hendL : sL.1.ended = false := by rw [hsL1]; exact hend
  have hanyL : (sL.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false := by
    rw [hsL1]; exact hany
  have hcontL : i ∉ sL.1.skipped := by rw [hsL1]; exact hcont
  have houtL : ¬ (i ≤ sL.1.receiverIdx ∨ maxSkip < i - sL.1.receiverIdx - 1) := by
    rw [hsL1]; exact hout
  have hR : (injectImpl (fromAEADPRG ae G maxSkip) (a, i, e)).run stR =
      pure (some .rejected, stR) := by
    rw [hsync.syncRM.stR_eq]
    simp only [injectImpl, modifyGet_run, FSAEAD.inject, beq_nat_prod_eq]
    simp [mkRState, hend, hany,
      receive_real_of_in_window ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont hout, hdec]
  have hM : (injectH ae G maxSkip (hp 0 0 false) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) (a, i, e)).run sM =
      pure (some .rejected, sM) := by
    unfold injectH
    simp only [StateT.run_bind, getH_run, pure_bind, hend, hany, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte,
      receiveH_none_run_of_lookahead_reject ae G maxSkip (hp 0 0 false) (DG G) a i e hcont hout
        ⟨⟨rfl, hlt⟩, huncompM⟩,
      StateT.run_pure]
  let sL' : St := ({ sL.1 with keys := keysUpTo G k (max sL.1.keys.length i) },
    .seed (chainFrom G 0 k (max sL.1.keys.length i)))
  have hL : (injectH ae G maxSkip (hp 0 0 true) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) (a, i, e)).run sL =
      pure (some .rejected, sL') := by
    have hlarejL : ¬ ((true = false ∧ sL.1.lastSentIdx < i) ∧ sL.1.isCompromised i = false) := by
      simp
    unfold injectH
    simp only [StateT.run_bind, getH_run, pure_bind, hendL, hanyL, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte,
      receiveH_none_run_of_in_window ae G maxSkip true hsync.wf_seedL a e hcontL houtL hlarejL,
      hdec, StateT.run_pure, sL']
  refine ⟨some .rejected, stR, sM, sL', hR, hM, hL,
    ⟨hsync.syncRM, wfSeed_after_genUpTo G _, ?_, ?_, hsync.uncorr, hsync.not_ended⟩⟩
  · dsimp only [sL']
    rw [hsL1]
  · dsimp only [sL']
    rw [keysUpTo_length]
    exact hsync.keys_le.trans (Nat.le_max_left _ _)

omit [DecidableEq M] in
theorem injectL_lookahead_some {k : CK} {stR : RState} {sM sL : St}
    (hsync : SyncRML ae G k stR sM sL) (a : AD) (i : ℕ) (e : C) (msg : M)
    (hend : sM.1.ended = false)
    (hany : (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false)
    (hcont : i ∉ sM.1.skipped)
    (hout : ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1))
    (hlt : sM.1.lastSentIdx < i)
    (hdec : ae.dec (keyAt G k (i - 1)) (i, a) e = some msg) :
    ∃ u sL',
      (injectH ae G maxSkip (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) (a, i, e)).run sL = pure (u, sL') ∧
      sL'.1.ended = true ∧ sL'.1.lf = true := by
  have hsL1 : sL.1 = { sM.1 with keys := sL.1.keys } := hsync.sL_eq
  have hendL : sL.1.ended = false := by rw [hsL1]; exact hend
  have hanyL : (sL.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false := by
    rw [hsL1]; exact hany
  have hcontL : i ∉ sL.1.skipped := by rw [hsL1]; exact hcont
  have houtL : ¬ (i ≤ sL.1.receiverIdx ∨ maxSkip < i - sL.1.receiverIdx - 1) := by
    rw [hsL1]; exact hout
  have hltL : sL.1.lastSentIdx < i := by rw [hsL1]; exact hlt
  have huncompL : sL.1.isCompromised i = false := by
    rw [hsL1]; simp [HState.isCompromised, hsync.uncorr]
  have hlarejL : ¬ ((true = false ∧ sL.1.lastSentIdx < i) ∧ sL.1.isCompromised i = false) := by
    simp
  let sL₁ : St := ({ sL.1 with keys := keysUpTo G k (max sL.1.keys.length i) },
    .seed (chainFrom G 0 k (max sL.1.keys.length i)))
  let forged := !sL.1.isCompromised i
  let lfNow := forged && decide (sL.1.lastSentIdx < i)
  let sL' : St := (HState.removeFromTransit
    { sL₁.1 with
      skipped := newSkipped sL.1.receiverIdx i ++ sL.1.skipped
      receiverIdx := max sL.1.receiverIdx i
      win := sL.1.win || forged
      lf := sL.1.lf || lfNow
      ended := sL.1.ended || lfNow } i, sL₁.2)
  refine ⟨some (.accepted i (some msg)), sL', ?_, ?_, ?_⟩
  · unfold injectH
    simp only [StateT.run_bind, getH_run, pure_bind, hendL, hanyL, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte,
      receiveH_none_run_of_in_window ae G maxSkip true hsync.wf_seedL a e hcontL houtL hlarejL,
      hdec, modifyH_run, StateT.run_pure, sL', sL₁, forged, lfNow]
    simp [hp]
  · simp [sL', sL₁, forged, lfNow, HState.removeFromTransit, huncompL, hltL]
  · simp [sL', sL₁, forged, lfNow, HState.removeFromTransit, huncompL, hltL]

end Regime1a

/-! ## Initial hybrid evaluation -/

section StartAssembly

variable [SampleableType MK] [SampleableType CK] (ideal : ℕ × AD → ProbComp C)
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

private lemma mem_support_liftM_run {σ α : Type} {p : ProbComp α} {s s' : σ} {a : α}
    (h : (a, s') ∈ support ((liftM p : StateT σ ProbComp α).run s)) : s' = s := by
  rw [StateT.run_monadLift, MonadAttach.mem_support_bind] at h
  rcases h with ⟨_, _, h2⟩
  simp only [support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h2
  exact h2.2

omit [SampleableType MK] [SampleableType CK] in
theorem b_eq_of_mem_support_simulateQ_real {α : Type}
    (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α) :
    ∀ {stR : RState} {z : α × RState},
      z ∈ support ((simulateQ (implR ae G maxSkip) oa).run stR) →
      z.2.b = stR.b := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro stR z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t r ih =>
    intro stR z hz
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, st₁⟩, h₁, h₂⟩
    rw [ih u h₂]
    rcases t with n | (((((q | q) | q) | q) | q) | q)
    · rw [mem_support_liftM_run h₁]
    · change (u, st₁) ∈ support (pure (transmit (fromAEADPRG ae G maxSkip) stR q.1 q.2) : ProbComp _) at h₁
      simp only [support_pure] at h₁
      rw [(Prod.ext_iff.mp h₁).2]
      unfold transmit
      repeat' (first | rfl | split)
    · change (u, st₁) ∈ support (pure (challenge (fromAEADPRG ae G maxSkip) stR q.1 q.2.1 q.2.2) : ProbComp _) at h₁
      simp only [support_pure] at h₁
      rw [(Prod.ext_iff.mp h₁).2]
      unfold challenge
      repeat' (first | rfl | split)
    · change (u, st₁) ∈ support (pure (corruptSender stR) : ProbComp _) at h₁
      simp only [support_pure] at h₁
      rw [(Prod.ext_iff.mp h₁).2]
      unfold corruptSender
      repeat' (first | rfl | split)
    · change (u, st₁) ∈ support (pure (corruptReceiver stR) : ProbComp _) at h₁
      simp only [support_pure] at h₁
      rw [(Prod.ext_iff.mp h₁).2]
      unfold corruptReceiver
      repeat' (first | rfl | split)
    · change (u, st₁) ∈ support (pure (deliver (fromAEADPRG ae G maxSkip) stR q.1 q.2) : ProbComp _) at h₁
      simp only [support_pure] at h₁
      rw [(Prod.ext_iff.mp h₁).2]
      unfold deliver State.removeFromTransit
      repeat' (first | rfl | split)
    · change (u, st₁) ∈ support (pure (inject (fromAEADPRG ae G maxSkip) stR q.1 q.2) : ProbComp _) at h₁
      simp only [support_pure] at h₁
      rw [(Prod.ext_iff.mp h₁).2]
      unfold inject State.removeFromTransit
      repeat' (first | rfl | split)

theorem hybA_zero_evalDist (la : Bool) (A : RatchetAdversary CK MK AD M C) :
    𝒟[hybridA ideal ae G maxSkip 0 la A] =
      𝒟[($ᵗ Bool) >>= fun b => ($ᵗ CK) >>= fun k =>
        (simulateQ (implH ideal ae G maxSkip la) A).run (hInit b (.seed k)) >>=
          fun z => pure (hOut la z)] := by
  unfold hybridA hRunWith
  simp only [hp_la]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  have hI := seedFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0
  have hK : ∀ h h' : HS, h.keys.length = h'.keys.length →
      seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0 h = seedFill 0 h' := by
    intro h h' hl; funext sl; cases sl <;> simp [seedFill, hl]
  have hGen := comm_genStep_seed (AD := AD) (M := M) (C := C) G (hp 0 0 la) 0 le_rfl
  have hRev := comm_reveal_seed (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) 0
  have hfill := (hOut_fill ideal ae G maxSkip A (hp 0 0 la) (DG G) hI hK hGen hRev (hInit b .unknown)).symm
  have h0 : fillSt (seedFill 0)
      (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown) =
      (($ᵗ CK) >>= fun k => pure (hInit b (.seed k))) := by
    simp [fillSt, seedFill, hInit, map_eq_bind_pure_comp]
  have heq := DEq.evalDist_eq hfill
  rw [h0, hp_la] at heq
  simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def] using heq

omit [SampleableType MK] in
theorem game_evalDist_eq (A : RatchetAdversary CK MK AD M C) :
    𝒟[game (fromAEADPRG ae G maxSkip) A] =
      𝒟[($ᵗ Bool) >>= fun b => ($ᵗ CK) >>= fun k =>
        (simulateQ (implR ae G maxSkip) A).run (initState (fromAEADPRG ae G maxSkip) k b) >>=
          fun z => pure (z.2.b == z.1 || z.2.win)] := by
  unfold game
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  refine evalDist_bind_congr_of_support ($ᵗ CK) _ _ fun k _ => ?_
  refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
  have hb := b_eq_of_mem_support_simulateQ_real ae G maxSkip A hz
  simp [initState] at hb
  simp [hb]

end StartAssembly

end CryptoGames.FSAEAD.Thm5.Ends

