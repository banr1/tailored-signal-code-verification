/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs

/-!
# Reachable-state invariants of the FS-AEAD hybrid games

Length and index bounds (`HInv`) on `HState` after `n` Figure 5 queries of `implWith` and
`multiImplWith`, bounding the fuel required by the costed `cumulativeChainPrgReduction` and
`multiSlotOtccaReduction` programs.
-/

@[expose] public section

namespace CryptoGames.FSAEAD.Thm5

open OracleComp OracleSpec

variable {CK MK AD M C : Type}

/-- Reachable-state invariant of a hybrid run after `n` Fig. 5 queries. -/
structure HInv (maxSkip n : ℕ) (st : HState CK MK AD M C) : Prop where
  sent_le : st.lastSentIdx ≤ n
  recv_le : st.receiverIdx ≤ (maxSkip + 1) * n
  keys_sent : st.lastSentIdx ≤ st.keys.length
  keys_recv : st.receiverIdx ≤ st.keys.length
  keys_le : st.keys.length ≤ (maxSkip + 1) * n
  corr_le : ∀ c, st.senderCorruptedAt = some c → c ≤ st.lastSentIdx
  transit_len : st.inTransit.length ≤ n
  chal_len : st.challengesInTransit.length ≤ n
  skipped_sorted : st.skipped.Pairwise (· > ·)
  skipped_pos : ∀ i ∈ st.skipped, 1 ≤ i
  skipped_le : ∀ i ∈ st.skipped, i ≤ st.receiverIdx

namespace HInv

variable {maxSkip n : ℕ} {st : HState CK MK AD M C}

theorem init (b : Bool) : HInv maxSkip 0 ({ b } : HState CK MK AD M C) where
  sent_le := le_rfl
  recv_le := by simp
  keys_sent := le_rfl
  keys_recv := le_rfl
  keys_le := by simp
  corr_le := by simp
  transit_len := le_rfl
  chal_len := le_rfl
  skipped_sorted := List.Pairwise.nil
  skipped_pos := by simp
  skipped_le := by simp

theorem mono (h : HInv maxSkip n st) {n'} (hn : n ≤ n') : HInv maxSkip n' st where
  sent_le := h.sent_le.trans hn
  recv_le := h.recv_le.trans (Nat.mul_le_mul_left _ hn)
  keys_sent := h.keys_sent
  keys_recv := h.keys_recv
  keys_le := h.keys_le.trans (Nat.mul_le_mul_left _ hn)
  corr_le := h.corr_le
  transit_len := h.transit_len.trans hn
  chal_len := h.chal_len.trans hn
  skipped_sorted := h.skipped_sorted
  skipped_pos := h.skipped_pos
  skipped_le := h.skipped_le

theorem length_le_of_sorted_gt : ∀ (l : List ℕ) (r : ℕ), l.Pairwise (· > ·) →
    (∀ i ∈ l, 1 ≤ i) → (∀ i ∈ l, i ≤ r) → l.length ≤ r
  | [], _, _, _, _ => Nat.zero_le _
  | a :: l, r, hs, hp, hl => by
    rw [List.pairwise_cons] at hs
    have ha1 := hp a (by simp)
    have har := hl a (by simp)
    have := length_le_of_sorted_gt l (a - 1) hs.2
      (fun i hi => hp i (by simp [hi]))
      (fun i hi => by have := hs.1 i hi; omega)
    simp only [List.length_cons]; omega

theorem skipped_len (h : HInv maxSkip n st) : st.skipped.length ≤ (maxSkip + 1) * n :=
  (length_le_of_sorted_gt _ _ h.skipped_sorted h.skipped_pos h.skipped_le).trans h.recv_le

end HInv

/-! ## Chain generation -/

section Gen

variable {ι : Type} {T : OracleSpec.{0, 0} ι} [MonadLiftT ProbComp (OracleComp T)]
  [SampleableType MK]
  (G : ℕ → PRGScheme CK (CK × MK)) (P : Params) (D : ℕ → ProbComp (CK × MK))

local notation "St" => HSt CK MK AD M C

theorem genStep_support (s : St) :
    ∀ z ∈ support ((genStep (m := OracleComp T) G P D).run s),
      ∃ K, z.2.1 = { s.1 with keys := s.1.keys ++ [K] } := by
  rcases s with ⟨h, sl⟩
  intro z hz
  cases sl with
  | seed w => simp [genStep] at hz; subst hz; exact ⟨_, rfl⟩
  | mat pos mt =>
    simp only [genStep, StateT.run_mk] at hz
    split at hz
    · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨K, -, rfl⟩ := hz; exact ⟨K, rfl⟩
    · simp at hz; subst hz; exact ⟨_, rfl⟩
  | unknown =>
    simp only [genStep, StateT.run_mk] at hz
    split at hz
    · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨K, -, rfl⟩ := hz; exact ⟨K, rfl⟩
    · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨mt, -, rfl⟩ := hz; exact ⟨mt.2, rfl⟩

theorem genN_support : ∀ (n : ℕ) (s : St),
    ∀ z ∈ support ((genN (m := OracleComp T) G P D n).run s),
      ∃ ks : List MK, ks.length = n ∧ z.2.1 = { s.1 with keys := s.1.keys ++ ks }
  | 0, s, z, hz => by
    simp [genN] at hz; subst hz; exact ⟨[], rfl, by simp⟩
  | n + 1, s, z, hz => by
    simp only [genN, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨K, hK⟩ := genStep_support G P D s y hy
    obtain ⟨ks, hl, hks⟩ := genN_support n y.2 z hz
    refine ⟨K :: ks, by simp [hl], ?_⟩
    rw [hks, hK]; simp

theorem genUpTo_support (i : ℕ) (s : St) :
    ∀ z ∈ support ((genUpTo (m := OracleComp T) G P D i).run s),
      ∃ ks : List MK, ks.length = i - s.1.keys.length ∧
        z.2.1 = { s.1 with keys := s.1.keys ++ ks } := by
  intro z hz
  simp only [genUpTo, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure,
    pure_bind] at hz
  exact genN_support G P D _ s z hz

end Gen

/-! ## Generic oracle handlers and invariant preservation -/

section Generic

variable {ι : Type} {T : OracleSpec.{0, 0} ι} [MonadLiftT ProbComp (OracleComp T)]

local notation "St" => HSt CK MK AD M C

def receiveG [SampleableType MK] (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (P : Params)
    (D : ℕ → ProbComp (CK × MK))
    (dec : Option M → ℕ → AD → C → StateT St (OracleComp T) (Option M))
    (hint : Option M) (a : AD) (c : ℕ × C) : StateT St (OracleComp T) (Option (ℕ × M)) := do
  let (i, e) := c
  let st ← getH
  if st.skipped.contains i then
    match ← dec hint i a e with
    | some msg =>
      modifyH fun st => { st with skipped := st.skipped.filter (· != i) }
      pure (some (i, msg))
    | none => pure none
  else if i ≤ st.receiverIdx ∨ maxSkip < i - st.receiverIdx - 1 then pure none
  else if !P.la && st.lastSentIdx < i && !st.isCompromised i then pure none
  else do
    genUpTo G P D i
    match ← dec hint i a e with
    | some msg =>
      modifyH fun st' => { st' with skipped := newSkipped st.receiverIdx i ++ st'.skipped }
      pure (some (i, msg))
    | none => pure none

def RecvPost (maxSkip : ℕ) (s : St) (z : Option (ℕ × M) × St) : Prop :=
  ∃ ks sk, z.2.1 = { s.1 with keys := s.1.keys ++ ks, skipped := sk } ∧
    ks.length ≤ maxSkip + 1 ∧ sk.Pairwise (· > ·) ∧ (∀ i ∈ sk, 1 ≤ i) ∧
    (∀ i ∈ sk, i ≤ max s.1.receiverIdx (z.1.elim 0 Prod.fst)) ∧
    (∀ r ∈ z.1, r.1 ≤ (s.1.keys ++ ks).length ∧ r.1 ≤ s.1.receiverIdx + (maxSkip + 1))

theorem receiveG_post [SampleableType MK] (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (P : Params) (D : ℕ → ProbComp (CK × MK))
    (dec : Option M → ℕ → AD → C → StateT St (OracleComp T) (Option M))
    (hdec : ∀ h i a e s, ∀ z ∈ support ((dec h i a e).run s), z.2 = s)
    (hint : Option M) (a : AD) (c : ℕ × C) (s : St)
    (hs : s.1.skipped.Pairwise (· > ·)) (hp : ∀ i ∈ s.1.skipped, 1 ≤ i)
    (hl : ∀ i ∈ s.1.skipped, i ≤ s.1.receiverIdx) (hk : s.1.receiverIdx ≤ s.1.keys.length) :
    ∀ z ∈ support ((receiveG G maxSkip P D dec hint a c).run s), RecvPost maxSkip s z := by
  rcases c with ⟨i, e⟩
  rcases s with ⟨h, sl⟩
  intro z hz
  simp only [receiveG, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure,
    pure_bind] at hz
  simp only at hs hp hl hk
  split_ifs at hz with h1 h2 h3
  · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hy2 := hdec _ _ _ _ _ y hy
    rcases y with ⟨_ | msg, s'⟩ <;> simp only at hy2 <;> subst hy2
    · simp at hz; subst hz
      exact ⟨[], h.skipped, by cases h; simp, by simp, hs, hp, by simpa using hl, by simp⟩
    · simp [modifyH, onH] at hz; subst hz
      have hi := hl i (by simpa using h1)
      refine ⟨[], h.skipped.filter (· != i), by cases h; simp, by simp, hs.filter _,
        fun j hj => hp j (List.mem_of_mem_filter hj),
        fun j hj => by have := hl j (List.mem_of_mem_filter hj); simp; omega, ?_⟩
      simp; omega
  · simp at hz; subst hz
    exact ⟨[], h.skipped, by cases h; simp, by simp, hs, hp, by simpa using hl, by simp⟩
  · simp at hz; subst hz
    exact ⟨[], h.skipped, by cases h; simp, by simp, hs, hp, by simpa using hl, by simp⟩
  · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨g, hg, y, hy, hz⟩ := hz
    obtain ⟨ks, hks, hg1⟩ := genUpTo_support G P D i (h, sl) g hg
    have hy2 := hdec _ _ _ _ _ y hy
    rcases y with ⟨_ | msg, s'⟩ <;> simp only at hy2 <;> subst hy2
    · simp at hz; subst hz
      refine ⟨ks, h.skipped, by rw [hg1], by simp at hks; omega, hs, hp, by simpa using hl,
        by simp⟩
    · simp [modifyH, onH] at hz; subst hz
      simp only [not_or, not_le, not_lt] at h2
      refine ⟨ks, newSkipped h.receiverIdx i ++ h.skipped, by rw [hg1], by simp at hks; omega,
        ?_, ?_, ?_, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨?_, hs, ?_⟩
        · simp only [newSkipped]
          rw [List.pairwise_reverse]; exact List.pairwise_lt_range' (step := 1) (by omega)
        · intro a ha b hb
          simp [newSkipped] at ha
          have := hl b hb; omega
      · intro j hj; rcases List.mem_append.mp hj with hj | hj
        · simp [newSkipped] at hj; omega
        · exact hp j hj
      · intro j hj; rcases List.mem_append.mp hj with hj | hj
        · simp [newSkipped] at hj; simp; omega
        · have := hl j hj; simp; omega
      · simp at hks ⊢; omega

section G2
variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]

def deliverG (maxSkip : ℕ)
    (recv : Option M → AD → ℕ × C → StateT St (OracleComp T) (Option (ℕ × M)))
    (q : AD × (ℕ × C)) : StateT St (OracleComp T) (Option (ReceiveResult M)) := do
  let st ← getH
  if st.ended then pure none else
  match st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
  | none => pure none
  | some r =>
    let inWindow := decide (r.idx ≤ st.receiverIdx + maxSkip + 1)
    let mustBeCorrect := !st.isCompromised r.idx && inWindow
    match ← recv (some r.msg) q.1 q.2 with
    | none =>
      modifyH fun st' => { st' with win := st'.win || mustBeCorrect }
      pure (some .rejected)
    | some (i', m') =>
      let incorrect := mustBeCorrect && (i' != r.idx || m' != r.msg)
      let out := if st.challengesInTransit.contains r.idx then none else some m'
      modifyH fun st' => ({ st' with receiverIdx := max st'.receiverIdx i',
                                     win := st'.win || incorrect }).removeFromTransit r.idx
      pure (some (.accepted i' out))

def injectG (P : Params)
    (recv : Option M → AD → ℕ × C → StateT St (OracleComp T) (Option (ℕ × M)))
    (q : AD × (ℕ × C)) : StateT St (OracleComp T) (Option (ReceiveResult M)) := do
  let st ← getH
  if st.ended || st.inTransit.any (fun r => r.ad == q.1 && r.ct == q.2) then pure none else
  match ← recv none q.1 q.2 with
  | none => pure (some .rejected)
  | some (i', m') =>
    let forged := !st.isCompromised i'
    let lfNow := forged && decide (st.lastSentIdx < i')
    modifyH fun st' => ({ st' with receiverIdx := max st'.receiverIdx i',
                                   win := st'.win || forged, lf := st'.lf || lfNow,
                                   ended := st'.ended || (P.la && lfNow) }).removeFromTransit i'
    pure (some (.accepted i' (some m')))

def transmitG [SampleableType MK] (G : ℕ → PRGScheme CK (CK × MK)) (P : Params)
    (D : ℕ → ProbComp (CK × MK)) (enc : ℕ → AD → M → StateT St (OracleComp T) C)
    (q : AD × M) : StateT St (OracleComp T) (Option (ℕ × C)) := do
  let st ← getH
  if st.ended then pure none else do
  let i := st.lastSentIdx + 1
  genUpTo G P D i
  let e ← enc i q.1 q.2
  modifyH fun st =>
    { st with lastSentIdx := i, inTransit := ⟨i, q.1, q.2, (i, e)⟩ :: st.inTransit }
  pure (some (i, e))

def challengeG [SampleableType MK] (G : ℕ → PRGScheme CK (CK × MK)) (P : Params)
    (D : ℕ → ProbComp (CK × MK)) (enc : ℕ → AD → M → StateT St (OracleComp T) C)
    (q : AD × M × M) : StateT St (OracleComp T) (Option (ℕ × C)) := do
  let st ← getH
  if st.ended || st.senderCorruptedAt.isSome then pure none else do
  let i := st.lastSentIdx + 1
  let msg := if st.b then q.2.2 else q.2.1
  genUpTo G P D i
  let e ← enc i q.1 msg
  modifyH fun st =>
    { st with lastSentIdx := i, inTransit := ⟨i, q.1, msg, (i, e)⟩ :: st.inTransit,
              challengesInTransit := i :: st.challengesInTransit }
  pure (some (i, e))

variable [SampleableType MK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK))
  (ops : Option (SpecialOps AD M C (OracleComp T)))

end G2

end Generic

namespace HInv
variable {ms n : ℕ}

theorem step {s s' : HState CK MK AD M C} (h : HInv ms n s)
    (hsent : s'.lastSentIdx ≤ s.lastSentIdx + 1)
    (hrecv : s'.receiverIdx ≤ s.receiverIdx + (ms + 1))
    (hks : s'.keys.length ≤ s.keys.length + (ms + 1))
    (hkS : s'.lastSentIdx ≤ s'.keys.length) (hkR : s'.receiverIdx ≤ s'.keys.length)
    (hcorr : ∀ c, s'.senderCorruptedAt = some c → c ≤ s'.lastSentIdx)
    (htr : s'.inTransit.length ≤ s.inTransit.length + 1)
    (hch : s'.challengesInTransit.length ≤ s.challengesInTransit.length + 1)
    (hs : s'.skipped.Pairwise (· > ·)) (hp : ∀ i ∈ s'.skipped, 1 ≤ i)
    (hl : ∀ i ∈ s'.skipped, i ≤ s'.receiverIdx) : HInv ms (n + 1) s' := by
  have e : (ms + 1) * (n + 1) = (ms + 1) * n + (ms + 1) := Nat.mul_succ _ _
  have h1 := h.sent_le; have h2 := h.recv_le; have h3 := h.keys_le
  have h4 := h.transit_len; have h5 := h.chal_len
  generalize (ms + 1) * n = a at h2 h3 e
  exact ⟨by omega, by omega, hkS, hkR, by omega, hcorr, by omega, by omega, hs, hp, hl⟩

end HInv

section Pres
variable {ι : Type} {T : OracleSpec.{0, 0} ι} [MonadLiftT ProbComp (OracleComp T)]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType MK]
  (G : ℕ → PRGScheme CK (CK × MK)) (P : Params) (D : ℕ → ProbComp (CK × MK)) {ms n : ℕ}

local notation "St" => HSt CK MK AD M C

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem transmitG_inv (enc : ℕ → AD → M → StateT St (OracleComp T) C)
    (henc : ∀ i a m s, ∀ z ∈ support ((enc i a m).run s), z.2 = s) (q : AD × M) (s : St)
    (h : HInv ms n s.1) :
    ∀ z ∈ support ((transmitG G P D enc q).run s), HInv ms (n + 1) z.2.1 := by
  rcases s with ⟨st, sl⟩
  intro z hz
  simp only [transmitG, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure,
    pure_bind] at hz
  split_ifs at hz with he
  · simp at hz; subst hz; exact h.mono (by omega)
  · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨g, hg, y, hy, hz⟩ := hz
    obtain ⟨ks, hks, hg1⟩ := genUpTo_support G P D _ _ g hg
    have hy2 := henc _ _ _ _ y hy
    simp [modifyH, onH] at hz; subst hz
    rw [hy2, hg1]
    have k1 : st.lastSentIdx ≤ st.keys.length := h.keys_sent
    have k2 : st.receiverIdx ≤ st.keys.length := h.keys_recv
    have k3 : ∀ c, st.senderCorruptedAt = some c → c ≤ st.lastSentIdx := h.corr_le
    simp only at hks
    apply h.step <;> simp <;> first | omega | (intro c hc; have := k3 c hc; omega) | skip
    · exact h.skipped_sorted
    · exact h.skipped_pos
    · exact h.skipped_le

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem challengeG_inv (enc : ℕ → AD → M → StateT St (OracleComp T) C)
    (henc : ∀ i a m s, ∀ z ∈ support ((enc i a m).run s), z.2 = s) (q : AD × M × M) (s : St)
    (h : HInv ms n s.1) :
    ∀ z ∈ support ((challengeG G P D enc q).run s), HInv ms (n + 1) z.2.1 := by
  rcases s with ⟨st, sl⟩
  intro z hz
  simp only [challengeG, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure,
    pure_bind] at hz
  split_ifs at hz with he
  · simp at hz; subst hz; exact h.mono (by omega)
  all_goals
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨g, hg, y, hy, hz⟩ := hz
    obtain ⟨ks, hks, hg1⟩ := genUpTo_support G P D _ _ g hg
    have hy2 := henc _ _ _ _ y hy
    simp [modifyH, onH] at hz; subst hz
    rw [hy2, hg1]
    have k1 : st.lastSentIdx ≤ st.keys.length := h.keys_sent
    have k2 : st.receiverIdx ≤ st.keys.length := h.keys_recv
    have k3 : ∀ c, st.senderCorruptedAt = some c → c ≤ st.lastSentIdx := h.corr_le
    simp only at hks
    apply h.step <;> simp <;> first | omega | (intro c hc; have := k3 c hc; omega) | skip
    · exact h.skipped_sorted
    · exact h.skipped_pos
    · exact h.skipped_le

variable (ms) in
def RecvOK (recv : Option M → AD → ℕ × C → StateT St (OracleComp T) (Option (ℕ × M))) : Prop :=
  ∀ hint a c (s : St), HInv ms n s.1 → ∀ z ∈ support ((recv hint a c).run s), RecvPost ms s z

omit [MonadLiftT ProbComp (OracleComp T)] [SampleableType MK] in
theorem deliverG_inv (recv : Option M → AD → ℕ × C → StateT St (OracleComp T) (Option (ℕ × M)))
    (hrecv : RecvOK ms (n := n) recv) (q : AD × (ℕ × C)) (s : St)
    (h : HInv ms n s.1) :
    ∀ z ∈ support ((deliverG ms recv q).run s), HInv ms (n + 1) z.2.1 := by
  rcases s with ⟨st, sl⟩
  intro z hz
  simp only [deliverG, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure,
    pure_bind] at hz
  split_ifs at hz with he
  · simp at hz; subst hz; exact h.mono (by omega)
  split at hz
  · simp at hz; subst hz; exact h.mono (by omega)
  rename_i r hfind
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨y, hy, hz⟩ := hz
  obtain ⟨ks, sk, hy1, hks, hs, hp, hl, hr⟩ := hrecv _ _ _ _ h y hy
  have k1 : st.lastSentIdx ≤ st.keys.length := h.keys_sent
  have k2 : st.receiverIdx ≤ st.keys.length := h.keys_recv
  have k3 : ∀ c, st.senderCorruptedAt = some c → c ≤ st.lastSentIdx := h.corr_le
  rcases y with ⟨_ | ⟨i', m'⟩, s'⟩
  · simp [modifyH, onH] at hz; subst hz
    simp only at hy1 ⊢; rw [hy1]
    simp at hl
    apply h.step <;> simp <;> omega
  · simp [modifyH, onH] at hz; subst hz
    simp only at hy1 hr ⊢; rw [hy1]
    simp at hl hr
    have f1 := List.length_filter_le (fun x : Record AD M (ℕ × C) => x.idx != r.idx) st.inTransit
    have f2 := List.length_filter_le (fun x : ℕ => x != r.idx) st.challengesInTransit
    simp [HState.removeFromTransit]
    apply h.step <;> simp <;> omega

omit [MonadLiftT ProbComp (OracleComp T)] [DecidableEq M] [SampleableType MK] in
theorem injectG_inv (recv : Option M → AD → ℕ × C → StateT St (OracleComp T) (Option (ℕ × M)))
    (hrecv : RecvOK ms (n := n) recv) (q : AD × (ℕ × C)) (s : St)
    (h : HInv ms n s.1) :
    ∀ z ∈ support ((injectG P recv q).run s), HInv ms (n + 1) z.2.1 := by
  rcases s with ⟨st, sl⟩
  intro z hz
  simp only [injectG, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure,
    pure_bind] at hz
  split_ifs at hz with he
  · simp at hz; subst hz; exact h.mono (by omega)
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨y, hy, hz⟩ := hz
  obtain ⟨ks, sk, hy1, hks, hs, hp, hl, hr⟩ := hrecv _ _ _ _ h y hy
  have k1 : st.lastSentIdx ≤ st.keys.length := h.keys_sent
  have k2 : st.receiverIdx ≤ st.keys.length := h.keys_recv
  have k3 : ∀ c, st.senderCorruptedAt = some c → c ≤ st.lastSentIdx := h.corr_le
  rcases y with ⟨_ | ⟨i', m'⟩, s'⟩
  · simp at hz; subst hz
    simp only at hy1 ⊢; rw [hy1]
    simp at hl
    apply h.step <;> simp <;> omega
  · simp [modifyH, onH] at hz; subst hz
    simp only at hy1 hr ⊢; rw [hy1]
    simp at hl hr
    have f1 := List.length_filter_le (fun x : Record AD M (ℕ × C) => x.idx != i') st.inTransit
    have f2 := List.length_filter_le (fun x : ℕ => x != i') st.challengesInTransit
    simp [HState.removeFromTransit]
    apply h.step <;> simp <;> omega

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType MK] in
theorem senderKey_fst [SampleableType CK] (s : St) :
    ∀ z ∈ support ((senderKey (m := OracleComp T) (AD := AD) (M := M)
      (C := C) (MK := MK) G).run s), z.2.1 = s.1 := by
  rcases s with ⟨st, sl⟩
  intro z hz
  simp only [senderKey, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure,
    pure_bind] at hz
  split at hz
  · simp at hz; subst hz; rfl
  · simp only [reveal, StateT.run_mk] at hz
    split at hz
    · simp at hz; subst hz; rfl
    · simp at hz; obtain ⟨u, -, rfl⟩ := hz; rfl

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType MK] in
theorem corruptSenderH_inv [SampleableType CK] (s : St) (h : HInv ms n s.1) :
    ∀ z ∈ support ((corruptSenderH (m := OracleComp T) (AD := AD) (M := M) (C := C) (MK := MK)
      G P ()).run s), HInv ms (n + 1) z.2.1 := by
  rcases s with ⟨st, sl⟩
  intro z hz
  simp only [corruptSenderH, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get, map_pure,
    pure_bind] at hz
  split_ifs at hz
  · simp at hz; subst hz; exact h.mono (by omega)
  · simp [modifyH, onH] at hz; subst hz; refine HInv.mono (n := n) ?_ (by omega)
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩
  · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw1 := senderKey_fst G _ w hw
    simp [modifyH, onH] at hz; subst hz
    rw [hw1]
    have k3 : ∀ c, st.senderCorruptedAt = some c → c ≤ st.lastSentIdx := h.corr_le
    refine HInv.mono (n := n) ?_ (by omega)
    refine ⟨h.1, h.2, h.3, h.4, h.5, ?_, h.7, h.8, h.9, h.10, h.11⟩
    intro c hc
    simp only at hc ⊢
    cases e : st.senderCorruptedAt with
    | none => simp [e] at hc; omega
    | some c' => simp [e] at hc; have := k3 c' e; omega

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType MK] in
theorem corruptReceiverH_inv [SampleableType CK] (s : St) (h : HInv ms n s.1) :
    ∀ z ∈ support ((corruptReceiverH (m := OracleComp T) (AD := AD) (M := M) (C := C) (MK := MK)
      G P ()).run s), HInv ms (n + 1) z.2.1 := by
  rcases s with ⟨st, sl⟩
  intro z hz
  simp only [corruptReceiverH, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    map_pure, pure_bind] at hz
  split_ifs at hz
  · simp at hz; subst hz; exact h.mono (by omega)
  · simp [modifyH, onH] at hz; subst hz; refine HInv.mono (n := n) ?_ (by omega)
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩
  · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw1 := senderKey_fst G _ w hw
    rcases w with ⟨w, ⟨st', sl'⟩⟩
    simp only at hw1; subst hw1
    simp [modifyH, onH] at hz; subst hz
    refine HInv.mono (n := n) ?_ (by omega)
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩

end Pres

section Frames
variable {ι : Type} {T : OracleSpec.{0, 0} ι} [MonadLiftT ProbComp (OracleComp T)]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (P : Params) (mSlot : ℕ)
  (ops : Option (SpecialOps AD M C (OracleComp T)))

local notation "St" => HSt CK MK AD M C

theorem multiEncIdxWith_frame : ∀ i a msg (s : St),
    ∀ z ∈ support ((multiEncIdxWith ideal ae (P.t.getD 0) mSlot ops i a msg).run s), z.2 = s := by
  intro i a msg s z hz
  simp only [multiEncIdxWith, getH, onH, sampleH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    map_pure, pure_bind] at hz
  split at hz <;> (try split at hz) <;> simp at hz <;>
    first | (subst hz; rfl) | (obtain ⟨_, _, rfl⟩ := hz; rfl)

omit [MonadLiftT ProbComp (OracleComp T)] in
theorem multiDecIdx_frame : ∀ h i a e (s : St),
    ∀ z ∈ support ((multiDecIdx ae (P.t.getD 0) mSlot ops h i a e).run s), z.2 = s := by
  intro h i a e s z hz
  cases h with
  | some msg => simp [multiDecIdx] at hz; subst hz; rfl
  | none =>
  simp only [multiDecIdx, getH, onH, StateT.run_bind, StateT.run_mk, StateT.run_get,
    map_pure, pure_bind] at hz
  split at hz <;> simp at hz <;>
    first | (subst hz; rfl) | (obtain ⟨_, _, rfl⟩ := hz; rfl)

end Frames

section Impl
variable {ι : Type} {T : OracleSpec.{0, 0} ι} [MonadLiftT ProbComp (OracleComp T)]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType MK] [SampleableType CK]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK))
  (ops : Option (SpecialOps AD M C (OracleComp T))) {ms n : ℕ}

local notation "St" => HSt CK MK AD M C

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] [SampleableType CK] in
theorem recvOK_of_frame (dec : Option M → ℕ → AD → C → StateT St (OracleComp T) (Option M))
    (hdec : ∀ h i a e s, ∀ z ∈ support ((dec h i a e).run s), z.2 = s) :
    RecvOK ms (n := n) (receiveG G ms P D dec) := fun hint a c s h =>
  receiveG_post G ms P D dec hdec hint a c s h.skipped_sorted h.skipped_pos h.skipped_le
    h.keys_recv

theorem multiImplWith_inv (t : ℕ ⊕ _) (s : St) (h : HInv ms n s.1) :
    ∀ z ∈ support (((multiImplWith (m := OracleComp T) ideal ae G ms P mSlot D ops) t).run s),
      HInv ms (if t.isRight = true then n + 1 else n) z.2.1 := by
  rcases t with u | (((((q | q) | u) | u) | q) | q)
  · intro z hz
    simp only [multiImplWith, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, StateT.run_monadLift, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact h
  · exact transmitG_inv G P D _ (multiEncIdxWith_frame ideal ae P mSlot ops) q s h
  · exact challengeG_inv G P D _ (multiEncIdxWith_frame ideal ae P mSlot ops) q s h
  · exact corruptSenderH_inv G P s h
  · exact corruptReceiverH_inv G P s h
  · exact deliverG_inv _ (recvOK_of_frame G P D _ (multiDecIdx_frame ae P mSlot ops)) q s h
  · exact injectG_inv P _ (recvOK_of_frame G P D _ (multiDecIdx_frame ae P mSlot ops)) q s h

end Impl

end CryptoGames.FSAEAD.Thm5

