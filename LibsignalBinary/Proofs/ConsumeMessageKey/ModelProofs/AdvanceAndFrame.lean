/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.ModelDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalSignalMessage

/-!
# `Mut.exec`, List-Frame, and Chain-Step Lemmas for `consume_message_key`

Helper lemmas unfolding `Mut.exec` (`ExceptT SignalProtocolError (StateM σ)`), preserving
`List.findIdx?` across `senderRatchetKey`-preserving `List.set` updates, and reducing
`storeSkippedKey`, `setReceiverChainKey`, and `takeSkippedKey` to closed forms.
-/

@[expose] public section

namespace CryptoVerification.SessionModel.AdvanceAndFrame

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

/-! ## `Mut.exec` Simplification Lemmas -/

@[local simp] theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := by
  rfl

@[local simp] theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r) s = (r, s) := by
  cases r <;> rfl

@[local simp] theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  simp only [Mut.exec, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind, StateT.run,
    ExceptT.bindCont]
  cases m s with
  | mk res s' => cases res <;> rfl

@[local simp] private theorem exec_map {σ α β : Type} (g : α → β) (m : Mut σ α) (s : σ) :
    Mut.exec (g <$> m) s =
      match Mut.exec m s with
      | (.ok a, s') => (.ok (g a), s')
      | (.error e, s') => (.error e, s') := by
  rw [← bind_pure_comp, exec_bind]
  cases Mut.exec m s with
  | mk res s' => cases res <;> rfl

@[local simp] private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := by
  rfl

@[local simp] private theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := by
  rfl

@[local simp] private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := by
  rfl

theorem findIdx?_go_set_of_eq {α : Type} (p : α → Bool) (xs : List α) (i k : ℕ) (x : α)
    (h : ∃ x₀ ∈ xs[i]?, p x₀ = p x) :
    List.findIdx?.go p (xs.set i x) k = List.findIdx?.go p xs k := by
  induction xs generalizing i k with
  | nil =>
    rcases h with ⟨_, hmem, _⟩
    simp at hmem
  | cons hd tl ih =>
    cases i with
    | zero =>
      rcases h with ⟨x₀, hmem, hp⟩
      simp only [List.getElem?_cons_zero, Option.mem_def, Option.some.injEq] at hmem
      subst hmem
      simp only [List.set_cons_zero, List.findIdx?.go, hp]
    | succ i' =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ, List.findIdx?.go]
      cases p hd with
      | true => rfl
      | false => exact ih i' (k + 1) h

theorem findReceiverChainIndex_set_thm (st : RatchetState) (their : PublicKey) (i : ℕ)
    (ch : ReceiverChain) (h : ∃ ch₀ ∈ st.receiverChains[i]?, ch₀.senderRatchetKey = ch.senderRatchetKey) :
    RatchetState.findReceiverChainIndex { st with receiverChains := st.receiverChains.set i ch } their =
      st.findReceiverChainIndex their := by
  simp only [RatchetState.findReceiverChainIndex, List.findIdx?]
  apply findIdx?_go_set_of_eq
  rcases h with ⟨ch₀, hmem, hkey⟩
  exact ⟨ch₀, hmem, by rw [hkey]⟩

private theorem getElem?_of_findIdx?_go {α : Type} (p : α → Bool) (xs : List α) (k i : ℕ)
    (h : List.findIdx?.go p xs k = some i) :
    k ≤ i ∧ ∃ x, xs[i - k]? = some x ∧ p x = true := by
  induction xs generalizing k with
  | nil => simp [List.findIdx?.go] at h
  | cons hd tl ih =>
    simp only [List.findIdx?.go] at h
    cases hphd : p hd with
    | true =>
      rw [hphd] at h
      simp only [ite_true, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hd, by simp, hphd⟩
    | false =>
      rw [hphd] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hle, x, hx, hpx⟩ := ih (k + 1) h
      refine ⟨by omega, x, ?_, hpx⟩
      have hsub : i - k = (i - (k + 1)) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ]
      exact hx

theorem getElem?_of_findIdx? {α : Type} (p : α → Bool) (xs : List α) (i : ℕ)
    (h : xs.findIdx? p = some i) :
    ∃ x, xs[i]? = some x ∧ p x = true := by
  simp only [List.findIdx?] at h
  obtain ⟨_, x, hx, hpx⟩ := getElem?_of_findIdx?_go p xs 0 i h
  simpa using ⟨x, hx, hpx⟩

theorem getElem?_of_findReceiverChainIndex (st : RatchetState) (their : PublicKey) (ci : ℕ)
    (h : st.findReceiverChainIndex their = some ci) :
    ∃ ch, st.receiverChains[ci]? = some ch ∧ (ch.senderRatchetKey == their) = true :=
  getElem?_of_findIdx? _ _ _ h

theorem getElem?_set_eq_of_some {α : Type} (xs : List α) (i : ℕ) (x₀ x : α)
    (h : xs[i]? = some x₀) :
    (xs.set i x)[i]? = some x := by
  induction xs generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.getElem?_cons_succ] at h
      simpa using ih i' h

theorem set_set_eq {α : Type} (xs : List α) (i : ℕ) (x₁ x₂ : α) :
    (xs.set i x₁).set i x₂ = xs.set i x₂ :=
  List.set_set x₁

theorem set_eq_self_of_getElem?_eq_some {α : Type} (xs : List α) (i : ℕ) (x : α)
    (h : xs[i]? = some x) :
    xs.set i x = xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      simp [h]
    | succ i' =>
      simp only [List.getElem?_cons_succ] at h
      simp [ih i' h]

theorem map_set_of_eq {α β : Type} (f : α → β) (xs : List α) (i : ℕ) (x : α)
    (h : ∃ x₀ ∈ xs[i]?, f x₀ = f x) :
    (xs.set i x).map f = xs.map f := by
  induction xs generalizing i with
  | nil =>
    rcases h with ⟨_, hmem, _⟩
    simp at hmem
  | cons hd tl ih =>
    cases i with
    | zero =>
      rcases h with ⟨x₀, hmem, hfx⟩
      simp only [List.getElem?_cons_zero, Option.mem_def, Option.some.injEq] at hmem
      subst hmem
      simp [hfx]
    | succ i' =>
      simp only [List.getElem?_cons_succ] at h
      simp [ih i' h]

theorem mem_of_getElem?_some {α : Type} (xs : List α) (i : ℕ) (x : α)
    (h : xs[i]? = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    | succ i' =>
      simp only [List.getElem?_cons_succ] at h
      exact List.mem_cons_of_mem hd (ih i' h)

theorem mem_set_or {α : Type} (xs : List α) (i : ℕ) (x y : α)
    (h : y ∈ xs.set i x) : y = x ∨ y ∈ xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at h
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem hd htl)
    | succ i' =>
      simp only [List.set_cons_succ, List.mem_cons] at h
      rcases h with rfl | htl
      · exact Or.inr (List.mem_cons_self ..)
      · exact (ih i' htl).imp id (List.mem_cons_of_mem hd)

theorem mem_of_mem_eraseIdx {α : Type} (xs : List α) (i : ℕ) (y : α)
    (h : y ∈ xs.eraseIdx i) : y ∈ xs :=
  List.mem_of_mem_eraseIdx h

def step1 (F : ShaCompress) (ck : ChainKey) : ChainKey :=
  ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩

theorem nextChainKey_eq_of_ne (F : ShaCompress) (ck : ChainKey)
    (h : ck.index ≠ BitVec.allOnes 32) :
    ck.nextChainKey F = .ok (step1 F ck) := by
  unfold ChainKey.nextChainKey
  split
  · exact absurd ‹_› h
  · rfl

theorem index_lt_of_add_succ_eq (ck : ChainKey) (c : BitVec 32) (m : ℕ)
    (h : ck.index.toNat + (m + 1) = c.toNat) :
    ck.index < c := by
  rw [BitVec.lt_def]
  omega

theorem index_ne_allOnes_of_add_succ_eq (ck : ChainKey) (c : BitVec 32) (m : ℕ)
    (h : ck.index.toNat + (m + 1) = c.toNat) :
    ck.index ≠ BitVec.allOnes 32 := by
  intro hall
  have hc : c.toNat < 2 ^ 32 := c.isLt
  have h1 : ck.index.toNat = 2 ^ 32 - 1 := by
    rw [hall]
    rfl
  omega

theorem step1_index_toNat_add (F : ShaCompress) (ck : ChainKey) (c : BitVec 32) (m : ℕ)
    (h : ck.index.toNat + (m + 1) = c.toNat) :
    (step1 F ck).index.toNat + m = c.toNat := by
  have hc : c.toNat < 2 ^ 32 := c.isLt
  have hadd : (ck.index + 1).toNat = ck.index.toNat + 1 := by
    rw [BitVec.toNat_add]
    change (ck.index.toNat + 1) % 2 ^ 32 = ck.index.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [step1]
  omega

theorem chainStepN_index_eq (F : ShaCompress) (n : ℕ) (ck : ChainKey) (c : BitVec 32)
    (h : ck.index.toNat + n = c.toNat) :
    (chainStepN F n ck).index = c := by
  induction n generalizing ck with
  | zero =>
    simp only [chainStepN]
    exact BitVec.eq_of_toNat_eq (by omega)
  | succ m ih =>
    simp only [chainStepN]
    exact ih (step1 F ck) (step1_index_toNat_add F ck c m h)

theorem index_toNat_add_sub_eq (ck : ChainKey) (c : BitVec 32) (h : ck.index ≤ c) :
    ck.index.toNat + (c - ck.index).toNat = c.toNat := by
  have hle : ck.index.toNat ≤ c.toNat := BitVec.le_def.mp h
  have hc : c.toNat < 2 ^ 32 := c.isLt
  have hck : ck.index.toNat < 2 ^ 32 := ck.index.isLt
  rw [BitVec.toNat_sub]
  omega

theorem storeSkippedKey_exec_some (their : PublicKey) (k : MessageKeyGenerator)
    (st : RatchetState) (ci : ℕ) (ch : ReceiverChain)
    (hci : st.findReceiverChainIndex their = some ci)
    (hch : st.receiverChains[ci]? = some ch) :
    (RatchetState.storeSkippedKey their k).exec st =
      let keys := if maxMessageKeys < (k :: ch.messageKeys).length then (k :: ch.messageKeys).dropLast else (k :: ch.messageKeys)
      (.ok (), { st with receiverChains := st.receiverChains.set ci { ch with messageKeys := keys } }) := by
  simp [RatchetState.storeSkippedKey, hci, hch]

theorem storeSkippedKey_exec_none (their : PublicKey) (k : MessageKeyGenerator)
    (st : RatchetState) (hci : st.findReceiverChainIndex their = none) :
    (RatchetState.storeSkippedKey their k).exec st = (.error .panic, st) := by
  simp [RatchetState.storeSkippedKey, hci]

theorem setReceiverChainKey_exec_some (their : PublicKey) (ck : ChainKey)
    (st : RatchetState) (ci : ℕ) (ch : ReceiverChain)
    (hci : st.findReceiverChainIndex their = some ci)
    (hch : st.receiverChains[ci]? = some ch) :
    (RatchetState.setReceiverChainKey their ck).exec st =
      (.ok (), { st with receiverChains := st.receiverChains.set ci { ch with chainKey := some ck } }) := by
  simp [RatchetState.setReceiverChainKey, hci, hch]

theorem setReceiverChainKey_exec_none (their : PublicKey) (ck : ChainKey)
    (st : RatchetState) (hci : st.findReceiverChainIndex their = none) :
    (RatchetState.setReceiverChainKey their ck).exec st = (.error .panic, st) := by
  simp [RatchetState.setReceiverChainKey, hci]

theorem takeSkippedKey_exec (their : PublicKey) (c : BitVec 32) (st : RatchetState) :
    (∃ st', (RatchetState.takeSkippedKey their c).exec st = (.ok none, st') ∧ st' = st) ∨
    (∃ k ci ch pos,
      st.findReceiverChainIndex their = some ci ∧
      st.receiverChains[ci]? = some ch ∧
      ch.messageKeys.findIdx? (fun mk => mk.counter == c) = some pos ∧
      ch.messageKeys[pos]? = some k ∧
      (RatchetState.takeSkippedKey their c).exec st =
        (.ok (some k),
          { st with receiverChains := st.receiverChains.set ci { ch with messageKeys := ch.messageKeys.eraseIdx pos } })) := by
  cases hci : st.findReceiverChainIndex their with
  | none =>
    exact Or.inl ⟨st, by simp [RatchetState.takeSkippedKey, hci], rfl⟩
  | some ci =>
    obtain ⟨ch, hch, _⟩ := getElem?_of_findReceiverChainIndex st their ci hci
    cases hpos : ch.messageKeys.findIdx? (fun mk => mk.counter == c) with
    | none =>
      exact Or.inl ⟨st, by simp [RatchetState.takeSkippedKey, hci, hch, hpos], rfl⟩
    | some pos =>
      obtain ⟨k, hk, _⟩ := getElem?_of_findIdx? _ _ _ hpos
      refine Or.inr ⟨k, ci, ch, pos, rfl, hch, hpos, hk, ?_⟩
      simp [RatchetState.takeSkippedKey, hci, hch, hpos, hk]


/-! ## Compatibility Lemmas -/

section MoveCompat
set_option linter.unusedSimpArgs false

private theorem length_eraseIdx_le {α : Type} (xs : List α) (i : ℕ) :
    (xs.eraseIdx i).length ≤ xs.length := by
  induction xs generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ j =>
      simp only [List.eraseIdx_cons_succ, List.length_cons]
      have := ih j
      omega

private theorem dropLast_eq_take_of_length {α : Type} (xs : List α) (n : ℕ)
    (h : xs.length = n + 1) :
    xs.dropLast = xs.take n := by
  induction xs generalizing n with
  | nil => simp at h
  | cons a as ih =>
    cases as with
    | nil =>
      cases n with
      | zero => rfl
      | succ m => simp at h
    | cons b bs =>
      cases n with
      | zero => simp at h
      | succ m =>
        simp only [List.length_cons] at h
        simp [List.dropLast, ih m (by simp; omega)]

private theorem take_of_length_le_eq {α : Type} (xs : List α) (n : ℕ)
    (h : xs.length ≤ n) :
    xs.take n = xs := by
  induction xs generalizing n with
  | nil => simp
  | cons a as ih =>
    cases n with
    | zero => simp at h
    | succ m =>
      simp only [List.length_cons] at h
      simp [ih m (by omega)]

private theorem storeSkippedKey_keys_eq {α : Type} (k : α) (ms : List α) (n : ℕ)
    (h : ms.length ≤ n) :
    (if n < (k :: ms).length then (k :: ms).dropLast else (k :: ms)) =
      (k :: ms).take n := by
  split
  · next hlt =>
    simp only [List.length_cons] at hlt
    have heq : (k :: ms).length = n + 1 := by simp; omega
    exact dropLast_eq_take_of_length (k :: ms) n heq
  · next hnlt =>
    simp only [List.length_cons] at hnlt
    exact (take_of_length_le_eq (k :: ms) n (by simp; omega)).symm

private theorem take_take_eq {α : Type} (xs : List α) (n m : ℕ) (h : n ≤ m) :
    (xs.take m).take n = xs.take n := by
  induction xs generalizing n m with
  | nil => simp
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n' =>
      cases m with
      | zero => omega
      | succ m' =>
        simp [ih n' m' (by omega)]

private theorem take_append_take_le {α : Type} (ys xs : List α) (n m : ℕ) (h : n ≤ m) :
    (ys ++ xs.take m).take n = (ys ++ xs).take n := by
  induction ys generalizing n with
  | nil => simpa using take_take_eq xs n m h
  | cons y ys ih =>
    cases n with
    | zero => rfl
    | succ n' =>
      simp [ih n' (by omega)]

private theorem take_append_take {α : Type} (ys xs : List α) (m : ℕ) :
    (ys ++ xs.take m).take m = (ys ++ xs).take m :=
  take_append_take_le ys xs m m le_rfl

private theorem length_take_le' {α : Type} (xs : List α) (n : ℕ) :
    (xs.take n).length ≤ n := by
  induction xs generalizing n with
  | nil => simp
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp only [List.take_succ_cons, List.length_cons]
      have := ih m
      omega

private theorem mem_of_mem_take' {α : Type} (xs : List α) (n : ℕ) (y : α)
    (h : y ∈ xs.take n) : y ∈ xs := by
  induction xs generalizing n with
  | nil => simp at h
  | cons a as ih =>
    cases n with
    | zero => simp at h
    | succ m =>
      simp only [List.take_succ_cons, List.mem_cons] at h
      rcases h with rfl | hy
      · exact List.Mem.head as
      · exact List.Mem.tail a (ih m hy)

private theorem length_sha256With (F : ShaCompress) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  generalize (chunks64 (sha256Pad m)).foldl F sha256IV = s
  rcases s with ⟨l, hl⟩
  simp [toBEBytes, List.length_flatMap, hl]

private theorem messageKeys_seed_ne_nil (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed ≠ [] := by
  intro h
  have hlen : (ck.messageKeys F).seed.length = 32 := length_sha256With F _
  rw [h] at hlen
  contradiction

private theorem mem_skippedKeys_seed_ne_nil (F : ShaCompress) (n : ℕ) (ck : ChainKey)
    (k : MessageKeyGenerator) (hk : k ∈ skippedKeys F n ck) :
    k.seed ≠ [] := by
  induction n generalizing ck with
  | zero => simp [skippedKeys] at hk
  | succ m ih =>
    simp only [skippedKeys, List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | rfl
    · exact ih _ hk
    · exact messageKeys_seed_ne_nil F ck

private theorem advanceChain_exec_some (F : ShaCompress) (their : PublicKey) (c : BitVec 32)
    (n : ℕ) (ck : ChainKey) (st : RatchetState) (ci : ℕ) (ch : ReceiverChain)
    (hn : ck.index.toNat + n = c.toNat)
    (hci : st.findReceiverChainIndex their = some ci)
    (hch : st.receiverChains[ci]? = some ch)
    (hlen : ch.messageKeys.length ≤ maxMessageKeys) :
    (RatchetState.advanceChain F their c n ck).exec st =
      (.ok (chainStepN F n ck),
        { st with
          receiverChains := st.receiverChains.set ci
            { ch with messageKeys := (skippedKeys F n ck ++ ch.messageKeys).take maxMessageKeys } }) := by
  induction n generalizing ck st ch with
  | zero =>
    simp only [RatchetState.advanceChain, exec_pure, chainStepN, skippedKeys, List.nil_append,
      take_of_length_le_eq ch.messageKeys maxMessageKeys hlen]
    have hch_eq : { ch with messageKeys := ch.messageKeys } = ch := rfl
    rw [hch_eq, set_eq_self_of_getElem?_eq_some st.receiverChains ci ch hch]
  | succ m ih =>
    have hlt : ck.index < c := index_lt_of_add_succ_eq ck c m hn
    have hne : ck.index ≠ BitVec.allOnes 32 := index_ne_allOnes_of_add_succ_eq ck c m hn
    have hnext : ck.nextChainKey F = .ok (step1 F ck) := nextChainKey_eq_of_ne F ck hne
    let ch₁ : ReceiverChain :=
      { ch with messageKeys := (ck.messageKeys F :: ch.messageKeys).take maxMessageKeys }
    let st₁ : RatchetState := { st with receiverChains := st.receiverChains.set ci ch₁ }
    have hstore : (RatchetState.storeSkippedKey their (ck.messageKeys F)).exec st = (.ok (), st₁) := by
      rw [storeSkippedKey_exec_some their (ck.messageKeys F) st ci ch hci hch]
      simp only [storeSkippedKey_keys_eq (ck.messageKeys F) ch.messageKeys maxMessageKeys hlen, st₁, ch₁]
    have hci₁ : st₁.findReceiverChainIndex their = some ci := by
      rw [findReceiverChainIndex_set_thm st their ci ch₁ ⟨ch, hch, rfl⟩, hci]
    have hch₁ : st₁.receiverChains[ci]? = some ch₁ :=
      getElem?_set_eq_of_some st.receiverChains ci ch ch₁ hch
    have hlen₁ : ch₁.messageKeys.length ≤ maxMessageKeys :=
      length_take_le' _ maxMessageKeys
    have hn₁ : (step1 F ck).index.toNat + m = c.toNat :=
      step1_index_toNat_add F ck c m hn
    simp only [RatchetState.advanceChain, hlt, ↓reduceIte, exec_bind, hstore, exec_liftE, hnext]
    rw [ih (step1 F ck) st₁ ch₁ hn₁ hci₁ hch₁ hlen₁]
    simp only [chainStepN, skippedKeys, st₁, ch₁, set_set_eq]
    have hkeys :
        (skippedKeys F m (step1 F ck) ++ (ck.messageKeys F :: ch.messageKeys).take maxMessageKeys).take maxMessageKeys =
          ((skippedKeys F m (step1 F ck) ++ [ck.messageKeys F]) ++ ch.messageKeys).take maxMessageKeys := by
      rw [take_append_take, List.append_assoc, List.singleton_append]
    rw [hkeys]
    rfl

private theorem advanceChain_exec_some_raw (F : ShaCompress) (their : PublicKey) (c : BitVec 32)
    (n : ℕ) (ck : ChainKey) (st : RatchetState) (ci : ℕ) (ch : ReceiverChain)
    (hn : ck.index.toNat + n = c.toNat)
    (hci : st.findReceiverChainIndex their = some ci)
    (hch : st.receiverChains[ci]? = some ch) :
    ∃ st' ch',
      (RatchetState.advanceChain F their c n ck).exec st = (.ok (chainStepN F n ck), st') ∧
      st'.findReceiverChainIndex their = some ci ∧
      st'.receiverChains[ci]? = some ch' := by
  induction n generalizing ck st ch with
  | zero =>
    exact ⟨st, ch, rfl, hci, hch⟩
  | succ m ih =>
    have hlt : ck.index < c := index_lt_of_add_succ_eq ck c m hn
    have hne : ck.index ≠ BitVec.allOnes 32 := index_ne_allOnes_of_add_succ_eq ck c m hn
    have hnext : ck.nextChainKey F = .ok (step1 F ck) := nextChainKey_eq_of_ne F ck hne
    let keys := if maxMessageKeys < (ck.messageKeys F :: ch.messageKeys).length then
      (ck.messageKeys F :: ch.messageKeys).dropLast else (ck.messageKeys F :: ch.messageKeys)
    let ch₁ : ReceiverChain := { ch with messageKeys := keys }
    let st₁ : RatchetState := { st with receiverChains := st.receiverChains.set ci ch₁ }
    have hstore : (RatchetState.storeSkippedKey their (ck.messageKeys F)).exec st = (.ok (), st₁) :=
      storeSkippedKey_exec_some their (ck.messageKeys F) st ci ch hci hch
    have hci₁ : st₁.findReceiverChainIndex their = some ci := by
      rw [findReceiverChainIndex_set_thm st their ci ch₁ ⟨ch, hch, rfl⟩, hci]
    have hch₁ : st₁.receiverChains[ci]? = some ch₁ :=
      getElem?_set_eq_of_some st.receiverChains ci ch ch₁ hch
    have hn₁ : (step1 F ck).index.toNat + m = c.toNat :=
      step1_index_toNat_add F ck c m hn
    simp only [RatchetState.advanceChain, hlt, ↓reduceIte, exec_bind, hstore, exec_liftE, hnext]
    exact ih (step1 F ck) st₁ ch₁ hn₁ hci₁ hch₁

theorem consumeMessageKey_advance_thm (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) (hc : c ≠ BitVec.allOnes 32)
    (h : ck.index ≤ c) (hj : (c - ck.index).toNat ≤ st.maxForwardJumps)
    (ci : ℕ) (hci : st.findReceiverChainIndex their = some ci) (hok : ChainsOk st) :
    ∃ ch, st.receiverChains[ci]? = some ch ∧
    (RatchetState.consumeMessageKey F their ck c t).exec st =
      let n := (c - ck.index).toNat
      let ckc := chainStepN F n ck
      (.ok (ckc.messageKeys F),
        { st with
          receiverChains := st.receiverChains.set ci
            ({ ch with
                messageKeys := (skippedKeys F n ck ++ ch.messageKeys).take maxMessageKeys
                chainKey := some (chainStepN F 1 ckc) }) }) := by
  obtain ⟨ch, hch, _⟩ := getElem?_of_findReceiverChainIndex st their ci hci
  refine ⟨ch, hch, ?_⟩
  have hmem : ch ∈ st.receiverChains := mem_of_getElem?_some st.receiverChains ci ch hch
  have hlen : ch.messageKeys.length ≤ maxMessageKeys := (hok ch hmem).1
  have hnlt : ¬ (c < ck.index) := BitVec.not_lt.mpr h
  have hnj : ¬ (st.maxForwardJumps < (c - ck.index).toNat) := Nat.not_lt.mpr hj
  let n := (c - ck.index).toNat
  have hn : ck.index.toNat + n = c.toNat := index_toNat_add_sub_eq ck c h
  have hadv := advanceChain_exec_some F their c n ck st ci ch hn hci hch hlen
  let ckc := chainStepN F n ck
  have hckc_idx : ckc.index = c := chainStepN_index_eq F n ck c hn
  have hckc_ne : ckc.index ≠ BitVec.allOnes 32 := by rw [hckc_idx]; exact hc
  have hnext : ckc.nextChainKey F = .ok (chainStepN F 1 ckc) :=
    nextChainKey_eq_of_ne F ckc hckc_ne
  let ch_mid : ReceiverChain :=
    { ch with messageKeys := (skippedKeys F n ck ++ ch.messageKeys).take maxMessageKeys }
  let st_mid : RatchetState := { st with receiverChains := st.receiverChains.set ci ch_mid }
  have hci_mid : st_mid.findReceiverChainIndex their = some ci := by
    rw [findReceiverChainIndex_set_thm st their ci ch_mid ⟨ch, hch, rfl⟩, hci]
  have hch_mid : st_mid.receiverChains[ci]? = some ch_mid :=
    getElem?_set_eq_of_some st.receiverChains ci ch ch_mid hch
  have hset := setReceiverChainKey_exec_some their (chainStepN F 1 ckc) st_mid ci ch_mid hci_mid hch_mid
  unfold RatchetState.consumeMessageKey
  simp only [hnlt, ↓reduceIte, exec_bind, exec_get, hnj, n, hadv, exec_liftE, ckc, hnext,
    exec_map, hset, exec_pure, st_mid, ch_mid, set_set_eq]

theorem consumeMessageKey_panic_iff_thm (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) :
    ((RatchetState.consumeMessageKey F their ck c t).exec st).1 = .error .panic ↔
      ck.index ≤ c ∧ (c - ck.index).toNat ≤ st.maxForwardJumps ∧
        (c = BitVec.allOnes 32 ∨ st.findReceiverChainIndex their = none) := by
  by_cases hlt : c < ck.index
  · have hnotle : ¬ (ck.index ≤ c) := BitVec.not_le.mpr hlt
    simp only [hnotle, false_and, iff_false]
    unfold RatchetState.consumeMessageKey
    simp only [hlt, ↓reduceIte, exec_bind]
    rcases takeSkippedKey_exec their c st with ⟨st', htake, _⟩ | ⟨k, ci, ch, pos, _, _, _, _, htake⟩
    · simp [htake]
    · simp [htake]
  · have hle : ck.index ≤ c := BitVec.not_lt.mp hlt
    by_cases hj : st.maxForwardJumps < (c - ck.index).toNat
    · have hnotle : ¬ ((c - ck.index).toNat ≤ st.maxForwardJumps) := Nat.not_le.mpr hj
      simp only [hle, hnotle, false_and, and_false, iff_false]
      unfold RatchetState.consumeMessageKey
      simp only [hlt, ↓reduceIte, exec_bind, exec_get, hj, exec_throw]
      rintro ⟨⟩
    · have hjle : (c - ck.index).toNat ≤ st.maxForwardJumps := Nat.not_lt.mp hj
      simp only [hle, hjle, true_and]
      let n := (c - ck.index).toNat
      have hn : ck.index.toNat + n = c.toNat := index_toNat_add_sub_eq ck c hle
      cases hci : st.findReceiverChainIndex their with
      | none =>
        have hrhs : (c = BitVec.allOnes 32 ∨ (none : Option ℕ) = none) ↔ True := by simp
        rw [hrhs, iff_true]
        unfold RatchetState.consumeMessageKey
        simp only [hlt, ↓reduceIte, exec_bind, exec_get, hj]
        cases hn_eq : (c - ck.index).toNat with
        | zero =>
          simp only [RatchetState.advanceChain, exec_bind, exec_pure, exec_liftE]
          by_cases hc : ck.index = BitVec.allOnes 32
          · simp only [ChainKey.nextChainKey, hc, ↓reduceIte]
          · simp only [ChainKey.nextChainKey, hc, ↓reduceIte,
              setReceiverChainKey_exec_none their _ st hci]
        | succ m =>
          have hn' : ck.index.toNat + (m + 1) = c.toNat := by omega
          have hlt' : ck.index < c := index_lt_of_add_succ_eq ck c m hn'
          simp only [RatchetState.advanceChain, hlt', ↓reduceIte, exec_bind,
            storeSkippedKey_exec_none their _ st hci]
      | some ci =>
        simp only [reduceCtorEq, or_false]
        obtain ⟨ch, hch, _⟩ := getElem?_of_findReceiverChainIndex st their ci hci
        obtain ⟨st', ch', hadv, hci', hch'⟩ :=
          advanceChain_exec_some_raw F their c n ck st ci ch hn hci hch
        let ckc := chainStepN F n ck
        have hckc_idx : ckc.index = c := chainStepN_index_eq F n ck c hn
        unfold RatchetState.consumeMessageKey
        simp only [hlt, ↓reduceIte, exec_bind, exec_get, hj, n, hadv, exec_liftE]
        by_cases hc : c = BitVec.allOnes 32
        · have hnext : ckc.nextChainKey F = .error .panic := by
            simp only [ChainKey.nextChainKey, hckc_idx, hc, ↓reduceIte]
          dsimp only [ckc, n] at hnext
          rw [hnext]
          simp only [hc]
        · have hnext : ckc.nextChainKey F = .ok (step1 F ckc) := by
            apply nextChainKey_eq_of_ne F ckc
            rw [hckc_idx]
            exact hc
          simp only [ckc, n, hnext, setReceiverChainKey_exec_some their _ st' ci ch' hci' hch',
            exec_map, exec_pure, hc, reduceCtorEq]

theorem consumeMessageKey_frame_thm (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) (hok : ChainsOk st) :
    let st' := ((RatchetState.consumeMessageKey F their ck c t).exec st).2
    ((RatchetState.consumeMessageKey F their ck c t).exec st).1 ≠ .error .panic →
      st'.rootKey = st.rootKey ∧ st'.senderChain = st.senderChain ∧
      st'.previousCounter = st.previousCounter ∧ st'.maxForwardJumps = st.maxForwardJumps ∧
      st'.receiverChains.map (·.senderRatchetKey) = st.receiverChains.map (·.senderRatchetKey) ∧
      ChainsOk st' := by
  dsimp only
  intro hne
  by_cases hlt : c < ck.index
  · have hcmk :
        ((RatchetState.consumeMessageKey F their ck c t).exec st).2 = st ∨
        ∃ ci ch pos,
          st.receiverChains[ci]? = some ch ∧
          ((RatchetState.consumeMessageKey F their ck c t).exec st).2 =
            { st with receiverChains := st.receiverChains.set ci { ch with messageKeys := ch.messageKeys.eraseIdx pos } } := by
      unfold RatchetState.consumeMessageKey
      simp only [hlt, ↓reduceIte, exec_bind]
      rcases takeSkippedKey_exec their c st with ⟨st₁, htake, rfl⟩ | ⟨k, ci, ch, pos, _, hch, _, _, htake⟩
      · left
        simp [htake]
      · right
        exact ⟨ci, ch, pos, hch, by simp [htake]⟩
    rcases hcmk with hst' | ⟨ci, ch, pos, hch, hst'⟩
    · rw [hst']
      exact ⟨rfl, rfl, rfl, rfl, rfl, hok⟩
    · rw [hst']
      refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
      · dsimp only
        exact map_set_of_eq (·.senderRatchetKey) st.receiverChains ci
          { ch with messageKeys := ch.messageKeys.eraseIdx pos } ⟨ch, hch, rfl⟩
      · intro c' hc'
        have hch_mem : ch ∈ st.receiverChains := mem_of_getElem?_some st.receiverChains ci ch hch
        rcases mem_set_or st.receiverChains ci _ c' hc' with rfl | hc'_mem
        · refine ⟨(length_eraseIdx_le ch.messageKeys pos).trans (hok ch hch_mem).1, ?_⟩
          intro k hk
          exact (hok ch hch_mem).2 k (mem_of_mem_eraseIdx ch.messageKeys pos k hk)
        · exact hok c' hc'_mem
  · have hle : ck.index ≤ c := BitVec.not_lt.mp hlt
    by_cases hj : st.maxForwardJumps < (c - ck.index).toNat
    · have hst' : ((RatchetState.consumeMessageKey F their ck c t).exec st).2 = st := by
        unfold RatchetState.consumeMessageKey
        simp only [hlt, ↓reduceIte, exec_bind, exec_get, hj, exec_throw]
      rw [hst']
      exact ⟨rfl, rfl, rfl, rfl, rfl, hok⟩
    · have hjle : (c - ck.index).toNat ≤ st.maxForwardJumps := Nat.not_lt.mp hj
      have hnot_panic : ¬ (c = BitVec.allOnes 32 ∨ st.findReceiverChainIndex their = none) := by
        intro hp
        exact hne ((consumeMessageKey_panic_iff_thm F st their ck c t).mpr ⟨hle, hjle, hp⟩)
      have hc : c ≠ BitVec.allOnes 32 := fun h => hnot_panic (Or.inl h)
      cases hci : st.findReceiverChainIndex their with
      | none => exact False.elim (hnot_panic (Or.inr hci))
      | some ci =>
        obtain ⟨ch, hch, heq⟩ :=
          consumeMessageKey_advance_thm F st their ck c t hc hle hjle ci hci hok
        have hst' :
            ((RatchetState.consumeMessageKey F their ck c t).exec st).2 =
              { st with
                receiverChains := st.receiverChains.set ci
                  { ch with
                    messageKeys := (skippedKeys F (c - ck.index).toNat ck ++ ch.messageKeys).take maxMessageKeys
                    chainKey := some (chainStepN F 1 (chainStepN F (c - ck.index).toNat ck)) } } := by
          rw [heq]
        rw [hst']
        refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
        · dsimp only
          exact map_set_of_eq (·.senderRatchetKey) st.receiverChains ci
            { ch with
              messageKeys := (skippedKeys F (c - ck.index).toNat ck ++ ch.messageKeys).take maxMessageKeys
              chainKey := some (chainStepN F 1 (chainStepN F (c - ck.index).toNat ck)) } ⟨ch, hch, rfl⟩
        · intro c' hc'
          have hch_mem : ch ∈ st.receiverChains := mem_of_getElem?_some st.receiverChains ci ch hch
          rcases mem_set_or st.receiverChains ci _ c' hc' with rfl | hc'_mem
          · refine ⟨length_take_le' _ maxMessageKeys, ?_⟩
            intro k hk
            have hk' := mem_of_mem_take' _ maxMessageKeys k hk
            simp only [List.mem_append] at hk'
            rcases hk' with hk_skip | hk_old
            · exact mem_skippedKeys_seed_ne_nil F _ ck k hk_skip
            · exact (hok ch hch_mem).2 k hk_old
          · exact hok c' hc'_mem

end MoveCompat

end CryptoVerification.SessionModel.AdvanceAndFrame
