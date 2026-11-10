/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalPqxdh.Model

/-!
# Injectivity of the First-Message MAC Input

Proves that `aeadMacInput (firstMsgAD ikA ikB e pq) ct` uniquely determines `(ikA, ikB, e, pq, ct)`
when the three EC keys are 32 bytes long, so any forgery query distinct from the challenge
evaluates the MAC on a fresh input.
-/

@[expose] public section

namespace SignalPqxdh

private theorem pbVarint_go_stable :
    ∀ (f g n : Nat), n ≤ f → n ≤ g → pbVarint.go f n = pbVarint.go g n := by
  intro f
  induction f with
  | zero =>
    intro g n hf _
    obtain rfl : n = 0 := by omega
    cases g <;> simp [pbVarint.go]
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero =>
      obtain rfl : n = 0 := by omega
      simp [pbVarint.go]
    | succ g =>
      simp only [pbVarint.go]
      split
      · rfl
      · congr 1
        exact ih g (n / 128) (by omega) (by omega)

theorem pbVarint_lt {n : Nat} (h : n < 128) : pbVarint n = [n.toUInt8] := by
  unfold pbVarint
  cases n with
  | zero => rfl
  | succ n => simp [pbVarint.go, h]

theorem pbVarint_ge {n : Nat} (h : ¬ n < 128) :
    pbVarint n = (n % 128 + 128).toUInt8 :: pbVarint (n / 128) := by
  unfold pbVarint
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [pbVarint.go, h, ↓reduceIte]
  congr 1
  exact pbVarint_go_stable _ _ _ (by omega) (Nat.le_refl _)

private theorem toUInt8_toNat (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp [Nat.toUInt8]

theorem pbVarint_append_inj :
    ∀ (m n : Nat) (r s : Bytes), pbVarint m ++ r = pbVarint n ++ s → m = n ∧ r = s := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n r s h
    by_cases hm : m < 128 <;> by_cases hn : n < 128
    · rw [pbVarint_lt hm, pbVarint_lt hn] at h
      simp only [List.singleton_append, List.cons.injEq] at h
      have := congrArg UInt8.toNat h.1
      rw [toUInt8_toNat, toUInt8_toNat] at this
      exact ⟨by omega, h.2⟩
    · exfalso
      rw [pbVarint_lt hm, pbVarint_ge hn] at h
      simp only [List.cons_append, List.cons.injEq] at h
      have := congrArg UInt8.toNat h.1
      rw [toUInt8_toNat, toUInt8_toNat] at this
      omega
    · exfalso
      rw [pbVarint_ge hm, pbVarint_lt hn] at h
      simp only [List.cons_append, List.cons.injEq] at h
      have := congrArg UInt8.toNat h.1
      rw [toUInt8_toNat, toUInt8_toNat] at this
      omega
    · rw [pbVarint_ge hm, pbVarint_ge hn] at h
      simp only [List.cons_append, List.cons.injEq] at h
      have hlo := congrArg UInt8.toNat h.1
      rw [toUInt8_toNat, toUInt8_toNat] at hlo
      obtain ⟨hq, hrs⟩ := ih (m / 128) (by omega) (n / 128) r s h.2
      exact ⟨by omega, hrs⟩

theorem pbBytesField_append_inj (t : Nat) (a b r s : Bytes)
    (h : pbBytesField t a ++ r = pbBytesField t b ++ s) : a = b ∧ r = s := by
  simp only [pbBytesField, List.cons_append, List.cons.injEq, List.append_assoc] at h
  obtain ⟨hl, hrest⟩ := pbVarint_append_inj _ _ _ _ h.2
  have hab : a = b := by
    have := List.append_inj hrest hl
    exact this.1
  subst hab
  exact ⟨rfl, List.append_cancel_left hrest⟩

private def adPrefix (ikA ikB e : Bytes) : Bytes :=
  encodeEC ikA ++ (encodeEC ikB ++ (0x44 :: (pbBytesField 1 (encodeEC e) ++ [0x10, 0x00, 0x18, 0x00])))

theorem pbVarint_33 : pbVarint 33 = [33] := pbVarint_lt (by omega)

private theorem adPrefix_length (ikA ikB e : Bytes) (h1 : ikA.length = 32) (h2 : ikB.length = 32)
    (h3 : e.length = 32) : (adPrefix ikA ikB e).length = 106 := by
  simp [adPrefix, pbBytesField, encodeEC, h1, h2, h3, pbVarint_33]

private def adTail (pq ct : Bytes) : Bytes :=
  pbBytesField 4 ct ++ (if pq.isEmpty then [] else pbBytesField 5 pq)

private theorem aeadMacInput_eq (ikA ikB e pq ct : Bytes) (h1 : ikA.length = 32)
    (h2 : ikB.length = 32) (h3 : e.length = 32) :
    aeadMacInput (firstMsgAD ikA ikB e pq) ct = adPrefix ikA ikB e ++ adTail pq ct := by
  have hfa : firstMsgAD ikA ikB e pq =
      adPrefix ikA ikB e ++ (if pq.isEmpty then [] else pbBytesField 5 pq) := by
    simp [firstMsgAD, adPrefix, List.append_assoc]
  have hl : (adPrefix ikA ikB e).length = firstMsgHdrLen := adPrefix_length _ _ _ h1 h2 h3
  rw [aeadMacInput, hfa, List.take_left' hl, List.drop_left' hl, adTail, List.append_assoc]

/-- Explicit byte layout of `aeadMacInput (firstMsgAD ikA ikB e pq) ct` for 32-byte EC keys. -/
theorem aeadMacInput_firstMsgAD (ikA ikB e pq ct : Bytes) (h1 : ikA.length = 32)
    (h2 : ikB.length = 32) (h3 : e.length = 32) :
    aeadMacInput (firstMsgAD ikA ikB e pq) ct =
      encodeEC ikA ++ encodeEC ikB ++ [0x44] ++ pbBytesField 1 (encodeEC e) ++
        [0x10, 0x00, 0x18, 0x00] ++ pbBytesField 4 ct ++
        (if pq.isEmpty then [] else pbBytesField 5 pq) := by
  rw [aeadMacInput_eq _ _ _ _ _ h1 h2 h3]
  simp [adPrefix, adTail, List.append_assoc]

private theorem adTail_inj (pq pq' ct ct' : Bytes) (h : adTail pq ct = adTail pq' ct') :
    pq = pq' ∧ ct = ct' := by
  unfold adTail at h
  obtain ⟨hct, hpq⟩ := pbBytesField_append_inj 4 ct ct' _ _ h
  refine ⟨?_, hct⟩
  by_cases hp : pq.isEmpty <;> by_cases hp' : pq'.isEmpty <;>
    simp only [hp, hp', ↓reduceIte, Bool.false_eq_true] at hpq
  · rw [List.isEmpty_iff.mp hp, List.isEmpty_iff.mp hp']
  · exfalso
    simp [pbBytesField] at hpq
  · exfalso
    simp [pbBytesField] at hpq
  · exact (pbBytesField_append_inj 5 pq pq' [] [] (by simpa using hpq)).1

private theorem encodeEC_inj {a b : Bytes} (h : encodeEC a = encodeEC b) : a = b := by
  simpa [encodeEC] using h

/-- `aeadMacInput (firstMsgAD ikA ikB e pq) ct` is injective in `(ikA, ikB, e, pq, ct)` for
    32-byte EC keys. -/
theorem aeadMacInput_firstMsgAD_inj (ikA ikB e pq ct ikA' ikB' e' pq' ct' : Bytes)
    (hA : ikA.length = 32) (hB : ikB.length = 32) (hE : e.length = 32)
    (hA' : ikA'.length = 32) (hB' : ikB'.length = 32) (hE' : e'.length = 32)
    (h : aeadMacInput (firstMsgAD ikA ikB e pq) ct = aeadMacInput (firstMsgAD ikA' ikB' e' pq') ct') :
    ikA = ikA' ∧ ikB = ikB' ∧ e = e' ∧ pq = pq' ∧ ct = ct' := by
  rw [aeadMacInput_eq _ _ _ _ _ hA hB hE, aeadMacInput_eq _ _ _ _ _ hA' hB' hE'] at h
  obtain ⟨hpre, htail⟩ := List.append_inj h
    (by rw [adPrefix_length _ _ _ hA hB hE, adPrefix_length _ _ _ hA' hB' hE'])
  obtain ⟨hpq, hct⟩ := adTail_inj _ _ _ _ htail
  unfold adPrefix at hpre
  have hlA : (encodeEC ikA).length = (encodeEC ikA').length := by simp [encodeEC, hA, hA']
  obtain ⟨h1, hpre⟩ := List.append_inj hpre hlA
  have hlB : (encodeEC ikB).length = (encodeEC ikB').length := by simp [encodeEC, hB, hB']
  obtain ⟨h2, hpre⟩ := List.append_inj hpre hlB
  simp only [List.cons.injEq, true_and] at hpre
  have h3 := (pbBytesField_append_inj 1 _ _ _ _ hpre).1
  exact ⟨encodeEC_inj h1, encodeEC_inj h2, encodeEC_inj h3, hpq, hct⟩

end SignalPqxdh
