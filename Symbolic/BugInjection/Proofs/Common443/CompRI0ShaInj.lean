/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open ByteSpecs
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed.Refinement (leBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
theorem leBytes_len : ∀ (n v : Nat), (leBytes n v).length = n
  | 0, _ => rfl
  | n + 1, v => by simp [leBytes, leBytes_len n]
theorem bytesToNat_leBytes : ∀ (k n : Nat), n < 2 ^ (8 * k) → bytesToNat (leBytes k n) = n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rfl
  | k + 1, n, h => by
    have hpow : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := (by rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]); have hk : n / 256 < 2 ^ (8 * k) := (by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega); simp only [leBytes, bytesToNat, BitVec.toNat_ofNat, bytesToNat_leBytes k (n / 256) hk]; omega
theorem eq_of_bytesToNat_eq {a b : HwBytes} (hlen : a.length = b.length) (h : bytesToNat a = bytesToNat b) : a = b := by rw [← leBytes_bytesToNat a, ← leBytes_bytesToNat b, hlen, h]
theorem rows_out_lt : (compSha256Rows.all fun r => decide (r.2.2 < 2 ^ 256)) = true := by decide +kernel
theorem rows_lt : ∀ r ∈ compSha256Rows, r.2.2 < 2 ^ (8 * 32) := by intro r hr; have := List.all_eq_true.mp rows_out_lt r hr; simpa using this
theorem rows_out_ne_iv : (compSha256Rows.all fun r => r.2.2 != bytesToNat (shaStateBytes sha256IV)) = true := by decide +kernel
theorem compSha256_inj_of_untagged {st₁ blk₁ st₂ blk₂ : HwBytes} (h₁ : (compSha256 st₁ blk₁).take 4 ≠ compTag4) (heq : compSha256 st₁ blk₁ = compSha256 st₂ blk₂) : st₁ = st₂ ∧ blk₁ = blk₂ := by
  have h₂ : (compSha256 st₂ blk₂).take 4 ≠ compTag4 := heq ▸ h₁; obtain ⟨-, hs₁, hb₁, row₁, hm₁, hr₁s, hr₁b, he₁⟩ := compSha256_row_of_untagged h₁; obtain ⟨-, hs₂, hb₂, row₂, hm₂, hr₂s, hr₂b, he₂⟩ := compSha256_row_of_untagged h₂
  have hout : row₁.2.2 = row₂.2.2 := by
    have hle : leBytes 32 row₁.2.2 = leBytes 32 row₂.2.2 := by rw [← he₁, ← he₂, heq]
    rw [← bytesToNat_leBytes 32 _ (rows_lt row₁ hm₁), ← bytesToNat_leBytes 32 _ (rows_lt row₂ hm₂), hle]
  have hrow : row₁ = row₂ := List.inj_on_of_nodup_map rows_out_nodup hm₁ hm₂ hout; subst hrow
  refine ⟨eq_of_bytesToNat_eq (by rw [hs₁, hs₂]) (by rw [← hr₁s, hr₂s]),
    eq_of_bytesToNat_eq (by rw [hb₁, hb₂]) (by rw [← hr₁b, hr₂b])⟩
theorem compSha256_length (st blk : HwBytes) : (compSha256 st blk).length = 32 := by
  have hd : (compDefaultSha256 st blk).length = 32 := by simp [compDefaultSha256, compTag4, compShaMix28]
  unfold compSha256
  split
  · exact hd
  · split
    · dsimp only
      split
      · exact leBytes_len _ _
      · exact hd
    · exact hd
private theorem word32_of_le_bytes (w : BitVec 32) : BitVec.ofNat 32 ((w.extractLsb' 0 8).toNat + 256 * (w.extractLsb' 8 8).toNat + 65536 * (w.extractLsb' 16 8).toNat + 16777216 * (w.extractLsb' 24 8).toNat) = w := by apply BitVec.eq_of_toNat_eq; have hw := w.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
theorem shaStateOfBytes_shaStateBytes' (st : ShaState) : shaStateOfBytes (shaStateBytes st) = st := by
  rcases st with ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals try (simp at hl; done)
  apply List.Vector.eq; simp only [shaStateOfBytes, shaStateBytes, List.Vector.toList_ofFn, List.Vector.toList_mk, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append, Nat.mul_zero, Nat.zero_add, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, word32_of_le_bytes]
private theorem ext0 (a b c d : BitVec 8) : (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 0 8 = a := by apply BitVec.eq_of_toNat_eq; have ha : a.toNat < 256 := a.isLt; have hb : b.toNat < 256 := b.isLt; have hc : c.toNat < 256 := c.isLt; have hd : d.toNat < 256 := d.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext8 (a b c d : BitVec 8) : (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 8 8 = b := by apply BitVec.eq_of_toNat_eq; have ha : a.toNat < 256 := a.isLt; have hb : b.toNat < 256 := b.isLt; have hc : c.toNat < 256 := c.isLt; have hd : d.toNat < 256 := d.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext16 (a b c d : BitVec 8) : (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 16 8 = c := by apply BitVec.eq_of_toNat_eq; have ha : a.toNat < 256 := a.isLt; have hb : b.toNat < 256 := b.isLt; have hc : c.toNat < 256 := c.isLt; have hd : d.toNat < 256 := d.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext24 (a b c d : BitVec 8) : (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 24 8 = d := by apply BitVec.eq_of_toNat_eq; have ha : a.toNat < 256 := a.isLt; have hb : b.toNat < 256 := b.isLt; have hc : c.toNat < 256 := c.isLt; have hd : d.toNat < 256 := d.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
theorem shaStateBytes_shaStateOfBytes (x : HwBytes) (hx : x.length = 32) : shaStateBytes (shaStateOfBytes x) = x := by
  match x, hx with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
     x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31], _ =>
    simp only [shaStateOfBytes, shaStateBytes, List.Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append, Nat.mul_zero, Nat.zero_add, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ext0, ext8, ext16, ext24]
theorem F0_inj_of_untagged {s₁ s₂ : ShaState} {b₁ b₂ : HwBytes} (h₁ : OnTab s₁ b₁) (heq : F0 s₁ b₁ = F0 s₂ b₂) : s₁ = s₂ ∧ b₁ = b₂ := by rw [F0_eq, F0_eq] at heq; have hc := congrArg shaStateBytes heq; rw [shaStateBytes_shaStateOfBytes _ (compSha256_length _ _), shaStateBytes_shaStateOfBytes _ (compSha256_length _ _)] at hc; obtain ⟨hs, hb⟩ := compSha256_inj_of_untagged h₁ hc; refine ⟨?_, hb⟩; rw [← shaStateOfBytes_shaStateBytes' s₁, ← shaStateOfBytes_shaStateBytes' s₂, hs]
theorem F0_ne_iv {s : ShaState} {b : HwBytes} (h : OnTab s b) : F0 s b ≠ sha256IV := by intro hiv; obtain ⟨r, hr, -, -, hF⟩ := row_step h; have h1 := congrArg (fun t => bytesToNat (shaStateBytes t)) (hF.symm.trans hiv); rw [shaStateBytes_shaStateOfBytes _ (leBytes_len 32 _), bytesToNat_leBytes 32 _ (rows_lt r hr)] at h1; have := List.all_eq_true.mp rows_out_ne_iv r hr; simp [h1] at this
def AllUntagged (L : List HwBytes) : Prop := ∀ l₁ b l₂, L = l₁ ++ b :: l₂ → OnTab (l₁.foldl F0 sha256IV) b
theorem AllUntagged.dropLast {L : List HwBytes} {a : HwBytes} (h : AllUntagged (L ++ [a])) : AllUntagged L := by intro l₁ b l₂ hL; exact h l₁ b (l₂ ++ [a]) (by rw [hL]; simp)
theorem AllUntagged.last {L : List HwBytes} {a : HwBytes} (h : AllUntagged (L ++ [a])) : OnTab (L.foldl F0 sha256IV) a := h L a [] rfl
theorem eq_nil_or_snoc {α : Type} (L : List α) : L = [] ∨ ∃ L' a, L = L' ++ [a] := by
  by_cases h : L = []
  · exact Or.inl h
  · exact Or.inr ⟨L.dropLast, L.getLast h, (dropLast_append_getLast h).symm⟩
theorem fold_inj_aux : ∀ (n : Nat) (A B : List HwBytes), A.length ≤ n → AllUntagged A → AllUntagged B → A.foldl F0 sha256IV = B.foldl F0 sha256IV → A = B := by
  intro n
  induction n with
  | zero =>
    intro A B hn _ hB heq; have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega); subst hA
    rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
    · rfl
    · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact F0_ne_iv hB.last heq.symm
  | succ n ih =>
    intro A B hn hA hB heq
    rcases eq_nil_or_snoc A with rfl | ⟨A', a, rfl⟩
    · rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
      · rfl
      · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact F0_ne_iv hB.last heq.symm
    · rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
      · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact F0_ne_iv hA.last heq
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; obtain ⟨hs, hb⟩ := F0_inj_of_untagged hA.last heq
        have hlen : A'.length ≤ n := by simp at hn; omega
        rw [ih A' B' hlen hA.dropLast hB.dropLast hs, hb]
theorem fold_inj_of_untagged (A B : List HwBytes) (hA : AllUntagged A) (hB : AllUntagged B) (heq : A.foldl F0 sha256IV = B.foldl F0 sha256IV) : A = B := fold_inj_aux A.length A B (Nat.le_refl _) hA hB heq
theorem toBEBytes4_inj {x y : BitVec 32} (h : toBEBytes 4 x = toBEBytes 4 y) : x = y := by simp only [toBEBytes, List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true] at h; obtain ⟨h0, h1, h2, h3⟩ := h; have e0 := congrArg BitVec.toNat h0; have e1 := congrArg BitVec.toNat h1; have e2 := congrArg BitVec.toNat h2; have e3 := congrArg BitVec.toNat h3; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Fin.val_zero, Fin.val_succ] at e0 e1 e2 e3; have hx : x.toNat < 4294967296 := x.isLt; have hy : y.toNat < 4294967296 := y.isLt; apply BitVec.eq_of_toNat_eq; omega
theorem flatMap_inj_of_len {α β : Type} (f : α → List β) (n : Nat) (hlen : ∀ a, (f a).length = n) (hinj : ∀ a b, f a = f b → a = b) : ∀ (l₁ l₂ : List α), l₁.length = l₂.length → l₁.flatMap f = l₂.flatMap f → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.flatMap_cons] at h; obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hlen, hlen]); rw [hinj a b h1, flatMap_inj_of_len f n hlen hinj l₁ l₂ (by simpa using hl) h2]
theorem digest_inj {s₁ s₂ : ShaState} (h : s₁.toList.flatMap (toBEBytes 4) = s₂.toList.flatMap (toBEBytes 4)) : s₁ = s₂ := by
  apply List.Vector.eq
  exact flatMap_inj_of_len (toBEBytes 4) 4 (fun a => toBEBytes_length 4 a)
    (fun _ _ h => toBEBytes4_inj h) _ _ (by simp) h
theorem flatten_chunks64_aux : ∀ (n : Nat) (x : List (BitVec 8)), x.length = 64 * n → (chunks64 x).flatten = x
  | 0, x, hx => by
    have : x = [] := List.eq_nil_of_length_eq_zero (by omega); subst this; rfl
  | n + 1, x, hx => by
    have hsplit : x = x.take 64 ++ x.drop 64 := (List.take_append_drop 64 x).symm
    have ht : (x.take 64).length = 64 := by simp; omega
    rw [hsplit, chunks64_append64 _ _ ht, List.flatten_cons,
      flatten_chunks64_aux n (x.drop 64) (by simp; omega)]
theorem chunks64_inj {x y : List (BitVec 8)} (hx : x.length % 64 = 0) (hy : y.length % 64 = 0) (h : chunks64 x = chunks64 y) : x = y := by
  rw [← flatten_chunks64_aux (x.length / 64) x (by omega),
    ← flatten_chunks64_aux (y.length / 64) y (by omega), h]
theorem sha256Pad_inj {m₁ m₂ : List (BitVec 8)} (h : sha256Pad m₁ = sha256Pad m₂) : m₁ = m₂ := by have hl := congrArg List.length h; rw [sha256Pad_length, sha256Pad_length] at hl; unfold sha256Pad at h; have hsuf := List.append_inj_right' h (by simp [toBEBytes_length]); have hlen : m₁.length = m₂.length := (by simp only [toBEBytes, List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true] at hsuf; obtain ⟨-, -, -, -, -, -, h6, h7⟩ := hsuf; have e6 := congrArg BitVec.toNat h6; have e7 := congrArg BitVec.toNat h7; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Fin.val_zero, Fin.val_succ] at e6 e7; omega); have hpre := List.append_inj_left' h (by simp [toBEBytes_length]); simp only [List.append_assoc] at hpre; exact List.append_inj_left hpre hlen
theorem sha256With_inj_of_allUntagged {m₁ m₂ : HwBytes} (h₁ : AllUntagged (chunks64 (sha256Pad m₁))) (h₂ : AllUntagged (chunks64 (sha256Pad m₂))) (heq : sha256With F0 m₁ = sha256With F0 m₂) : m₁ = m₂ := by unfold sha256With at heq; have hs := digest_inj heq; have hc := fold_inj_of_untagged _ _ h₁ h₂ hs; exact sha256Pad_inj (chunks64_inj (sha256Pad_length_mod m₁) (sha256Pad_length_mod m₂) hc)
theorem allUntagged_of_sha256With {m : HwBytes} (h : (sha256With F0 m).take 4 ≠ compTag4) : AllUntagged (chunks64 (sha256Pad m)) :=
  fun l₁ b l₂ hs => onTab_of_sha256With_untagged m h l₁ b l₂ hs
theorem sha256With_inj_of_untagged {m₁ m₂ : HwBytes} (h₁ : (sha256With F0 m₁).take 4 ≠ compTag4) (heq : sha256With F0 m₁ = sha256With F0 m₂) : m₁ = m₂ := sha256With_inj_of_allUntagged (allUntagged_of_sha256With h₁) (allUntagged_of_sha256With (heq ▸ h₁)) heq
theorem kblk_inj {k₁ k₂ : HwBytes} (pad : BitVec 8) (hl : k₁.length = k₂.length) (h : kblk k₁ pad = kblk k₂ pad) : k₁ = k₂ := by
  have h' := congrArg (List.map (· ^^^ pad)) h
  simp only [kblk, map_xor_xor] at h'; exact List.append_inj_left h' hl
theorem hmacWith_inj_of_untagged {k₁ k₂ m₁ m₂ : HwBytes} (hl : k₁.length = k₂.length) (hk : k₁.length ≤ 64) (h₁ : (hmacWith F0 k₁ m₁).take 4 ≠ compTag4) (heq : hmacWith F0 k₁ m₁ = hmacWith F0 k₂ m₂) : k₁ = k₂ ∧ m₁ = m₂ := by have hk₂ : k₂.length ≤ 64 := hl ▸ hk; have hin₁ := hmac_inner_untagged k₁ m₁ hk h₁; rw [hmacWith_eq k₁ m₁ hk] at h₁ heq; rw [hmacWith_eq k₂ m₂ hk₂] at heq; have ho := sha256With_inj_of_untagged h₁ heq; have hx₁ := kblk_length k₁ 0x5c hk; have hx₂ := kblk_length k₂ 0x5c hk₂; obtain ⟨hko, hino⟩ := List.append_inj ho (by rw [hx₁, hx₂]); have hkeq := kblk_inj 0x5c hl hko; subst hkeq; have hi := sha256With_inj_of_untagged hin₁ hino; exact ⟨rfl, List.append_inj_right hi rfl⟩
end Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
