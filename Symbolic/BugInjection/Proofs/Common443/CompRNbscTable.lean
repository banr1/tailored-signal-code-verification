/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.CompRTag

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open ByteSpecs
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed.Refinement (leBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRTag
private theorem shaStateOfBytes_head_eq_take4 (bytes : HwBytes) : (shaStateOfBytes bytes).head = (shaStateOfBytes (bytes.take 4)).head := by rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, bs⟩⟩⟩⟩ <;> rfl
theorem compI0_sha256Compress (st blk : HwBytes) : compI0 DY.Libsignal.Refinement.sha256CompressSymbol [st, blk] = some (compSha256 st blk) := rfl
theorem sha256CompressFunction_compI0_head (st : ShaState) (blk : HwBytes) : (sha256CompressFunction compI0 st blk).head = (shaStateOfBytes ((compSha256 (shaStateBytes st) blk).take 4)).head := by unfold sha256CompressFunction; rw [compI0_sha256Compress, Option.getD_some, shaStateOfBytes_head_eq_take4]
theorem compDefaultSha256_take4 (st blk : HwBytes) : (compDefaultSha256 st blk).take 4 = compTag4 := by simp [compDefaultSha256, compTag4]
theorem compSha256_row_of_untagged {st blk : HwBytes} (h : (compSha256 st blk).take 4 ≠ compTag4) : st.take 4 ≠ compTag4 ∧ st.length = 32 ∧ blk.length = 64 ∧ ∃ row ∈ compSha256Rows, row.1 = bytesToNat st ∧ row.2.1 = bytesToNat blk ∧ compSha256 st blk = leBytes 32 row.2.2 := by
  unfold compSha256 at h ⊢
  by_cases htag : (st.take 4 == compTag4 || blk.take 4 == compTag4 || blk.take 4 == compTag4Ipad || blk.take 4 == compTag4Opad) = true
  · simp only [htag, ↓reduceIte] at h; exact absurd (compDefaultSha256_take4 st blk) h
  · have hst : st.take 4 ≠ compTag4 := fun he => by apply htag; simp [he]
    simp only [htag, ↓reduceIte, Bool.false_eq_true] at h ⊢
    by_cases hlen : (st.length == 32 && blk.length == 64) = true
    · simp only [hlen, ↓reduceIte] at h ⊢; simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      cases hf : List.find? (fun r => r.1 == bytesToNat st && r.2.1 == bytesToNat blk) compSha256Rows with
      | none => simp only [hf] at h; exact absurd (compDefaultSha256_take4 st blk) h
      | some row =>
        rcases row with ⟨r1, r2, r3⟩; have hmem := List.mem_of_find?_eq_some hf; have hp := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact ⟨hst, hlen.1, hlen.2, ⟨r1, r2, r3⟩, hmem, hp.1, hp.2, rfl⟩
    · simp only [hlen, ↓reduceIte, Bool.false_eq_true] at h; exact absurd (compDefaultSha256_take4 st blk) h
theorem leBytes_bytesToNat : ∀ bs : HwBytes, leBytes bs.length (bytesToNat bs) = bs
  | [] => rfl
  | b :: bs => by
    have hb : b.toNat < 256 := b.isLt; have h1 : (b.toNat + 256 * bytesToNat bs) / 256 = bytesToNat bs := by omega
    simp only [List.length_cons, leBytes, bytesToNat, h1, leBytes_bytesToNat bs]
    congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
abbrev F0 : ShaState → HwBytes → ShaState := sha256CompressFunction compI0
def OnTab (s : ShaState) (b : HwBytes) : Prop := (compSha256 (shaStateBytes s) b).take 4 ≠ compTag4
def tagW : BitVec 32 := 0xd7d7d7d7#32
theorem toBEBytes_tagW : toBEBytes 4 tagW = compTag4 := by decide
theorem shaStateOfBytes_compTag4_head : (shaStateOfBytes compTag4).head = tagW := by decide
theorem hstep0 : ∀ s b, ¬ OnTab s b → (F0 s b).head = tagW := by intro s b h; rw [sha256CompressFunction_compI0_head, Classical.not_not.mp h, shaStateOfBytes_compTag4_head]
theorem shaStateBytes_take4_of_head (s : ShaState) (hs : s.head = tagW) : (shaStateBytes s).take 4 = compTag4 := by
  obtain ⟨l, hl⟩ := s
  match l, hl with
  | w :: ws, _ =>
    have hw : w = tagW := hs; subst hw; simp only [shaStateBytes, List.Vector.toList, List.flatMap_cons]; rw [List.take_append_of_le_length (by simp)]; decide
theorem hT1_0 : ∀ s b, s.head = tagW → ¬ OnTab s b := by intro s b hs h; apply h; have hst := shaStateBytes_take4_of_head s hs; unfold compSha256; simp only [hst, beq_self_eq_true, Bool.true_or, ↓reduceIte]; exact compDefaultSha256_take4 _ _
theorem hT2_0 : ∀ s b, b.take 4 = toBEBytes 4 tagW → ¬ OnTab s b := by intro s b hb h; rw [toBEBytes_tagW] at hb; apply h; unfold compSha256; simp only [hb, beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte]; exact compDefaultSha256_take4 _ _
theorem onTab_of_sha256With_untagged (m : HwBytes) (h : (sha256With F0 m).take 4 ≠ compTag4) (l₁ : List HwBytes) (b : HwBytes) (l₂ : List HwBytes) (hsplit : chunks64 (sha256Pad m) = l₁ ++ b :: l₂) : OnTab (l₁.foldl F0 sha256IV) b := by intro hoff; apply h; rw [sha256With_take4_of_offTable OnTab tagW F0 hstep0 hT1_0 m l₁ b l₂ hsplit (fun h' => h' hoff), toBEBytes_tagW]
def kblk (k : HwBytes) (pad : BitVec 8) : HwBytes := (k ++ List.replicate (64 - k.length) 0).map (· ^^^ pad)
theorem kblk_length (k : HwBytes) (pad : BitVec 8) (hk : k.length ≤ 64) : (kblk k pad).length = 64 := by simp only [kblk, List.length_map, List.length_append, List.length_replicate]; omega
theorem hmacWith_eq (k m : HwBytes) (hk : k.length ≤ 64) : hmacWith F0 k m = sha256With F0 (kblk k 0x5c ++ sha256With F0 (kblk k 0x36 ++ m)) := by
  have hk' : ¬ 64 < k.length := by omega
  simp only [hmacWith, hk', ↓reduceIte, kblk]
theorem hmac_inner_untagged (k m : HwBytes) (hk : k.length ≤ 64) (h : (hmacWith F0 k m).take 4 ≠ compTag4) : (sha256With F0 (kblk k 0x36 ++ m)).take 4 ≠ compTag4 := by intro hin; apply h; rw [hmacWith_take4_of_inner OnTab tagW F0 hstep0 hT1_0 hT2_0 k m hk (by rw [toBEBytes_tagW]; exact hin), toBEBytes_tagW]
theorem hmac_outer_first_onTab (k m : HwBytes) (hk : k.length ≤ 64) (h : (hmacWith F0 k m).take 4 ≠ compTag4) : OnTab sha256IV (kblk k 0x5c) := by
  rw [hmacWith_eq k m hk] at h; have hx := kblk_length k 0x5c hk
  exact onTab_of_sha256With_untagged _ h [] _ (chunks64 (padTail64 (sha256With F0 (kblk k 0x36 ++ m))))
    (by rw [sha256Pad_append64 _ _ hx, chunks64_append64 _ _ hx]; rfl)
def ivNat : Nat := bytesToNat (shaStateBytes sha256IV)
theorem mem_rows_of_onTab_iv {x : HwBytes} (hx : x.length = 64) (h : OnTab sha256IV x) : ∃ row ∈ compSha256Rows, row.1 = ivNat ∧ x = leBytes 64 row.2.1 := by obtain ⟨_, _, _, row, hrow, h1, h2, _⟩ := compSha256_row_of_untagged h; refine ⟨row, hrow, h1, ?_⟩; have hrt := leBytes_bytesToNat x; rw [hx] at hrt; rw [h2, hrt]
def compHmacKeys32 : List HwBytes :=
  compSha256Rows.filterMap fun r =>
    if r.1 = ivNat then
      if ((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).drop 32 = List.replicate 32 0 then
        some (((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).take 32)
      else none
    else none
theorem map_xor_xor (l : HwBytes) (p : BitVec 8) : (l.map (· ^^^ p)).map (· ^^^ p) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]
theorem hmacWith_untagged_key_mem (k m : HwBytes) (hk : k.length = 32) (h : (hmacWith F0 k m).take 4 ≠ compTag4) : k ∈ compHmacKeys32 := by
  have hx := kblk_length k 0x5c (by omega); obtain ⟨row, hrow, h1, h2⟩ := mem_rows_of_onTab_iv hx (hmac_outer_first_onTab k m (by omega) h)
  have hk0 : (leBytes 64 row.2.1).map (· ^^^ (0x5c : BitVec 8)) = k ++ List.replicate 32 0 := by rw [← h2, kblk, map_xor_xor, hk]
  rw [compHmacKeys32, List.mem_filterMap]; refine ⟨row, hrow, ?_⟩; simp only [h1, ↓reduceIte, hk0, List.drop_left' hk, List.take_left' hk]
def digestOfOut (o : Nat) : HwBytes := (shaStateOfBytes (leBytes 32 o)).toList.flatMap (toBEBytes 4)
def rowOfTake8 (v : HwBytes) : Option (Nat × Nat × Nat) := compSha256Rows.find? fun r => (digestOfOut r.2.2).take 8 == v
def rowByOut (o : Nat) : Option (Nat × Nat × Nat) := compSha256Rows.find? fun r => r.2.2 == o
def keyOfRow1 (r : Nat × Nat × Nat) : HwBytes := ((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).take 32
def keyOfTake8 (v : HwBytes) : Option HwBytes :=
  match rowOfTake8 v with
  | none => none
  | some r2 => match rowByOut r2.1 with | none => none | some r1 => if r1.1 = ivNat then some (keyOfRow1 r1) else none
def natElem (a : Nat) : List Nat → Bool
  | [] => false
  | b :: bs => match Nat.beq a b with | true => true | false => natElem a bs
def natNodup : List Nat → Bool
  | [] => true
  | x :: xs => match natElem x xs with | true => false | false => natNodup xs
theorem not_mem_of_natElem_false {a : Nat} : ∀ {l : List Nat}, natElem a l = false → a ∉ l
  | [], _, hmem => nomatch hmem
  | b :: bs, h, hmem => by
    unfold natElem at h; cases hbeq : Nat.beq a b
    · rw [hbeq] at h; rcases List.mem_cons.mp hmem with rfl | hbs
      · rw [Nat.beq_eq.mpr rfl] at hbeq; nomatch hbeq
      · exact not_mem_of_natElem_false h hbs
    · rw [hbeq] at h; nomatch h
theorem nodup_of_natNodup : ∀ {l : List Nat}, natNodup l = true → l.Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    unfold natNodup at h; cases he : natElem x xs
    · rw [he] at h; exact List.Pairwise.cons (fun y hy hxy => not_mem_of_natElem_false he (hxy ▸ hy)) (nodup_of_natNodup h)
    · rw [he] at h; nomatch h
def low16Bytes (v : HwBytes) : Nat := (v.getD 3 0#8).toNat + 256 * (v.getD 2 0#8).toNat
private theorem ext0 (a b c d : BitVec 8) : (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 0 8 = a := by apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext8 (a b c d : BitVec 8) : (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 8 8 = b := by apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
theorem low16Bytes_digestOfOut_take8 (o : Nat) : low16Bytes ((digestOfOut o).take 8) = o % 65536 := by let b0 : BitVec 8 := BitVec.ofNat 8 o; let b1 : BitVec 8 := BitVec.ofNat 8 (o / 256); let b2 : BitVec 8 := BitVec.ofNat 8 (o / 256 / 256); let b3 : BitVec 8 := BitVec.ofNat 8 (o / 256 / 256 / 256); have hle : leBytes 32 o = b0 :: b1 :: b2 :: b3 :: leBytes 28 (o / 256 / 256 / 256 / 256) := rfl; unfold low16Bytes digestOfOut; rw [hle]; simp only [shaStateOfBytes, List.Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Nat.mul_zero, Nat.zero_add, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, List.flatMap_cons, toBEBytes, List.cons_append, List.nil_append, List.take_succ_cons, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, ext0, ext8]; simp only [b0, b1, BitVec.toNat_ofNat]; omega
theorem rows_mod65536_nodup : (compSha256Rows.map fun r => r.2.2 % 65536).Nodup := by apply nodup_of_natNodup; decide +kernel
theorem rows_out_nodup : (compSha256Rows.map fun r => r.2.2).Nodup := by have h := rows_mod65536_nodup; have hfun : (fun r : Nat × Nat × Nat => r.2.2 % 65536) = ((fun x : Nat => x % 65536) ∘ fun r : Nat × Nat × Nat => r.2.2) := rfl; rw [hfun, ← List.map_map] at h; exact List.Nodup.of_map _ h
theorem rows_take8_nodup : (compSha256Rows.map fun r => (digestOfOut r.2.2).take 8).Nodup := by have h := rows_mod65536_nodup; have hfun : (fun r : Nat × Nat × Nat => r.2.2 % 65536) = (low16Bytes ∘ fun r : Nat × Nat × Nat => (digestOfOut r.2.2).take 8) := (by funext r; exact (low16Bytes_digestOfOut_take8 r.2.2).symm); rw [hfun, ← List.map_map] at h; exact List.Nodup.of_map _ h
theorem leBytes_len : ∀ (n v : Nat), (leBytes n v).length = n
  | 0, _ => rfl
  | n + 1, v => by simp [leBytes, leBytes_len n]
theorem bytesToNat_leBytes : ∀ (k n : Nat), n < 2 ^ (8 * k) → bytesToNat (leBytes k n) = n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rfl
  | k + 1, n, h => by
    have hpow : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
    have hk : n / 256 < 2 ^ (8 * k) := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
    simp only [leBytes, bytesToNat, BitVec.toNat_ofNat, bytesToNat_leBytes k (n / 256) hk]; omega
private theorem ext16 (a b c d : BitVec 8) : (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 16 8 = c := by apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext24 (a b c d : BitVec 8) : (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 24 8 = d := by apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
theorem shaStateBytes_shaStateOfBytes (x : HwBytes) (hx : x.length = 32) : shaStateBytes (shaStateOfBytes x) = x := by
  match x, hx with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
     x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31], _ =>
    simp only [shaStateOfBytes, shaStateBytes, List.Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append, Nat.mul_zero, Nat.zero_add, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ext0, ext8, ext16, ext24]
theorem rows_out_lt : (compSha256Rows.all fun r => Nat.ble r.2.2 (2 ^ 256 - 1)) = true := by decide +kernel
theorem rows_lt : ∀ r ∈ compSha256Rows, r.2.2 < 2 ^ (8 * 32) := by intro r hr; have h := Nat.le_of_ble_eq_true (List.all_eq_true.mp rows_out_lt r hr); omega
theorem rows_out_roundtrip : (compSha256Rows.all fun r => bytesToNat (shaStateBytes (shaStateOfBytes (leBytes 32 r.2.2))) == r.2.2) = true := by rw [List.all_eq_true]; intro r hr; rw [shaStateBytes_shaStateOfBytes _ (leBytes_len 32 _), bytesToNat_leBytes 32 _ (rows_lt r hr), beq_self_eq_true]
theorem find?_eq_some_of_nodup {α β : Type} [BEq β] [LawfulBEq β] (l : List α) (f : α → β) (b : β) (hnd : (l.map f).Nodup) (a : α) (ha : a ∈ l) (hfa : f a = b) : l.find? (fun x => f x == b) = some a := by
  cases hf : l.find? (fun x => f x == b) with
  | none => have := List.find?_eq_none.mp hf a ha; simp [hfa] at this
  | some a' =>
    have hmem := List.mem_of_find?_eq_some hf; have hp := List.find?_some hf; simp only [beq_iff_eq] at hp; rw [List.inj_on_of_nodup_map hnd hmem ha (hp.trans hfa.symm)]
theorem F0_eq (s : ShaState) (b : HwBytes) : F0 s b = shaStateOfBytes (compSha256 (shaStateBytes s) b) := by show sha256CompressFunction compI0 s b = _; unfold sha256CompressFunction; rw [compI0_sha256Compress, Option.getD_some]
theorem row_step {s : ShaState} {b : HwBytes} (h : OnTab s b) : ∃ r ∈ compSha256Rows, r.1 = bytesToNat (shaStateBytes s) ∧ r.2.1 = bytesToNat b ∧ F0 s b = shaStateOfBytes (leBytes 32 r.2.2) := by obtain ⟨_, _, _, r, hr, h1, h2, h3⟩ := compSha256_row_of_untagged h; exact ⟨r, hr, h1, h2, by rw [F0_eq, h3]⟩
theorem keyOfTake8_hmacWith (k m : HwBytes) (hk : k.length = 32) (h : (hmacWith F0 k m).take 4 ≠ compTag4) : keyOfTake8 ((hmacWith F0 k m).take 8) = some k := by
  have hk64 : k.length ≤ 64 := by omega
  have hx := kblk_length k 0x5c hk64; have h1 := hmac_outer_first_onTab k m hk64 h; have hil : (sha256With F0 (kblk k 0x36 ++ m)).length = 32 := sha256With_length F0 _; rw [hmacWith_eq k m hk64] at h ⊢; generalize sha256With F0 (kblk k 0x36 ++ m) = inner at h hil ⊢; have hch : chunks64 (sha256Pad (kblk k 0x5c ++ inner)) = [kblk k 0x5c] ++ padTail64 inner :: [] := (by rw [sha256Pad_append64 _ _ hx, chunks64_append64 _ _ hx, chunks64_padTail64_32 inner hil]; rfl); have h2' : OnTab ([kblk k 0x5c].foldl F0 sha256IV) (padTail64 inner) := onTab_of_sha256With_untagged _ h [kblk k 0x5c] (padTail64 inner) [] hch; rw [List.foldl_cons, List.foldl_nil] at h2'; obtain ⟨r1, hr1, hr1a, hr1b, hF1⟩ := row_step h1; obtain ⟨r2, hr2, hr2a, _, hF2⟩ := row_step h2'; have hsha : sha256With F0 (kblk k 0x5c ++ inner) = digestOfOut r2.2.2 := (by unfold sha256With digestOfOut; rw [hch, List.singleton_append, List.foldl_cons, List.foldl_cons, List.foldl_nil, hF2])
  have hr2r1 : r2.1 = r1.2.2 := by rw [hr2a, hF1]; exact beq_iff_eq.mp (List.all_eq_true.mp rows_out_roundtrip r1 hr1)
  have hblk : leBytes 64 r1.2.1 = kblk k 0x5c := by have hrt := leBytes_bytesToNat (kblk k 0x5c); rw [hx] at hrt; rw [hr1b, hrt]
  have hfind2 : rowOfTake8 ((digestOfOut r2.2.2).take 8) = some r2 :=
    find?_eq_some_of_nodup compSha256Rows (fun r => (digestOfOut r.2.2).take 8) ((digestOfOut r2.2.2).take 8) rows_take8_nodup r2 hr2 rfl
  have hfind1 : rowByOut r2.1 = some r1 :=
    find?_eq_some_of_nodup compSha256Rows (fun r => r.2.2) r2.1 rows_out_nodup r1 hr1 hr2r1.symm
  have hiv : r1.1 = ivNat := hr1a
  have hkey : keyOfRow1 r1 = k := by unfold keyOfRow1; rw [hblk, kblk, map_xor_xor, hk]; exact List.take_left' hk
  rw [hsha]; unfold keyOfTake8; simp only [hfind2, hfind1, hiv, ↓reduceIte, hkey]
end Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
