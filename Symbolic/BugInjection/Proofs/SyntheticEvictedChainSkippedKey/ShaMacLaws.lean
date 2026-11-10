/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public import Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound

/-!
# SHA-256, HMAC, and `computeMac` Injectivity for `evictedI0`

Proves untagged SHA-256 and HMAC-SHA-256 injectivity on `evictedSha256Rows`, 8-byte MAC key
recovery (`keyOfTake8_hmacWithE`), key and seed pinning (`computeMac_pins_macKey_prk_seed`,
`computeMac_pins_salt_and_seed`), and `not_macTagForgeryOrCollision_of_honest_mac`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws

open ByteSpecs
  (ShaState sha256IV sha256Pad chunks64 sha256With hmacWith toBEBytes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.TripleRatchet (hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys computeMac TRSignalMsg)
open DY.Libsignal.Composed.Refinement
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compTag4 compTag4Ipad compTag4Opad compDefaultSha256 compShaMix28)
open Symbolic.BugInjection.Proofs.Common443.CompRTag
  (sha256With_length sha256Pad_length_mod sha256Pad_append64 chunks64_append64
   chunks64_padTail64_32 padTail64 sha256With_take4_of_offTable hmacWith_take4_of_inner)
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
  (compDefaultSha256_take4 leBytes_bytesToNat tagW toBEBytes_tagW shaStateOfBytes_compTag4_head
   shaStateBytes_take4_of_head kblk kblk_length ivNat map_xor_xor digestOfOut
   nodup_of_natNodup leBytes_len bytesToNat_leBytes shaStateBytes_shaStateOfBytes
   find?_eq_some_of_nodup)
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
  (eq_of_bytesToNat_eq shaStateOfBytes_shaStateBytes' digest_inj chunks64_inj sha256Pad_inj
   eq_nil_or_snoc kblk_inj)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_lit ms_pack_kdf ms_pack_trunc ms_pack_concat)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsShaRows
  (evictedSha256Bucket evictedSha256Rows evictedSha256)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)

private theorem shaStateOfBytes_head_eq_take4 (bytes : HwBytes) :
    (shaStateOfBytes bytes).head = (shaStateOfBytes (bytes.take 4)).head := by
  rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, bs⟩⟩⟩⟩ <;> rfl

theorem evictedI0_sha256Compress (st blk : HwBytes) :
    evictedI0 DY.Libsignal.Refinement.sha256CompressSymbol [st, blk] = some (evictedSha256 st blk) := rfl

abbrev FE : ShaState → HwBytes → ShaState := sha256CompressFunction evictedI0
def OnTabE (s : ShaState) (b : HwBytes) : Prop := (evictedSha256 (shaStateBytes s) b).take 4 ≠ compTag4

theorem FE_eq (s : ShaState) (b : HwBytes) :
    FE s b = shaStateOfBytes (evictedSha256 (shaStateBytes s) b) := by
  show sha256CompressFunction evictedI0 s b = _
  unfold sha256CompressFunction; rw [evictedI0_sha256Compress, Option.getD_some]

theorem sha256CompressFunction_evictedI0_head (st : ShaState) (blk : HwBytes) :
    (FE st blk).head = (shaStateOfBytes ((evictedSha256 (shaStateBytes st) blk).take 4)).head := by
  rw [FE_eq, shaStateOfBytes_head_eq_take4]

theorem evictedSha256_row_of_untagged {st blk : HwBytes} (h : (evictedSha256 st blk).take 4 ≠ compTag4) :
    st.take 4 ≠ compTag4 ∧ st.length = 32 ∧ blk.length = 64 ∧
      ∃ row ∈ evictedSha256Rows, row.1 = bytesToNat st ∧ row.2.1 = bytesToNat blk ∧
        evictedSha256 st blk = leBytes 32 row.2.2 := by
  unfold evictedSha256 at h ⊢
  by_cases htag : (st.take 4 == compTag4 || blk.take 4 == compTag4 || blk.take 4 == compTag4Ipad || blk.take 4 == compTag4Opad) = true
  · simp only [htag, ↓reduceIte] at h; exact absurd (compDefaultSha256_take4 st blk) h
  · have hst : st.take 4 ≠ compTag4 := fun he => by apply htag; simp [he]
    simp only [htag, ↓reduceIte, Bool.false_eq_true] at h ⊢
    by_cases hlen : (st.length == 32 && blk.length == 64) = true
    · simp only [hlen, ↓reduceIte] at h ⊢; simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      cases hf : List.find? (fun r => r.1 == bytesToNat st && r.2.1 == bytesToNat blk) (evictedSha256Bucket (bytesToNat blk % 64)) with
      | none => simp only [hf] at h; exact absurd (compDefaultSha256_take4 st blk) h
      | some row =>
        rcases row with ⟨r1, r2, r3⟩
        have hmem_b := List.mem_of_find?_eq_some hf
        have hmem : (r1, r2, r3) ∈ evictedSha256Rows :=
          List.mem_flatMap.mpr ⟨bytesToNat blk % 64, List.mem_range.mpr (Nat.mod_lt _ (by decide)), hmem_b⟩
        have hp := List.find?_some hf; simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact ⟨hst, hlen.1, hlen.2, ⟨r1, r2, r3⟩, hmem, hp.1, hp.2, rfl⟩
    · simp only [hlen, ↓reduceIte, Bool.false_eq_true] at h; exact absurd (compDefaultSha256_take4 st blk) h

theorem evictedSha256_length (st blk : HwBytes) : (evictedSha256 st blk).length = 32 := by
  have hd : (compDefaultSha256 st blk).length = 32 := by simp [compDefaultSha256, compTag4, compShaMix28]
  unfold evictedSha256
  split
  · exact hd
  · split
    · dsimp only; split
      · exact leBytes_len _ _
      · exact hd
    · exact hd

theorem hstepE : ∀ s b, ¬ OnTabE s b → (FE s b).head = tagW := by
  intro s b h; rw [sha256CompressFunction_evictedI0_head, Classical.not_not.mp h, shaStateOfBytes_compTag4_head]

theorem hT1_E : ∀ s b, s.head = tagW → ¬ OnTabE s b := by
  intro s b hs h; apply h; have hst := shaStateBytes_take4_of_head s hs
  unfold evictedSha256; simp only [hst, beq_self_eq_true, Bool.true_or, ↓reduceIte]; exact compDefaultSha256_take4 _ _

theorem hT2_E : ∀ s b, b.take 4 = toBEBytes 4 tagW → ¬ OnTabE s b := by
  intro s b hb h; rw [toBEBytes_tagW] at hb; apply h
  unfold evictedSha256; simp only [hb, beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte]; exact compDefaultSha256_take4 _ _

theorem onTabE_of_sha256With_untagged (m : HwBytes) (h : (sha256With FE m).take 4 ≠ compTag4)
    (l₁ : List HwBytes) (b : HwBytes) (l₂ : List HwBytes)
    (hsplit : chunks64 (sha256Pad m) = l₁ ++ b :: l₂) : OnTabE (l₁.foldl FE sha256IV) b := by
  intro hoff; apply h
  rw [sha256With_take4_of_offTable OnTabE tagW FE hstepE hT1_E m l₁ b l₂ hsplit (fun h' => h' hoff), toBEBytes_tagW]

theorem hmacWith_eqE (k m : HwBytes) (hk : k.length ≤ 64) :
    hmacWith FE k m = sha256With FE (kblk k 0x5c ++ sha256With FE (kblk k 0x36 ++ m)) := by
  have hk' : ¬ 64 < k.length := by omega
  simp only [hmacWith, hk', ↓reduceIte, kblk]

theorem hmac_inner_untaggedE (k m : HwBytes) (hk : k.length ≤ 64)
    (h : (hmacWith FE k m).take 4 ≠ compTag4) :
    (sha256With FE (kblk k 0x36 ++ m)).take 4 ≠ compTag4 := by
  intro hin; apply h
  rw [hmacWith_take4_of_inner OnTabE tagW FE hstepE hT1_E hT2_E k m hk (by rw [toBEBytes_tagW]; exact hin), toBEBytes_tagW]

theorem hmac_outer_first_onTabE (k m : HwBytes) (hk : k.length ≤ 64)
    (h : (hmacWith FE k m).take 4 ≠ compTag4) : OnTabE sha256IV (kblk k 0x5c) := by
  rw [hmacWith_eqE k m hk] at h; have hx := kblk_length k 0x5c hk
  exact onTabE_of_sha256With_untagged _ h [] _ (chunks64 (padTail64 (sha256With FE (kblk k 0x36 ++ m))))
    (by rw [sha256Pad_append64 _ _ hx, chunks64_append64 _ _ hx]; rfl)

def low32Bytes (v : HwBytes) : Nat :=
  (v.getD 3 0#8).toNat + 256 * (v.getD 2 0#8).toNat +
    65536 * (v.getD 1 0#8).toNat + 16777216 * (v.getD 0 0#8).toNat

private theorem ext0 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 0 8 = a := by
  apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext8 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 8 8 = b := by
  apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext16 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 16 8 = c := by
  apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext24 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 24 8 = d := by
  apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

theorem low32Bytes_digestOfOut_take8 (o : Nat) :
    low32Bytes ((digestOfOut o).take 8) = o % 4294967296 := by
  let b0 : BitVec 8 := BitVec.ofNat 8 o
  let b1 : BitVec 8 := BitVec.ofNat 8 (o / 256)
  let b2 : BitVec 8 := BitVec.ofNat 8 (o / 256 / 256)
  let b3 : BitVec 8 := BitVec.ofNat 8 (o / 256 / 256 / 256)
  have hle : leBytes 32 o = b0 :: b1 :: b2 :: b3 :: leBytes 28 (o / 256 / 256 / 256 / 256) := rfl
  unfold low32Bytes digestOfOut; rw [hle]
  simp only [shaStateOfBytes, List.Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero,
    Fin.val_zero, Fin.val_succ, Nat.mul_zero, Nat.zero_add, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.flatMap_cons, toBEBytes, List.cons_append,
    List.nil_append, List.take_succ_cons, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    ext0, ext8, ext16, ext24]
  simp only [b0, b1, b2, b3, BitVec.toNat_ofNat, Nat.div_div_eq_div_mul, Nat.reduceMul]; omega

theorem rows_mod32_nodup : (evictedSha256Rows.map fun r => r.2.2 % 4294967296).Nodup := by
  apply nodup_of_natNodup; decide +kernel

theorem rows_out_nodupE : (evictedSha256Rows.map fun r => r.2.2).Nodup := by
  have h := rows_mod32_nodup
  have hfun : (fun r : Nat × Nat × Nat => r.2.2 % 4294967296) =
    ((fun x : Nat => x % 4294967296) ∘ fun r : Nat × Nat × Nat => r.2.2) := rfl
  rw [hfun, ← List.map_map] at h; exact List.Nodup.of_map _ h

theorem rows_take8_nodupE : (evictedSha256Rows.map fun r => (digestOfOut r.2.2).take 8).Nodup := by
  have h := rows_mod32_nodup
  have hfun : (fun r : Nat × Nat × Nat => r.2.2 % 4294967296) =
    (low32Bytes ∘ fun r : Nat × Nat × Nat => (digestOfOut r.2.2).take 8) := by
    funext r; exact (low32Bytes_digestOfOut_take8 r.2.2).symm
  rw [hfun, ← List.map_map] at h; exact List.Nodup.of_map _ h

theorem rows_out_ltE : (evictedSha256Rows.all fun r => decide (r.2.2 < 2 ^ 256)) = true := by
  decide +kernel

theorem rows_ltE : ∀ r ∈ evictedSha256Rows, r.2.2 < 2 ^ (8 * 32) := by
  intro r hr; have := List.all_eq_true.mp rows_out_ltE r hr; simpa using this

theorem rows_out_ne_ivE :
    (evictedSha256Rows.all fun r => r.2.2 != bytesToNat (shaStateBytes sha256IV)) = true := by
  decide +kernel

theorem rows_out_roundtripE :
    (evictedSha256Rows.all fun r => bytesToNat (shaStateBytes (shaStateOfBytes (leBytes 32 r.2.2))) == r.2.2) = true := by
  rw [List.all_eq_true]; intro r hr
  rw [shaStateBytes_shaStateOfBytes _ (leBytes_len 32 _), bytesToNat_leBytes 32 _ (rows_ltE r hr), beq_self_eq_true]

def rowOfTake8E (v : HwBytes) : Option (Nat × Nat × Nat) :=
  evictedSha256Rows.find? fun r => (digestOfOut r.2.2).take 8 == v
def rowByOutE (o : Nat) : Option (Nat × Nat × Nat) :=
  evictedSha256Rows.find? fun r => r.2.2 == o
def keyOfRow1E (r : Nat × Nat × Nat) : HwBytes :=
  ((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).take 32
def keyOfTake8E (v : HwBytes) : Option HwBytes :=
  match rowOfTake8E v with
  | none => none
  | some r2 => match rowByOutE r2.1 with | none => none | some r1 => if r1.1 = ivNat then some (keyOfRow1E r1) else none

theorem row_stepE {s : ShaState} {b : HwBytes} (h : OnTabE s b) :
    ∃ r ∈ evictedSha256Rows, r.1 = bytesToNat (shaStateBytes s) ∧ r.2.1 = bytesToNat b ∧
      FE s b = shaStateOfBytes (leBytes 32 r.2.2) := by
  obtain ⟨_, _, _, r, hr, h1, h2, h3⟩ := evictedSha256_row_of_untagged h
  exact ⟨r, hr, h1, h2, by rw [FE_eq, h3]⟩

theorem keyOfTake8_hmacWithE (k m : HwBytes) (hk : k.length = 32)
    (h : (hmacWith FE k m).take 4 ≠ compTag4) :
    keyOfTake8E ((hmacWith FE k m).take 8) = some k := by
  have hk64 : k.length ≤ 64 := by omega
  have hx := kblk_length k 0x5c hk64
  have h1 := hmac_outer_first_onTabE k m hk64 h
  have hil : (sha256With FE (kblk k 0x36 ++ m)).length = 32 := sha256With_length FE _
  rw [hmacWith_eqE k m hk64] at h ⊢
  generalize sha256With FE (kblk k 0x36 ++ m) = inner at h hil ⊢
  have hch : chunks64 (sha256Pad (kblk k 0x5c ++ inner)) = [kblk k 0x5c] ++ padTail64 inner :: [] := by
    rw [sha256Pad_append64 _ _ hx, chunks64_append64 _ _ hx, chunks64_padTail64_32 inner hil]; rfl
  have h2' : OnTabE ([kblk k 0x5c].foldl FE sha256IV) (padTail64 inner) :=
    onTabE_of_sha256With_untagged _ h [kblk k 0x5c] (padTail64 inner) [] hch
  rw [List.foldl_cons, List.foldl_nil] at h2'
  obtain ⟨r1, hr1, hr1a, hr1b, hF1⟩ := row_stepE h1
  obtain ⟨r2, hr2, hr2a, _, hF2⟩ := row_stepE h2'
  have hsha : sha256With FE (kblk k 0x5c ++ inner) = digestOfOut r2.2.2 := by
    unfold sha256With digestOfOut; rw [hch, List.singleton_append, List.foldl_cons, List.foldl_cons, List.foldl_nil, hF2]
  have hr2r1 : r2.1 = r1.2.2 := by
    rw [hr2a, hF1]; exact beq_iff_eq.mp (List.all_eq_true.mp rows_out_roundtripE r1 hr1)
  have hblk : leBytes 64 r1.2.1 = kblk k 0x5c := by
    have hrt := leBytes_bytesToNat (kblk k 0x5c); rw [hx] at hrt; rw [hr1b, hrt]
  have hfind2 : rowOfTake8E ((digestOfOut r2.2.2).take 8) = some r2 :=
    find?_eq_some_of_nodup evictedSha256Rows (fun r => (digestOfOut r.2.2).take 8) _ rows_take8_nodupE r2 hr2 rfl
  have hfind1 : rowByOutE r2.1 = some r1 :=
    find?_eq_some_of_nodup evictedSha256Rows (fun r => r.2.2) r2.1 rows_out_nodupE r1 hr1 hr2r1.symm
  have hiv : r1.1 = ivNat := hr1a
  have hkey : keyOfRow1E r1 = k := by
    unfold keyOfRow1E; rw [hblk, kblk, map_xor_xor, hk]; exact List.take_left' hk
  rw [hsha]; unfold keyOfTake8E; simp only [hfind2, hfind1, hiv, ↓reduceIte, hkey]

theorem evictedSha256_inj_of_untagged {st₁ blk₁ st₂ blk₂ : HwBytes}
    (h₁ : (evictedSha256 st₁ blk₁).take 4 ≠ compTag4)
    (heq : evictedSha256 st₁ blk₁ = evictedSha256 st₂ blk₂) : st₁ = st₂ ∧ blk₁ = blk₂ := by
  have h₂ : (evictedSha256 st₂ blk₂).take 4 ≠ compTag4 := heq ▸ h₁
  obtain ⟨-, hs₁, hb₁, row₁, hm₁, hr₁s, hr₁b, he₁⟩ := evictedSha256_row_of_untagged h₁
  obtain ⟨-, hs₂, hb₂, row₂, hm₂, hr₂s, hr₂b, he₂⟩ := evictedSha256_row_of_untagged h₂
  have hout : row₁.2.2 = row₂.2.2 := by
    have hle : leBytes 32 row₁.2.2 = leBytes 32 row₂.2.2 := by rw [← he₁, ← he₂, heq]
    rw [← bytesToNat_leBytes 32 _ (rows_ltE row₁ hm₁), ← bytesToNat_leBytes 32 _ (rows_ltE row₂ hm₂), hle]
  have hrow : row₁ = row₂ := List.inj_on_of_nodup_map rows_out_nodupE hm₁ hm₂ hout; subst hrow
  refine ⟨eq_of_bytesToNat_eq (by rw [hs₁, hs₂]) (by rw [← hr₁s, hr₂s]),
          eq_of_bytesToNat_eq (by rw [hb₁, hb₂]) (by rw [← hr₁b, hr₂b])⟩

theorem FE_inj_of_untagged {s₁ s₂ : ShaState} {b₁ b₂ : HwBytes}
    (h₁ : OnTabE s₁ b₁) (heq : FE s₁ b₁ = FE s₂ b₂) : s₁ = s₂ ∧ b₁ = b₂ := by
  rw [FE_eq, FE_eq] at heq; have hc := congrArg shaStateBytes heq
  rw [shaStateBytes_shaStateOfBytes _ (evictedSha256_length _ _),
      shaStateBytes_shaStateOfBytes _ (evictedSha256_length _ _)] at hc
  obtain ⟨hs, hb⟩ := evictedSha256_inj_of_untagged h₁ hc
  refine ⟨?_, hb⟩; rw [← shaStateOfBytes_shaStateBytes' s₁, ← shaStateOfBytes_shaStateBytes' s₂, hs]

theorem FE_ne_iv {s : ShaState} {b : HwBytes} (h : OnTabE s b) : FE s b ≠ sha256IV := by
  intro hiv; obtain ⟨r, hr, -, -, hF⟩ := row_stepE h
  have h1 := congrArg (fun t => bytesToNat (shaStateBytes t)) (hF.symm.trans hiv)
  rw [shaStateBytes_shaStateOfBytes _ (leBytes_len 32 _), bytesToNat_leBytes 32 _ (rows_ltE r hr)] at h1
  have := List.all_eq_true.mp rows_out_ne_ivE r hr; simp [h1] at this

def AllUntaggedE (L : List HwBytes) : Prop :=
  ∀ l₁ b l₂, L = l₁ ++ b :: l₂ → OnTabE (l₁.foldl FE sha256IV) b

theorem AllUntaggedE.dropLast {L : List HwBytes} {a : HwBytes} (h : AllUntaggedE (L ++ [a])) : AllUntaggedE L :=
  fun l₁ b l₂ hL => h l₁ b (l₂ ++ [a]) (by rw [hL]; simp)
theorem AllUntaggedE.last {L : List HwBytes} {a : HwBytes} (h : AllUntaggedE (L ++ [a])) : OnTabE (L.foldl FE sha256IV) a :=
  h L a [] rfl

theorem fold_inj_auxE : ∀ (n : Nat) (A B : List HwBytes),
    A.length ≤ n → AllUntaggedE A → AllUntaggedE B → A.foldl FE sha256IV = B.foldl FE sha256IV → A = B := by
  intro n; induction n with
  | zero =>
    intro A B hn _ hB heq; have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega); subst hA
    rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
    · rfl
    · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact FE_ne_iv hB.last heq.symm
  | succ n ih =>
    intro A B hn hA hB heq
    rcases eq_nil_or_snoc A with rfl | ⟨A', a, rfl⟩
    · rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
      · rfl
      · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact FE_ne_iv hB.last heq.symm
    · rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
      · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact FE_ne_iv hA.last heq
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq
        obtain ⟨hs, hb⟩ := FE_inj_of_untagged hA.last heq
        have hlen : A'.length ≤ n := by simp at hn; omega
        rw [ih A' B' hlen hA.dropLast hB.dropLast hs, hb]

theorem sha256With_inj_of_untaggedE {m₁ m₂ : HwBytes}
    (h₁ : (sha256With FE m₁).take 4 ≠ compTag4)
    (heq : sha256With FE m₁ = sha256With FE m₂) : m₁ = m₂ := by
  have ha₁ : AllUntaggedE (chunks64 (sha256Pad m₁)) := fun l₁ b l₂ hs => onTabE_of_sha256With_untagged m₁ h₁ l₁ b l₂ hs
  have ha₂ : AllUntaggedE (chunks64 (sha256Pad m₂)) := fun l₁ b l₂ hs => onTabE_of_sha256With_untagged m₂ (heq ▸ h₁) l₁ b l₂ hs
  unfold sha256With at heq
  have hc := fold_inj_auxE _ _ _ (Nat.le_refl _) ha₁ ha₂ (digest_inj heq)
  exact sha256Pad_inj (chunks64_inj (sha256Pad_length_mod m₁) (sha256Pad_length_mod m₂) hc)

def normKeyE (k : HwBytes) : HwBytes := if 64 < k.length then sha256With FE k else k

theorem normKeyE_length_le (k : HwBytes) : (normKeyE k).length ≤ 64 := by
  unfold normKeyE; split
  · rw [sha256With_length]; omega
  · omega

theorem hmacWith_eq_normKeyE (k m : HwBytes) : hmacWith FE k m = hmacWith FE (normKeyE k) m := by
  unfold normKeyE; split
  · rename_i h; have hle : ¬ 64 < (sha256With FE k).length := by rw [sha256With_length]; omega
    simp only [hmacWith, h, hle, ↓reduceIte]
  · rfl

private theorem kblk_36_of_5c (k₁ k₂ : HwBytes) (h : kblk k₁ 0x5c = kblk k₂ 0x5c) :
    kblk k₁ 0x36 = kblk k₂ 0x36 := by
  have hpad : k₁ ++ List.replicate (64 - k₁.length) 0 = k₂ ++ List.replicate (64 - k₂.length) 0 := by
    have h' := congrArg (List.map (· ^^^ (0x5c : BitVec 8))) h
    simpa only [kblk, map_xor_xor] using h'
  unfold kblk; rw [hpad]

/-- Untagged HMAC-SHA-256 is injective in the message regardless of key length. -/
theorem hmacWith_msg_inj_of_untaggedE {k₁ k₂ m₁ m₂ : HwBytes}
    (h₁ : (hmacWith FE k₁ m₁).take 4 ≠ compTag4)
    (heq : hmacWith FE k₁ m₁ = hmacWith FE k₂ m₂) : m₁ = m₂ := by
  rw [hmacWith_eq_normKeyE k₁ m₁] at h₁ heq
  rw [hmacWith_eq_normKeyE k₂ m₂] at heq
  have hk₁ := normKeyE_length_le k₁
  have hk₂ := normKeyE_length_le k₂
  have hin₁ := hmac_inner_untaggedE _ m₁ hk₁ h₁
  rw [hmacWith_eqE _ m₁ hk₁] at h₁ heq; rw [hmacWith_eqE _ m₂ hk₂] at heq
  have ho := sha256With_inj_of_untaggedE h₁ heq
  obtain ⟨hko, hino⟩ := List.append_inj ho (by rw [kblk_length _ 0x5c hk₁, kblk_length _ 0x5c hk₂])
  have hk36 := kblk_36_of_5c _ _ hko
  have hi := sha256With_inj_of_untaggedE hin₁ hino
  rw [hk36] at hi
  exact List.append_inj_right hi rfl

theorem hmacWith_inj_of_untaggedE {k₁ k₂ m₁ m₂ : HwBytes}
    (hl : k₁.length = k₂.length) (hk : k₁.length ≤ 64)
    (h₁ : (hmacWith FE k₁ m₁).take 4 ≠ compTag4)
    (heq : hmacWith FE k₁ m₁ = hmacWith FE k₂ m₂) : k₁ = k₂ ∧ m₁ = m₂ := by
  have hk₂ : k₂.length ≤ 64 := hl ▸ hk
  have hm := hmacWith_msg_inj_of_untaggedE h₁ heq
  rw [hmacWith_eqE k₁ m₁ hk] at h₁ heq; rw [hmacWith_eqE k₂ m₂ hk₂] at heq
  have ho := sha256With_inj_of_untaggedE h₁ heq
  obtain ⟨hko, -⟩ := List.append_inj ho (by rw [kblk_length _ 0x5c hk, kblk_length _ 0x5c hk₂])
  exact ⟨kblk_inj 0x5c hl hko, hm⟩

def evictedHmacKeys32 : List HwBytes :=
  evictedSha256Rows.filterMap fun r =>
    if r.1 = ivNat then
      if ((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).drop 32 = List.replicate 32 0 then
        some (((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).take 32)
      else none
    else none

theorem evictedHmacKeys32_untagged : (evictedHmacKeys32.all fun k => k.take 4 != compTag4) = true := by
  decide +kernel

theorem keyOfRow1E_untagged {r1 : Nat × Nat × Nat} (hr1 : r1 ∈ evictedSha256Rows)
    (hiv : r1.1 = ivNat) (hk : ((leBytes 64 r1.2.1).map (· ^^^ (0x5c : BitVec 8))).drop 32 = List.replicate 32 0) :
    (keyOfRow1E r1).take 4 ≠ compTag4 := by
  have hmem : keyOfRow1E r1 ∈ evictedHmacKeys32 := by
    unfold evictedHmacKeys32 keyOfRow1E; rw [List.mem_filterMap]
    exact ⟨r1, hr1, by simp only [hiv, hk, ↓reduceIte]⟩
  have h := List.all_eq_true.mp evictedHmacKeys32_untagged _ hmem
  simpa [bne_iff_ne] using h

theorem hmacWith_key_untagged_of_untaggedE {k m : HwBytes} (hk : k.length = 32)
    (h : (hmacWith FE k m).take 4 ≠ compTag4) : k.take 4 ≠ compTag4 := by
  have hx := kblk_length k 0x5c (by omega)
  obtain ⟨_, _, _, row, hrow, h1, h2, _⟩ := evictedSha256_row_of_untagged (hmac_outer_first_onTabE k m (by omega) h)
  have hrt := leBytes_bytesToNat (kblk k 0x5c); rw [hx] at hrt
  have hblk : leBytes 64 row.2.1 = kblk k 0x5c := by rw [h2, hrt]
  have hk0 : (leBytes 64 row.2.1).map (· ^^^ (0x5c : BitVec 8)) = k ++ List.replicate 32 0 := by
    rw [hblk, kblk, map_xor_xor, hk]
  have hdrop : ((leBytes 64 row.2.1).map (· ^^^ (0x5c : BitVec 8))).drop 32 = List.replicate 32 0 := by
    rw [hk0, List.drop_left' hk]
  have hkey : keyOfRow1E row = k := by unfold keyOfRow1E; rw [hk0, List.take_left' hk]
  rw [← hkey]; exact keyOfRow1E_untagged hrow h1 hdrop

theorem gamma_hmacE (S : OpaqueSymbolSemantics) (g : Ghost) (k m : DY.Bytes) :
    gamma evictedI0 S g (hmac k m) = hmacWith FE (gamma evictedI0 S g k) (gamma evictedI0 S g m) := by
  unfold gamma
  rw [show hmac k m = ({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
      ms_pack_kdf evictedI0 S g ⟨k, m⟩]
  rfl

theorem gamma_hmacE_length (S : OpaqueSymbolSemantics) (g : Ghost) (k m : DY.Bytes) :
    (gamma evictedI0 S g (hmac k m)).length = 32 := by
  rw [gamma_hmacE]; unfold hmacWith; split <;> exact sha256With_length FE _

theorem gamma_concatE (S : OpaqueSymbolSemantics) (g : Ghost) (a b : DY.Bytes) :
    gamma evictedI0 S g (DY.Concat.concat a b) = gamma evictedI0 S g a ++ gamma evictedI0 S g b := by
  unfold gamma
  rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
      ms_pack_concat evictedI0 S g ⟨a, b⟩]
  rfl

theorem gamma_trunc8E (S : OpaqueSymbolSemantics) (g : Ghost) (x : DY.Bytes) :
    gamma evictedI0 S g (DY.Trunc.trunc8 x) = (gamma evictedI0 S g x).take 8 := by
  unfold gamma
  rw [show DY.Trunc.trunc8 x = ({ input := x } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
      ms_pack_trunc evictedI0 S g ⟨x⟩]
  rfl

theorem gamma_computeMacE (S : OpaqueSymbolSemantics) (g : Ghost) (mk sIk rIk w : DY.Bytes) :
    gamma evictedI0 S g (computeMac mk sIk rIk w) =
      (hmacWith FE (gamma evictedI0 S g mk)
        (gamma evictedI0 S g sIk ++ (gamma evictedI0 S g rIk ++ gamma evictedI0 S g w))).take 8 := by
  unfold computeMac; rw [gamma_trunc8E, gamma_hmacE, gamma_concatE, gamma_concatE]

theorem spqrKeyBytes_length (v : HwBytes) : (spqrKeyBytes v).length = 32 := by
  unfold spqrKeyBytes; simp

theorem gamma_spqrSendKey_length (S : OpaqueSymbolSemantics) (g : Ghost) (st c : DY.Bytes) :
    (gamma evictedI0 S g (({ st := st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes).pack)).length = 32 := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (gSpqrSendKey S) (gAll evictedI0 S g)]
  exact spqrKeyBytes_length _

theorem gamma_spqrRecvKey_length (S : OpaqueSymbolSemantics) (g : Ghost) (st m : DY.Bytes) :
    (gamma evictedI0 S g (({ st := st, msg := m } : DY.Spqr.RecvKey.SubF DY.Bytes).pack)).length = 32 := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (gSpqrRecvKey S) (gAll evictedI0 S g)]
  exact spqrKeyBytes_length _

theorem gamma_trMsgKeys_congr_prk {S₁ S₂ : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {salt₁ seed₁ salt₂ seed₂ : DY.Bytes}
    (hprk : gamma evictedI0 S₁ g₁ (hmac salt₁ seed₁) = gamma evictedI0 S₂ g₂ (hmac salt₂ seed₂)) :
    gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).cipherKey = gamma evictedI0 S₂ g₂ (trMsgKeys salt₂ seed₂).cipherKey ∧
    gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey = gamma evictedI0 S₂ g₂ (trMsgKeys salt₂ seed₂).macKey ∧
    gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).iv = gamma evictedI0 S₂ g₂ (trMsgKeys salt₂ seed₂).iv := by
  have hlit : ∀ s, gamma evictedI0 S₁ g₁ (DY.Libsignal.TripleRatchet.lit s) = gamma evictedI0 S₂ g₂ (DY.Libsignal.TripleRatchet.lit s) := fun s => by
    unfold gamma DY.Libsignal.TripleRatchet.lit
    rw [show DY.Literal.literalToBytes s.toUTF8 = ({ lit := s.toUTF8 } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl,
        ms_pack_lit evictedI0 S₁ g₁ ⟨s.toUTF8⟩, ms_pack_lit evictedI0 S₂ g₂ ⟨s.toUTF8⟩]
    rfl
  have hlb : ∀ b, gamma evictedI0 S₁ g₁ (DY.Libsignal.TripleRatchet.litByte b) = gamma evictedI0 S₂ g₂ (DY.Libsignal.TripleRatchet.litByte b) := fun b => by
    unfold gamma DY.Libsignal.TripleRatchet.litByte
    rw [show DY.Literal.literalToBytes ⟨#[b]⟩ = ({ lit := ⟨#[b]⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl,
        ms_pack_lit evictedI0 S₁ g₁ ⟨⟨#[b]⟩⟩, ms_pack_lit evictedI0 S₂ g₂ ⟨⟨#[b]⟩⟩]
    rfl
  have hb1 : gamma evictedI0 S₁ g₁ (hkdfBlock1 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma evictedI0 S₂ g₂ (hkdfBlock1 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock1
    rw [gamma_hmacE S₁ g₁, gamma_hmacE S₂ g₂]
    simp only [gamma_concatE, hprk, hlit, hlb]
  have hb2 : gamma evictedI0 S₁ g₁ (hkdfBlock2 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma evictedI0 S₂ g₂ (hkdfBlock2 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock2
    rw [gamma_hmacE S₁ g₁, gamma_hmacE S₂ g₂]
    simp only [gamma_concatE, hprk, hb1, hlit, hlb]
  have hb3 : gamma evictedI0 S₁ g₁ (hkdfBlock3 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma evictedI0 S₂ g₂ (hkdfBlock3 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock3
    rw [gamma_hmacE S₁ g₁, gamma_hmacE S₂ g₂]
    simp only [gamma_concatE, hprk, hb2, hlit, hlb]
  exact ⟨hb1, hb2, hb3⟩

/-- An untagged 8-byte `computeMac` equality determines `macKey`, `hmac salt seed`, and `seed`
without length assumptions on `salt₁` or `salt₂`. -/
theorem computeMac_pins_macKey_prk_seed
    {S₁ S₂ : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {salt₁ seed₁ a₁ b₁ w₁ salt₂ seed₂ a₂ b₂ w₂ : DY.Bytes}
    (huntag : (gamma evictedI0 S₁ g₁ (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁)).take 4 ≠ compTag4)
    (heq : gamma evictedI0 S₁ g₁ (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁) =
           gamma evictedI0 S₂ g₂ (computeMac (trMsgKeys salt₂ seed₂).macKey a₂ b₂ w₂)) :
    gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey = gamma evictedI0 S₂ g₂ (trMsgKeys salt₂ seed₂).macKey ∧
    gamma evictedI0 S₁ g₁ (hmac salt₁ seed₁) = gamma evictedI0 S₂ g₂ (hmac salt₂ seed₂) ∧
    gamma evictedI0 S₁ g₁ seed₁ = gamma evictedI0 S₂ g₂ seed₂ := by
  have hlen1 : (gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey).length = 32 := gamma_hmacE_length _ _ _ _
  have hlen2 : (gamma evictedI0 S₂ g₂ (trMsgKeys salt₂ seed₂).macKey).length = 32 := gamma_hmacE_length _ _ _ _
  have huntag2 : (gamma evictedI0 S₂ g₂ (computeMac (trMsgKeys salt₂ seed₂).macKey a₂ b₂ w₂)).take 4 ≠ compTag4 := heq ▸ huntag
  rw [gamma_computeMacE] at huntag; rw [gamma_computeMacE] at huntag2
  rw [List.take_take, show min 4 8 = 4 by decide] at huntag huntag2
  have hk1 := keyOfTake8_hmacWithE _ _ hlen1 huntag
  have hk2 := keyOfTake8_hmacWithE _ _ hlen2 huntag2
  have ht8 := heq
  simp only [gamma_computeMacE] at ht8
  rw [ht8, hk2] at hk1; injection hk1 with hmk_rev
  have hmk := hmk_rev.symm
  have hmk_untag : (gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey).take 4 ≠ compTag4 :=
    hmacWith_key_untagged_of_untaggedE hlen1 huntag
  have hprk_len1 : (gamma evictedI0 S₁ g₁ (hmac salt₁ seed₁)).length = 32 := gamma_hmacE_length _ _ _ _
  have hprk_len2 : (gamma evictedI0 S₂ g₂ (hmac salt₂ seed₂)).length = 32 := gamma_hmacE_length _ _ _ _
  have hmk_unfold1 : gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey =
      hmacWith FE (gamma evictedI0 S₁ g₁ (hmac salt₁ seed₁))
        (gamma evictedI0 S₁ g₁ (DY.Concat.concat (hkdfBlock1 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys"))
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2)))) :=
    gamma_hmacE _ _ _ _
  have hmk_unfold2 : gamma evictedI0 S₂ g₂ (trMsgKeys salt₂ seed₂).macKey =
      hmacWith FE (gamma evictedI0 S₂ g₂ (hmac salt₂ seed₂))
        (gamma evictedI0 S₂ g₂ (DY.Concat.concat (hkdfBlock1 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys"))
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2)))) :=
    gamma_hmacE _ _ _ _
  have hmk' := hmk
  rw [hmk_unfold1, hmk_unfold2] at hmk'
  have hprk_inj := @hmacWith_inj_of_untaggedE
    (gamma evictedI0 S₁ g₁ (hmac salt₁ seed₁))
    (gamma evictedI0 S₂ g₂ (hmac salt₂ seed₂)) _ _
    (by rw [hprk_len1, hprk_len2]) (by omega) (hmk_unfold1 ▸ hmk_untag) hmk'
  have hprk := hprk_inj.1
  have hprk_untag : (gamma evictedI0 S₁ g₁ (hmac salt₁ seed₁)).take 4 ≠ compTag4 :=
    hmacWith_key_untagged_of_untaggedE hprk_len1 (hmk_unfold1 ▸ hmk_untag)
  have hprk' := hprk
  rw [gamma_hmacE S₁ g₁ salt₁ seed₁, gamma_hmacE S₂ g₂ salt₂ seed₂] at hprk'
  have hseed := hmacWith_msg_inj_of_untaggedE
    (gamma_hmacE S₁ g₁ salt₁ seed₁ ▸ hprk_untag) hprk'
  exact ⟨hmk, hprk, hseed⟩

/-- When both salts concretize to 32 bytes, an untagged `computeMac` equality also determines
`gamma evictedI0 S₁ g₁ salt₁ = gamma evictedI0 S₂ g₂ salt₂`. -/
theorem computeMac_pins_salt_and_seed
    {S₁ S₂ : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {salt₁ seed₁ a₁ b₁ w₁ salt₂ seed₂ a₂ b₂ w₂ : DY.Bytes}
    (hs₁ : (gamma evictedI0 S₁ g₁ salt₁).length = 32)
    (hs₂ : (gamma evictedI0 S₂ g₂ salt₂).length = 32)
    (huntag : (gamma evictedI0 S₁ g₁ (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁)).take 4 ≠ compTag4)
    (heq : gamma evictedI0 S₁ g₁ (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁) =
           gamma evictedI0 S₂ g₂ (computeMac (trMsgKeys salt₂ seed₂).macKey a₂ b₂ w₂)) :
    gamma evictedI0 S₁ g₁ salt₁ = gamma evictedI0 S₂ g₂ salt₂ ∧
    gamma evictedI0 S₁ g₁ seed₁ = gamma evictedI0 S₂ g₂ seed₂ := by
  obtain ⟨hmk, hprk, hseed⟩ := computeMac_pins_macKey_prk_seed huntag heq
  have hlen1 : (gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey).length = 32 := gamma_hmacE_length _ _ _ _
  have huntag' : (hmacWith FE (gamma evictedI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey)
      (gamma evictedI0 S₁ g₁ a₁ ++ (gamma evictedI0 S₁ g₁ b₁ ++ gamma evictedI0 S₁ g₁ w₁))).take 4 ≠ compTag4 := by
    rw [gamma_computeMacE, List.take_take, show min 4 8 = 4 by decide] at huntag; exact huntag
  have hmk_untag := hmacWith_key_untagged_of_untaggedE hlen1 huntag'
  have hprk_untag := hmacWith_key_untagged_of_untaggedE (gamma_hmacE_length _ _ _ _)
    (gamma_hmacE S₁ g₁ (hmac salt₁ seed₁) _ ▸ hmk_untag)
  have hprk' := hprk
  rw [gamma_hmacE S₁ g₁ salt₁ seed₁, gamma_hmacE S₂ g₂ salt₂ seed₂] at hprk'
  have hsalt := (@hmacWith_inj_of_untaggedE
    (gamma evictedI0 S₁ g₁ salt₁) (gamma evictedI0 S₂ g₂ salt₂)
    (gamma evictedI0 S₁ g₁ seed₁) (gamma evictedI0 S₂ g₂ seed₂)
    (by rw [hs₁, hs₂]) (by omega)
    (gamma_hmacE S₁ g₁ salt₁ seed₁ ▸ hprk_untag) hprk').1
  exact ⟨hsalt, hseed⟩

/-- If `msg.mac` concretizes to an untagged honest `computeMac` tag with `salt_h ∈ honest`, then
`MacTagForgeryOrCollision` does not hold for any `known` or `ctxs`. -/
theorem not_macTagForgeryOrCollision_of_honest_mac
    {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop} {honest : List DY.Bytes}
    {msg : TRSignalMsg} {ctxs : List TrialCtx} {salt_h seed_h a_h b_h w_h : DY.Bytes}
    (hmem : salt_h ∈ honest)
    (hmac_eq : gamma evictedI0 S g msg.mac =
               gamma evictedI0 S g (computeMac (trMsgKeys salt_h seed_h).macKey a_h b_h w_h))
    (huntag : (gamma evictedI0 S g msg.mac).take 4 ≠ compTag4) :
    ¬ MacTagForgeryOrCollision evictedI0 S g known honest msg ctxs := by
  rintro (⟨ctx, _, seed, _, k_own, _, hmac1, _, hne⟩ |
          ⟨ctx, _, seed, _, k_own, _, hmac1, ctx₀, _, seed₀, _, hseed_ne, hcol⟩)
  · obtain ⟨-, hprk, hseed⟩ := computeMac_pins_macKey_prk_seed (hmac1.symm ▸ huntag) (hmac1.trans hmac_eq)
    have hprk' : gamma evictedI0 S g (hmac salt_h seed) = gamma evictedI0 S g (hmac k_own seed) := by
      rw [gamma_hmacE, hseed, ← gamma_hmacE, hprk.symm]
    obtain ⟨hc, hm, hiv⟩ := gamma_trMsgKeys_congr_prk hprk'
    exact hne salt_h hmem (Prod.ext hc (Prod.ext hm hiv))
  · rcases hcol with ⟨salt₀, _, hmac0⟩ | ⟨pIk₀, mIk₀, salt₀, w₀, hmsg_eq, _⟩
    · obtain ⟨-, -, hseed⟩ := computeMac_pins_macKey_prk_seed (hmac1.symm ▸ huntag) (hmac1.trans hmac0.symm)
      exact hseed_ne hseed
    · have hmac0 : gamma evictedI0 S g (computeMac (trMsgKeys salt₀ seed₀).macKey pIk₀ mIk₀ w₀) =
          gamma evictedI0 S g msg.mac := by rw [hmsg_eq]
      obtain ⟨-, -, hseed⟩ := computeMac_pins_macKey_prk_seed (hmac1.symm ▸ huntag) (hmac1.trans hmac0.symm)
      exact hseed_ne hseed

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
