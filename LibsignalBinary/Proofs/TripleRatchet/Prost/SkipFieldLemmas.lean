/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.VarintBridge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


private theorem bv_sub_add_96 (sp v : BitVec 64) :
    sp - 96#64 = sp - (v + 96#64) + v := by bv_lin

private theorem bv_sub_96_sub (sp v : BitVec 64) :
    sp - 96#64 - v = sp - (v + 96#64) := by bv_lin

private theorem bv_sub_96_add_cancel (sp u w : BitVec 64) :
    sp - 96#64 - w = sp - 96#64 - (u + w) + u := by bv_lin

theorem memRegion_48_skipSlice (sp : BitVec 64) :
    memRegion (sp - 96#64) 48 =
      memRegion (sp - 96#64) 24 ∗ memRegion (sp - 72#64) 24 := by
  have s1 := memRegion_split (sp - 96#64) 24 24 (by decide)
  rw [bv_sub_add_lit sp 96 24] at s1
  exact s1

theorem skipSliceErr_entails_memRegion48 (sp v0 v1 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
      memRegion (sp - 80#64) 8 ∗ memRegion (sp - 72#64) 24 ⊢
      memRegion (sp - 96#64) 48 := by
  have s1 := memRegion_split (sp - 96#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 96 8] at s1
  have s2 := memRegion_split (sp - 88#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 88 8] at s2
  have s3 := memRegion_split (sp - 80#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s3
  rw [s1, s2, s3]
  exact sepConj_mono (pointsTo64_entails_memRegion8 _ v0)
    (sepConj_mono (pointsTo64_entails_memRegion8 _ v1) (Entails.refl _))

theorem skipSliceOk_entails_memRegion48 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
      ((sp - 80#64) ↦₆₄ v2) ∗ memRegion (sp - 72#64) 24 ⊢
      memRegion (sp - 96#64) 48 := by
  refine Entails.trans ?_ (skipSliceErr_entails_memRegion48 sp v0 v1)
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion8 _ v2)))


theorem memRegion_48_split2 (sp : BitVec 64) :
    memRegion (sp - 96#64) 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v1) ∗ ((sp - 88#64) ↦₆₄ v0)) ∗
        memRegion (sp - 80#64) 32 := by
  have s1 := memRegion_split (sp - 96#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 96 8] at s1
  have s2 := memRegion_split (sp - 88#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 88 8] at s2
  rw [s1, s2, memRegion_eight (sp - 96#64), memRegion_eight (sp - 88#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem pointsTo64_memRegion32_entails_40 (sp v1 : BitVec 64) :
    ((sp - 88#64) ↦₆₄ v1) ∗ memRegion (sp - 80#64) 32 ⊢
      memRegion (sp - 88#64) 40 := by
  have s2 := memRegion_split (sp - 88#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 88 8] at s2
  rw [s2]
  exact sepConj_mono_left (pointsTo64_entails_memRegion8 _ v1)

/-! ## Branch and arithmetic helpers for `skip_field` -/

theorem cbz_depth_zero {w : BitVec 64} (h : w.setWidth 32 = BitVec.ofNat 32 0) :
    (BitVec.truncate 32 w == 0#32) = true := by
  change (w.setWidth 32 == 0#32) = true
  rw [h]; rfl

theorem cbz_depth_succ {w : BitVec 64} {d : Nat}
    (h : w.setWidth 32 = BitVec.ofNat 32 (d + 1)) (hd : d + 1 < 2 ^ 32) :
    (BitVec.truncate 32 w == 0#32) = false := by
  change (w.setWidth 32 == 0#32) = false
  rw [h, beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd] at h1
  simp at h1

theorem w0_and_255_eq {w : BitVec 64} {wt : WireType}
    (h : w.setWidth 8 = BitVec.ofNat 8 wt.toNat) :
    BitVec.truncate 32 w &&& 255#32 = BitVec.ofNat 32 wt.toNat := by
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat] at h1 ⊢
  rw [Nat.and_two_pow_sub_one_eq_mod _ 8, Nat.mod_mod_of_dvd w.toNat (by decide : 2 ^ 8 ∣ 2 ^ 32), h1]
  cases wt <;> rfl

theorem skipField_depth_zero (fuel tag : Nat) (wt : WireType) (bs : List (BitVec 8)) :
    skipField fuel 0 tag wt bs = none := by
  cases fuel <;> rfl

theorem skipField_succ_endGroup (fuel d tag : Nat) (bs : List (BitVec 8)) :
    skipField (fuel + 1) (d + 1) tag .endGroup bs = none := rfl

theorem skipField_succ_varint (fuel d tag : Nat) (bs : List (BitVec 8)) :
    skipField (fuel + 1) (d + 1) tag .varint bs = (decodeVarint bs).map (·.2) := rfl

theorem skipField_succ_thirtyTwoBit (fuel d tag : Nat) (bs : List (BitVec 8)) :
    skipField (fuel + 1) (d + 1) tag .thirtyTwoBit bs = skipBytes 4 bs := rfl

theorem skipField_succ_sixtyFourBit (fuel d tag : Nat) (bs : List (BitVec 8)) :
    skipField (fuel + 1) (d + 1) tag .sixtyFourBit bs = skipBytes 8 bs := rfl

theorem skipField_succ_lengthDelimited (fuel d tag : Nat) (bs : List (BitVec 8)) :
    skipField (fuel + 1) (d + 1) tag .lengthDelimited bs =
      match decodeVarint bs with
      | none => none
      | some (len, rest) => skipBytes len.toNat rest := rfl

theorem skipField_succ_startGroup (fuel d tag : Nat) (bs : List (BitVec 8)) :
    skipField (fuel + 1) (d + 1) tag .startGroup bs = skipGroup fuel (d + 1) tag bs := rfl

theorem decodeVarint_1 {b0 : BitVec 8} (bs1 : List (BitVec 8)) (hb0 : b0 ≤ 0x7f#8) :
    decodeVarint (b0 :: bs1) = some ((b0 &&& 0x7f#8).zeroExtend 64, bs1) := by
  rw [decodeVarint, decodeVarintAux]
  simp [toNat_le_0x7f_iff, hb0]

theorem signExtend64_eq_and_0x7f {b0 : BitVec 8} (hb0 : b0 ≤ 0x7f#8) :
    BitVec.signExtend 64 b0 = (b0 &&& 0x7f#8).zeroExtend 64 := by
  have hle : b0.toNat < 128 := by rw [← toNat_le_0x7f_iff] at hb0; omega
  have hmsb : b0.msb = false := by rw [BitVec.msb_eq_decide, decide_eq_false_iff_not]; omega
  have hand : b0 &&& 0x7f#8 = b0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_two_pow_sub_one_eq_mod b0.toNat 7, Nat.mod_eq_of_lt hle]
  rw [hand]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]
  by_cases h8 : i < 8
  · simp [hi, h8]
  · simp [hi, h8, hmsb, BitVec.getLsbD_of_ge b0 i (by omega)]

theorem ule_len_of_lt {rest : List (BitVec 8)} {n : BitVec 64}
    (hlt : rest.length < n.toNat) (hr : rest.length < 2 ^ 63) :
    n.ule (BitVec.ofNat 64 rest.length) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem ule_len_of_ge {rest : List (BitVec 8)} {n : BitVec 64}
    (hge : ¬ rest.length < n.toNat) (hr : rest.length < 2 ^ 63) :
    n.ule (BitVec.ofNat 64 rest.length) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem bv_len_sub_skip {rest : List (BitVec 8)} {n : BitVec 64}
    (hge : ¬ rest.length < n.toNat) :
    BitVec.ofNat 64 rest.length - n = BitVec.ofNat 64 (rest.drop n.toNat).length := by
  rw [List.length_drop]
  have hsplit : rest.length = (rest.length - n.toNat) + n.toNat := by omega
  conv => lhs; arg 1; rw [hsplit]
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_sub_cancel]

theorem bv_ptr_add_skip {bs rest : List (BitVec 8)} {ptr n : BitVec 64}
    (hsub : rest.length ≤ bs.length) (hge : ¬ rest.length < n.toNat) :
    ptr + BitVec.ofNat 64 (bs.length - rest.length) + n =
      ptr + BitVec.ofNat 64 (bs.length - (rest.drop n.toNat).length) := by
  rw [List.length_drop]
  have h1 : bs.length - (rest.length - n.toNat) = (bs.length - rest.length) + n.toNat := by omega
  rw [h1, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

theorem bv_ptr_add_skip_top {bs : List (BitVec 8)} {ptr n : BitVec 64}
    (hge : ¬ bs.length < n.toNat) :
    ptr + n = ptr + BitVec.ofNat 64 (bs.length - (bs.drop n.toNat).length) := by
  have h := bv_ptr_add_skip (bs := bs) (rest := bs) (ptr := ptr) (n := n) (Nat.le_refl _) hge
  rw [Nat.sub_self] at h
  change ptr + 0#64 + n = _ at h
  rwa [BitVec.add_zero] at h

theorem allowPanic_frame' {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace)
    (hpan : sf.mem ⊨ ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R := by
  have h := allowPanic_frame (allocFailedIn_trans htr) hpan
  rwa [sepConj_assoc, satisfies_pure_sepConj] at h


theorem skipSliceTail_entails_memRegion40 (sp v1 v2 : BitVec 64) :
    ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗ memRegion (sp - 72#64) 24 ⊢
      memRegion (sp - 88#64) 40 := by
  have s2 := memRegion_split (sp - 88#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 88 8] at s2
  have s3 := memRegion_split (sp - 80#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s3
  rw [s2, s3]
  exact sepConj_mono (pointsTo64_entails_memRegion8 _ v1)
    (sepConj_mono (pointsTo64_entails_memRegion8 _ v2) (Entails.refl _))


/-! ## Suffix and cursor-splitting helpers for `StartGroup` -/

theorem decodeVarint_suffix {bs r : List (BitVec 8)} {v : BitVec 64}
    (h : decodeVarint bs = some (v, r)) :
    r = bs.drop (bs.length - r.length) := by
  obtain ⟨k, _, _, hr⟩ := decodeVarintAux_suffix bs 0 0#64 v r h
  have hk : bs.length - r.length = k := by rw [hr, List.length_drop]; omega
  rw [hk, hr]

theorem skipBytes_suffix {n : Nat} {bs r : List (BitVec 8)} (h : skipBytes n bs = some r) :
    r = bs.drop (bs.length - r.length) := by
  simp only [skipBytes] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    rw [List.length_drop, Nat.sub_sub_self (by omega)]

theorem suffix_trans {bs r1 r2 : List (BitVec 8)}
    (hle1 : r1.length ≤ bs.length) (hs1 : r1 = bs.drop (bs.length - r1.length))
    (hle2 : r2.length ≤ r1.length) (hs2 : r2 = r1.drop (r1.length - r2.length)) :
    r2 = bs.drop (bs.length - r2.length) := by
  have h : r1.drop (r1.length - r2.length) =
      (bs.drop (bs.length - r1.length)).drop (r1.length - r2.length) := by
    rw [← hs1]
  conv => lhs; rw [hs2, h, List.drop_drop]
  congr 1
  omega

theorem decodeKey_suffix {bs rest : List (BitVec 8)} {k : Nat × WireType}
    (h : decodeKey bs = some (k, rest)) :
    rest = bs.drop (bs.length - rest.length) := by
  unfold decodeKey at h
  split at h
  · simp at h
  · rename_i key r hv
    split at h
    · simp at h
    · split at h
      · simp at h
      · dsimp only at h
        split at h
        · simp at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact decodeVarint_suffix hv

theorem skipScalar_suffix {wt : WireType} {bs r : List (BitVec 8)}
    (h : skipScalar wt bs = some r) : r = bs.drop (bs.length - r.length) := by
  cases wt with
  | varint =>
    simp only [skipScalar, Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, rfl⟩ := h
    exact decodeVarint_suffix hv
  | thirtyTwoBit => exact skipBytes_suffix h
  | sixtyFourBit => exact skipBytes_suffix h
  | lengthDelimited =>
    simp only [skipScalar] at h
    split at h
    · simp at h
    · rename_i len r' hv
      have hr_le : r.length ≤ r'.length := by
        simp only [skipBytes] at h
        split at h
        · simp at h
        · simp only [Option.some.injEq] at h; subst h; simp
      exact suffix_trans (Nat.le_of_lt (decodeVarint_length hv)) (decodeVarint_suffix hv)
        hr_le (skipBytes_suffix h)
  | startGroup => simp [skipScalar] at h
  | endGroup => simp [skipScalar] at h

theorem skip_suffix (fuel : Nat) :
    (∀ d t wt (bs r : List (BitVec 8)), skipField fuel d t wt bs = some r →
      r = bs.drop (bs.length - r.length)) ∧
    (∀ d t (bs r : List (BitVec 8)), skipGroup fuel d t bs = some r →
      r = bs.drop (bs.length - r.length)) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ _ h => by simp [skipField] at h,
      fun _ _ _ _ h => by simp [skipGroup] at h⟩
  | succ f ih =>
    refine ⟨fun d t wt bs r h => ?_, fun d t bs r h => ?_⟩
    · simp only [skipField] at h
      split at h
      · simp at h
      · cases wt with
        | endGroup => simp at h
        | startGroup => exact ih.2 _ _ _ _ h
        | varint => exact skipScalar_suffix h
        | thirtyTwoBit => exact skipScalar_suffix h
        | sixtyFourBit => exact skipScalar_suffix h
        | lengthDelimited => exact skipScalar_suffix h
    · simp only [skipGroup] at h
      split at h
      · simp at h
      · rename_i itag rest hk
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact decodeKey_suffix hk
        · simp at h
      · rename_i itag iwt rest _ hk
        split at h
        · simp at h
        · rename_i rest' hs
          have hle_k := Nat.le_of_lt (decodeKey_length hk)
          have hle_s := (skip_length f).1 _ _ _ _ _ hs
          have hle_g := (skip_length f).2 _ _ _ _ h
          exact suffix_trans hle_k (decodeKey_suffix hk) (by omega)
            (suffix_trans hle_s (ih.1 _ _ _ _ _ hs) hle_g (ih.2 _ _ _ _ h))

theorem sliceCursorAfter_eq_split {slot ptr : BitVec 64} {bs rest : List (BitVec 8)}
    (hle : rest.length ≤ bs.length)
    (hsuf : rest = bs.drop (bs.length - rest.length)) :
    sliceCursorAfter slot ptr bs rest =
      (ptr ↦ₛ bs.take (bs.length - rest.length)) ∗
        sliceCursorAt slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest := by
  simp only [sliceCursorAfter, sliceCursorAt]
  have hbs : bs = bs.take (bs.length - rest.length) ++ rest := by
    conv => rhs; arg 2; rw [hsuf]
    exact (List.take_append_drop _ _).symm
  have hlen : (bs.take (bs.length - rest.length)).length = bs.length - rest.length := by
    rw [List.length_take]; omega
  conv => lhs; arg 2; arg 2; rw [hbs, pointsToBytes_append, hlen]
  ac_rfl

theorem sliceCursorAfter_join {slot ptr : BitVec 64} {bs rest finalRest : List (BitVec 8)}
    (hle1 : rest.length ≤ bs.length)
    (hsuf1 : rest = bs.drop (bs.length - rest.length))
    (hle2 : finalRest.length ≤ rest.length) :
    (ptr ↦ₛ bs.take (bs.length - rest.length)) ∗
      sliceCursorAfter slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest finalRest ⊢
      sliceCursorAfter slot ptr bs finalRest := by
  simp only [sliceCursorAfter]
  have hbs : bs = bs.take (bs.length - rest.length) ++ rest := by
    conv => rhs; arg 2; rw [hsuf1]
    exact (List.take_append_drop _ _).symm
  have hlen : (bs.take (bs.length - rest.length)).length = bs.length - rest.length := by
    rw [List.length_take]; omega
  have hptr :
      ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - finalRest.length) =
        ptr + BitVec.ofNat 64 (bs.length - finalRest.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  have hpts : (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.take (bs.length - rest.length)) ∗
        ((ptr + BitVec.ofNat 64 (bs.length - rest.length)) ↦ₛ rest) := by
    conv => lhs; rw [hbs, pointsToBytes_append, hlen]
  rw [hptr, hpts]
  exact Entails.of_eq (by ac_rfl)

theorem pointsToBytes_prefix_join {ptr : BitVec 64} {bs rest : List (BitVec 8)}
    (hle : rest.length ≤ bs.length)
    (hsuf : rest = bs.drop (bs.length - rest.length)) :
    (ptr ↦ₛ bs.take (bs.length - rest.length)) ∗
      ((ptr + BitVec.ofNat 64 (bs.length - rest.length)) ↦ₛ rest) ⊢
      (ptr ↦ₛ bs) := by
  have hbs : bs = bs.take (bs.length - rest.length) ++ rest := by
    conv => rhs; arg 2; rw [hsuf]
    exact (List.take_append_drop _ _).symm
  have hlen : (bs.take (bs.length - rest.length)).length = bs.length - rest.length := by
    rw [List.length_take]; omega
  conv => rhs; rw [hbs, pointsToBytes_append, hlen]
  exact Entails.refl _

theorem skip_fuel_eq (f1 : Nat) :
    (∀ f2 d t wt (bs : List (BitVec 8)),
      2 * bs.length + 2 ≤ f1 → 2 * bs.length + 2 ≤ f2 →
      skipField f1 d t wt bs = skipField f2 d t wt bs) ∧
    (∀ f2 d t (bs : List (BitVec 8)),
      2 * bs.length + 1 ≤ f1 → 2 * bs.length + 1 ≤ f2 →
      skipGroup f1 d t bs = skipGroup f2 d t bs) := by
  induction f1 with
  | zero =>
    exact ⟨fun _ _ _ _ _ h1 _ => by omega, fun _ _ _ _ h1 _ => by omega⟩
  | succ f1 ih =>
    refine ⟨fun f2 d t wt bs h1 h2 => ?_, fun f2 d t bs h1 h2 => ?_⟩
    · cases f2 with
      | zero => omega
      | succ f2 =>
        simp only [skipField]
        split
        · rfl
        · cases wt <;> first | rfl | exact ih.2 f2 _ _ bs (by omega) (by omega)
    · cases f2 with
      | zero => omega
      | succ f2 =>
        simp only [skipGroup]
        split
        · rfl
        · rfl
        · rename_i itag iwt rest _ hk
          have hlt := decodeKey_length hk
          rw [ih.1 f2 (d - 1) itag iwt rest (by omega) (by omega)]
          split
          · rfl
          · rename_i rest' hs
            have hle := (skip_length f2).1 (d - 1) itag iwt rest rest' hs
            exact ih.2 f2 d t rest' (by omega) (by omega)

theorem skipGroup_unfold (d tag : Nat) (cur : List (BitVec 8)) :
    skipGroup (2 * cur.length + 1) (d + 1) tag cur =
      match decodeKey cur with
      | none => none
      | some ((itag, .endGroup), rest) =>
        if itag = tag then some rest else none
      | some ((itag, iwt), rest) =>
        match skipField (2 * rest.length + 2) d itag iwt rest with
        | none => none
        | some rest' => skipGroup (2 * rest'.length + 1) (d + 1) tag rest' := by
  rw [show 2 * cur.length + 1 = (2 * cur.length) + 1 from rfl, skipGroup]
  simp only [Nat.add_sub_cancel]
  cases hk : decodeKey cur with
  | none => rfl
  | some p =>
    rcases p with ⟨⟨itag, iwt⟩, rest⟩
    have hlt := decodeKey_length hk
    cases iwt with
    | endGroup => rfl
    | varint =>
      dsimp only
      rw [(skip_fuel_eq (2 * cur.length)).1 (2 * rest.length + 2) d itag .varint rest (by omega) (by omega)]
      cases hs : skipField (2 * rest.length + 2) d itag .varint rest with
      | none => rfl
      | some rest' =>
        have hle := (skip_length (2 * rest.length + 2)).1 d itag .varint rest rest' hs
        exact (skip_fuel_eq (2 * cur.length)).2 (2 * rest'.length + 1) (d + 1) tag rest' (by omega) (by omega)
    | sixtyFourBit =>
      dsimp only
      rw [(skip_fuel_eq (2 * cur.length)).1 (2 * rest.length + 2) d itag .sixtyFourBit rest (by omega) (by omega)]
      cases hs : skipField (2 * rest.length + 2) d itag .sixtyFourBit rest with
      | none => rfl
      | some rest' =>
        have hle := (skip_length (2 * rest.length + 2)).1 d itag .sixtyFourBit rest rest' hs
        exact (skip_fuel_eq (2 * cur.length)).2 (2 * rest'.length + 1) (d + 1) tag rest' (by omega) (by omega)
    | lengthDelimited =>
      dsimp only
      rw [(skip_fuel_eq (2 * cur.length)).1 (2 * rest.length + 2) d itag .lengthDelimited rest (by omega) (by omega)]
      cases hs : skipField (2 * rest.length + 2) d itag .lengthDelimited rest with
      | none => rfl
      | some rest' =>
        have hle := (skip_length (2 * rest.length + 2)).1 d itag .lengthDelimited rest rest' hs
        exact (skip_fuel_eq (2 * cur.length)).2 (2 * rest'.length + 1) (d + 1) tag rest' (by omega) (by omega)
    | startGroup =>
      dsimp only
      rw [(skip_fuel_eq (2 * cur.length)).1 (2 * rest.length + 2) d itag .startGroup rest (by omega) (by omega)]
      cases hs : skipField (2 * rest.length + 2) d itag .startGroup rest with
      | none => rfl
      | some rest' =>
        have hle := (skip_length (2 * rest.length + 2)).1 d itag .startGroup rest rest' hs
        exact (skip_fuel_eq (2 * cur.length)).2 (2 * rest'.length + 1) (d + 1) tag rest' (by omega) (by omega)
    | thirtyTwoBit =>
      dsimp only
      rw [(skip_fuel_eq (2 * cur.length)).1 (2 * rest.length + 2) d itag .thirtyTwoBit rest (by omega) (by omega)]
      cases hs : skipField (2 * rest.length + 2) d itag .thirtyTwoBit rest with
      | none => rfl
      | some rest' =>
        have hle := (skip_length (2 * rest.length + 2)).1 d itag .thirtyTwoBit rest rest' hs
        exact (skip_fuel_eq (2 * cur.length)).2 (2 * rest'.length + 1) (d + 1) tag rest' (by omega) (by omega)

theorem skipGroup_of_decodeVarint_none {d tag : Nat} {cur : List (BitVec 8)}
    (hd : decodeVarint cur = none) :
    skipGroup (2 * cur.length + 1) (d + 1) tag cur = none := by
  rw [skipGroup_unfold, decodeKey, hd]

theorem skipGroup_of_key_ge {d tag : Nat} {cur rest : List (BitVec 8)} {key : BitVec 64}
    (hd : decodeVarint cur = some (key, rest)) (hk : 2 ^ 32 ≤ key.toNat) :
    skipGroup (2 * cur.length + 1) (d + 1) tag cur = none := by
  have hk' : 4294967296 ≤ key.toNat := hk
  rw [skipGroup_unfold, decodeKey, hd]
  simp [hk']

theorem skipGroup_of_wt_none {d tag : Nat} {cur rest : List (BitVec 8)} {key : BitVec 64}
    (hd : decodeVarint cur = some (key, rest)) (hk : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = none) :
    skipGroup (2 * cur.length + 1) (d + 1) tag cur = none := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  rw [skipGroup_unfold, decodeKey, hd]
  simp [hk', hwt]

theorem skipGroup_of_tag_zero {d tag : Nat} {cur rest : List (BitVec 8)} {key : BitVec 64}
    {iwt : WireType} (hd : decodeVarint cur = some (key, rest)) (hk : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt) (htag : key.toNat / 8 < 1) :
    skipGroup (2 * cur.length + 1) (d + 1) tag cur = none := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  have htag' : key.toNat < 8 := by omega
  rw [skipGroup_unfold, decodeKey, hd]
  simp [hk', hwt, htag']

theorem skipGroup_of_endGroup {d tag : Nat} {cur rest : List (BitVec 8)} {key : BitVec 64}
    (hd : decodeVarint cur = some (key, rest)) (hk : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some .endGroup) (htag : ¬ key.toNat / 8 < 1) :
    skipGroup (2 * cur.length + 1) (d + 1) tag cur =
      if key.toNat / 8 = tag then some rest else none := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  have htag' : ¬ key.toNat < 8 := by omega
  rw [skipGroup_unfold, decodeKey, hd]
  simp [hk', hwt, htag']

theorem skipGroup_of_ne_endGroup {d tag : Nat} {cur rest : List (BitVec 8)} {key : BitVec 64}
    {iwt : WireType} (hd : decodeVarint cur = some (key, rest)) (hk : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt) (htag : ¬ key.toNat / 8 < 1)
    (hne : iwt ≠ .endGroup) :
    skipGroup (2 * cur.length + 1) (d + 1) tag cur =
      match skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest with
      | none => none
      | some rest' => skipGroup (2 * rest'.length + 1) (d + 1) tag rest' := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  have htag' : ¬ key.toNat < 8 := by omega
  rw [skipGroup_unfold, decodeKey, hd]
  cases iwt <;> first | contradiction | simp [hk', hwt, htag']

theorem sf_truncate32_ofNat64 (n : Nat) :
    BitVec.truncate 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]

theorem bv32_zeroExtend_ofNat {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).zeroExtend 64 = BitVec.ofNat 64 n ∧
      BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  have h1 : (BitVec.ofNat 32 n).zeroExtend 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [sf_truncate32_ofNat64]
  exact ⟨h1, h1⟩

theorem bv32_add_neg1_eq_sub1 (x : BitVec 32) : x + 4294967295#32 = x - 1#32 := by
  bv_lin

theorem bv32_sub_one_ofNat (d : Nat) :
    BitVec.ofNat 32 (d + 1) - 1#32 = BitVec.ofNat 32 d := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem bv32_sub_one_zeroExtend {d : Nat} (h : d + 1 < 2 ^ 32) :
    (BitVec.ofNat 32 (d + 1) + 4294967295#32).zeroExtend 64 = BitVec.ofNat 64 d ∧
      (BitVec.ofNat 32 (d + 1) - 1#32).zeroExtend 64 = BitVec.ofNat 64 d := by
  rw [bv32_add_neg1_eq_sub1, bv32_sub_one_ofNat]
  have hd : (BitVec.ofNat 32 d).zeroExtend 64 = BitVec.ofNat 64 d :=
    (bv32_zeroExtend_ofNat (by omega)).1
  exact ⟨hd, hd⟩

theorem key_shr32_of_ge {key : BitVec 64} (h : 2 ^ 32 ≤ key.toNat) :
    (key >>> 32 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] at h1
  omega

theorem key_shr32_of_lt {key : BitVec 64} (h : ¬ 2 ^ 32 ≤ key.toNat) :
    (key >>> 32 == 0#64) = true := by
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega

theorem toNat_and_7_eq_mod_8 (key : BitVec 64) :
    (key &&& 7#64).toNat = key.toNat % 8 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact Nat.and_two_pow_sub_one_eq_mod key.toNat 3

theorem key_wt_none {key : BitVec 64} (hwt : WireType.ofNat? (key.toNat % 8) = none) :
    (key &&& 7#64).ult 6#64 = false ∧ (6#64).ule (key &&& 7#64) = true := by
  have hmod : key.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  have hand := toNat_and_7_eq_mod_8 key
  simp only [BitVec.ult, BitVec.ule, hand, BitVec.toNat_ofNat,
    decide_eq_false_iff_not, decide_eq_true_eq]
  rcases (by omega : key.toNat % 8 = 0 ∨ key.toNat % 8 = 1 ∨ key.toNat % 8 = 2 ∨
    key.toNat % 8 = 3 ∨ key.toNat % 8 = 4 ∨ key.toNat % 8 = 5 ∨
    key.toNat % 8 = 6 ∨ key.toNat % 8 = 7) with h | h | h | h | h | h | h | h <;>
    simp [h, WireType.ofNat?] at hwt ⊢

theorem key_wt_some {key : BitVec 64} {iwt : WireType}
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt) :
    (key &&& 7#64).ult 6#64 = true ∧
      (6#64).ule (key &&& 7#64) = false ∧
      key &&& 7#64 = BitVec.ofNat 64 iwt.toNat ∧
      (BitVec.ofNat 64 iwt.toNat).ult 6#64 = true ∧
      (6#64).ule (BitVec.ofNat 64 iwt.toNat) = false := by
  have hmod : key.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  have hand := toNat_and_7_eq_mod_8 key
  have h1 : (key &&& 7#64).ult 6#64 = true := by
    simp only [BitVec.ult, hand, BitVec.toNat_ofNat, decide_eq_true_eq]
    rcases (by omega : key.toNat % 8 = 0 ∨ key.toNat % 8 = 1 ∨ key.toNat % 8 = 2 ∨
      key.toNat % 8 = 3 ∨ key.toNat % 8 = 4 ∨ key.toNat % 8 = 5 ∨
      key.toNat % 8 = 6 ∨ key.toNat % 8 = 7) with h | h | h | h | h | h | h | h <;>
      simp [h, WireType.ofNat?] at hwt ⊢
  have h2 : (6#64).ule (key &&& 7#64) = false := by
    simp only [BitVec.ule, hand, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    rcases (by omega : key.toNat % 8 = 0 ∨ key.toNat % 8 = 1 ∨ key.toNat % 8 = 2 ∨
      key.toNat % 8 = 3 ∨ key.toNat % 8 = 4 ∨ key.toNat % 8 = 5 ∨
      key.toNat % 8 = 6 ∨ key.toNat % 8 = 7) with h | h | h | h | h | h | h | h <;>
      simp [h, WireType.ofNat?] at hwt ⊢
  have h3 : key &&& 7#64 = BitVec.ofNat 64 iwt.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [hand]
    rcases (by omega : key.toNat % 8 = 0 ∨ key.toNat % 8 = 1 ∨ key.toNat % 8 = 2 ∨
      key.toNat % 8 = 3 ∨ key.toNat % 8 = 4 ∨ key.toNat % 8 = 5 ∨
      key.toNat % 8 = 6 ∨ key.toNat % 8 = 7) with h | h | h | h | h | h | h | h <;>
      simp [h, WireType.ofNat?] at hwt <;> subst hwt <;> simp [h, WireType.toNat]
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rwa [← h3]
  · rwa [← h3]

theorem w1_tag_eq {key : BitVec 64} (hk : ¬ 2 ^ 32 ≤ key.toNat) :
    BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) ∧
      BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3) =
        BitVec.ofNat 32 (key.toNat / 8) := by
  have h1 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat]
    omega
  have h2 : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3) =
      BitVec.ofNat 32 (key.toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat]
    omega
  exact ⟨h1, h2⟩

theorem tag_cbz_false {key : BitVec 64} (hk : ¬ 2 ^ 32 ≤ key.toNat)
    (htag : ¬ key.toNat / 8 < 1) :
    (BitVec.ofNat 32 (key.toNat / 8) == 0#32) = false ∧
      (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 0#32) = false := by
  have h1 : (BitVec.ofNat 32 (key.toNat / 8) == 0#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have h2 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 32)] at h2
    omega
  rw [sf_truncate32_ofNat64]
  exact ⟨h1, h1⟩

theorem iwt_beq_4_false {iwt : WireType} (hne : iwt ≠ .endGroup) :
    (BitVec.ofNat 64 iwt.toNat == 4#64) = false := by
  cases iwt <;> first | contradiction | decide

theorem itag_beq_tag_false {itag tag : Nat} (hne : itag ≠ tag)
    (hi : itag < 2 ^ 32) (ht : tag < 2 ^ 32) :
    (BitVec.ofNat 32 itag == BitVec.ofNat 32 tag) = false ∧
      (BitVec.truncate 32 (BitVec.ofNat 64 itag) ==
        BitVec.truncate 32 (BitVec.ofNat 64 tag)) = false := by
  have h1 : (BitVec.ofNat 32 itag == BitVec.ofNat 32 tag) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have h2 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt ht] at h2
    exact hne h2
  rw [sf_truncate32_ofNat64, sf_truncate32_ofNat64]
  exact ⟨h1, h1⟩

theorem iwt_w0_setWidth8 (iwt : WireType) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 iwt.toNat))).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat ∧
    (BitVec.ofNat 64 iwt.toNat).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> decide

/-- Wrapper for `cur = bs.drop (bs.length - cur.length)` that is opaque to `isLightweightSimpHyp`
    so `wp_steps` does not add it as a self-referential `simp` rewrite rule. -/
def IsDropSuffix (bs cur : List (BitVec 8)) : Prop :=
  cur = bs.drop (bs.length - cur.length)

abbrev HighCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

/-! ## In-image variant of `skip_field` -/

abbrev skipBelowX (sp : BitVec 64) (depth : Nat) : SepProp :=
  stackAt (sp - 96#64) (depth * 0x60 + decodeVarintSliceStackX)

theorem stackAt_skipFieldX (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    stackAt sp (skipFieldStackX depth) =
      (∃∗ v19 : BitVec 64, ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64,
        ∃∗ v22 : BitVec 64, ∃∗ v_lr : BitVec 64, ∃∗ v_fp : BitVec 64,
        skipBelowX sp depth ∗
          memRegion (sp - 96#64) 48 ∗
          ((sp - 48#64) ↦₆₄ v_fp) ∗ ((sp - 40#64) ↦₆₄ v_lr) ∗
          ((sp - 32#64) ↦₆₄ v22) ∗ ((sp - 24#64) ↦₆₄ v21) ∗
          ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v19)) := by
  simp only [stackAt, skipBelowX]
  have hlen : skipFieldStackX depth = (depth * 0x60 + decodeVarintSliceStackX) + 96 := by
    simp only [skipFieldStackX]; omega
  have hbound : skipFieldStackX depth ≤ 2 ^ 64 := by
    simp only [skipFieldStackX, decodeVarintSliceStackX, decodeErrorHookStackX, extHookStack]
    omega
  have hbit : BitVec.ofNat 64 (skipFieldStackX depth) =
      BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX) + 96#64 := by
    rw [hlen, BitVec.ofNat_add]
  have h1 := memRegion_split'
    (b := sp - BitVec.ofNat 64 (skipFieldStackX depth))
    (b' := sp - 96#64)
    (n := depth * 0x60 + decodeVarintSliceStackX) (k := 96)
    (N := skipFieldStackX depth) hlen
    (by rw [hbit]; exact bv_sub_add_96 sp _)
    hbound
  have hsp_sub :
      sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX) =
        sp - BitVec.ofNat 64 (skipFieldStackX depth) := by
    rw [hbit]; exact bv_sub_96_sub sp _
  have h2 := memRegion_split' (b := sp - 96#64) (b' := sp - 48#64)
    (n := 48) (k := 48) (N := 96) rfl (by bv_lin) (by decide)
  have h3 := memRegion_split' (b := sp - 48#64) (b' := sp - 40#64)
    (n := 8) (k := 40) (N := 48) rfl (by bv_lin) (by decide)
  have h4 := memRegion_split' (b := sp - 40#64) (b' := sp - 32#64)
    (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have h5 := memRegion_split' (b := sp - 32#64) (b' := sp - 24#64)
    (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have h6 := memRegion_split' (b := sp - 24#64) (b' := sp - 16#64)
    (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have h7 := memRegion_split' (b := sp - 16#64) (b' := sp - 8#64)
    (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [hsp_sub, h1, h2, h3, h4, h5, h6, h7,
    memRegion_eight (sp - 48#64), memRegion_eight (sp - 40#64),
    memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
    memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

abbrev skipLeafRestX (sp : BitVec 64) (depth : Nat) : SepProp :=
  memRegion (sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX)) (depth * 0x60)

theorem skipBelowX_leaf (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipBelowX sp depth =
      skipLeafRestX sp depth ∗ stackAt (sp - 96#64) decodeVarintSliceStackX := by
  simp only [skipBelowX, skipLeafRestX, stackAt]
  have hbound : depth * 0x60 + decodeVarintSliceStackX ≤ 2 ^ 64 := by
    simp only [decodeVarintSliceStackX, decodeErrorHookStackX, extHookStack]; omega
  have hbit : BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX) =
      BitVec.ofNat 64 (depth * 0x60) + BitVec.ofNat 64 decodeVarintSliceStackX :=
    BitVec.ofNat_add _ _
  exact memRegion_split'
    (b := sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX))
    (b' := sp - 96#64 - BitVec.ofNat 64 decodeVarintSliceStackX)
    (n := depth * 0x60) (k := decodeVarintSliceStackX)
    (N := depth * 0x60 + decodeVarintSliceStackX) rfl
    (by rw [hbit]; exact bv_sub_96_add_cancel sp _ _)
    hbound

theorem skipBelowX_leaf_entails (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipLeafRestX sp depth ∗ stackAt (sp - 96#64) decodeVarintSliceStackX ⊢
      skipBelowX sp depth :=
  Entails.of_eq (skipBelowX_leaf sp depth hdepth).symm

abbrev skipSlowRestX (sp : BitVec 64) (depth : Nat) : SepProp :=
  memRegion (sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX))
    (depth * 0x60 + 0x10)

theorem skipBelowX_slow (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipBelowX sp depth =
      skipSlowRestX sp depth ∗ stackAt (sp - 96#64) decodeVarintSlowStackX := by
  simp only [skipBelowX, skipSlowRestX, stackAt]
  have hlen : depth * 0x60 + decodeVarintSliceStackX =
      (depth * 0x60 + 0x10) + decodeVarintSlowStackX := by
    simp only [decodeVarintSliceStackX, decodeVarintSlowStackX]; omega
  have hbound : depth * 0x60 + decodeVarintSliceStackX ≤ 2 ^ 64 := by
    simp only [decodeVarintSliceStackX, decodeErrorHookStackX, extHookStack]; omega
  have hbit : BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX) =
      BitVec.ofNat 64 (depth * 0x60 + 0x10) + BitVec.ofNat 64 decodeVarintSlowStackX := by
    rw [hlen, BitVec.ofNat_add]
  exact memRegion_split'
    (b := sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX))
    (b' := sp - 96#64 - BitVec.ofNat 64 decodeVarintSlowStackX)
    (n := depth * 0x60 + 0x10) (k := decodeVarintSlowStackX)
    (N := depth * 0x60 + decodeVarintSliceStackX) hlen
    (by rw [hbit]; exact bv_sub_96_add_cancel sp _ _)
    hbound

theorem skipBelowX_slow_entails (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipSlowRestX sp depth ∗ stackAt (sp - 96#64) decodeVarintSlowStackX ⊢
      skipBelowX sp depth :=
  Entails.of_eq (skipBelowX_slow sp depth hdepth).symm

abbrev skipErrRestX (sp : BitVec 64) (depth : Nat) : SepProp :=
  memRegion (sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX))
    (depth * 0x60 + 0x50)

theorem skipBelowX_err (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipBelowX sp depth =
      skipErrRestX sp depth ∗ stackAt (sp - 96#64) decodeErrorHookStackX := by
  simp only [skipBelowX, skipErrRestX, stackAt]
  have hlen : depth * 0x60 + decodeVarintSliceStackX =
      (depth * 0x60 + 0x50) + decodeErrorHookStackX := by
    simp only [decodeVarintSliceStackX]; omega
  have hbound : depth * 0x60 + decodeVarintSliceStackX ≤ 2 ^ 64 := by
    simp only [decodeVarintSliceStackX, decodeErrorHookStackX, extHookStack]; omega
  have hbit : BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX) =
      BitVec.ofNat 64 (depth * 0x60 + 0x50) + BitVec.ofNat 64 decodeErrorHookStackX := by
    rw [hlen, BitVec.ofNat_add]
  exact memRegion_split'
    (b := sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarintSliceStackX))
    (b' := sp - 96#64 - BitVec.ofNat 64 decodeErrorHookStackX)
    (n := depth * 0x60 + 0x50) (k := decodeErrorHookStackX)
    (N := depth * 0x60 + decodeVarintSliceStackX) hlen
    (by rw [hbit]; exact bv_sub_96_add_cancel sp _ _)
    hbound

theorem skipBelowX_err_entails (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipErrRestX sp depth ∗ stackAt (sp - 96#64) decodeErrorHookStackX ⊢
      skipBelowX sp depth :=
  Entails.of_eq (skipBelowX_err sp depth hdepth).symm

def skipFieldSpecAtX (A : RustAlloc) (depth : Nat) (P : SkipFieldGhost → Prop) :
    Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜P x ∧ x.depth = depth ∧
      (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth ∧ depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipFieldStackX depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipFieldStackX depth) ∗
      match skipField (2 * x.bs.length + 2) depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem subroutine_ok_skipFieldX_or {A : RustAlloc} {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry ((skipFieldSpecAtX A depth P).inImage img))
    (h2 : subroutine_ok prog entry ((skipFieldSpecAtX A depth Q).inImage img)) :
    subroutine_ok prog entry ((skipFieldSpecAtX A depth (fun x => P x ∨ Q x)).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.2.1.1 with hP | hQ
  · refine h1.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [Spec.inImage, skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1, ⟨hP, hpre.2.1.2⟩, hpre.2.2⟩
  · refine h2.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [Spec.inImage, skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1, ⟨hQ, hpre.2.1.2⟩, hpre.2.2⟩

theorem subroutine_ok_skipFieldX_imp {A : RustAlloc} {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry ((skipFieldSpecAtX A depth Q).inImage img)) :
    subroutine_ok prog entry ((skipFieldSpecAtX A depth P).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [Spec.inImage, skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1, ⟨himp x hpre.2.1.1, hpre.2.1.2⟩, hpre.2.2⟩

theorem subroutine_ok_skipFieldX_or_lscl {A : RustAlloc} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A depth P)))
    (h2 : subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A depth Q))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A depth (fun x => P x ∨ Q x))) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.1 with hP | hQ
  · refine h1.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hpre.1.2⟩, hpre.2⟩
  · refine h2.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_skipFieldX_imp_lscl {A : RustAlloc} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A depth Q))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A depth P)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome x R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

abbrev skipGroupLoopPreX (A : RustAlloc) (s0 : State) (d : Nat)
    (bufRef slot ptr : BitVec 64) (bs cur : List (BitVec 8)) : SepProp :=
  (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool ∗
    memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    skipBelowX s0.sp (d + 1)

end CryptoVerification.LibsignalTripleRatchet.Prost
