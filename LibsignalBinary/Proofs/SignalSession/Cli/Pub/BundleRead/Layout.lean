/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import ProofLib.SepLogic.Basic
import Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.BundleRead.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Stack, `sret`, and Tail-Call Layout Helpers -/

theorem stk_lt_two_pow_64 {m : Memory} {ret sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hm : m ⊨ memRegion ret 48 ∗ stackAt sp stk ∗ R) :
    stk < 2 ^ 64 := by
  by_contra hge
  have hin1 : InRegion ret 48 ret := by simp [InRegion]
  have hin2 : InRegion (sp - BitVec.ofNat 64 stk) stk ret := by
    simp only [InRegion]
    have := (ret - (sp - BitVec.ofNat 64 stk)).isLt
    omega
  exact not_satisfies_ownsRW_ownsRW
    (ownsRW_memRegion ret 48 ret hin1)
    (ownsRW_sepConj_left (ownsRW_memRegion (sp - BitVec.ofNat 64 stk) stk ret hin2))
    (by simpa [sepConj_assoc] using hm)

theorem stk_le_two_pow_64 {m : Memory} {ret sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hm : m ⊨ memRegion ret 48 ∗ stackAt sp stk ∗ R) :
    stk ≤ 2 ^ 64 :=
  Nat.le_of_lt (stk_lt_two_pow_64 hm)

theorem strRefAt_read_intro (a ptrRead : BitVec 64) :
    ((a ↦₆₄ ptrRead) ∗ ((a + 8#64) ↦₆₄ 4#64) ∗ (ptrRead ↦ᵣ utf8 "read")) ⊢
      strRefAt a (utf8 "read") := by
  have hlen : BitVec.ofNat 64 (utf8 "read").length = 4#64 := by
    simp only [utf8, List.length_map, String.toUTF8_eq_toByteArray]
    decide +kernel
  dsimp only [strRefAt]
  refine Entails.sepExists_right ptrRead ?_
  rw [hlen]
  exact Entails.refl _

theorem vecU8_22_intro (A : RustAlloc) (a buf : BitVec 64) (hbuf : buf ≠ 0#64) :
    ((a ↦₆₄ 22#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗ ((a + 16#64) ↦₆₄ 22#64) ∗
      A.live buf 22 1 ∗ memRegion buf 22) ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  rw [memRegion_eq_exists_bytes buf 22 (by decide)]
  rw [sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs
  have hcomm :
      ((a ↦₆₄ 22#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗ ((a + 16#64) ↦₆₄ 22#64) ∗
        A.live buf 22 1 ∗ (⌜bs.length = 22⌝ ∗ (buf ↦ₛ bs))) =
      (⌜bs.length = 22⌝ ∗ ((a ↦₆₄ 22#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗
        ((a + 16#64) ↦₆₄ 22#64) ∗ A.live buf 22 1 ∗ (buf ↦ₛ bs))) := by
    ac_rfl
  rw [hcomm]
  apply Entails.pure_left
  intro hlen
  refine Entails.sepExists_right bs ?_
  dsimp only [vecU8, vecU8At, vecHeader]
  refine Entails.sepExists_right 22#64 ?_
  refine Entails.sepExists_right buf ?_
  have h22 : BitVec.ofNat 64 bs.length = 22#64 := by rw [hlen]
  have h22nat : (22#64 : BitVec 64).toNat = 22 := rfl
  have hne22 : (22#64 : BitVec 64) ≠ 0 := by decide
  have hsub : 22 - bs.length = 0 := by omega
  simp only [h22, hne22, ↓reduceIte, h22nat, hsub, memRegion_zero, sepConj_emp]
  have hpure : bs.length ≤ 22 ∧ 22 < 2 ^ 63 ∧ buf ≠ 0 := by
    refine ⟨by omega, by decide, hbuf⟩
  have hgoal :
      ((a ↦₆₄ 22#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗ ((a + 16#64) ↦₆₄ 22#64)) ∗
        (A.live buf 22 1 ∗ (buf ↦ₛ bs)) ⊢
      ((a ↦₆₄ 22#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗ ((a + 16#64) ↦₆₄ 22#64)) ∗
        ⌜bs.length ≤ 22 ∧ 22 < 2 ^ 63 ∧ buf ≠ 0⌝ ∗
        (A.live buf 22 1 ∗ (buf ↦ₛ bs)) :=
    sepConj_mono_right (Entails.pure_right hpure (Entails.refl _))
  simpa [sepConj_assoc] using hgoal

theorem err_result_intro (A : RustAlloc) (ret buf ptrRead : BitVec 64) (hbuf : buf ≠ 0#64) :
    ((ret ↦₆₄ speWord 1) ∗
      (((ret + 8#64) ↦₆₄ 22#64) ∗ ((ret + 16#64) ↦₆₄ buf) ∗ ((ret + 24#64) ↦₆₄ 22#64) ∗
        A.live buf 22 1 ∗ memRegion buf 22) ∗
      (((ret + 32#64) ↦₆₄ ptrRead) ∗ ((ret + 40#64) ↦₆₄ 4#64) ∗ (ptrRead ↦ᵣ utf8 "read"))) ⊢
      getResultAt A ret (.error ()) := by
  dsimp only [getResultAt, speAt]
  have h1 := vecU8_22_intro A (ret + 8#64) buf hbuf
  have h2 := strRefAt_read_intro (ret + 32#64) ptrRead
  have h1' :
      (((ret + 8#64) ↦₆₄ 22#64) ∗ ((ret + 16#64) ↦₆₄ buf) ∗ ((ret + 24#64) ↦₆₄ 22#64) ∗
        A.live buf 22 1 ∗ memRegion buf 22) ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A (ret + 8#64) bs := by
    simpa [BitVec.add_assoc] using h1
  have h2' :
      (((ret + 32#64) ↦₆₄ ptrRead) ∗ ((ret + 40#64) ↦₆₄ 4#64) ∗ (ptrRead ↦ᵣ utf8 "read")) ⊢
      strRefAt (ret + 32#64) (utf8 "read") := by
    simpa [BitVec.add_assoc] using h2
  exact sepConj_mono_right (sepConj_mono h1' h2')

theorem ok_result_intro (A : RustAlloc) (ret cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((ret ↦₆₄ okTagVec) ∗
      (((ret + 8#64) ↦₆₄ cap) ∗ ((ret + 16#64) ↦₆₄ ptr) ∗
        ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗
      memRegion (ret + 32#64) 16) ⊢
      getResultAt A ret (.ok bs) := by
  dsimp only [getResultAt, vecResultAt, vecU8, vecU8At, vecHeader]
  refine sepConj_mono_right (sepConj_mono_left ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  simpa [BitVec.add_assoc, sepConj_assoc] using (Entails.refl _)

theorem path_buf_dealloc_pack (ptr : BitVec 64) (capNat : Nat) (p : List (BitVec 8))
    (hle : p.length ≤ capNat) (hcap : capNat < 2 ^ 63) :
    ((ptr ↦ₛ p) ∗ memRegion (ptr + BitVec.ofNat 64 p.length) (capNat - p.length)) ⊢
      memRegion ptr capNat := by
  have heq : p.length + (capNat - p.length) = capNat := by omega
  conv_rhs => rw [← heq, memRegion_split ptr p.length (capNat - p.length) (by omega)]
  exact sepConj_mono_left (IsBlock.pointsToBytes ptr p).entails_memRegion

private theorem bv_sub_ofNat_add (sp : BitVec 64) (a b : Nat) :
    sp - BitVec.ofNat 64 (a + b) = (sp - BitVec.ofNat 64 b) - BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem stackAt_frame_80_eq (sp : BitVec 64) (stk : Nat) (hge : 80 ≤ stk) (hle : stk ≤ 2 ^ 64) :
    stackAt sp stk = stackAt (sp - 80#64) (stk - 80) ∗ memRegion (sp - 80#64) 80 := by
  have hsum : (stk - 80) + 80 = stk := by omega
  dsimp only [stackAt]
  conv_lhs => rw [← hsum]
  rw [bv_sub_ofNat_add sp (stk - 80) 80]
  have h80 : BitVec.ofNat 64 80 = 80#64 := rfl
  rw [h80, memRegion_split ((sp - 80#64) - BitVec.ofNat 64 (stk - 80)) (stk - 80) 80 (by omega),
    BitVec.sub_add_cancel]

theorem stackAt_split_sub (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big) (h2 : big ≤ 2 ^ 64) :
    stackAt sp big = memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have hsum : (big - small) + small = big := by omega
  dsimp only [stackAt]
  conv_lhs => arg 2; rw [← hsum]
  rw [memRegion_split (sp - BitVec.ofNat 64 big) (big - small) small (by omega)]
  have haddr : (sp - BitVec.ofNat 64 big) + BitVec.ofNat 64 (big - small) =
      sp - BitVec.ofNat 64 small := by
    conv_lhs => arg 1; rw [← hsum]
    rw [bv_sub_ofNat_add sp (big - small) small, BitVec.sub_add_cancel]
  rw [haddr]

theorem memRegion_8_eq_exists_u64 (a : BitVec 64) :
    memRegion a 8 = ∃∗ v : BitVec 64, (a ↦₆₄ v) :=
  IsBlock.eq (IsBlock.memRegion a 8) (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun m => ⟨fun _ => ⟨m.read64 a, rfl⟩, fun _ => trivial⟩

theorem slot24_pack (a w0 w1 w2 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ⊢ memRegion a 24 := by
  have h24 : memRegion a 24 =
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 := by
    rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split a 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (a + 8#64) 8 8 (by decide),
      BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 from rfl]
  rw [h24]
  exact sepConj_mono (IsBlock.pointsTo64 a w0).entails_memRegion
    (sepConj_mono (IsBlock.pointsTo64 (a + 8#64) w1).entails_memRegion
      (IsBlock.pointsTo64 (a + 16#64) w2).entails_memRegion)

theorem err_slot24_pack (a : BitVec 64) :
    ((a ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (a + 8#64) 16) ⊢ memRegion a 24 := by
  rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split a 8 16 (by decide)]
  exact sepConj_mono_left (IsBlock.pointsTo64 a 0xFFFFFFFFFFFFFFFF#64).entails_memRegion

theorem frame_80_unpack (sp' : BitVec 64) :
    memRegion sp' 80 ⊢ ∃∗ v19 : BitVec 64, ∃∗ v20 : BitVec 64,
      ∃∗ v30 : BitVec 64, ∃∗ v29 : BitVec 64,
        memRegion sp' 24 ∗ memRegion (sp' + 24#64) 24 ∗
          ((sp' + 48#64) ↦₆₄ v29) ∗ ((sp' + 56#64) ↦₆₄ v30) ∗
          ((sp' + 64#64) ↦₆₄ v20) ∗ ((sp' + 72#64) ↦₆₄ v19) := by
  have hsplit : memRegion sp' 80 =
      memRegion sp' 24 ∗ memRegion (sp' + 24#64) 24 ∗
        memRegion (sp' + 48#64) 8 ∗ memRegion (sp' + 56#64) 8 ∗
          memRegion (sp' + 64#64) 8 ∗ memRegion (sp' + 72#64) 8 := by
    rw [show (80 : Nat) = 24 + 56 from rfl, memRegion_split sp' 24 56 (by decide),
      show (56 : Nat) = 24 + 32 from rfl, memRegion_split (sp' + 24#64) 24 32 (by decide),
      BitVec.add_assoc, show (24#64 : BitVec 64) + 24#64 = 48#64 from rfl,
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split (sp' + 48#64) 8 24 (by decide),
      BitVec.add_assoc, show (48#64 : BitVec 64) + 8#64 = 56#64 from rfl,
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split (sp' + 56#64) 8 16 (by decide),
      BitVec.add_assoc, show (56#64 : BitVec 64) + 8#64 = 64#64 from rfl,
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp' + 64#64) 8 8 (by decide),
      BitVec.add_assoc, show (64#64 : BitVec 64) + 8#64 = 72#64 from rfl]
  rw [hsplit, memRegion_8_eq_exists_u64 (sp' + 48#64),
    memRegion_8_eq_exists_u64 (sp' + 56#64),
    memRegion_8_eq_exists_u64 (sp' + 64#64),
    memRegion_8_eq_exists_u64 (sp' + 72#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem frame_80_pack (sp' cap ptr len v29 v30 v20 v19 : BitVec 64) :
    (memRegion sp' 24 ∗
      ((sp' + 24#64) ↦₆₄ cap) ∗ ((sp' + 32#64) ↦₆₄ ptr) ∗ ((sp' + 40#64) ↦₆₄ len) ∗
      ((sp' + 48#64) ↦₆₄ v29) ∗ ((sp' + 56#64) ↦₆₄ v30) ∗
      ((sp' + 64#64) ↦₆₄ v20) ∗ ((sp' + 72#64) ↦₆₄ v19)) ⊢
      memRegion sp' 80 := by
  have hsplit : memRegion sp' 80 =
      memRegion sp' 24 ∗ memRegion (sp' + 24#64) 24 ∗
        memRegion (sp' + 48#64) 8 ∗ memRegion (sp' + 56#64) 8 ∗
          memRegion (sp' + 64#64) 8 ∗ memRegion (sp' + 72#64) 8 := by
    rw [show (80 : Nat) = 24 + 56 from rfl, memRegion_split sp' 24 56 (by decide),
      show (56 : Nat) = 24 + 32 from rfl, memRegion_split (sp' + 24#64) 24 32 (by decide),
      BitVec.add_assoc, show (24#64 : BitVec 64) + 24#64 = 48#64 from rfl,
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split (sp' + 48#64) 8 24 (by decide),
      BitVec.add_assoc, show (48#64 : BitVec 64) + 8#64 = 56#64 from rfl,
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split (sp' + 56#64) 8 16 (by decide),
      BitVec.add_assoc, show (56#64 : BitVec 64) + 8#64 = 64#64 from rfl,
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp' + 64#64) 8 8 (by decide),
      BitVec.add_assoc, show (64#64 : BitVec 64) + 8#64 = 72#64 from rfl]
  rw [hsplit]
  have hmid : (((sp' + 24#64) ↦₆₄ cap) ∗ ((sp' + 32#64) ↦₆₄ ptr) ∗ ((sp' + 40#64) ↦₆₄ len)) ⊢
      memRegion (sp' + 24#64) 24 := by
    simpa [BitVec.add_assoc] using slot24_pack (sp' + 24#64) cap ptr len
  have hlhs :
      (memRegion sp' 24 ∗
        ((sp' + 24#64) ↦₆₄ cap) ∗ ((sp' + 32#64) ↦₆₄ ptr) ∗ ((sp' + 40#64) ↦₆₄ len) ∗
        ((sp' + 48#64) ↦₆₄ v29) ∗ ((sp' + 56#64) ↦₆₄ v30) ∗
        ((sp' + 64#64) ↦₆₄ v20) ∗ ((sp' + 72#64) ↦₆₄ v19)) =
      memRegion sp' 24 ∗ (((sp' + 24#64) ↦₆₄ cap) ∗ ((sp' + 32#64) ↦₆₄ ptr) ∗
        ((sp' + 40#64) ↦₆₄ len)) ∗
        ((sp' + 48#64) ↦₆₄ v29) ∗ ((sp' + 56#64) ↦₆₄ v30) ∗
          ((sp' + 64#64) ↦₆₄ v20) ∗ ((sp' + 72#64) ↦₆₄ v19) := by
    ac_rfl
  rw [hlhs]
  exact sepConj_mono_right (sepConj_mono hmid
    (sepConj_mono (IsBlock.pointsTo64 _ _).entails_memRegion
      (sepConj_mono (IsBlock.pointsTo64 _ _).entails_memRegion
        (sepConj_mono (IsBlock.pointsTo64 _ _).entails_memRegion
          (IsBlock.pointsTo64 _ _).entails_memRegion))))

theorem sret_32_unpack (ret : BitVec 64) :
    memRegion ret 48 ⊢ ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
          ((ret + 24#64) ↦₆₄ w3) ∗ memRegion (ret + 32#64) 16 := by
  have hsplit : memRegion ret 48 =
      memRegion ret 8 ∗ memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 8 ∗
        memRegion (ret + 24#64) 8 ∗ memRegion (ret + 32#64) 16 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split ret 8 40 (by decide),
      show (40 : Nat) = 8 + 32 from rfl, memRegion_split (ret + 8#64) 8 32 (by decide),
      BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 from rfl,
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split (ret + 16#64) 8 24 (by decide),
      BitVec.add_assoc, show (16#64 : BitVec 64) + 8#64 = 24#64 from rfl,
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split (ret + 24#64) 8 16 (by decide),
      BitVec.add_assoc, show (24#64 : BitVec 64) + 8#64 = 32#64 from rfl]
  rw [hsplit, memRegion_8_eq_exists_u64 ret,
    memRegion_8_eq_exists_u64 (ret + 8#64),
    memRegion_8_eq_exists_u64 (ret + 16#64),
    memRegion_8_eq_exists_u64 (ret + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem sret_48_unpack (ret : BitVec 64) :
    memRegion ret 48 ⊢ ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
          ((ret + 24#64) ↦₆₄ w3) ∗ ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) := by
  have hsplit : memRegion ret 48 =
      memRegion ret 8 ∗ memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 8 ∗
        memRegion (ret + 24#64) 8 ∗ memRegion (ret + 32#64) 8 ∗ memRegion (ret + 40#64) 8 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split ret 8 40 (by decide),
      show (40 : Nat) = 8 + 32 from rfl, memRegion_split (ret + 8#64) 8 32 (by decide),
      BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 from rfl,
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split (ret + 16#64) 8 24 (by decide),
      BitVec.add_assoc, show (16#64 : BitVec 64) + 8#64 = 24#64 from rfl,
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split (ret + 24#64) 8 16 (by decide),
      BitVec.add_assoc, show (24#64 : BitVec 64) + 8#64 = 32#64 from rfl,
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (ret + 32#64) 8 8 (by decide),
      BitVec.add_assoc, show (32#64 : BitVec 64) + 8#64 = 40#64 from rfl]
  rw [hsplit, memRegion_8_eq_exists_u64 ret,
    memRegion_8_eq_exists_u64 (ret + 8#64),
    memRegion_8_eq_exists_u64 (ret + 16#64),
    memRegion_8_eq_exists_u64 (ret + 24#64),
    memRegion_8_eq_exists_u64 (ret + 32#64),
    memRegion_8_eq_exists_u64 (ret + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

end CryptoVerification.SignalSession.Cli.BundleRead.Helpers
