/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.GrowOne
import ProofLib.SepLogic.WPp

/-!
# Verification of In-Image `<DecodeError>::push`

Verifies `<prost::error::DecodeError>::push`, dispatching to `grow_one` when
`len = cap` and appending a `(description, field)` entry.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack and `Vec` buffer lemmas for `<prost::error::DecodeError>::push` -/

def pushStackPad (sp : BitVec 64) : SepProp :=
  memRegion (sp - 8192#64) 3920

theorem stackAt_push (sp : BitVec 64) :
    stackAt sp decodeErrorHookStack =
      pushStackPad sp ∗
      stackAt (sp - 176#64) allocHookStack ∗
      cells (sp - 176#64) 4 ∗
      cells (sp - 144#64) 8 ∗
      cells (sp - 80#64) 2 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := stackAt_split_bottom sp 4272 3920 (by decide)
  change stackAt sp decodeErrorHookStack = pushStackPad sp ∗ stackAt sp 4272 at h1
  have h2 := stackAt_split_cells sp 4208 8 (by decide)
  change stackAt sp 4272 = stackAt (sp - 64#64) 4208 ∗ cells (sp - 64#64) 8 at h2
  have h3 := stackAt_split_cells (sp - 64#64) 4192 2 (by decide)
  have h3' : sp - 64#64 - BitVec.ofNat 64 (2 * 8) = sp - 80#64 := by bv_omega
  rw [h3'] at h3
  change stackAt (sp - 64#64) 4208 = stackAt (sp - 80#64) 4192 ∗ cells (sp - 80#64) 2 at h3
  have h4 := stackAt_split_cells (sp - 80#64) 4128 8 (by decide)
  have h4' : sp - 80#64 - BitVec.ofNat 64 (8 * 8) = sp - 144#64 := by bv_omega
  rw [h4'] at h4
  change stackAt (sp - 80#64) 4192 = stackAt (sp - 144#64) 4128 ∗ cells (sp - 144#64) 8 at h4
  have h5 := stackAt_split_cells (sp - 144#64) 4096 4 (by decide)
  have h5' : sp - 144#64 - BitVec.ofNat 64 (4 * 8) = sp - 176#64 := by bv_omega
  rw [h5'] at h5
  change stackAt (sp - 144#64) 4128 =
    stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 at h5
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, h3, h4, h5, hc8]
  ac_rfl

theorem arrayAt_stackEntryAt_replicate :
    ∀ (n : Nat) (ptr : BitVec 64), n * 32 ≤ 2 ^ 64 →
      arrayAt stackEntryAt 32 ptr (List.replicate n ()) = memRegion ptr (n * 32)
  | 0, ptr, _ => by
      simp only [List.replicate_zero, arrayAt, Nat.zero_mul]
      exact (memRegion_zero ptr).symm
  | n + 1, ptr, h => by
      have hn : n * 32 ≤ 2 ^ 64 := by omega
      have h1 : (n + 1) * 32 = 32 + n * 32 := by omega
      rw [List.replicate_succ, arrayAt, stackEntryAt, arrayAt_stackEntryAt_replicate n _ hn,
        h1, memRegion_split ptr 32 (n * 32) (by omega)]

theorem vecBuf_stackEntryAt_memRegion (A : RustAlloc) (k : Nat) (cap ptr : BitVec 64)
    (hle : k ≤ cap.toNat) (hbound : cap.toNat * 32 < 2 ^ 63) :
    A.live ptr (cap.toNat * 32) 8 ∗
      arrayAt stackEntryAt 32 ptr (List.replicate k ()) ∗
      memRegion (ptr + BitVec.ofNat 64 (k * 32)) ((cap.toNat - k) * 32) =
    A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32) := by
  congr 1
  have hk : k * 32 ≤ 2 ^ 64 := by omega
  have hsplit : cap.toNat * 32 = k * 32 + (cap.toNat - k) * 32 := by
    have hsub : k + (cap.toNat - k) = cap.toNat := Nat.add_sub_of_le hle
    calc cap.toNat * 32 = (k + (cap.toNat - k)) * 32 := by rw [hsub]
      _ = k * 32 + (cap.toNat - k) * 32 := Nat.add_mul k (cap.toNat - k) 32
  rw [arrayAt_stackEntryAt_replicate k ptr hk, hsplit,
    ← memRegion_split ptr (k * 32) ((cap.toNat - k) * 32) (by omega)]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v3) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗ ((a + 24#64) ↦₆₄ v0)) := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) by rfl,
    memRegion_split a 8 (8 + (8 + 8)) (by decide),
    memRegion_split (a + 8#64) 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem ofNat_lsl5_eq {n : Nat} (hn : n * 32 < 2 ^ 64) :
    (BitVec.ofNat 64 n <<< 5) = BitVec.ofNat 64 (n * 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem ofNat_add_one_eq (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]

theorem memRegion_split_entry (ptr : BitVec 64) (n capNat : Nat)
    (hlt : n < capNat) (hbound : capNat * 32 < 2 ^ 63) :
    memRegion ptr (capNat * 32) =
      memRegion ptr (n * 32) ∗
      memRegion (ptr + (BitVec.ofNat 64 n <<< 5) + 32#64) ((capNat - (n + 1)) * 32) ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((ptr + (BitVec.ofNat 64 n <<< 5)) ↦₆₄ v3) ∗
        ((ptr + (BitVec.ofNat 64 n <<< 5) + 8#64) ↦₆₄ v2) ∗
        ((ptr + (BitVec.ofNat 64 n <<< 5) + 16#64) ↦₆₄ v1) ∗
        ((ptr + (BitVec.ofNat 64 n <<< 5) + 24#64) ↦₆₄ v0)) := by
  have hlsl : (BitVec.ofNat 64 n <<< 5) = BitVec.ofNat 64 (n * 32) := ofNat_lsl5_eq (by omega)
  have hsplit1 : capNat * 32 = n * 32 + (32 + (capNat - (n + 1)) * 32) := by
    have hsub : (n + 1) + (capNat - (n + 1)) = capNat := Nat.add_sub_of_le hlt
    calc capNat * 32 = ((n + 1) + (capNat - (n + 1))) * 32 := by rw [hsub]
      _ = (n + 1) * 32 + (capNat - (n + 1)) * 32 := Nat.add_mul (n + 1) (capNat - (n + 1)) 32
      _ = n * 32 + (32 + (capNat - (n + 1)) * 32) := by omega
  rw [hsplit1,
    memRegion_split ptr (n * 32) (32 + (capNat - (n + 1)) * 32) (by omega),
    memRegion_split (ptr + BitVec.ofNat 64 (n * 32)) 32 ((capNat - (n + 1)) * 32) (by omega),
    ← hlsl, memRegion_32_cells (ptr + (BitVec.ofNat 64 n <<< 5))]
  ac_rfl

theorem bv_sub_64_sub (sp : BitVec 64) :
    sp - 64#64 - 16#64 = sp - 80#64 ∧
    sp - 64#64 - 80#64 = sp - 144#64 ∧
    sp - 64#64 - 112#64 = sp - 176#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega⟩

/-! ## Verification of `<prost::error::DecodeError>::push` -/

theorem decodeErrorPush_ok'_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A) := by
  unfold decodeErrorPushSpec decodeErrorAtStackLen vecOf vecAt vecHeader vecBuf
  simp only [List.length_replicate, sepExists_sepConj_left, sepExists_sepConj_right]
  simp only [stackAt_push]
  have hfn := (ls_lemma% fnOff "<prost::error::DecodeError>::push")
  have hgrow := grow_one_str_pair_ok_trap (b := b) (C := C) hA
  rw [Program.fnAddr_rel (name := "<prost::error::DecodeError>::push")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one") (k := 128) (by decide)] at hgrow
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "<prost::error::DecodeError>::push")) 128
  dsimp only [trTrapProgAt, decodeErrorPushName, growOneStrPairName] at hgrow ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
    "<prost::error::DecodeError>::push" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, e, n⟩ := x
  dsimp only at *
  rcases h with ⟨hkind1, hkind2⟩
  have hn_toNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hptr_ne0 : v_stk_2 ≠ 0#64 := h_3
  conv =>
    arg 4
    simp only [BitVec.ofNat_eq_ofNat,
      vecBuf_stackEntryAt_memRegion A n v_stk_1 v_stk_2 (by omega) (by omega)]
  by_cases heq : BitVec.ofNat 64 n = v_stk_1
  · -- Slow path (`BitVec.ofNat 64 n = v_stk_1`): branch taken to `0x4aafc` (`entry + 84#64`), calls `grow_one`
    subst v_stk_1
    have hcap_lt : (BitVec.ofNat 64 n).toNat < 2 ^ 32 := by rw [hn_toNat]; exact h_1
    have hnew_toNat : (newCap (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [newCap_toNat hcap_lt, hn_toNat]
    have hn_lt_new : n < (newCap (BitVec.ofNat 64 n)).toNat := by omega
    have hn1_le_new : n + 1 ≤ (newCap (BitVec.ofNat 64 n)).toNat := by omega
    have hnew_bound : (newCap (BitVec.ofNat 64 n)).toNat * 32 < 2 ^ 63 := by omega
    have hnew_ne0 : newCap (BitVec.ofNat 64 n) ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      change (newCap (BitVec.ofNat 64 n)).toNat = 0 at ht
      omega
    apply SepWPp.of_sepWP (mid := entry + bv% (128))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.call_frame (ret_pc := entry + bv% (108)) (x := (e, BitVec.ofNat 64 n, v_stk_2, s0.sp - 64#64))
      hgrow (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) rfl
      ⟨by wp_norm_goal, by wp_norm_goal, hcap_lt, hptr_ne0⟩
      (by
        simp only [bv_sub_64_sub]
        sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => allowPanic_frame id hm)
      (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    rcases hcs_sf with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
    simp only [wp_norm, arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hsp_sf
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc, bv_sub_64_sub]
    apply SepWPp.exists_elim; intro p'
    refine SepWPp.pure_elim fun ⟨hp', htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [memRegion_split_entry p' n (newCap (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps
    apply SepWP.instantiate_post_exists v_stk
    apply SepWP.instantiate_post_exists (newCap (BitVec.ofNat 64 n))
    apply SepWP.instantiate_post_exists p'
    simp only [BitVec.ofNat_eq_ofNat, hnew_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion A (n + 1) (newCap (BitVec.ofNat 64 n)) p' hn1_le_new hnew_bound,
      memRegion_split_entry p' n (newCap (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound]
    wp_done
  · -- Fast path (`BitVec.ofNat 64 n ≠ v_stk_1`): branch not taken, falls through to `0x4aad0`
    have hbeq : (BitVec.ofNat 64 n == v_stk_1) = false := beq_eq_false_iff_ne.mpr heq
    have hne_nat : n ≠ v_stk_1.toNat := by
      intro hnat
      apply heq
      apply BitVec.eq_of_toNat_eq
      rw [hn_toNat, hnat]
    have hn_lt_cap : n < v_stk_1.toNat := by omega
    have hn1_le_cap : n + 1 ≤ v_stk_1.toNat := by omega
    have hcap_ne0 : v_stk_1 ≠ 0#64 := by
      intro h0
      subst h0
      change n < 0 at hn_lt_cap
      omega
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [hcap_ne0, ite_false,
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps
    apply SepWP.instantiate_post_exists v_stk
    apply SepWP.instantiate_post_exists v_stk_1
    apply SepWP.instantiate_post_exists v_stk_2
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion A (n + 1) v_stk_1 v_stk_2 hn1_le_cap (by omega),
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

theorem decodeErrorPush_ok' (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeErrorPushName]
  exact subroutine_ok_kit_of_trTrap (decodeErrorPush_ok'_trap b C A abs hA)

end CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
