/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`) — Part D

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant9d.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. Callee Contract for `Ct1Sent::from_pb` -/

private theorem v9_stackAt_authFromPb (sp : BitVec 64) :
    stackAt sp authFromPbStack =
      stackAt (sp - 64#64) allocHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗
        ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4096 8 (by decide)
  change stackAt sp authFromPbStack = stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗ ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private theorem v9_memRegion_24 (a : BitVec 64) :
    memRegion a 24 = (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem v9_memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      (a ↦₆₄ w5) ∗ ((a + 8#64) ↦₆₄ w4) ∗ ((a + 16#64) ↦₆₄ w3) ∗
      ((a + 24#64) ↦₆₄ w2) ∗ ((a + 32#64) ↦₆₄ w1) ∗ ((a + 40#64) ↦₆₄ w0)) := by
  rw [ProofLib.memRegion_split a 24 24 (by decide), v9_memRegion_24, v9_memRegion_24]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

private theorem v9_cap_ne_zero_of_pos {cap : BitVec 64} {n : Nat} (hpos : 0 < n) (hle : n ≤ cap.toNat) :
    cap ≠ 0#64 := by
  intro h; subst h; change n ≤ 0 at hle; omega

private theorem v9_vecU8_of_zero (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A v [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

private theorem v9_vecU8_of_pos (A : RustAlloc) (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8 A v bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h; have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; change bs.length = 0 at ht; omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 bs.length))
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte, Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ A.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

private theorem v9_out_add24_add8 (out : BitVec 64) : (out + 24#64) + 8#64 = out + 32#64 := by bv_omega
private theorem v9_out_add24_add16 (out : BitVec 64) : (out + 24#64) + 16#64 = out + 40#64 := by bv_omega

set_option maxHeartbeats 1600000 in
theorem v9_auth_from_pb_pinned_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext)) (blkPl_330).base
      (authFromPbPinnedSpec A) := by
  have hshim : subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec :=
    spqr_hook_ok_of_mem hA.shim
  simp only [sessionShimSpec] at hshim
  have halloc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A) :=
    spqr_hook_ok_of_mem hA.alloc
  simp only [rustAllocSpec] at halloc
  have hmc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpySpec :=
    spqr_hook_ok_of_mem hA.memcpy
  simp only [sessionMemcpySpec] at hmc
  have hpanic : ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext)).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked :=
    Eq.trans spqr_externAt?_of_mem hA.panic_ok
  clear hA
  simp only [authFromPbPinnedSpec, authenticatorPBPinnedAt, authenticatorAt, Authenticator.fromPb,
    vecU8At, vecHeader, v9_memRegion_48_cells, v9_stackAt_authFromPb,
    v9_out_add24_add8, v9_out_add24_add16, BitVec.ofNat_eq_ofNat,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  obtain ⟨out, pbA, ⟨⟨cap0, ptr0⟩, ⟨cap1, ptr1⟩⟩, ⟨rootKey, macKey⟩⟩ := x
  dsimp only at *
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hr_le : rootKey.length ≤ cap0.toNat := ‹_›
  have hr_cap : cap0.toNat < 2 ^ 63 := ‹_›
  have hm_le : macKey.length ≤ cap1.toNat := ‹_›
  have hm_cap : cap1.toNat < 2 ^ 63 := ‹_›
  have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
  have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
  have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
  have hm_lt64 : macKey.length < 2 ^ 64 := by omega
  have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
  have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hr_cases with rfl | hr_pos <;> rcases hm_cases with rfl | hm_pos
  · simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at *
    apply SepWPp.of_sepWP_ret; wp_steps
    apply SepWP.fold (v9_vecU8_of_zero A out) (by sep_focus)
    have h2 : ((out + 24#64) ↦₆₄ 0#64) ∗ ((out + 32#64) ↦₆₄ 1#64) ∗ ((out + 40#64) ↦₆₄ 0#64) ⊢
        vecU8 A (out + 24#64) [] := by
      simpa only [v9_out_add24_add8, v9_out_add24_add16] using v9_vecU8_of_zero A (out + 24#64)
    apply SepWP.fold h2 (by sep_focus); wp_done
  · have hcap1_ne : cap1 ≠ 0#64 := v9_cap_ne_zero_of_pos hm_pos hm_le
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hlay1 : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hcap1_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := (blkPl_330).base + 104#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (macKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, ite_true]; rw [pull_alloc_pure]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, ite_false, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret; wp_steps; wp_apply; wp_steps
      apply SepWP.fold (v9_vecU8_of_zero A out) (by sep_focus)
      have h2 : ((out + 24#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗ ((out + 32#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((out + 40#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗ A.live (sf_1.readReg64 Reg.x0) macKey.length 1 ∗
          (sf_1.readReg64 Reg.x0 ↦ₛ macKey) ⊢ vecU8 A (out + 24#64) macKey := by
        simpa only [v9_out_add24_add8, v9_out_add24_add16] using
          v9_vecU8_of_pos A (out + 24#64) (sf_1.readReg64 Reg.x0) macKey hm_pos hm_lt63 hoom1
      apply SepWP.fold h2 (by sep_focus); wp_done
  · have hcap0_ne : cap0 ≠ 0#64 := v9_cap_ne_zero_of_pos hr_pos hr_le
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hlay0 : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hcap0_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := (blkPl_330).base + 56#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, ite_true]; rw [pull_alloc_pure]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, ite_false, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret; wp_steps; wp_apply; wp_steps
      apply SepWP.fold (v9_vecU8_of_pos A out (sf_1.readReg64 Reg.x0) rootKey hr_pos hr_lt63 hoom0) (by sep_focus)
      have h2 : ((out + 24#64) ↦₆₄ 0#64) ∗ ((out + 32#64) ↦₆₄ 1#64) ∗ ((out + 40#64) ↦₆₄ 0#64) ⊢
          vecU8 A (out + 24#64) [] := by
        simpa only [v9_out_add24_add8, v9_out_add24_add16] using v9_vecU8_of_zero A (out + 24#64)
      apply SepWP.fold h2 (by sep_focus); wp_done
  · have hcap0_ne : cap0 ≠ 0#64 := v9_cap_ne_zero_of_pos hr_pos hr_le
    have hcap1_ne : cap1 ≠ 0#64 := v9_cap_ne_zero_of_pos hm_pos hm_le
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hlay0 : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    have hlay1 : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    simp only [hcap0_ne, hcap1_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := (blkPl_330).base + 56#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ite_true]; rw [pull_alloc_pure]; refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP (mid := (blkPl_330).base + 104#64)
      wp_steps; wp_apply; wp_steps; wp_apply; wp_steps; wp_call halloc (macKey.length, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom1 : sf_4.readReg64 Reg.x0 = 0#64
      · simp only [hoom1, BitVec.ofNat_eq_ofNat, ite_true]; rw [pull_alloc_pure]; refine SepWPp.pure_elim fun htrace => ?_
        apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"); wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      · simp only [hoom1, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
        have hoom1_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
        rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr4⟩ => ?_
        have htr_sf4 : sf_4.trace = s0.trace := by rw [htr4]; simp only [wp_norm, arm64_norm, *]
        apply SepWPp.of_sepWP_ret; wp_steps; wp_apply; wp_steps
        apply SepWP.fold (v9_vecU8_of_pos A out (sf_1.readReg64 Reg.x0) rootKey hr_pos hr_lt63 hoom0) (by sep_focus)
        have h2 : ((out + 24#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗ ((out + 32#64) ↦₆₄ sf_4.readReg64 Reg.x0) ∗
            ((out + 40#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗ A.live (sf_4.readReg64 Reg.x0) macKey.length 1 ∗
            (sf_4.readReg64 Reg.x0 ↦ₛ macKey) ⊢ vecU8 A (out + 24#64) macKey := by
          simpa only [v9_out_add24_add8, v9_out_add24_add16] using
            v9_vecU8_of_pos A (out + 24#64) (sf_4.readReg64 Reg.x0) macKey hm_pos hm_lt63 hoom1
        apply SepWP.fold h2 (by sep_focus); wp_done

theorem v9_auth_from_pb_pinned_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hA : FromPbAllocHooks A ext) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) := by
  have hcl330 : subroutine_ok (lsProg_330 (Rust.withPanics ext)) (lsmpl.base 330)
      (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) := by
    rw [← ls_blockPlacement_base (i := 330)]
    exact subroutine_ok_withLsCodeLoaded_of_plain (v9_auth_from_pb_pinned_placed_ok hA)
  exact ls_subroutine_ok_of_block hcl330 hidx

/-! ## 2. Stepping Lemmas for `+2864 -> lsmpl.base 376` and `+3044 -> +8588 | +8180` -/

section StepLemmas

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  v9_x25_add_209 v9_x25_add_209_sext v9_pbA_add_145 v9_x21_add_57 v9_x21_add_57_sext
  v9_x24_add_9 v9_x24_add_9_sext v9_x21_add_15 v9_x21_add_15_sext v9_x21_add_39
  v9_x21_add_39_sext v9_fsp_add_247_sext
  v9_bv_add_add_lit

/-- At `+2864`, when `ct1SentFromPb` returned `Ok(uc)` (`rkCap.toNat < 2 ^ 63`) and
    `receivingEk = some d` (`decW0.toNat < 2 ^ 63`), spills `uc` fields to `fsp + 40..255`,
    copies `pbToProtoPolyDecoder d` to `fsp + 896..936`, and sets up `DecoderFromPbPlacedOkExt`
    at `lsmpl.base 376` (`+3040` `bl`). -/
theorem v9_step_2864_ok_some_to_3040_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (decW0 decW8 decW16 : BitVec 64) (decD24 decD28 : BitVec 32) (decW32 : BitVec 64) (d : PolynomialDecoder)
    (w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 : BitVec 64) (d96 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hrk_lt : rkCap.toNat < 2 ^ 63) (hdec_lt : decW0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = decW8) (hx21 : s.readReg64 .x21 = decW0) (hx23 : s.readReg64 .x23 = decW32)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s
      (((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗
        ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗ ((fsp + 144#64) ↦₆₄ w144) ∗
        ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
        ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗
        memRegion (fsp + 896#64) 40 ∗
        v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) decW0 decW8 decW16 decD24 decD28 decW32 ∗
        v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) decW0 decW8 decW16 decD24 decD28 decW32 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ protoPolynomialDecoderAt A (fsp + 896#64) (pbToProtoPolyDecoder d) ∗ memRegion (fsp + 1888#64) 128 ∗
          ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
          ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) decW0 decW8 decW16 decD24 decD28 decW32 ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧ s1.readReg64 .x1 = fsp + 896#64 ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = fsp + 848#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = esLen ∧
        s1.readReg64 .x26 = rkLen ∧ s1.readReg64 .x28 = rkPtr ∧
        s1.readReg64 .x30 = lsmpl.base 333 + 3044#64 ∧
        TraceCalleeSaved s1 s0) := by
  subst hsp
  have hrk_ne : (rkCap + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hrk_lt)
  have hdec_ne : (decW0 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hdec_lt)
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (v9_memRegion_896_40_split s.sp)))))))))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro z32; apply ProofLib.SepWP.exists_left; intro z24
  apply ProofLib.SepWP.exists_left; intro z16; apply ProofLib.SepWP.exists_left; intro z8
  apply ProofLib.SepWP.exists_left; intro z0
  dsimp only [v9_optProtoUcWordsAt, v9_optProtoPolyDecoderWordsAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  change s.pc = (blkPl_333).base + 2864#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 376) s _ _
  iterate 21 wp_step
  wp_conv_pre => rw [v9_fsp_2000_realign_rest s.sp ct1Len ep]
  wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v9_fsp_240_realign_64_rest s.sp (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) w248,
        v9_fsp_2000_unrealign_rest s.sp ct1Len ep]
  iterate 3 wp_step
  wp_conv_pre => rw [v9_pbA_144_triple_rest pbA decW8 decW16 decD24 decD28]
  wp_step
  wp_conv_pre =>
    rw [← v9_pbA_144_triple_rest pbA decW8 decW16 decD24 decD28,
        v9_pbA_160_pair32_eq_64_rest pbA decD24 decD28]
  iterate 12 wp_step
  wp_conv_pre => rw [v9_fsp_904_triple_rest s.sp z8 z16 z24]
  wp_step; wp_step
  wp_conv_pre =>
    rw [v9_fsp_913_realign_rest s.sp
          (EncoderFromPb.unshiftWord decW16 (EncoderFromPb.loByte (decD28 ++ decD24))) z24]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm1888 := v9_optProtoUcWordsAt_entails_128 (s.sp + 1888#64)
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
    dsimp only [v9_optProtoUcWordsAt] at hm1888; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1888
    have hp32_160 := (v9_pointsTo32_pair_eq_pointsTo64 (pbA + 160#64) decD24 decD28).symm
    have ha164 : (pbA + 160#64) + 4#64 = pbA + 164#64 := by bv_omega
    rw [ha164] at hp32_160
    have hp32_920 := (v9_pointsTo32_pair_eq_pointsTo64 (s.sp + 920#64) decD24 decD28).symm
    have ha924 : (s.sp + 920#64) + 4#64 = s.sp + 924#64 := by bv_omega
    rw [ha924] at hp32_920
    have hlo_w8 : BitVec.zeroExtend 8 decW8 = EncoderFromPb.loByte decW8 := by
      unfold EncoderFromPb.loByte; bv_kernel
    have h904_comb :
        ((s.sp + 904#64) ↦₈ BitVec.zeroExtend 8 decW8) ∗
        ((s.sp + 905#64) ↦₆₄ EncoderFromPb.unshiftWord decW8 (EncoderFromPb.loByte decW16)) ∗
        ((s.sp + 913#64) ↦ₛ EncoderFromPb.loBytes7
          (EncoderFromPb.unshiftWord decW16 (EncoderFromPb.loByte (decD28 ++ decD24)))) ∗
        ((s.sp + 920#64) ↦₆₄ (decD28 ++ decD24)) =
        ((s.sp + 904#64) ↦₆₄ decW8) ∗ ((s.sp + 912#64) ↦₆₄ decW16) ∗
        ((s.sp + 920#64) ↦₃₂ decD24) ∗ ((s.sp + 924#64) ↦₃₂ decD28) := by
      rw [hlo_w8]
      have h1 := v9_dst24_realign_final (s.sp + 904#64) decW8 decW16 (decD28 ++ decD24)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1; rw [h1, hp32_920]
    have hpack := v9_protoPolyDecoderAt_pack A (s.sp + 896#64) (pbToProtoPolyDecoder d)
      decW0 decW8 decW16 decD24 decD28 decW32
    dsimp only [v9_optProtoPolyDecoderWordsAt] at hpack; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
    rw [hp32_160]
    refine Entails.trans (Entails.of_eq (show _ =
      (((s.sp + 896#64) ↦₆₄ decW0) ∗
       (((s.sp + 904#64) ↦₈ BitVec.zeroExtend 8 decW8) ∗
        ((s.sp + 905#64) ↦₆₄ EncoderFromPb.unshiftWord decW8 (EncoderFromPb.loByte decW16)) ∗
        ((s.sp + 913#64) ↦ₛ EncoderFromPb.loBytes7
          (EncoderFromPb.unshiftWord decW16 (EncoderFromPb.loByte (decD28 ++ decD24)))) ∗
        ((s.sp + 920#64) ↦₆₄ (decD28 ++ decD24))) ∗
       ((s.sp + 928#64) ↦₆₄ decW32) ∗
       v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) decW0 decW8 decW16 decD24 decD28 decW32) ∗
      ((((s.sp + 1888#64) ↦₆₄ rkCap) ∗ ((s.sp + 1896#64) ↦₆₄ rkPtr) ∗ ((s.sp + 1904#64) ↦₆₄ rkLen) ∗
        ((s.sp + 1912#64) ↦₆₄ mkCap) ∗ ((s.sp + 1920#64) ↦₆₄ mkPtr) ∗ ((s.sp + 1928#64) ↦₆₄ mkLen) ∗
        ((s.sp + 1936#64) ↦₆₄ hdrCap) ∗ ((s.sp + 1944#64) ↦₆₄ hdrPtr) ∗ ((s.sp + 1952#64) ↦₆₄ hdrLen) ∗
        ((s.sp + 1960#64) ↦₆₄ esCap) ∗ ((s.sp + 1968#64) ↦₆₄ esPtr) ∗ ((s.sp + 1976#64) ↦₆₄ esLen) ∗
        ((s.sp + 1984#64) ↦₆₄ ct1Cap) ∗ ((s.sp + 1992#64) ↦₆₄ ct1Ptr) ∗ ((s.sp + 2000#64) ↦₆₄ ct1Len) ∗
        ((s.sp + 2008#64) ↦₆₄ ep)) ∗
       ((s.sp + 40#64) ↦₆₄ mkLen) ∗ ((s.sp + 48#64) ↦₆₄ ct1Cap) ∗ ((s.sp + 56#64) ↦₆₄ rkCap) ∗
       ((s.sp + 72#64) ↦₆₄ esPtr) ∗ ((s.sp + 80#64) ↦₆₄ hdrLen) ∗
       ((s.sp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
       ((s.sp + 128#64) ↦₆₄ esCap) ∗ ((s.sp + 136#64) ↦₆₄ mkPtr) ∗ ((s.sp + 144#64) ↦₆₄ hdrPtr) ∗
       ((s.sp + 152#64) ↦₆₄ hdrCap) ∗ ((s.sp + 200#64) ↦₆₄ ct1Ptr) ∗ ((s.sp + 216#64) ↦₆₄ mkCap) ∗
       ((s.sp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
       ((s.sp + 247#64) ↦₆₄ ep) ∗
       (((pbA + 136#64) ↦₆₄ decW0) ∗ ((pbA + 144#64) ↦₆₄ decW8) ∗ ((pbA + 152#64) ↦₆₄ decW16) ∗
        ((pbA + 160#64) ↦₃₂ decD24) ∗ ((pbA + 164#64) ↦₃₂ decD28) ∗ ((pbA + 168#64) ↦₆₄ decW32)) ∗ Rest) by ac_rfl)) ?_
    rw [h904_comb]
    have hpack' :
        ((s.sp + 896#64) ↦₆₄ decW0) ∗
        (((s.sp + 904#64) ↦₆₄ decW8) ∗ ((s.sp + 912#64) ↦₆₄ decW16) ∗
         ((s.sp + 920#64) ↦₃₂ decD24) ∗ ((s.sp + 924#64) ↦₃₂ decD28)) ∗
        ((s.sp + 928#64) ↦₆₄ decW32) ∗
        v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) decW0 decW8 decW16 decD24 decD28 decW32 ⊢
        protoPolynomialDecoderAt A (s.sp + 896#64) (pbToProtoPolyDecoder d) :=
      Entails.trans (Entails.of_eq (by ac_rfl)) hpack
    exact Entails.trans (sepConj_mono hpack' (sepConj_mono_left hm1888)) (Entails.of_eq (by ac_rfl))
  · dsimp only [blkPl_333, Obj.MultiPlacedLib.blockPlacement]
    wp_done

/-- At `+3044`, when `decoderFromPbResult pbDec = .error err` (`[fsp + 1888] = noneCap`),
    collapses `fsp + 1888..2288` into `memRegion (fsp + 1888#64) 400` and branches at `+3052`
    (`b.eq +8588`) to `+8588`. -/
theorem v9_step_3044_err_to_8588_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out rkPtr : BitVec 64) (err : PolynomialError) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8588#64) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ memRegion (fsp + 1888#64) 400 ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) := by
  refine SepWP.weaken_pre (sepConj_mono_left (v9_resultPolyDecoder_err_entails_tag_392 A fsp err)) ?_
  wp_simp_pre [sepConj_assoc]
  dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  change s.pc = (blkPl_333).base + 3044#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8588#64) s _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm400 : ((fsp + 1888#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 1896#64) 392 ⊢
        memRegion (fsp + 1888#64) 400 := by
      rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 8) (k := 392)
            (b' := fsp + 1896#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
    rw [← sepConj_assoc]; exact sepConj_mono_left hm400
  · wp_done

/-- At `+3044`, when `decoderFromPbResult pbDec = .ok dec` (`(v9_wordAt bs 0).toNat < 2 ^ 63`),
    copies the `PolyDecoder` cells and `Ct1Sent` fields into the epilogue stack slots and
    registers and branches at `+3344` (`b +8180`) to `+8180`. -/
theorem v9_step_3044_ok_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s0 s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 w2272 w2280 : BitVec 64) (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (bs : List (BitVec 8)) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 848#64) (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = esLen) (hx26 : s.readReg64 .x26 = rkLen)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
        ((fsp + 247#64) ↦₆₄ ep) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
        ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
        ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
        v9_decCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ v9_wordAt bs 376) ∗ ((fsp + 112#64) ↦₆₄ w2272) ∗ ((fsp + 120#64) ↦₆₄ w2280) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ v9_wordAt bs 312) ∗
          ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs 8)).zeroExtend 32) ∗
          ((fsp + 192#64) ↦₆₄ v9_wordAt bs 360) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ v9_wordAt bs 344) ∗
          ((fsp + 232#64) ↦₆₄ v9_wordAt bs 296) ∗
          ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗
          ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs 48) ∗
          ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs 80) ∗
          ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs 112) ∗
          ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs 144) ∗
          ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs 176) ∗
          ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs 208) ∗
          ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs 240) ∗
          ((fsp + 832#64) ↦₆₄ v9_wordAt bs 256) ∗
          ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)) ∗
          ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs 24 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) ∗
          ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (ep >>> 8)) ∗
          v9_decCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = esPtr ∧ s1.readReg64 .x1 = v9_wordAt bs 336 ∧
        s1.readReg64 .x2 = v9_wordAt bs 264 ∧ s1.readReg32 .x3 = esLen.extractLsb' 0 32 ∧
        s1.readReg64 .x4 = ct1Cap ∧ s1.readReg64 .x5 = ct1Ptr ∧ s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x7 = v9_wordAt bs 0 ∧ s1.readReg64 .x8 = 11#64 ∧ s1.readReg64 .x9 = hdrCap ∧
        s1.readReg64 .x10 = v9_wordAt bs 304 ∧ s1.readReg64 .x11 = v9_wordAt bs 272 ∧
        s1.readReg64 .x12 = v9_wordAt bs 328 ∧ s1.readReg64 .x13 = mkCap ∧
        s1.readReg64 .x14 = hdrPtr ∧ s1.readReg64 .x15 = rkCap ∧
        s1.readReg64 .x16 = v9_wordAt bs 368 ∧ s1.readReg64 .x17 = esCap ∧
        s1.readReg64 .x18 = hdrLen ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x20 = rkLen ∧
        s1.readReg32 .x21 = (EncoderFromPb.loByte ct1Len).zeroExtend 32 ∧
        s1.readReg64 .x22 = v9_wordAt bs 280 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x24 = v9_wordAt bs 288 ∧ s1.readReg64 .x25 = mkPtr ∧
        s1.readReg64 .x26 = v9_wordAt bs 320 ∧ s1.readReg64 .x27 = esLen >>> 8 ∧
        s1.readReg32 .x27 = (esLen >>> 8).extractLsb' 0 32 ∧
        s1.readReg64 .x28 = v9_wordAt bs 352 ∧ s1.readReg64 .x30 = mkLen ∧ TraceCalleeSaved s1 s0) := by
  subst hsp
  have hw0_ne : (v9_wordAt bs 0 + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hw0_lt)
  unfold v9_decCellsAt pointsTo128; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  change s.pc = (blkPl_333).base + 3044#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8180#64) s _ _
  iterate 3 wp_step
  wp_conv_pre => rw [v9_fsp_1896_realign_rest s.sp (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)]
  wp_step
  wp_conv_pre =>
    rw [v9_fsp_1896_unrealign_rest s.sp (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24),
        v9_fsp_1896_split_1_7_rest s.sp (v9_wordAt bs 8)]
  iterate 8 wp_step
  wp_conv_pre =>
    rw [v9_fsp_856_realign_rest s.sp
          ((v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 64 64) w864]
  wp_step
  wp_conv_pre => rw [v9_fsp_856_unrealign_midQ128_rest s.sp (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)]
  iterate 19 wp_step
  wp_conv_pre => rw [v9_fsp_240_realign_overlap_rest s.sp ct1Len ep]
  iterate 5 wp_step
  wp_conv_pre => rw [← v9_fsp_240_realign_overlap_rest s.sp ct1Len ep]
  iterate 8 wp_step
  wp_conv_pre =>
    rw [v9_fsp_880_realign_64_rest s.sp (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) w888]
  wp_step
  wp_conv_pre =>
    rw [v9_fsp_880_realign_rest s.sp (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) ep,
        v9_overlapLow7_unshift ct1Len ep]
  wp_steps
  wp_conv_pre => rw [v9_fsp_1896_unsplit_1_7_rest s.sp (v9_wordAt bs 8)]
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

end StepLemmas

/-! ## 3. Composition Helpers & Exit Tails (`+5368`, `+5360`, `+6904`, `+8588`, `+3044`) -/

theorem v9_seq_err_7084_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64) (P : SepProp) (err : LibsignalSpqrV1.Error)
    {Q : State → Prop}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_eq : fsp = s0.sp - 2400#64)
    (hstep : SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s P
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          (memRegion pbA optProtoInnerStateSize ∗ A.pool)) ∧
        Q sm))
    (hQ : ∀ sm, Q sm →
      sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧ TraceCalleeSaved sm s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 7084#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool))
    (Q := Q) hstep ?_
  intro sm hpcm hrunm hq
  obtain ⟨hspm, hx19m, herr_m, htrm⟩ := hQ sm hq
  rw [hfsp_eq] at hspm
  refine SepWP.mono (v9_states_from_pb_err_7084_placed (A := A) (F := F) s0 sm out err
    (memRegion pbA optProtoInnerStateSize ∗ A.pool)
    hsp0_align hpcm hrunm hspm hx19m herr_m htrm) ?_
  intro sf Pf _ _ ⟨hPf, hrest⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩

/-- From `+5368` (`dealloc_proto_decoder_5368`) through `+7084` (`err_7084`) to `s0.x30`
    when `receivingEk = some d` is still live in `v9_optProtoPolyDecoderHeap`. -/
theorem v9_tail_5368_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (d : ProtoPolynomialDecoder) (err : LibsignalSpqrV1.Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A (some d) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  dsimp only [v9_optProtoPolyDecoderHeap]; rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
  refine SepWP.weaken_pre
    (Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))))
      (Entails.of_eq (show _ =
        (if w0 = 0#64 then emp
         else A.live w8 (w0.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 d.pts ∗
           memRegion (w8 + BitVec.ofNat 64 (d.pts.length * 24)) ((w0.toNat - d.pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
         memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
  refine v9_seq_err_7084_placed s0 s fsp out pbA _ err hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_dealloc_proto_decoder_5368_placed hA s0 s fsp out w8 w0 x28_val d.pts
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
         memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hle hcap hpc hrun hpres hx22))
    (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono_left (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))

/-- From `+5360` (`dealloc_none/some_proto_decoder_5360`) through `+7084` (`err_7084`) to `s0.x30`
    for arbitrary `optDec : Option ProtoPolynomialDecoder`. -/
theorem v9_tail_5360_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (err : LibsignalSpqrV1.Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A optDec w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases optDec with
  | none =>
    dsimp only [v9_optProtoPolyDecoderHeap]
    apply SepWP.pure_elim; rintro rfl
    refine v9_seq_err_7084_placed s0 s fsp out pbA _ err hsp0_align hfsp_eq
      (SepWP.strengthen_entails_const ?_
        (v9_states_from_pb_dealloc_none_proto_decoder_5360_placed s0 s fsp out w8 x28_val
          (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          hpc hrun hpres))
      (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
    subst hfsp_eq; exact Entails.of_eq (by ac_rfl)
  | some d =>
    dsimp only [v9_optProtoPolyDecoderHeap]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))))
        (Entails.of_eq (show _ =
          (if w0 = 0#64 then emp
           else A.live w8 (w0.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 d.pts ∗
             memRegion (w8 + BitVec.ofNat 64 (d.pts.length * 24)) ((w0.toNat - d.pts.length) * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
    refine v9_seq_err_7084_placed s0 s fsp out pbA _ err hsp0_align hfsp_eq
      (SepWP.strengthen_entails_const ?_
        (v9_states_from_pb_dealloc_some_proto_decoder_5360_placed hA s0 s fsp out w8 w0 x28_val d.pts
          (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          hfsp_align hle hcap hpc hrun hpres hx22))
      (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
    subst hfsp_eq
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
      memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
    exact sepConj_mono_left (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))

/-- From `+6904` (`drop_uc_6904`) through `+7084` (`err_7084`) to `s0.x30`
    producing `.error (.err .stateDecode)`. -/
theorem v9_tail_6904_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 6904#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr) (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap) (hx13 : s.readReg64 .x13 = ct1Cap)
    (hx14 : s.readReg64 .x14 = ct1Ptr) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v9_ct1SentHeap_entails_dealloc A (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
    stackAt fsp encoderFromPbStack ∗
    (((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
     ((fsp + 152#64) ↦₆₄ hdrCap) ∗ A.pool ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
    (sepConj_mono hdealloc (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))) ?_
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro _hrk_lt
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
    ((fsp + 152#64) ↦₆₄ hdrCap) ∗ vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗
    vecCapPtrDealloc A hdrCap hdrPtr ∗ vecCapPtrDealloc A esCap esPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr ∗
    A.pool ∗ stackAt fsp allocHookStack ∗
    (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
  refine v9_seq_err_7084_placed s0 s fsp out pbA _ .stateDecode hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_drop_uc_6904_placed hA s0 s fsp out rkPtr rkCap mkPtr mkCap hdrPtr hdrCap esPtr esCap ct1Ptr ct1Cap
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
         memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hpc hrun hsp hx0 hx1 hx10 hx13 hx14 hx19 hx28 htr))
    (fun sm ⟨hspm, hx19m, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m]; rfl, htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    (memRegion (s0.sp - 2400#64) 72 ∗ ((s0.sp - 2400#64 + 72#64) ↦₆₄ esPtr) ∗
     memRegion (s0.sp - 2400#64 + 80#64) 48 ∗ ((s0.sp - 2400#64 + 128#64) ↦₆₄ esCap) ∗
     memRegion (s0.sp - 2400#64 + 136#64) 8 ∗ ((s0.sp - 2400#64 + 144#64) ↦₆₄ hdrPtr) ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ hdrCap) ∗ memRegion (s0.sp - 2400#64 + 160#64) 2144) ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    (sepConj_mono_left (v9_fsp_6904_entails_2304 (s0.sp - 2400#64) esPtr esCap hdrPtr hdrCap))

/-- From `+8588` (`drop_uc_8588`) through `+7084` (`err_7084`) to `s0.x30`
    producing `.error (.err .stateDecode)`. -/
theorem v9_tail_8588_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 8588#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
        memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v9_ct1SentHeap_entails_dealloc A (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
    stackAt fsp encoderFromPbStack ∗
    (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
     ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
     ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗ A.pool ∗
     memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
    (sepConj_mono hdealloc (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))) ?_
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro _hrk_lt
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
    ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
    ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
    vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗ vecCapPtrDealloc A hdrCap hdrPtr ∗
    vecCapPtrDealloc A esCap esPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr ∗ A.pool ∗ stackAt fsp allocHookStack ∗
    (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗
     memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
     memRegion (fsp + 224#64) 2080 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
  refine v9_seq_err_7084_placed s0 s fsp out pbA _ .stateDecode hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_drop_uc_8588_placed hA s0 s fsp out rkPtr rkCap mkPtr mkCap hdrPtr hdrCap esPtr esCap ct1Ptr ct1Cap
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
         memRegion (fsp + 224#64) 2080 ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hpc hrun hsp hx19 hx28 htr))
    (fun sm ⟨hspm, hx19m, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m]; rfl, htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    (memRegion (s0.sp - 2400#64) 48 ∗ ((s0.sp - 2400#64 + 48#64) ↦₆₄ ct1Cap) ∗
     ((s0.sp - 2400#64 + 56#64) ↦₆₄ rkCap) ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
     ((s0.sp - 2400#64 + 72#64) ↦₆₄ esPtr) ∗ memRegion (s0.sp - 2400#64 + 80#64) 48 ∗
     ((s0.sp - 2400#64 + 128#64) ↦₆₄ esCap) ∗ ((s0.sp - 2400#64 + 136#64) ↦₆₄ mkPtr) ∗
     ((s0.sp - 2400#64 + 144#64) ↦₆₄ hdrPtr) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ hdrCap) ∗
     memRegion (s0.sp - 2400#64 + 160#64) 40 ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ct1Ptr) ∗
     memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ mkCap) ∗
     memRegion (s0.sp - 2400#64 + 224#64) 2080) ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    (sepConj_mono_left (v9_fsp_8588_entails_2304 (s0.sp - 2400#64)
      ct1Cap rkCap esPtr esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap))

/-- From `+3044` (after `decoderFromPb` returns) to `s0.x30`. -/
theorem v9_tail_3044_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (d : PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = fsp + 848#64)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64) (hx25 : s.readReg64 .x25 = esLen)
    (hx26 : s.readReg64 .x26 = rkLen) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7
          (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
        memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
        memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (match decoderFromPbResult (pbToProtoPolyDecoder d) with
             | .ok dec => .ok (.ct1Acknowledged { uc := uc, receiving_ek := (dec : spqrPolyApi.PolyDecoder) })
             | .error _ => .error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases decoderFromPbResult (pbToProtoPolyDecoder d) with
  | error err =>
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 8588#64)
      (v9_step_3044_err_to_8588_placed s0 s fsp out rkPtr err _
        hfsp_align hpc hrun hsp hx19 hx28 htr) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx28_1, htr1⟩
    refine SepWP.weaken_pre ?_
      (v9_tail_8588_to_ret_placed hA s0 s1 fsp out pbA
        rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
        hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx19_1 hx28_1 htr1)
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen)) ∗
       (((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 8 ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗ memRegion (fsp + 100#64) 28) ∗
       (memRegion (fsp + 224#64) 16 ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16)) ∗
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
       ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
       ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
       memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
       v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (v9_memRegion_3044_collapse_err fsp mkLen hdrLen
      (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) uc.epoch
      ((EncoderFromPb.loByte ct1Len).zeroExtend 32))) (Entails.of_eq (by ac_rfl))
  | ok dec =>
    dsimp only [resultPolyDecoderFromPbAt]
    refine SepWP.weaken_pre (Entails.trans
      (sepConj_mono_left (v9_polyDecoderAt_relocate A (fsp + 1888#64) (out + 136#64) dec))
      (Entails.of_eq (show _ =
        (∃∗ bs : { l : List (BitVec 8) // l.length = 384 }, ∃∗ w392 : BitVec 64, ∃∗ P_heap : SepProp,
          ⌜(v9_wordAt bs.val 0).toNat < 2 ^ 63 ∧ EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
            (((out + 136#64) ↦ₛ bs.val) ∗ (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
             (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A (out + 136#64) dec)⌝ ∗
          ((fsp + 1888#64) ↦ₛ bs.val) ∗ (((fsp + 1888#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((fsp + 1888#64) + 392#64) ↦₆₄ w392) ∗ P_heap) ∗
        (memRegion (fsp + 88#64) 8 ∗ memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗
         memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641) ∗
        (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
         ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
         ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
         ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
         ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
         ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
         ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (v9_memRegion_3044_split_ok fsp))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine ProofLib.SepWP.exists_left fun w888 => ProofLib.SepWP.exists_left fun w880 =>
      ProofLib.SepWP.exists_left fun w864 => ProofLib.SepWP.exists_left fun q848 =>
      ProofLib.SepWP.exists_left fun w832 => ProofLib.SepWP.exists_left fun q816 =>
      ProofLib.SepWP.exists_left fun q800 => ProofLib.SepWP.exists_left fun q784 =>
      ProofLib.SepWP.exists_left fun q768 => ProofLib.SepWP.exists_left fun q752 =>
      ProofLib.SepWP.exists_left fun q736 => ProofLib.SepWP.exists_left fun q720 =>
      ProofLib.SepWP.exists_left fun q704 => ProofLib.SepWP.exists_left fun q688 =>
      ProofLib.SepWP.exists_left fun q672 => ProofLib.SepWP.exists_left fun q656 =>
      ProofLib.SepWP.exists_left fun q640 => ProofLib.SepWP.exists_left fun q624 =>
      ProofLib.SepWP.exists_left fun q608 => ProofLib.SepWP.exists_left fun w592 =>
      ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun w232 =>
      ProofLib.SepWP.exists_left fun w224 => ProofLib.SepWP.exists_left fun w208 =>
      ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
      ProofLib.SepWP.exists_left fun w160 => ProofLib.SepWP.exists_left fun w120 =>
      ProofLib.SepWP.exists_left fun w112 => ProofLib.SepWP.exists_left fun w104 =>
      ProofLib.SepWP.exists_left fun d92 => ProofLib.SepWP.exists_left fun bs =>
      ProofLib.SepWP.exists_left fun w392 => ProofLib.SepWP.exists_left fun P_heap => ?_
    apply SepWP.pure_elim; rintro ⟨hw0_lt, _, hreloc⟩
    wp_conv_pre => rw [v9_bs384_eq_decCells bs.val bs.property (fsp + 1888#64)]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
      ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
      ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
      ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
      ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
      ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
      ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
      ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
      ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
      ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
      ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
      ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
      ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
      ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
      v9_decCellsAt (fsp + 1888#64) bs.val ∗
      ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 2280#64) ↦₆₄ w392) ∗
      (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 4 ∗ memRegion (fsp + 100#64) 4 ∗
       memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 255#64) 313 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗
       memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗
       memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
       v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 8180#64)
      (v9_step_3044_ok_to_8180_placed s0 s fsp out
        rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
        w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 (BitVec.ofNat 64 dec.ptsNeeded) w392 d172
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 bs.val _
        hfsp_align hw0_lt hpc hrun hsp hx19 hx21 hx24 hx25 hx26 hx28 htr) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1,
      hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx27_32_1,
      hx28_1, hx30_1, htr1⟩
    have hpre8180 :
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗ ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((fsp + 120#64) ↦₆₄ w392) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
        ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
        ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗
        ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
        ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
        ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
        ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
        ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
        ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
        ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
        ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
        ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
        ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
        ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
        ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
        v9_decCellsAt (fsp + 1888#64) bs.val ∗ ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((fsp + 2280#64) ↦₆₄ w392) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 4 ∗ memRegion (fsp + 100#64) 4 ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 255#64) 313 ∗
         memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗
         memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗
         memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) ⊢
        (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
        (((fsp + 1888#64) ↦₁₂₈ (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)) ∗
         ((fsp + 1904#64) ↦₁₂₈ (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16)) ∗
         ((fsp + 1920#64) ↦₆₄ v9_wordAt bs.val 32) ∗ memRegion (fsp + 1928#64) 376) ∗
        (memRegion fsp 92 ∗ memRegion (fsp + 96#64) 8 ∗ memRegion (fsp + 128#64) 32 ∗
         memRegion (fsp + 200#64) 8 ∗ memRegion (fsp + 216#64) 8 ∗ memRegion (fsp + 895#64) 993) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
         ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 120#64) ↦₆₄ w392) ∗
         ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
         ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
         ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
         ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗ ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
         ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
         ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
         ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
         ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
         ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
         ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
         ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
         ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
         ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
         ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
         ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
         ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 568#64) 8 ∗
         memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) := by
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
         ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 313) ∗
        (v9_decCellsAt (fsp + 1888#64) bs.val ∗ ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
         ((fsp + 2280#64) ↦₆₄ w392) ∗ memRegion (fsp + 2288#64) 16) ∗
        ((memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 56#64) ↦₆₄ rkCap) ∗ memRegion (fsp + 64#64) 8 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
          ((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 4) ∗
         (((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗ memRegion (fsp + 100#64) 4) ∗
         (((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap)) ∗
         ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
         (memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952)) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
         ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 120#64) ↦₆₄ w392) ∗
         ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
         ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
         ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
         ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗ ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
         ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
         ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
         ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
         ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
         ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
         ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
         ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
         ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
         ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
         ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
         ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
         ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 568#64) 8 ∗
         memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      exact sepConj_mono (v9_loBytes7_64_313_entails_bs328 fsp
        (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) uc.epoch)
        (sepConj_mono (v9_fsp_1888_entails_epilogue fsp (BitVec.ofNat 64 dec.ptsNeeded) w392 bs.val bs.property)
          (sepConj_mono_left (v9_fsp_8180_gaps_collapse fsp mkLen ct1Cap rkCap esPtr hdrLen
            esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap ((EncoderFromPb.loByte ct1Len).zeroExtend 32))))
    refine SepWP.weaken_pre hpre8180 ?_
    subst hfsp_eq; rw [sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro bs240
    have hep := states_from_pb_epilogue_8180_placed hA.memcpy s0 s1 out
      d92 ((EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32)
      (v9_wordAt bs.val 376) (BitVec.ofNat 64 dec.ptsNeeded) w392
      (v9_wordAt bs.val 312) (v9_wordAt bs.val 360) rkPtr
      (v9_wordAt bs.val 344) (v9_wordAt bs.val 296) bs240.val bs240.property q576 w592
      (v9_quadAt bs.val 32) (v9_quadAt bs.val 48) (v9_quadAt bs.val 64) (v9_quadAt bs.val 80)
      (v9_quadAt bs.val 96) (v9_quadAt bs.val 112) (v9_quadAt bs.val 128) (v9_quadAt bs.val 144)
      (v9_quadAt bs.val 160) (v9_quadAt bs.val 176) (v9_quadAt bs.val 192) (v9_quadAt bs.val 208)
      (v9_quadAt bs.val 224) (v9_quadAt bs.val 240) (v9_wordAt bs.val 256)
      (v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24))
      (v9_wordAt bs.val 24 >>> 8) (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))
      (uc.epoch >>> 8) (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)
      (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16) (v9_wordAt bs.val 32)
      (v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
         esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool)
      hsp0_align hpc1 hrun1 hsp1 hx6_1 hx19_1 hx23_1 htr1
    rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
        hx3_1, hx27_32_1, hx27_1, hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1,
        hx10_1, hx26_1, hx12_1, hx1_1, hx28_1, hx16_1] at hep
    refine SepWP.weaken_pre (by unfold epilogueStackSlots epilogueStackGaps; exact Entails.of_eq (by ac_rfl))
      (SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ => ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩)
    have hb96 : (esLen.extractLsb' 0 32).setWidth 8 = esLen.extractLsb' 0 8 := by bv_kernel
    have hd97 : (esLen >>> 8).extractLsb' 0 32 = esLen.extractLsb' 8 32 := by bv_kernel
    have hh101 : (((esLen >>> 8) >>> 32).setWidth 32).setWidth 16 = esLen.extractLsb' 40 16 := by bv_kernel
    have hb103 : (((esLen >>> 8) >>> 48).setWidth 32).setWidth 8 = esLen.extractLsb' 56 8 := by bv_kernel
    have hb120 : ((EncoderFromPb.loByte ct1Len).zeroExtend 32).setWidth 8 = EncoderFromPb.loByte ct1Len :=
      v9_zext32_setWidth8 (EncoderFromPb.loByte ct1Len)
    rw [hb96, hd97, hh101, hb103, hb120]
    have hreloc' :
        ((out + 136#64) ↦ₛ bs.val) ∗ (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A (out + 136#64) dec := by
      simpa only [v9_bv_add_add_lit, Nat.reduceAdd] using hreloc
    have hout := v9_epilogueOutFull_entails_ct1Acknowledged A (F := F) out
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc bs.val bs.property w392 dec P_heap hreloc'
      (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val bs240.property
      (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)
      (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16) (v9_wordAt bs.val 32)
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hout)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlaced (
  v9_auth_from_pb_pinned_placed_ok
  v9_auth_from_pb_pinned_cl_on
  v9_step_2864_ok_some_to_3040_placed
  v9_step_3044_err_to_8588_placed
  v9_step_3044_ok_to_8180_placed
  v9_seq_err_7084_placed
  v9_tail_5368_to_ret_placed
  v9_tail_5360_to_ret_placed
  v9_tail_6904_to_ret_placed
  v9_tail_8588_to_ret_placed
  v9_tail_3044_to_ret_placed
)

end CryptoVerification.SpqrV1.States.FromPb
