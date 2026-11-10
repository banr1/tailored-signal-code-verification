/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymC
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `RawVec<(String, Vec<u8>)>::grow_one` (Block `586`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.GrowOne.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem memRegion_24_cells_p (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem pull_fg0_err_p (O1 O2 O3 P A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ P ∗ A ∗ S) ∗ R = P ∗ ((A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg0_ok_p (O1 O2 O3 P L M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg1_post_p (O1 O2 O3 P L B M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ B ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ B ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

theorem finish_grow_zero_cells_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (hFG : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowSpecX A))) :
    subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowZeroCellsSpec A)) := by
  intro ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [finishGrowZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells_p, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  have hpre' := satisfies_lscro_pre hcrl hpre0
  rcases hFG hcall R s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    simp only [finishGrowSpecX, finishGrowZeroCellsSpec, hcall,
      FinishGrowCall.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err_p, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg0_ok_p, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hq⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))⟩

theorem finish_grow_ne_cells_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (hFG : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowSpecX A))) :
    subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowNeCellsSpec A)) := by
  intro ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [finishGrowNeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells_p, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  have hpre' := satisfies_lscro_pre hcrl hpre0
  rcases hFG hcall R s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    simp only [finishGrowSpecX, finishGrowNeCellsSpec, hcall,
      FinishGrowCall.oldBuf, hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post_p, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post_p, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hq⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))⟩

theorem growOneDirBytes_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hpan : CliPanicHooksPlaced H)
    (hFG : subroutine_ok (lsProg_586 H) (lsmpl.base 587)
      (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowSpecX A))) :
    subroutine_ok (lsProg_586 H) (blkPl_586).base
      (StoreKit.withLsCodeRoLoaded lsmpl (growOneDirBytesInnerSpec A)) := by
  have hpanic : (lsProg_586 H).externAt? (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Rust.panicked :=
    ls_panicAt_of_cliPanic hpan
  dsimp only [StoreKit.withLsCodeRoLoaded]
  simp only [growOneDirBytesInnerSpec, stackAt_cliGrowOne, sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  have hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  clear h
  dsimp only at *
  have hfg0 := finish_grow_zero_cells_placed_ok_x hFG
  have hfg1 := finish_grow_ne_cells_placed_ok_x hFG
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (48#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 48; omega, hpow, ?_⟩
    change new.toNat * 48 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 48 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 48 = new.toNat * 48 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_586).base + 60#64)
    apply StoreKit.sepWP_seq_lscro hcrl (mid := lsmpl.base 587)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    wp_call_lscro hfg0 hcrl1 (s0.sp - 56#64, 0#64, ptr, new, 8#64, 48#64, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : max (2 * cap.toNat) 4 * 48 - bs.length = new.toNat * 48 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 48 = new.toNat * 48 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_586).base + 60#64)
    apply StoreKit.sepWP_seq_lscro hcrl (mid := lsmpl.base 587)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    wp_call_lscro hfg1 hcrl1 (s0.sp - 56#64, cap, ptr, new, 8#64, 48#64, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

private def vecHeaderBytesP (cap ptr len : BitVec 64) : List (BitVec 8) :=
  unpack64 cap ++ (unpack64 ptr ++ unpack64 len)

private theorem vecHeader_eq_bytes_p (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len = (a ↦ₛ vecHeaderBytesP cap ptr len) := by
  unfold vecHeader vecHeaderBytesP
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  simp only [pointsToBytes_append, unpack64_length, h16, ← pointsTo64_eq_pointsToBytes]

private theorem dirEntry_body_eq_p (b c1 p1 l1 c2 p2 l2 : BitVec 64) (R1 R2 : SepProp) :
    (vecHeader b c1 p1 l1 ∗ R1) ∗ (vecHeader (b + 0x18#64) c2 p2 l2 ∗ R2) =
      (b ↦ₛ (vecHeaderBytesP c1 p1 l1 ++ vecHeaderBytesP c2 p2 l2)) ∗ (R1 ∗ R2) := by
  have hl : (vecHeaderBytesP c1 p1 l1).length = 24 := by simp [vecHeaderBytesP, unpack64_length]
  rw [vecHeader_eq_bytes_p, vecHeader_eq_bytes_p, pointsToBytes_append, hl]
  change _ = (_ ∗ ((b + 0x18#64) ↦ₛ _)) ∗ _
  ac_rfl

private theorem dirEntry_reloc_p (A : RustAlloc) (e : List (BitVec 8) × List (BitVec 8)) (a : BitVec 64) :
    dirEntryAt A e a ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 48 ∧ ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ dirEntryAt A e b⌝ ∗ (a ↦ₛ bs) ∗ H := by
  dsimp only [dirEntryAt, vecU8, vecU8At]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  rw [dirEntry_body_eq_p]
  apply Entails.sepExists_right
    (vecHeaderBytesP c1 p1 (BitVec.ofNat 64 e.1.length) ++
      vecHeaderBytesP c2 p2 (BitVec.ofNat 64 e.2.length))
  apply Entails.sepExists_right
  refine Entails.pure_right ⟨by simp [vecHeaderBytesP, unpack64_length], fun b => ?_⟩ (Entails.refl _)
  rw [← dirEntry_body_eq_p]
  exact sepConj_mono
    (Entails.sepExists_right c1 (Entails.sepExists_right p1 (Entails.refl _)))
    (Entails.sepExists_right c2 (Entails.sepExists_right p2 (Entails.refl _)))

private theorem arrayAt_dirEntry_reloc_p (A : RustAlloc) :
    ∀ (xs : List (List (BitVec 8) × List (BitVec 8))) (a : BitVec 64),
      arrayAt (dirEntryAt A) 48 a xs ⊢
        ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = xs.length * 48 ∧
            ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ arrayAt (dirEntryAt A) 48 b xs⌝ ∗
          (a ↦ₛ bs) ∗ H
  | [], a => by
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    simp only [arrayAt, pointsToBytes_nil, List.length_nil, Nat.zero_mul, emp_sepConj]
    exact Entails.pure_right ⟨trivial, fun _ => Entails.refl emp⟩ (Entails.refl emp)
  | e :: xs, a => by
    dsimp only [arrayAt]
    refine Entails.trans (sepConj_mono (dirEntry_reloc_p A e a) (arrayAt_dirEntry_reloc_p A xs (a + 48#64))) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs1
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro H1
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs2
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro H2
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hl1, hr1⟩
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hl2, hr2⟩
    refine Entails.sepExists_right (bs1 ++ bs2) (Entails.sepExists_right (H1 ∗ H2) ?_)
    have hlen : (bs1 ++ bs2).length = (e :: xs).length * 48 := by
      simp only [List.length_append, List.length_cons, hl1, hl2]; omega
    refine Entails.pure_right ⟨hlen, fun b => ?_⟩ ?_
    · rw [pointsToBytes_append, hl1]
      change ((b ↦ₛ bs1) ∗ ((b + 48#64) ↦ₛ bs2)) ∗ (H1 ∗ H2) ⊢
        dirEntryAt A e b ∗ arrayAt (dirEntryAt A) 48 (b + 48#64) xs
      have harr : ((b ↦ₛ bs1) ∗ ((b + 48#64) ↦ₛ bs2)) ∗ (H1 ∗ H2) =
          ((b ↦ₛ bs1) ∗ H1) ∗ (((b + 48#64) ↦ₛ bs2) ∗ H2) := by ac_rfl
      rw [harr]
      exact sepConj_mono (hr1 b) (hr2 (b + 48#64))
    · rw [pointsToBytes_append, hl1]
      change (a ↦ₛ bs1) ∗ H1 ∗ ((a + 48#64) ↦ₛ bs2) ∗ H2 ⊢
        ((a ↦ₛ bs1) ∗ ((a + 48#64) ↦ₛ bs2)) ∗ (H1 ∗ H2)
      exact Entails.of_eq (by ac_rfl)

theorem growOneDir_placed_of_bytes [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hbs_ok : subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (growOneDirBytesInnerSpec A)))
    (hstk : 0x40 + finishGrowStackX ≤ stk) :
    subroutine_ok prog entry (growOneDirSpecPlaced A stk) := by
  intro ⟨v, cap, ptr, xs⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [growOneDirSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hcap32⟩, hmem⟩
  dsimp only [vecAt, vecHeader, vecBuf] at hmem
  have hmem_p : s0.mem ⊨
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           arrayAt (dirEntryAt A) 48 ptr xs ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
             ((cap.toNat - xs.length) * 48)) ∗
        stackAt s0.sp stk ∗ A.pool ∗ R) := by
    convert hmem using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hmem_p
  rcases hmem_p with ⟨⟨hxs_le, _, hptr_ne⟩, hmem_s⟩
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk) (a := v) (v := cap)
      (R := ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           arrayAt (dirEntryAt A) 48 ptr xs ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
             ((cap.toNat - xs.length) * 48)) ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem_s
    convert hmem_s using 1; ac_rfl
  rw [stackAt_split_stk s0.sp hstk hstk_hi] at hmem_s
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliGrowOneStack)
  let newCap := max (2 * cap.toNat) 4
  have hmax_eq : max (2 * cap.toNat) 4 = newCap := rfl
  have hbound : newCap * 48 + 8 ≤ 2 ^ 63 := by dsimp [newCap]; omega
  have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [newCap]; omega)]
  have hnew_ne : BitVec.ofNat 64 newCap ≠ 0 := by
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [hnew_toNat] at ht
    change newCap = 0 at ht
    dsimp [newCap] at ht; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hxs0 : xs = [] :=
      List.eq_nil_of_length_eq_zero (by simpa using hxs_le)
    subst hxs0
    simp only [ite_true] at hmem_s
    let F_extra := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗ stkRem
    have hpre0 : s0.mem ⊨ (growOneDirBytesInnerSpec A).pre (v, 0#64, ptr, []) s0 ∗ (F_extra ∗ R) := by
      simp only [growOneDirBytesInnerSpec, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, Nat.zero_le _, hptr_ne, hbound⟩, ?_⟩
      convert hmem_s using 1
      dsimp [F_extra, stkRem]
      ac_rfl
    have hpre' := satisfies_lscro_pre hcrl hpre0
    rcases hbs_ok (v, 0#64, ptr, []) (F_extra ∗ R) s0 hpc hrun hpre' hsp hcl with
      ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
    · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
      dsimp only [StoreKit.withLsCodeRoLoaded, growOneDirBytesInnerSpec, growOneDirSpecPlaced] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨htrace, hq⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
      rcases hq with ⟨p', hq⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨⟨hp', _⟩, hmemf⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htrace, ?_⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨p', ?_⟩
      dsimp only [vecAt, vecHeader, vecBuf, List.length_nil]
      rw [hmax_eq] at hmemf ⊢
      simp only [hnew_ne, ite_false, hnew_toNat, Nat.sub_zero, Nat.zero_mul,
        pointsToBytes_nil, emp_sepConj, BitVec.add_zero] at hmemf ⊢
      have harray0 : arrayAt (dirEntryAt A) 48 p' [] = emp := rfl
      rw [harray0, emp_sepConj]
      have hpost_p : sf.mem ⊨
          ⌜0 ≤ newCap ∧ newCap * 48 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
            (A.live p' (newCap * 48) 8 ∗ memRegion p' (newCap * 48)) ∗
            (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool) ∗ R) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨Nat.zero_le _, by omega, hp'⟩, ?_⟩
        convert hmemf using 1
        dsimp [F_extra, stkRem]
        ac_rfl
      rw [← stackAt_split_stk s0.sp hstk hstk_hi] at hpost_p
      convert hpost_p using 1; ac_rfl
    · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
      dsimp only [StoreKit.withLsCodeRoLoaded, growOneDirBytesInnerSpec, growOneDirSpecPlaced] at hq ⊢
      exact allowPanic_frame id (by rwa [sepConj_assoc])
    · exact (allowPanic_not_exited hq).elim
    · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  · simp only [hcap0, ite_false] at hmem_s
    have hsplit : s0.mem ⊨
        (∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = xs.length * 48 ∧
            ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ arrayAt (dirEntryAt A) 48 b xs⌝ ∗
          (ptr ↦ₛ bs) ∗ H) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
            ((cap.toNat - xs.length) * 48) ∗
          (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool ∗ R) := by
      refine Satisfies.mono (sepConj_mono_left (arrayAt_dirEntry_reloc_p A xs ptr)) ?_
      dsimp only [stkRem]
      convert hmem_s using 1; ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hsplit
    rcases hsplit with ⟨bs, hsplit⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hsplit
    rcases hsplit with ⟨H, hsplit⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsplit
    rcases hsplit with ⟨⟨hbs_len, hrec⟩, hsplit⟩
    let F_extra := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗ H ∗ stkRem
    have hbs_le : bs.length ≤ cap.toNat * 48 := by rw [hbs_len]; omega
    have hmr_old :
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 48 - bs.length) =
        memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48) := by
      rw [hbs_len, Nat.sub_mul]
    have hpre0 : s0.mem ⊨ (growOneDirBytesInnerSpec A).pre (v, cap, ptr, bs) s0 ∗ (F_extra ∗ R) := by
      simp only [growOneDirBytesInnerSpec, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hbs_le, hptr_ne, hbound⟩, ?_⟩
      rw [hmr_old]
      convert hsplit using 1
      dsimp [F_extra, stkRem]
      ac_rfl
    have hpre' := satisfies_lscro_pre hcrl hpre0
    rcases hbs_ok (v, cap, ptr, bs) (F_extra ∗ R) s0 hpc hrun hpre' hsp hcl with
      ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
    · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
      dsimp only [StoreKit.withLsCodeRoLoaded, growOneDirBytesInnerSpec, growOneDirSpecPlaced] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨htrace, hq⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
      rcases hq with ⟨p', hq⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨⟨hp', _⟩, hmemf⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htrace, ?_⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨p', ?_⟩
      dsimp only [vecAt, vecHeader, vecBuf]
      rw [hmax_eq] at hmemf ⊢
      simp only [hnew_ne, ite_false, hnew_toNat]
      have hmr_new :
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap * 48 - bs.length) =
          memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48) := by
        rw [hbs_len, Nat.sub_mul]
      have hreasm : sf.mem ⊨
          arrayAt (dirEntryAt A) 48 p' xs ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
            A.live p' (newCap * 48) 8 ∗
            memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48) ∗
            (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool) ∗ R) := by
        refine Satisfies.mono (sepConj_mono_left (hrec p')) ?_
        rw [hmr_new] at hmemf
        convert hmemf using 1
        dsimp [F_extra, stkRem]
        ac_rfl
      rw [← stackAt_split_stk s0.sp hstk hstk_hi] at hreasm
      have hpost_p : sf.mem ⊨
          ⌜xs.length ≤ newCap ∧ newCap * 48 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
            (A.live p' (newCap * 48) 8 ∗ arrayAt (dirEntryAt A) 48 p' xs ∗
              memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48)) ∗
            stackAt s0.sp stk ∗ A.pool) ∗ R) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨by dsimp [newCap]; omega, by omega, hp'⟩, ?_⟩
        convert hreasm using 1; ac_rfl
      convert hpost_p using 1; ac_rfl
    · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
      dsimp only [StoreKit.withLsCodeRoLoaded, growOneDirBytesInnerSpec, growOneDirSpecPlaced] at hq ⊢
      exact allowPanic_frame id (by rwa [sepConj_assoc])
    · exact (allowPanic_not_exited hq).elim
    · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim

end CryptoVerification.SignalSession.Cli.GrowOne.Helpers
