/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFsPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-!
# Relocatable `do_reserve_and_handle [local#9]` (Block `561`)

Relocatable `[LibsignalPlacement]` contracts for `do_reserve_and_handle [local#9]` on Block `561`
(calling `finish_grow` on Block `587`), proving `doReserveStrideRawSpecX`, `reserve1`, `cliDoReserve`,
and `reserve16` variants and lifting them to caller blocks via `StoreKit.withLsRoCl`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open Reserve11Norm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

/-! ## 1. Arithmetic & Post-Condition Helpers -/

abbrev handleErrorSymCli : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

private theorem drop_rocl_post {α : Type} {P : Program} {e : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok P e (LibsignalPublicApi.StoreKit.withLsRoCl pl spec)) :
    subroutine_ok P e (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

private theorem adds_cs_eq_false_p {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_stride_eq_p {stride cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63) :
    (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
          (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else if (stride == 1#64) = true then 8#64 else 4#64) =
      BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional) := by
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hmax : max (max (len + additional) (2 * cap.toNat))
      (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm0 : (if (stride == 1#64) = true then 8#64 else 4#64).toNat =
      SpqrV1.Alloc.reserveMinCap stride.toNat := by
    by_cases hs : (stride == 1#64) = true
    · have hs' : stride = 1#64 := beq_iff_eq.mp hs
      subst hs'
      rfl
    · have hs' : stride.toNat ≠ 1 := by
        intro h1
        apply hs
        exact beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h1)
      simp only [hs, Bool.false_eq_true, ite_false, SpqrV1.Alloc.reserveMinCap, hs']
      rfl
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [SpqrV1.Alloc.reserveCapStride]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (stride == 1#64) = true then 8#64 else 4#64) = m0 at hm0 ⊢
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : m0.ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false, hm0]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega

/-! ## 2. Block `561` General `(stride, align)` Raw Contracts (`reserve11_raw_blk561_ok`, `reserve11_raw_fs_blk561_ok`) -/

set_option maxHeartbeats 1200000 in
theorem reserve11_raw_blk561_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (doReserveStrideRawSpecX A)) := by
  have hpanic : ((blkPC_561).rebase (blkPl_561).base H).externAt? (lsρ handleErrorSymCli) =
      some Rust.panicked :=
    (ls_externAt?_of_mem (prog := lsProg_561 H) (i := 561) (by decide)).trans hpan
  have hfg0 := drop_rocl_post (finish_grow_zero_cells_placed_ok_at (prog := lsProg_561 H) (i := 561) hA)
  have hfg1 := drop_rocl_post (finish_grow_ne_cells_placed_ok_at (prog := lsProg_561 H) (i := 561) hA)
  dsimp only [lsProg_561] at hfg0 hfg1
  unfold LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  simp only [doReserveStrideRawSpecX, GrowOne.Helpers.stackAt_cliGrowOne, sepExists_sepConj_right]
  change subroutine_ok ((blkPC_561).rebase (blkPl_561).base H) (blkPl_561).base _
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hlay0 : LayoutOk
      (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat)
      align.toNat := by assumption
  have hsz_pos : 0 < SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
    hlay0.1
  have hpow : ∃ k, align.toNat = 2 ^ k := hlay0.2.1
  have hbound :
      SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat +
        align.toNat ≤ 2 ^ 63 := hlay0.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hnew_lt63 : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat))
      (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 := hnew_lt63
  have hcs := adds_cs_eq_false_p (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq_p (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hlay0
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
           else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : SpqrV1.Alloc.reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_561).base + 88#64)
    apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsmpl.base 587) hcrl0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcrl1
    simp only [wp_norm] at hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ handleErrorSymCli)
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
    have hsub_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_561).base + 88#64)
    apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsmpl.base 587) hcrl0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcrl1
    simp only [wp_norm] at hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ handleErrorSymCli)
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

set_option maxHeartbeats 1200000 in
theorem reserve11_raw_fs_blk561_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hFs : AllocContractsFsPlaced A H)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (doReserveStrideRawSpecX A).keepsFs) := by
  have hpanic : ((blkPC_561).rebase (blkPl_561).base H).externAt? (lsρ handleErrorSymCli) =
      some Rust.panicked :=
    (ls_externAt?_of_mem (prog := lsProg_561 H) (i := 561) (by decide)).trans hpan
  have hfg0 := drop_rocl_post
    (finish_grow_zero_cells_fs_placed_ok_at (prog := lsProg_561 H) (i := 561) hFs)
  have hfg1 := drop_rocl_post
    (finish_grow_ne_cells_fs_placed_ok_at (prog := lsProg_561 H) (i := 561) hFs)
  dsimp only [lsProg_561] at hfg0 hfg1
  unfold LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  simp only [Spec.keepsFs, doReserveStrideRawSpecX, GrowOne.Helpers.stackAt_cliGrowOne,
    sepExists_sepConj_right]
  change subroutine_ok ((blkPC_561).rebase (blkPl_561).base H) (blkPl_561).base _
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hlay0 : LayoutOk
      (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat)
      align.toNat := by assumption
  have hsz_pos : 0 < SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
    hlay0.1
  have hpow : ∃ k, align.toNat = 2 ^ k := hlay0.2.1
  have hbound :
      SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat +
        align.toNat ≤ 2 ^ 63 := hlay0.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hnew_lt63 : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat))
      (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 := hnew_lt63
  have hcs := adds_cs_eq_false_p (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq_p (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hlay0
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
           else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : SpqrV1.Alloc.reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_561).base + 88#64)
    apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsmpl.base 587) hcrl0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcrl1
    simp only [wp_norm] at hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ handleErrorSymCli)
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
    have hsub_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_561).base + 88#64)
    apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsmpl.base 587) hcrl0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcrl1
    simp only [wp_norm] at hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ handleErrorSymCli)
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

/-! ## 3. Pure `doReserveSpecOf` & `reserve16` Refinements -/

private theorem vecU8At_eq_p (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

theorem doReserveStrideRaw_refines_doReserveSpecOf_pure {A : RustAlloc}
    {resStack : Nat} (hstk : doReserveStackX ≤ resStack) :
    SpecRefines
      (doReserveStrideRawSpecX A)
      (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A) := by
  intro x R s0 hpre
  simp only [SpqrV1.Varint.doReserveSpecOf, vecU8At_eq_p,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hhi : resStack ≤ 2 ^ 64 := by
    have hm := hmem
    rw [stackAt, repack_stack_bound] at hm
    exact GrowOne.Helpers.memRegion_bound_of_pointsTo64 hm
  have hlo : 64 + finishGrowStackX ≤ resStack := by
    have : 64 + finishGrowStackX = doReserveStackX := by decide
    omega
  have hsplit : stackAt s0.sp resStack =
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
        stackAt s0.sp doReserveStackX :=
    GrowOne.Helpers.stackAt_split_stk s0.sp hlo hhi
  rw [hsplit, repack_raw_pre] at hmem
  let xs : SpqrV1.Alloc.DoReserveStrideCall :=
    ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  let F : SepProp :=
    ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R
  have hpre' : s0.mem ⊨ (doReserveStrideRawSpecX A).pre xs s0 ∗ F := by
    simp only [doReserveStrideRawSpecX, xs, BitVec.toNat_ofNat, Nat.one_mod,
      SpqrV1.Alloc.reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hlay⟩, hmem⟩
  refine ⟨xs, F, hpre', ?_, ?_, ?_, ?_⟩
  · intro sf hq
    simp only [doReserveStrideRawSpecX, SpqrV1.Varint.doReserveSpecOf, vecU8At_eq_p,
      xs, BitVec.toNat_ofNat, Nat.one_mod, SpqrV1.Alloc.reserveCapStride_one, Nat.mul_one,
      Nat.mod_one, and_true] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hpost_mem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at ht
      dsimp [reserveCap] at ht; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, Nat.mod_eq_of_lt hlt, hsplit]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rw [← repack_raw_post]
    dsimp only [F] at hpost_mem
    exact hpost_mem
  · intro sf hq
    dsimp only [doReserveStrideRawSpecX, SpqrV1.Varint.doReserveSpecOf, doReserveSpec, F] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    rw [repack_anyHeap] at hq
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq.2
  · intro _ _ hq
    exact (allowPanic_not_exited hq).elim
  · intro _ hq
    exact (allowPanic_not_exited hq).elim

theorem reserve1_blk561_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs) :=
  (doReserveStrideRaw_refines_doReserveSpecOf_pure hres).apply_keepsFs_withLsCodeRoLoaded
    (reserve11_raw_fs_blk561_ok hCF hpan)

theorem cliDoReserve_blk561_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hA : AllocContractsXCliPlaced A H)
    (hstk : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A)) :=
  (doReserveStrideRaw_refines_doReserveSpecOf_pure hstk).apply_withLsCodeRoLoaded
    (reserve11_raw_blk561_ok hA hpan)

private theorem vec16At_eq_p (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vec16At A v cap ptr bs =
      ⌜bs.length % 16 = 0 ∧ bs.length ≤ 16 * cap.toNat ∧ 16 * cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length / 16)) ∗
      (if cap = 0#64 then emp
       else A.live ptr (16 * cap.toNat) 8 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (16 * cap.toNat - bs.length)) := by
  simp only [vec16At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

theorem reserve16Cap_blk561_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (reserve16CapSpec A resStack)) := by
  intro x R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre0⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [reserve16CapSpec, vec16At_eq_p, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap62⟩,
    ⟨hmod16, hbs_le, hcap63, hptr⟩, hmem⟩
  have hhi : resStack ≤ 2 ^ 64 := by
    have hm := hmem
    rw [stackAt, repack_stack_bound] at hm
    exact GrowOne.Helpers.memRegion_bound_of_pointsTo64 hm
  have hlo : 64 + finishGrowStackX ≤ resStack := by
    have : 64 + finishGrowStackX = doReserveStackX := by decide
    omega
  have hsplit : stackAt s0.sp resStack =
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
        stackAt s0.sp doReserveStackX :=
    GrowOne.Helpers.stackAt_split_stk s0.sp hlo hhi
  rw [hsplit, repack_raw_pre] at hmem
  let len := x.bs.length / 16
  let newCap := SpqrV1.Alloc.reserveCapStride 16 x.cap.toNat len 1
  have hx1_nat : (s0.readReg64 .x1).toNat = len := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [len]; omega)]
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  have hlen_le_cap : len ≤ x.cap.toNat := by dsimp [len]; omega
  have hnew_mul : newCap * 16 + 8 ≤ 2 ^ 63 := by
    dsimp [newCap, SpqrV1.Alloc.reserveCapStride, SpqrV1.Alloc.reserveMinCap, len]
    omega
  have hlay : LayoutOk (newCap * 16) 8 :=
    ⟨by dsimp [newCap, SpqrV1.Alloc.reserveCapStride, SpqrV1.Alloc.reserveMinCap]; omega,
     ⟨3, rfl⟩, hnew_mul⟩
  let xs : SpqrV1.Alloc.DoReserveStrideCall :=
    ⟨x.v, x.cap, x.ptr, x.bs, len, 1, 8#64, 16#64⟩
  let F : SepProp :=
    ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R
  have hcap_comm : x.cap.toNat * 16 = 16 * x.cap.toNat := Nat.mul_comm _ _
  have hpre' : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (doReserveStrideRawSpecX A).keepsFs).pre xs s0 ∗ F := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [doReserveStrideRawSpecX, xs,
      show (8#64 : BitVec 64).toNat = 8 from rfl,
      show (16#64 : BitVec 64).toNat = 16 from rfl,
      hcap_comm, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_nat, hx2_nat, hx3, hx4, hlen_le_cap, hbs_le, hptr, by decide, hlay⟩, hmem⟩
  rcases reserve11_raw_fs_blk561_ok hCF hpan xs F s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan', hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [Spec.keepsFs,
      doReserveStrideRawSpecX, reserve16CapSpec, reserve16Spec, vec16At_eq_p, xs,
      show (8#64 : BitVec 64).toNat = 8 from rfl,
      show (16#64 : BitVec 64).toNat = 16 from rfl] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hfs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hp'_ne, _⟩, hpost_mem⟩
    have hnew_lt64 : newCap < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hgrow : len + 1 ≤ newCap := by
      dsimp [newCap, SpqrV1.Alloc.reserveCapStride]; omega
    have hbs_le' : x.bs.length ≤ 16 * newCap := by dsimp [len] at hgrow; omega
    have hcap63' : 16 * newCap < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 newCap ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [htoNat] at ht
      change newCap = 0 at ht
      omega
    have hnew_comm : newCap * 16 = 16 * newCap := Nat.mul_comm _ _
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrace, hfs⟩, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨BitVec.ofNat 64 newCap, p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat, hsplit]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hgrow, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hmod16, hbs_le', hcap63', hp'_ne⟩, ?_⟩
    rw [hnew_comm] at hpost_mem
    rw [← repack_raw_post]
    dsimp only [F] at hpost_mem
    exact hpost_mem
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan', ?_⟩)⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs,
      doReserveStrideRawSpecX, reserve16CapSpec, reserve16Spec, F] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1.1, ?_⟩
    rw [repack_anyHeap] at hq
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq.2
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

theorem reserve16Eq_blk561_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (reserve16EqSpec A resStack)) := by
  intro x R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre0⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [reserve16EqSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap_eq⟩, hmem⟩
  have hcap62 : 16 * x.cap.toNat < 2 ^ 62 := by
    rw [hcap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hpre' : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (reserve16CapSpec A resStack)).pre x s0 ∗ R := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [reserve16CapSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap62⟩, hmem⟩
  exact reserve16Cap_blk561_ok hCF hres hpan x R s0 hpc hrun hpre' hsp hcl

theorem reserve16_blk561_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (reserve16Spec A resStack)) :=
  reserve16Cap_blk561_ok hCF hres hpan

/-! ## 4. Cross-Block Lifted Contracts (`withLsRoCl lsmpl`, Block `561` → Any Caller Block & Block `617`) -/

section CallerBlock
variable [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
  {prog : Program} {i : Nat} [IsLsBlockProg prog i H]

theorem reserve1_placed_ok_at {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (reserve1_blk561_ok hCF hres hpan) hi

theorem cliDoReserve_placed_ok_at {resStack : Nat}
    (hA : AllocContractsXCliPlaced A H)
    (hstk : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (cliDoReserve_blk561_ok hA hstk hpan) hi

theorem reserve16Cap_placed_ok_at {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (reserve16CapSpec A resStack)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (reserve16Cap_blk561_ok hCF hres hpan) hi

theorem reserve16Eq_placed_ok_at {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (reserve16EqSpec A resStack)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (reserve16Eq_blk561_ok hCF hres hpan) hi

theorem reserve16_placed_ok_at {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (reserve16Spec A resStack)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (reserve16_blk561_ok hCF hres hpan) hi

end CallerBlock

theorem reserve1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs) :=
  reserve1_placed_ok_at (prog := lsProg_617 H) (i := 617) hCF hres hpan

theorem cliDoReserve_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hA : AllocContractsXCliPlaced A H)
    (hstk : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A)) :=
  cliDoReserve_placed_ok_at (prog := lsProg_617 H) (i := 617) hA hstk hpan

theorem reserve16Cap_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (reserve16CapSpec A resStack)) :=
  reserve16Cap_placed_ok_at (prog := lsProg_617 H) (i := 617) hCF hres hpan

theorem reserve16Eq_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (reserve16EqSpec A resStack)) :=
  reserve16Eq_placed_ok_at (prog := lsProg_617 H) (i := 617) hCF hres hpan

theorem reserve16_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (reserve16Spec A resStack)) :=
  reserve16_placed_ok_at (prog := lsProg_617 H) (i := 617) hCF hres hpan

end CryptoVerification.SignalSession.Cli.MainHops
