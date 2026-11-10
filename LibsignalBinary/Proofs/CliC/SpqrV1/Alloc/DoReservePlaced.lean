/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrowPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `RawVecInner::do_reserve_and_handle` Proofs for `CliC`

Proves `[LibsignalPlacement]` contracts (`doReserveStrideRawSpec`, `doReserveRawSpec`,
`doReserveSpec`, and `AllocContractsX` variants) for `CliC` `do_reserve_and_handle` (Block `561`,
calling `finish_grow` on Block `587`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.CodeLayout
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli.Placed
open DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem vecU8At_eq_placed (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem finish_grow_8_zero_cells_of_spec_cli {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow8ZeroCellsSpecG A hookStack) :=
  finish_grow_8_zero_cells_placed_of_spec hfg

private theorem finish_grow_8_ne_cells_of_spec_cli {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow8NeCellsSpecG A hookStack) :=
  finish_grow_8_ne_cells_placed_of_spec hfg

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_placed_ok_of_fg
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64 := by decide)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok (lsProg_587 H) (blkPl_587).base
      (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack A hookStack)) := by
  unfold withLsCodeLoaded doReserveStrideRawSpecWithStack
  simp only [stackAt_doReserve_gen _ hhook, sepExists_sepConj_right]
  have hpanic : (lsProg_561 H).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hlay : LayoutOk (reserveCapStride stride.toNat cap.toNat len additional * stride.toNat) align.toNat := by
    assumption
  have hsz_pos : 0 < reserveCapStride stride.toNat cap.toNat len additional * stride.toNat := hlay.1
  have hpow : ∃ k, align.toNat = 2 ^ k := hlay.2.1
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤ 2 ^ 63 :=
    hlay.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hlay
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
    have hmul_eq : reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_561).base + 88#64)
    wp_steps_lscl (lsmpl.base 587)
    have hfg0 := lscall_blk (callerProg := lsProg_561 H)
      (finish_grow_8_zero_cells_of_spec_cli hfg) ‹_›
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
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
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_561).base + 88#64)
    wp_steps_lscl (lsmpl.base 587)
    have hfg1 := lscall_blk (callerProg := lsProg_561 H)
      (finish_grow_8_ne_cells_of_spec_cli hfg) ‹_›
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
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

private theorem do_reserve_7_raw_placed_of_stride_cli [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hs : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack)) := by
  intro x R s0 hpc hrun hpre hsp hcl
  simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 := by
    refine ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack A hookStack)).pre xs s0 ∗ R := by
    simp only [doReserveStrideRawSpecWithStack, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hlay⟩, hmem⟩
  rcases hs xs R s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | hfail⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [doReserveStrideRawSpecWithStack, doReserveRawSpecWithStack, xs,
      BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, Nat.mod_one, and_true]
      at hq ⊢
    exact hq
  · exact ⟨sf, hsteps, Or.inr hfail⟩

private theorem do_reserve_vec_placed_of_raw_cli [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hraw : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveSpecWithStack A hookStack)) := by
  intro x R s0 hpc hrun hpre hsp hcl
  simp only [doReserveSpecWithStack, vecU8At_eq_placed, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack)).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    ac_nf at hmem ⊢
  rcases hraw x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [doReserveRawSpecWithStack, doReserveSpecWithStack, vecU8At_eq_placed] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rwa [doReserve_post_repack]
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [doReserveRawSpecWithStack, doReserveSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSymCli (rustReallocSpec A)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpec A)) :=
  CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_placed_ok_of_fg
    (hookStack := allocHookStack) (by decide) h_panic
    (CryptoVerification.CliC.SpqrV1.Alloc.finish_grow_8_placed_ok hshim halloc hrealloc)

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_placed_ok_x
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSymCli (rustReallocSpec A)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecX A)) :=
  CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_placed_ok_of_fg
    (hookStack := extHookStack) (by decide) h_panic
    (CryptoVerification.CliC.SpqrV1.Alloc.finish_grow_8_placed_ok_x hshim halloc hrealloc)

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_raw_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSymCli (rustReallocSpec A)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec A)) :=
  do_reserve_7_raw_placed_of_stride_cli
    (CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_placed_ok h_panic hshim halloc hrealloc)

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_raw_placed_ok_x
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSymCli (rustReallocSpec A)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX A)) :=
  do_reserve_7_raw_placed_of_stride_cli (hookStack := extHookStack)
    (CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_placed_ok_x h_panic hshim halloc hrealloc)

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSymCli (rustReallocSpec A)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
  do_reserve_vec_placed_of_raw_cli
    (CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_raw_placed_ok h_panic hshim halloc hrealloc)

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_placed_ok_x
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSymCli (rustReallocSpec A)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveSpecX A)) :=
  do_reserve_vec_placed_of_raw_cli (hookStack := extHookStack)
    (CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_raw_placed_ok_x h_panic hshim halloc hrealloc)

end CryptoVerification.SpqrV1.Alloc
