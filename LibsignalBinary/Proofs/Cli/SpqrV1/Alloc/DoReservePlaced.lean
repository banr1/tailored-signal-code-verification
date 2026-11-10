/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FinishGrowPlaced
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Relocatable `RawVecInner::do_reserve_and_handle [local#7]` (Block `460`)

Proves `do_reserve_2_raw32_placed_ok`, `do_reserve_2_raw1_placed_ok`,
`do_reserve_2_raw_placed_ok`, and `do_reserve_2_placed_ok` (plus `_x` variants) on Block `460`
calling Block `465` (`finish_grow [local#8]`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
  CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
  CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Alloc.DoReserveNorm
  CryptoVerification.Cli.SpqrV1.Alloc.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem finish_grow_24_zero_cells_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow24ZeroCellsSpecG A hookStack) :=
  finish_grow_24_zero_cells_placed_of_spec hfg

private theorem finish_grow_24_ne_cells_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow24NeCellsSpecG A hookStack) :=
  finish_grow_24_ne_cells_placed_of_spec hfg

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem stackAt_doReserve_eq_32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      memRegion (sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16 ∗
        stackAt sp ((hookStack + 32) + 64) := by
  have heq : (hookStack + 48) + 64 = ((hookStack + 32) + 64) + 16 := by omega
  rw [heq]
  exact ProofLib.stackAt_split_bottom sp ((hookStack + 32) + 64) 16 (by omega)

theorem do_reserve_2_raw32_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack A hookStack)) := by
  unfold withLsCodeLoaded doReserve1Raw32SpecWithStack
  simp only [stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  have hpanic : ((blkPC_460).rebase (blkPl_460).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at h_1 ⊢; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := (blkPl_460).base + 68#64)
    wp_steps_lscl (lsmpl.base 465)
    have hfg0 := lscall_blk (callerProg := (blkPC_460).rebase (blkPl_460).base H)
      (finish_grow_24_zero_cells_of_spec hfg) ‹_›
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
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
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_460).base + 68#64)
    wp_steps_lscl (lsmpl.base 465)
    have hfg1 := lscall_blk (callerProg := (blkPC_460).rebase (blkPl_460).base H)
      (finish_grow_24_ne_cells_of_spec hfg) ‹_›
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
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
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

private theorem do_reserve_vec_placed_of_raw [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hraw : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveSpecWithStack A hookStack)) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithStack, vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack)).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    ac_nf at hmem ⊢
  refine (hraw.to_outcome x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserveRawSpecWithStack, doReserveSpecWithStack, vecU8At_eq] at hq ⊢
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
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [doReserveRawSpecWithStack, doReserveSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_raw1_placed_of_raw32 [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64)
    (h32 : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack A hookStack)) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1RawSpecWithStack, stackAt_doReserve_eq_32_gen _ hhook, sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack A hookStack)).pre x s0 ∗
      (btm ∗ R) := by
    simp only [doReserve1Raw32SpecWithStack, btm, sepConj_assoc]
    ac_nf at hpre ⊢
  refine (h32.to_outcome x (btm ∗ R) s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack,
      stackAt_doReserve_eq_32_gen _ hhook, btm, sepConj_assoc] at hq ⊢
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_raw_placed_of_raw1 [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h1 : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack)) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack A hookStack)).pre x s0 ∗ R := by
    simp only [doReserve1RawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, hmem⟩
  exact (h1.to_outcome x R s0 hpc hrun hpre' hsp).mono_outcome fun _ hout => hout

/-- Relocatable `do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)`. -/
theorem do_reserve_2_raw32_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)) :=
  do_reserve_2_raw32_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_2_placed_ok hshim halloc hrealloc)

theorem do_reserve_2_raw32_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecX A)) :=
  do_reserve_2_raw32_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_2_placed_ok_x hshim halloc hrealloc)

/-- Relocatable `do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeLoaded lsmpl (doReserve1RawSpec A)`. -/
theorem do_reserve_2_raw1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpec A)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := allocHookStack) (by decide)
    (do_reserve_2_raw32_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw1_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpecX A)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := extHookStack) (by decide)
    (do_reserve_2_raw32_placed_ok_x h_panic hshim halloc hrealloc)

/-- Relocatable `do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeLoaded lsmpl (doReserveRawSpec A)`. -/
theorem do_reserve_2_raw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec A)) :=
  do_reserve_raw_placed_of_raw1
    (do_reserve_2_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX A)) :=
  do_reserve_raw_placed_of_raw1 (hookStack := extHookStack)
    (do_reserve_2_raw1_placed_ok_x h_panic hshim halloc hrealloc)

/-- Relocatable `do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeLoaded lsmpl (doReserveSpec A)`. -/
theorem do_reserve_2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
  do_reserve_vec_placed_of_raw
    (do_reserve_2_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserveSpecX A)) :=
  do_reserve_vec_placed_of_raw (hookStack := extHookStack)
    (do_reserve_2_raw_placed_ok_x h_panic hshim halloc hrealloc)

abbrev doReserve2_raw32_placed_ok_of_fg := @do_reserve_2_raw32_placed_ok_of_fg
abbrev doReserve2_raw32_placed_ok := @do_reserve_2_raw32_placed_ok
abbrev doReserve2_raw32_placed_ok_x := @do_reserve_2_raw32_placed_ok_x
abbrev doReserve2_raw1_placed_ok := @do_reserve_2_raw1_placed_ok
abbrev doReserve2_raw1_placed_ok_x := @do_reserve_2_raw1_placed_ok_x
abbrev doReserve2_raw_placed_ok := @do_reserve_2_raw_placed_ok
abbrev doReserve2_raw_placed_ok_x := @do_reserve_2_raw_placed_ok_x
abbrev doReserve2_placed_ok := @do_reserve_2_placed_ok
abbrev doReserve2_placed_ok_x := @do_reserve_2_placed_ok_x

end CryptoVerification.Cli.SpqrV1.Alloc
