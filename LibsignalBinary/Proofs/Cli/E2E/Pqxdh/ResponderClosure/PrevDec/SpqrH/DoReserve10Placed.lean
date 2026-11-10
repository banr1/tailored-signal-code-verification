/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WPp
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Handshake `finish_grow [local#9]` and `do_reserve_and_handle [local#8]`

Verifies `[LibsignalPlacement]` `<RawVecInner>::finish_grow [local#9]` (Block `522`) and
`<RawVecInner>::reserve::do_reserve_and_handle [local#8]` (Block `517`) and lifts their contracts
to `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC
open CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed
open ReserveNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable `[LibsignalPlacement]` contract for `<alloc::raw_vec::RawVecInner>::finish_grow [local#9]`
(Block `522`, `(blkPl_522).base = lsmpl.base 522`) on `lsProg_518 ext`. -/
def FinishGrow11PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 522)
    (withLsCl lsmpl (finishGrow1Spec A))

/-- Relocatable `[LibsignalPlacement]` raw 1-byte `do_reserve_and_handle [local#8]` contract
(Block `517`, `(blkPl_517).base = lsmpl.base 517`) on `lsProg_518 ext`. -/
def DoReserve10PlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 517)
    (withLsCl lsmpl (doReserveSpecX A))

/-- Relocatable `[LibsignalPlacement]` `Vec<u8>` `do_reserve_and_handle [local#8]` contract
(Block `517`, `(blkPl_517).base = lsmpl.base 517`) on `lsProg_518 ext`. -/
def DoReserve10VecPlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 517)
    (withLsCl lsmpl (doReserve1VecSpecX A))

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

private theorem stackAt_finishGrow32 (sp : BitVec 64) :
    stackAt sp finishGrow32Stack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp 16384 4 (by decide)

def finishGrow1AllocSpec (A : RustAlloc) : Spec FinishGrow1Call :=
  { finishGrow1Spec A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp finishGrow32Stack }

def finishGrow1ReallocSpec (A : RustAlloc) : Spec FinishGrow1Call :=
  { finishGrow1Spec A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp finishGrow32Stack }

theorem finish_grow_11_zero_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_522 H)
      (lsρ lsRustNoAllocShimSym) session2ShimSpecX)
    (halloc : subroutine_ok (lsProg_522 H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A extHookStack)) :
    subroutine_ok (lsProg_522 H) (blkPl_522).base
      (finishGrow1AllocSpec A) := by
  unfold finishGrow1AllocSpec finishGrow1Spec
  simp only [memRegion_24, stackAt_finishGrow32, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat, 1)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

theorem finish_grow_11_ne_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hrealloc : subroutine_ok (lsProg_522 H)
      (lsρ lsRustReallocSym) (rustReallocExternSpecWithStack A extHookStack)) :
    subroutine_ok (lsProg_522 H) (blkPl_522).base
      (finishGrow1ReallocSpec A) := by
  unfold finishGrow1ReallocSpec finishGrow1Spec
  simp only [memRegion_24, stackAt_finishGrow32, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]
    wp_done

theorem finish_grow_11_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_522 H)
      (lsρ lsRustNoAllocShimSym) session2ShimSpecX)
    (halloc : subroutine_ok (lsProg_522 H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A extHookStack))
    (hrealloc : subroutine_ok (lsProg_522 H)
      (lsρ lsRustReallocSym) (rustReallocExternSpecWithStack A extHookStack)) :
    subroutine_ok (lsProg_522 H) (blkPl_522).base
      (finishGrow1Spec A) := by
  intro x R s0 hpc hrun hpre hsp
  by_cases hcap0 : x.cap = 0#64
  · refine finish_grow_11_zero_placed_ok_of_hooks hshim halloc x R s0 hpc hrun ?_ hsp
    simp only [finishGrow1Spec, finishGrow1AllocSpec, FinishGrow1Call.oldBuf,
      hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine finish_grow_11_ne_placed_ok_of_hooks hrealloc x R s0 hpc hrun ?_ hsp
    simp only [finishGrow1Spec, finishGrow1ReallocSpec, FinishGrow1Call.oldBuf,
      hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

private theorem finish_grow_24_zero_cells_placed_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrow1Spec A)) :
    subroutine_ok P addr (finishGrow24ZeroCellsSpec A) := by
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  simp only [finishGrow24ZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrow1Call := ⟨out, 0#64, ptr, new, []⟩
  have hpre' : s0.mem ⊨ (finishGrow1Spec A).pre hcall s0 ∗ R := by
    simp only [finishGrow1Spec, hcall, FinishGrow1Call.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, fun _ => trivial, Nat.zero_le _, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  rcases hfg hcall R s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | hfail⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [finishGrow1Spec, finishGrow24ZeroCellsSpec, hcall, FinishGrow1Call.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', new, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact ⟨sf, hsteps, Or.inr hfail⟩

private theorem finish_grow_24_ne_cells_placed_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrow1Spec A)) :
    subroutine_ok P addr (finishGrow24NeCellsSpec A) := by
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  simp only [finishGrow24NeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrow1Call := ⟨out, cap, ptr, new, bs⟩
  have hpre' : s0.mem ⊨ (finishGrow1Spec A).pre hcall s0 ∗ R := by
    simp only [finishGrow1Spec, hcall, FinishGrow1Call.oldBuf, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, False.elim, hbs, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  rcases hfg hcall R s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | hfail⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [finishGrow1Spec, finishGrow24NeCellsSpec, hcall, FinishGrow1Call.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', new, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact ⟨sf, hsteps, Or.inr hfail⟩

theorem do_reserve_10_raw32_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok (lsProg_522 H) (blkPl_522).base (finishGrow1Spec A)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)) := by
  unfold withLsCodeLoaded doReserve1Raw32Spec
  simp only [stackAt_doReserve32, sepExists_sepConj_right]
  have hpanic : (lsProg_517 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
    (ls_externAt?_of_caller (sym := lsHandleErrorSym) (by decide)).trans h_panic
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
    apply SepWPp.of_sepWP (mid := (blkPl_517).base + 68#64)
    wp_steps_lscl (lsmpl.base 522)
    have hfg0 := lscall_blk (callerProg := lsProg_517 H)
      (finish_grow_24_zero_cells_placed_of_spec hfg) ‹_›
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
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
    apply SepWPp.of_sepWP (mid := (blkPl_517).base + 68#64)
    wp_steps_lscl (lsmpl.base 522)
    have hfg1 := lscall_blk (callerProg := lsProg_517 H)
      (finish_grow_24_ne_cells_placed_of_spec hfg) ‹_›
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
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

private theorem stackAt_doReserve_eq_32 (sp : BitVec 64) :
    stackAt sp doReserveStackX =
      memRegion (sp - 16496#64) 16 ∗ stackAt sp doReserve32Stack :=
  ProofLib.stackAt_split_bottom sp 16480 16 (by decide)

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem do_reserve_raw1_placed_of_raw32 [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64}
    (h32 : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1Raw32Spec A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1RawSpec A)) := by
  intro x R s0 hpc hrun hpre hsp hcl
  simp only [doReserve1RawSpec, stackAt_doReserve_eq_32, sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - 16496#64) 16
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)).pre x s0 ∗
      (btm ∗ R) := by
    simp only [doReserve1Raw32Spec, btm, sepConj_assoc]
    ac_nf at hpre ⊢
  rcases h32 x (btm ∗ R) s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [doReserve1Raw32Spec, doReserve1RawSpec,
      stackAt_doReserve_eq_32, btm, sepConj_assoc] at hq ⊢
    ac_nf at hq ⊢
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [doReserve1Raw32Spec, doReserve1RawSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_raw_placed_of_raw1 [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64}
    (h1 : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1RawSpec A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecX A)) := by
  intro x R s0 hpc hrun hpre hsp hcl
  simp only [doReserveRawSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserve1RawSpec A)).pre x s0 ∗ R := by
    simp only [doReserve1RawSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, hmem⟩
  exact h1 x R s0 hpc hrun hpre' hsp hcl

private theorem do_reserve_vec_placed_of_raw [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64}
    (hraw : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecX A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveSpecX A)) := by
  intro x R s0 hpc hrun hpre hsp hcl
  simp only [doReserveSpecX, vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserveRawSpecX A)).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecX, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    ac_nf at hmem ⊢
  rcases hraw x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [doReserveRawSpecX, doReserveSpecX, vecU8At_eq] at hq ⊢
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
    dsimp only [doReserveRawSpecX, doReserveSpecX] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_vec1_placed_of_raw1 [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64}
    (hraw : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1RawSpec A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1VecSpecX A)) := by
  intro x R s0 hpc hrun hpre hsp hcl
  simp only [doReserve1VecSpecX, vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbound⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserve1RawSpec A)).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserve1RawSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, ?_⟩
    ac_nf at hmem ⊢
  rcases hraw x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simp only [doReserve1RawSpec, doReserve1VecSpecX, doReserveSpecX, vecU8At_eq] at hq ⊢
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
    dsimp only [doReserve1RawSpec, doReserve1VecSpecX, doReserveSpecX] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem session2ShimX_of_noAllocShim {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr noAllocShimSpec) :
    subroutine_ok P addr session2ShimSpecX := by
  intro u R s0 hpc hrun hpre hsp hcl
  dsimp only [session2ShimSpecX] at hpre
  have hpre' : s0.mem ⊨ noAllocShimSpec.pre () s0 ∗ (stackAt s0.sp extHookStack ∗ R) := by
    dsimp only [noAllocShimSpec]
    rwa [emp_sepConj]
  rcases h () (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [noAllocShimSpec, session2ShimSpecX] at hq ⊢
    rwa [← sepConj_assoc] at hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem finish_grow_11_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (lsProg_522 H) (blkPl_522).base
      (finishGrow1Spec A) :=
  finish_grow_11_placed_ok_of_hooks
    (session2ShimX_of_noAllocShim (ls_hook_ok_of_mem (prog := lsProg_522 H) (i := 522) hshim))
    (rustAllocWithStack_of_rustAlloc (ls_hook_ok_of_mem (prog := lsProg_522 H) (i := 522) halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (ls_hook_ok_of_mem (prog := lsProg_522 H) (i := 522) hrealloc) (by decide) (by decide))

theorem finish_grow_11_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    FinishGrow11PlacedOkExt A H :=
  ls_subroutine_ok_cl_of_plain (callerProg := lsProg_518 H)
    (finish_grow_11_placed_ok hshim halloc hrealloc)

theorem do_reserve_10_raw32_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)) :=
  do_reserve_10_raw32_placed_ok_of_fg h_panic
    (finish_grow_11_placed_ok hshim halloc hrealloc)

theorem do_reserve_10_raw1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpec A)) :=
  do_reserve_raw1_placed_of_raw32
    (do_reserve_10_raw32_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_raw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX A)) :=
  do_reserve_raw_placed_of_raw1
    (do_reserve_10_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserveSpecX A)) :=
  do_reserve_vec_placed_of_raw
    (do_reserve_10_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_vec1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserve1VecSpecX A)) :=
  do_reserve_vec1_placed_of_raw1
    (do_reserve_10_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    DoReserve10PlacedOkExtX A H :=
  ls_subroutine_ok_cl_of_block (callerProg := lsProg_518 H)
    (do_reserve_10_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_vec_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    DoReserve10VecPlacedOkExtX A H :=
  ls_subroutine_ok_cl_of_block (callerProg := lsProg_518 H)
    (do_reserve_10_vec1_placed_ok h_panic hshim halloc hrealloc)

abbrev doReserve10_placed_ok := @do_reserve_10_placed_ok_ext_x




end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export SpqrH (
  FinishGrow11PlacedOkExt
  DoReserve10PlacedOkExtX
  DoReserve10VecPlacedOkExtX
  finish_grow_11_placed_ok_of_hooks
  finish_grow_11_placed_ok
  finish_grow_11_placed_ok_ext
  do_reserve_10_raw32_placed_ok_of_fg
  do_reserve_10_raw32_placed_ok
  do_reserve_10_raw1_placed_ok
  do_reserve_10_raw_placed_ok
  do_reserve_10_placed_ok
  do_reserve_10_vec1_placed_ok
  do_reserve_10_placed_ok_ext_x
  do_reserve_10_vec_placed_ok_ext_x
  doReserve10_placed_ok
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
