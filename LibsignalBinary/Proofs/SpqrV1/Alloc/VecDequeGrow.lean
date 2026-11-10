/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<VecDeque<spqr::chain::ChainEpoch>>::grow`

Verifies `<alloc::collections::vec_deque::VecDeque<spqr::chain::ChainEpoch>>::grow` (`0x5f93c`,
block 353): grows the 112-byte-stride `RawVec<ChainEpoch>` buffer via `grow_one` and
handles the non-wrapping fast return (`head + len ≤ cap`), wrapping `memcpy` tail-call
(`head < cap - head`), and wrapping `memmove` shift (`cap - head ≤ head`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open GrowOneNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev vecDequeGrowName : String :=
  "<alloc::collections::vec_deque::VecDeque<spqr::chain::ChainEpoch>>::grow"

/-- Stack budget of `VecDeque<ChainEpoch>::grow` (`growOneStack + 32` = `4240` B). -/
abbrev vecDequeGrowStack : Nat := growOneStack + 32

private theorem stackAt_vecDequeGrow (sp : BitVec 64) :
    stackAt sp vecDequeGrowStack =
      stackAt (sp - 32#64) growOneStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4208 4 (by decide)
  change stackAt sp vecDequeGrowStack =
    stackAt (sp - 32#64) growOneStack ∗ cells (sp - 32#64) 4 at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, hc4]

/-- Ghost parameters `(d, cap, ptr, head, len, bs)` for `VecDeque<ChainEpoch>::grow`,
with header `[d + 0] = cap`, `[d + 8] = ptr`, `[d + 16] = head`, `[d + 24] = len`. -/
abbrev VecDequeGrowGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)

/-- Non-wrapping contract (`head.toNat + len.toNat ≤ cap.toNat`): reallocates to
`max (2 * cap.toNat) 4` slots and leaves `head` and `len` unchanged. -/
def vecDequeGrowNonwrapBsSpec (A : RustAlloc) : Spec VecDequeGrowGhost where
  pre := fun (d, cap, ptr, head, len, bs) s =>
    let newCap := max (2 * cap.toNat) 4
    ⌜s.readReg64 .x0 = d ∧ bs.length ≤ cap.toNat * 112 ∧ ptr ≠ 0#64 ∧
      head.toNat + len.toNat ≤ cap.toNat ∧
      newCap * 112 + 8 ≤ 2 ^ 63⌝ ∗
    (d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ len) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 112 - bs.length)) ∗
    A.pool ∗ stackAt s.sp vecDequeGrowStack
  post := fun (d, cap, _ptr, head, len, bs) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (d ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ len) ∗
      A.live p' (newCap * 112) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (newCap * 112 - bs.length)) ∗
    A.pool ∗ stackAt s0.sp vecDequeGrowStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Empty-`VecDeque` specialization (`cap = 0, head = 0, len = 0`), allocating 4 slots (`448` B). -/
def vecDequeGrowEmptySpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (d, ptr) s =>
    ⌜s.readReg64 .x0 = d ∧ ptr ≠ 0#64⌝ ∗
    (d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ 0#64) ∗ ((d + 24#64) ↦₆₄ 0#64) ∗
    A.pool ∗ stackAt s.sp vecDequeGrowStack
  post := fun (d, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (d ↦₆₄ 4#64) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ 0#64) ∗ ((d + 24#64) ↦₆₄ 0#64) ∗
      A.live p' 448 8 ∗ memRegion p' 448) ∗
    A.pool ∗ stackAt s0.sp vecDequeGrowStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem vec_deque_nonwrap_ule {cap head len : BitVec 64}
    (h : head.toNat + len.toNat ≤ cap.toNat) :
    head.ule (cap - len) = true := by
  have hle : len.toNat ≤ cap.toNat := by omega
  rw [BitVec.ule_eq_decide, decide_eq_true_iff, BitVec.toNat_sub_of_le hle]
  omega

/-- `VecDeque<ChainEpoch>::grow` meets `vecDequeGrowNonwrapBsSpec A`. -/
theorem vec_deque_grow_nonwrap_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
      (vecDequeGrowNonwrapBsSpec A) := by
  simp only [vecDequeGrowNonwrapBsSpec, stackAt_vecDequeGrow, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff vecDequeGrowName = 0x5a544 :=
    libsignalSessionCode_fnOff_0x5a544
  have hgrow := grow_one_chain_epoch_bs_ok_ext hA
  rw [Program.fnAddr_rel (name := vecDequeGrowName)
    hfn libsignalSessionCode_fnOff_0x5a6e0 (k := 412) (by decide)] at hgrow
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x5a544 152
  dsimp only [tripleRatchetProgAtExt] at hgrow ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr vecDequeGrowName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, len, bs⟩ := x
  dsimp only at *
  have hule := vec_deque_nonwrap_ule (cap := cap) (head := head) (len := len) (by omega)
  apply SepWPp.of_sepWP (mid := entry + 412#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ len) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hgrow
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], ‹_›, ‹_›, by change max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63; omega⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

theorem vec_deque_grow_empty_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
      (vecDequeGrowEmptySpec A) := by
  have h := vec_deque_grow_nonwrap_bs_ok_ext hA
  refine subroutine_ok_outcome_intro fun ⟨d, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (vecDequeGrowNonwrapBsSpec A).pre (d, 0#64, ptr, 0#64, 0#64, []) s0 ∗ R := by
    simp only [vecDequeGrowEmptySpec, vecDequeGrowNonwrapBsSpec,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      List.length_nil, Nat.le_refl, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, trivial, hpre.1.2, trivial, by decide⟩, hpre.2⟩
  refine h.mono_outcome (d, 0#64, ptr, 0#64, 0#64, []) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have h0 : max (2 * (0#64 : BitVec 64).toNat) 4 = 4 := rfl
    simp only [vecDequeGrowEmptySpec, vecDequeGrowNonwrapBsSpec, h0,
      Nat.sub_zero, List.length_nil, BitVec.add_zero, pointsToBytes_nil, emp_sepConj,
      sepExists_sepConj_left, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact hpost
  · exact Or.inr hfail

abbrev vec_deque_grow_ok_ext := @vec_deque_grow_nonwrap_bs_ok_ext

/-! ## Wrapping Ring-Buffer Cases -/

/-- Wrapping ghost parameters `(d, cap, ptr, head, bs_back, bs_front)` for a full ring buffer
(`len = cap`, `0 < head.toNat < cap.toNat`, `bs_back` at `[0..head)`, `bs_front` at `[head..cap)`). -/
abbrev VecDequeGrowWrapGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)

/-- Wrapping `memcpy` case (`head < cap - head`): copies `bs_back` into `[cap .. cap + head)`
and leaves `head` unchanged. -/
def vecDequeGrowWrapMemcpyBsSpec (A : RustAlloc) : Spec VecDequeGrowWrapGhost where
  pre := fun (d, cap, ptr, head, bs_back, bs_front) s =>
    let newCap := max (2 * cap.toNat) 4
    ⌜s.readReg64 .x0 = d ∧ ptr ≠ 0#64 ∧
      0 < head.toNat ∧ head.toNat < cap.toNat ∧
      head.toNat < cap.toNat - head.toNat ∧
      bs_back.length = head.toNat * 112 ∧
      bs_front.length = (cap.toNat - head.toNat) * 112 ∧
      newCap * 112 + 8 ≤ 2 ^ 63⌝ ∗
    (d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
    A.live ptr (cap.toNat * 112) 8 ∗
    (ptr ↦ₛ (bs_back ++ bs_front)) ∗
    A.pool ∗ stackAt s.sp vecDequeGrowStack
  post := fun (d, cap, _ptr, head, bs_back, bs_front) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (d ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (newCap * 112) 8 ∗
      memRegion p' (head.toNat * 112) ∗
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
      memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
        ((newCap - (cap.toNat + head.toNat)) * 112)) ∗
    A.pool ∗ stackAt s0.sp vecDequeGrowStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Wrapping `memmove` case (`cap - head ≤ head`): shifts `bs_front` to `[newCap - (cap - head) .. newCap)`
and updates `head`. -/
def vecDequeGrowWrapMemmoveBsSpec (A : RustAlloc) : Spec VecDequeGrowWrapGhost where
  pre := fun (d, cap, ptr, head, bs_back, bs_front) s =>
    let newCap := max (2 * cap.toNat) 4
    ⌜s.readReg64 .x0 = d ∧ ptr ≠ 0#64 ∧
      0 < head.toNat ∧ head.toNat < cap.toNat ∧
      cap.toNat - head.toNat ≤ head.toNat ∧
      bs_back.length = head.toNat * 112 ∧
      bs_front.length = (cap.toNat - head.toNat) * 112 ∧
      newCap * 112 + 8 ≤ 2 ^ 63⌝ ∗
    (d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
    A.live ptr (cap.toNat * 112) 8 ∗
    (ptr ↦ₛ (bs_back ++ bs_front)) ∗
    A.pool ∗ stackAt s.sp vecDequeGrowStack
  post := fun (d, cap, _ptr, head, bs_back, bs_front) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    let newHead := newCap - (cap.toNat - head.toNat)
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (d ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ BitVec.ofNat 64 newHead) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (newCap * 112) 8 ∗
      (p' ↦ₛ bs_back) ∗
      memRegion (p' + BitVec.ofNat 64 (head.toNat * 112)) ((newCap - cap.toNat) * 112) ∗
      ((p' + BitVec.ofNat 64 (newHead * 112)) ↦ₛ bs_front)) ∗
    A.pool ∗ stackAt s0.sp vecDequeGrowStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem vec_deque_wrap_ule_false {cap head : BitVec 64}
    (h : 0 < head.toNat) :
    head.ule (cap - cap) = false := by
  rw [BitVec.sub_self, BitVec.ule_eq_decide, decide_eq_false_iff_not]
  change ¬ (head.toNat ≤ 0)
  omega

private theorem vec_deque_memcpy_branch {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat) (h2 : head.toNat < cap.toNat - head.toNat) :
    (cap - head).ule head = false := by
  have hsub1 : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, hsub1]
  omega

private theorem vec_deque_memcpy_fit {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat)
    (hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63) :
    (BitVec.ofNat 64 (max (2 * cap.toNat) 4) - cap).ult head = false := by
  have hnc : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle : cap ≤ BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
    rw [BitVec.le_def, hnc]; omega
  have hsub1 : (BitVec.ofNat 64 (max (2 * cap.toNat) 4) - cap).toNat =
      max (2 * cap.toNat) 4 - cap.toNat := by
    rw [BitVec.toNat_sub_of_le hle, hnc]
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub1]
  omega

private theorem vec_deque_memmove_branch {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat) (h2 : cap.toNat - head.toNat ≤ head.toNat) :
    (cap - head).ule head = true := by
  have hsub1 : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  rw [BitVec.ule_eq_decide, decide_eq_true_iff, hsub1]
  omega

private theorem shift_128_sub_16_toNat {x : BitVec 64} (h : x.toNat * 128 < 2 ^ 64) :
    (x <<< 7 - x <<< 4).toNat = x.toNat * 112 := by
  have h7 : (x <<< 7).toNat = x.toNat * 128 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have h4 : (x <<< 4).toNat = x.toNat * 16 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hle : x <<< 4 ≤ x <<< 7 := by
    rw [BitVec.le_def, h4, h7]; omega
  rw [BitVec.toNat_sub_of_le hle, h7, h4]
  omega

private theorem listMove_append_to_end {bs1 bs2 : List (BitVec 8)} :
    listMove (bs1 ++ bs2) bs2.length 0 bs1.length =
      (bs1 ++ bs2).take bs2.length ++ bs1 := by
  unfold listMove
  have hdrop0 : (bs1 ++ bs2).drop 0 = bs1 ++ bs2 := rfl
  have htake1 : (bs1 ++ bs2).take bs1.length = bs1 := by
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop_end : (bs1 ++ bs2).drop (bs2.length + bs1.length) = [] := by
    rw [Nat.add_comm, ← List.length_append, List.drop_length]
  rw [hdrop0, htake1, hdrop_end, List.append_nil]

private theorem pointsToBytes_listMove_append_entails (base : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) :
    (base ↦ₛ listMove (bs1 ++ bs2) bs2.length 0 bs1.length) ⊢
      memRegion base bs2.length ∗ ((base + BitVec.ofNat 64 bs2.length) ↦ₛ bs1) := by
  rw [listMove_append_to_end, pointsToBytes_append]
  have hlen : ((bs1 ++ bs2).take bs2.length).length = bs2.length :=
    List.length_take_of_le (by rw [List.length_append]; omega)
  rw [hlen]
  apply sepConj_mono_left
  have hreg := pointsToBytes_entails_memRegion base ((bs1 ++ bs2).take bs2.length)
  rwa [hlen] at hreg

private theorem madd_112_eq (p x : BitVec 64) (_h : x.toNat * 112 < 2 ^ 64) :
    p + x * 112#64 = p + BitVec.ofNat 64 (x.toNat * 112) := by
  have hx : x * 112#64 = BitVec.ofNat 64 (x.toNat * 112) := by
    apply BitVec.eq_of_toNat_eq
    have h112 : (112#64 : BitVec 64).toNat = 112 := rfl
    rw [BitVec.toNat_mul, h112, BitVec.toNat_ofNat]
  rw [hx]

private def sessionMemmoveFrontToEndSpec (hookStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (base, bs_front, uninitLen) s0 =>
    ⌜s0.readReg64 .x0 = base + BitVec.ofNat 64 uninitLen ∧
      s0.readReg64 .x1 = base ∧
      (s0.readReg64 .x2).toNat = bs_front.length ∧
      uninitLen ≤ 2 ^ 64⌝ ∗
      (base ↦ₛ bs_front) ∗
      memRegion (base + BitVec.ofNat 64 bs_front.length) uninitLen ∗
      stackAt s0.sp hookStack
  post := fun (base, bs_front, uninitLen) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 uninitLen ∧ sf.trace = s0.trace⌝ ∗
      memRegion base uninitLen ∗
      ((base + BitVec.ofNat 64 uninitLen) ↦ₛ bs_front) ∗
      stackAt s0.sp hookStack

private theorem session_memmove_front_to_end_ok {prog : Program} {addr : BitVec 64}
    {hookStack : Nat} (hmm : subroutine_ok prog addr (sessionMemmoveSpec hookStack)) :
    subroutine_ok prog addr (sessionMemmoveFrontToEndSpec hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨base, bs_front, uninitLen⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [sessionMemmoveFrontToEndSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, huninit_le⟩, hmem⟩
  rw [memRegion_eq_exists_bytes (base + BitVec.ofNat 64 bs_front.length) uninitLen huninit_le,
      sepExists_sepConj_left, sepExists_sepConj_right] at hmem
  rw [satisfies_sepExists] at hmem
  obtain ⟨bs_uninit, hmem⟩ := hmem
  have hmem1 : s0.mem ⊨
      ⌜bs_uninit.length = uninitLen⌝ ∗
        (((base + BitVec.ofNat 64 bs_front.length) ↦ₛ bs_uninit) ∗
          ((base ↦ₛ bs_front) ∗ (stackAt s0.sp hookStack ∗ R))) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨hbs_uninit, hmem1⟩
  have hpre' : s0.mem ⊨
      (sessionMemmoveSpec hookStack).pre
        (base, bs_front ++ bs_uninit, uninitLen, 0, bs_front.length) s0 ∗ R := by
    dsimp only [sessionMemmoveSpec, libcMemmoveSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by rw [BitVec.add_zero]; exact hx1, hx2,
      by rw [List.length_append, hbs_uninit]; omega,
      by rw [List.length_append]; omega⟩, ?_⟩
    rw [pointsToBytes_append, sepConj_assoc]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1
  refine hmm.mono_outcome (base, bs_front ++ bs_uninit, uninitLen, 0, bs_front.length) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemmoveSpec, libcMemmoveSpec, sessionMemmoveFrontToEndSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    have hent := pointsToBytes_listMove_append_entails base bs_front bs_uninit
    rw [hbs_uninit] at hent
    have hpost2 := Satisfies.mono (sepConj_mono_left hent) hpost.2
    simpa only [sepConj_assoc] using hpost2
  · exact Or.inr hfail

set_option maxHeartbeats 800000 in
/-- `VecDeque<ChainEpoch>::grow` meets `vecDequeGrowWrapMemcpyBsSpec A`. -/
theorem vec_deque_grow_wrap_memcpy_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
      (vecDequeGrowWrapMemcpyBsSpec A) := by
  simp only [vecDequeGrowWrapMemcpyBsSpec, stackAt_vecDequeGrow, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff vecDequeGrowName = 0x5a544 :=
    libsignalSessionCode_fnOff_0x5a544
  have hgrow := grow_one_chain_epoch_bs_ok_ext hA
  rw [Program.fnAddr_rel (name := vecDequeGrowName)
    hfn libsignalSessionCode_fnOff_0x5a6e0 (k := 412) (by decide)] at hgrow
  have hmc := hA.session_memcpy_region_ok_at vecDequeGrowName
    (num% (ls_off% "memcpy" - 0x5a544)) (by rw [hfn, (ls_stub% "memcpy")])
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x5a544 152
  dsimp only [tripleRatchetProgAtExt] at hgrow hmc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr vecDequeGrowName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, bs_back, bs_front⟩ := x
  dsimp only at *
  have hhead_pos : 0 < head.toNat := ‹_›
  have hhead_lt : head.toNat < cap.toNat := ‹_›
  have hbranch : head.toNat < cap.toNat - head.toNat := ‹_›
  have hbs_back : bs_back.length = head.toNat * 112 := ‹_›
  have hbs_front : bs_front.length = (cap.toNat - head.toNat) * 112 := ‹_›
  have hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hcap_ne : cap ≠ 0#64 := by
    intro h0; rw [h0] at hhead_lt; change head.toNat < 0 at hhead_lt; omega
  have hbs_len : (bs_back ++ bs_front).length = cap.toNat * 112 := by
    rw [List.length_append, hbs_back, hbs_front]; omega
  have hule1 := vec_deque_wrap_ule_false (cap := cap) hhead_pos
  have hule2 := vec_deque_memcpy_branch hhead_lt hbranch
  have hult3 := vec_deque_memcpy_fit hhead_lt hmax
  have hsub_head : cap - (cap - head) = head := by bv_arith
  have hshift_head : (head <<< 7 - head <<< 4).toNat = head.toNat * 112 :=
    shift_128_sub_16_toNat (by omega)
  apply SepWPp.of_sepWP (mid := entry + 412#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs_back ++ bs_front))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hgrow
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], by dsimp only; omega, ‹_›, hmax⟩
    (by simp only [wp_norm, arm64_norm, Nat.sub_self, memRegion_zero,
          ite_false, sepConj_emp, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  have hmadd_cap : p' + cap * 112#64 = p' + BitVec.ofNat 64 (cap.toNat * 112) :=
    madd_112_eq p' cap (by omega)
  have hsplit_bs : (p' ↦ₛ (bs_back ++ bs_front)) =
      (p' ↦ₛ bs_back) ∗ ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) := by
    rw [pointsToBytes_append, hbs_back]
  have hsplit_reg :
      memRegion (p' + BitVec.ofNat 64 (bs_back ++ bs_front).length)
        (max (2 * cap.toNat) 4 * 112 - (bs_back ++ bs_front).length) =
      memRegion (p' + BitVec.ofNat 64 (cap.toNat * 112)) bs_back.length ∗
        memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
          ((max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112) := by
    rw [hbs_len, hbs_back]
    have hlen_eq : max (2 * cap.toNat) 4 * 112 - cap.toNat * 112 =
        head.toNat * 112 + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112 := by
      have : max (2 * cap.toNat) 4 - cap.toNat =
          head.toNat + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) := by omega
      calc max (2 * cap.toNat) 4 * 112 - cap.toNat * 112
          = (max (2 * cap.toNat) 4 - cap.toNat) * 112 := (Nat.sub_mul _ _ 112).symm
        _ = (head.toNat + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat))) * 112 := by rw [this]
        _ = head.toNat * 112 + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112 :=
          Nat.add_mul _ _ 112
    have hoff : p' + BitVec.ofNat 64 (cap.toNat * 112) + BitVec.ofNat 64 (head.toNat * 112) =
        p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    rw [hlen_eq, memRegion_split (p' + BitVec.ofNat 64 (cap.toNat * 112)) (head.toNat * 112) _ (by omega), hoff]
  rw [hsplit_bs, hsplit_reg]
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - 0x5a544))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (p' + BitVec.ofNat 64 (cap.toNat * 112), p', bs_back))
    (F := (d ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) ∗
      memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
        ((max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) growOneStack ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hmc
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := s0.readReg64 .x30)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *]⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ h => (not_satisfies_false_sepConj (sepConj_assoc _ _ _ ▸ h)).elim)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [sessionMemcpyRegionSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_hx0f, htrf⟩ => ?_
  have htr_sf : sf.trace = s0.trace := by
    rw [htrf]; simp only [wp_norm, arm64_norm, *]
  have hsp_sf : sf.sp = s0.sp := by
    rw [hspf]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩ := hcsf
  apply SepWPp.of_sepWP_ret
  have hreg_back : (p' ↦ₛ bs_back) ⊢ memRegion p' (head.toNat * 112) := by
    rw [← hbs_back]
    exact pointsToBytes_entails_memRegion p' bs_back
  have hcomb_fb :
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) ∗
        ((p' + BitVec.ofNat 64 (cap.toNat * 112)) ↦ₛ bs_back) =
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) := by
    rw [pointsToBytes_append, hbs_front]
    have hoff : p' + BitVec.ofNat 64 (head.toNat * 112) +
        BitVec.ofNat 64 ((cap.toNat - head.toNat) * 112) =
        p' + BitVec.ofNat 64 (cap.toNat * 112) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
      congr 2; omega
    rw [hoff]
  apply SepWP.fold hreg_back (by sep_focus)
  apply SepWP.fold (Entails.of_eq hcomb_fb) (by sep_focus)
  wp_done

set_option maxHeartbeats 800000 in
/-- `VecDeque<ChainEpoch>::grow` meets `vecDequeGrowWrapMemmoveBsSpec A`. -/
theorem vec_deque_grow_wrap_memmove_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
      (vecDequeGrowWrapMemmoveBsSpec A) := by
  simp only [vecDequeGrowWrapMemmoveBsSpec, stackAt_vecDequeGrow, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff vecDequeGrowName = 0x5a544 :=
    libsignalSessionCode_fnOff_0x5a544
  have hgrow := grow_one_chain_epoch_bs_ok_ext hA
  rw [Program.fnAddr_rel (name := vecDequeGrowName)
    hfn libsignalSessionCode_fnOff_0x5a6e0 (k := 412) (by decide)] at hgrow
  have hmm := session_memmove_front_to_end_ok
    (hA.session_memmove_ok_at vecDequeGrowName
      (num% (ls_off% "memmove" - 0x5a544)) growOneStack (by rw [hfn, (ls_stub% "memmove")]))
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x5a544 152
  dsimp only [tripleRatchetProgAtExt] at hgrow hmm ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr vecDequeGrowName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, bs_back, bs_front⟩ := x
  dsimp only at *
  have hhead_pos : 0 < head.toNat := ‹_›
  have hhead_lt : head.toNat < cap.toNat := ‹_›
  have hbranch : cap.toNat - head.toNat ≤ head.toNat := ‹_›
  have hbs_back : bs_back.length = head.toNat * 112 := ‹_›
  have hbs_front : bs_front.length = (cap.toNat - head.toNat) * 112 := ‹_›
  have hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hcap_ne : cap ≠ 0#64 := by
    intro h0; rw [h0] at hhead_lt; change head.toNat < 0 at hhead_lt; omega
  have hbs_len : (bs_back ++ bs_front).length = cap.toNat * 112 := by
    rw [List.length_append, hbs_back, hbs_front]; omega
  have hule1 := vec_deque_wrap_ule_false (cap := cap) hhead_pos
  have hule2 := vec_deque_memmove_branch hhead_lt hbranch
  have hsub_head : cap - (cap - head) = head := by bv_arith
  have hnc : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hch : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have hle_nc : cap - head ≤ BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
    rw [BitVec.le_def, hch, hnc]; omega
  have hsub_newHead :
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) - (cap - head) =
        BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hle_nc, hnc, hch,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift_front : ((cap - head) <<< 7 - (cap - head) <<< 4).toNat =
      (cap.toNat - head.toNat) * 112 := by
    rw [← hch]
    exact shift_128_sub_16_toNat (by omega)
  apply SepWPp.of_sepWP (mid := entry + 412#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs_back ++ bs_front))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hgrow
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], by dsimp only; omega, ‹_›, hmax⟩
    (by simp only [wp_norm, arm64_norm, Nat.sub_self, memRegion_zero,
          ite_false, sepConj_emp, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  have hmadd_head : p' + head * 112#64 = p' + BitVec.ofNat 64 (head.toNat * 112) :=
    madd_112_eq p' head (by omega)
  have hmadd_newHead :
      p' + BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112#64 =
        p' + BitVec.ofNat 64 (head.toNat * 112) +
          BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - cap.toNat) * 112) := by
    have h1 := madd_112_eq p' (BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat))) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 2; omega
  have hsplit_bs : (p' ↦ₛ (bs_back ++ bs_front)) =
      (p' ↦ₛ bs_back) ∗ ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) := by
    rw [pointsToBytes_append, hbs_back]
  have hreg_eq :
      memRegion (p' + BitVec.ofNat 64 (bs_back ++ bs_front).length)
        (max (2 * cap.toNat) 4 * 112 - (bs_back ++ bs_front).length) =
      memRegion (p' + BitVec.ofNat 64 (head.toNat * 112) + BitVec.ofNat 64 bs_front.length)
        ((max (2 * cap.toNat) 4 - cap.toNat) * 112) := by
    rw [hbs_len, hbs_front, ← Nat.sub_mul, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 3; omega
  rw [hsplit_bs, hreg_eq]
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memmove" - 0x5a544))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame
    (x := (p' + BitVec.ofNat 64 (head.toNat * 112), bs_front,
           (max (2 * cap.toNat) 4 - cap.toNat) * 112))
    (F := (d ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      (p' ↦ₛ bs_back) ∗ A.pool ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hmm
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 136#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by dsimp only; omega⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ h => (not_satisfies_false_sepConj (sepConj_assoc _ _ _ ▸ h)).elim)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [sessionMemmoveFrontToEndSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_hx0f, htrf⟩ => ?_
  have htr_sf : sf.trace = s0.trace := by
    rw [htrf]; simp only [wp_norm, arm64_norm, *]
  have hsp_sf : sf.sp = s0.sp - 32#64 := by
    rw [hspf]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19f_eq, hx20f_eq, hx21f_eq, hx22f_eq, hx23f_eq, hx24f_eq, hx25f_eq, hx26f_eq, hx27f_eq, hx28f_eq, hx29f_eq, hvregsf⟩ := hcsf
  have hx19f : sf.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19f_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20f : sf.readReg64 (Reg.gpr 20#5) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) := by
    rw [hx20f_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29f : sf.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sf.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29f_eq]; simp only [wp_norm, arm64_norm, *]
  have hoff_nh :
      p' + BitVec.ofNat 64 (head.toNat * 112) +
        BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - cap.toNat) * 112) =
      p' + BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 2; omega
  rw [hoff_nh]
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

/-! ## High-Level `ChainProofs.vecDequeGrowSpec` -/

private theorem stackAt_extHookStack_vecDequeGrow (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp vecDequeGrowStack ∗ memRegion (sp - 16384#64) 12144 := by
  have hsplit : stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12144 ∗ stackAt sp vecDequeGrowStack := by
    change memRegion (sp - 16384#64) 16384 =
      memRegion (sp - 16384#64) 12144 ∗ memRegion (sp - 4240#64) 4240
    rw [ProofLib.memRegion_split (sp - 16384#64) 12144 4240 (by decide),
      bv_sub_add_lit sp 16384 12144 (by decide)]
  rw [hsplit, sepConj_comm]

/-- `VecDeque<ChainEpoch>::grow` meets `ChainProofs.vecDequeGrowSpec A`. -/
theorem vec_deque_grow_spec_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ChainProofs.vecDequeGrowName)
      (ChainProofs.vecDequeGrowSpec A) := by
  change subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr vecDequeGrowName)
    (ChainProofs.vecDequeGrowSpec A)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [ChainProofs.vecDequeGrowSpec, ChainProofs.newCapChainEpoch] at hpre ⊢
  simp only [stackAt_extHookStack_vecDequeGrow, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hmax⟩, hmem⟩
  have hmax8 : max (2 * x.cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by
    change max (2 * x.cap.toNat) 4 * 112 < 2 ^ 63 at hmax
    omega
  by_cases hhead0 : x.head = 0#64
  · rw [hhead0] at hmem
    have hmem1 := Satisfies.mono
      (sepConj_mono_left (vecDequeAt_head_zero_entails_bytes A x.v x.cap x.ptr x.xs hlen)) hmem
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hmem1
    rcases hmem1 with ⟨bs, ⟨hbs, hbs_len, hptr⟩, hmem1⟩
    let F := chainEpochHeaps A x.xs ∗ memRegion (s0.sp - 16384#64) 12144
    have hpre' : s0.mem ⊨
        (vecDequeGrowNonwrapBsSpec A).pre (x.v, x.cap, x.ptr, 0#64, x.cap, bs) s0 ∗ (F ∗ R) := by
      dsimp only [vecDequeGrowNonwrapBsSpec, F]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, by omega, hptr, by change 0 + x.cap.toNat ≤ x.cap.toNat; omega, hmax8⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1
    refine (vec_deque_grow_nonwrap_bs_ok_ext hA).mono_outcome
      (x.v, x.cap, x.ptr, 0#64, x.cap, bs) (F ∗ R)
      s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [vecDequeGrowNonwrapBsSpec, F] at hpost
      simp only [stackAt_extHookStack_vecDequeGrow, sepExists_sepConj_left,
        sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
      refine ⟨p', 0#64, htr, fun _ => rfl, ?_⟩
      have hpost1 : sf.mem ⊨
          ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
            ((x.v + 16#64) ↦₆₄ 0#64) ∗ ((x.v + 24#64) ↦₆₄ x.cap) ∗
            A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
            (p' ↦ₛ bs) ∗
            memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * x.cap.toNat) 4 * 112 - bs.length) ∗
            chainEpochHeaps A x.xs) ∗
          (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗
            memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      have hpost2 := Satisfies.mono
        (sepConj_mono_left (vecDequeAt_head_zero_of_post A x.v x.cap p' x.xs hlen hbs hmax hp'))
        hpost1
      simpa only [sepConj_assoc] using hpost2
    · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
        (by simpa only [vecDequeGrowNonwrapBsSpec, sepConj_assoc] using hpost)⟩)
    · exact (allowPanic_not_exited hpost).elim
    · exact (allowPanic_not_exited hpost).elim
  · have hhead_pos : 0 < x.head.toNat := by
      refine Nat.pos_of_ne_zero fun h0 => hhead0 ?_
      exact BitVec.eq_of_toNat_eq h0
    have hmem1 := Satisfies.mono
      (sepConj_mono_left (vecDequeAt_wrap_entails_bytes A x.v x.cap x.ptr x.head x.xs hlen hhead_pos))
      hmem
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hmem1
    rcases hmem1 with ⟨bs_back, bs_front,
      ⟨hhead_lt, hptr, hbs_back, hbs_front, hlen_back, hlen_front⟩, hmem1⟩
    let F := chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
      chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat)) ∗
      memRegion (s0.sp - 16384#64) 12144
    by_cases hcmp : x.head.toNat < x.cap.toNat - x.head.toNat
    · have hpre' : s0.mem ⊨
          (vecDequeGrowWrapMemcpyBsSpec A).pre
            (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) s0 ∗ (F ∗ R) := by
        dsimp only [vecDequeGrowWrapMemcpyBsSpec, F]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hptr, hhead_pos, hhead_lt, hcmp, hlen_back, hlen_front, hmax8⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1
      refine (vec_deque_grow_wrap_memcpy_bs_ok_ext hA).mono_outcome
        (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) (F ∗ R)
        s0 hpc hrun hpre' hsp ?_
      rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [vecDequeGrowWrapMemcpyBsSpec, F] at hpost
        simp only [stackAt_extHookStack_vecDequeGrow, sepExists_sepConj_left,
          sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
        refine ⟨p', x.head, htr, fun h0 => (hhead0 h0).elim, ?_⟩
        have hpost1 : sf.mem ⊨
            ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
              ((x.v + 16#64) ↦₆₄ x.head) ∗ ((x.v + 24#64) ↦₆₄ x.cap) ∗
              A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
              memRegion p' (x.head.toNat * 112) ∗
              ((p' + BitVec.ofNat 64 (x.head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
              memRegion (p' + BitVec.ofNat 64 ((x.cap.toNat + x.head.toNat) * 112))
                ((max (2 * x.cap.toNat) 4 - (x.cap.toNat + x.head.toNat)) * 112) ∗
              chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
              chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat))) ∗
            (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗
              memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
        have hpost2 := Satisfies.mono
          (sepConj_mono_left (vecDequeAt_wrap_memcpy_of_post A x.v x.cap p' x.head x.xs
            hlen hhead_pos hcmp hbs_back hbs_front hmax hp'))
          hpost1
        simpa only [sepConj_assoc] using hpost2
      · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
          (by simpa only [vecDequeGrowWrapMemcpyBsSpec, sepConj_assoc] using hpost)⟩)
      · exact (allowPanic_not_exited hpost).elim
      · exact (allowPanic_not_exited hpost).elim
    · have hge : x.cap.toNat - x.head.toNat ≤ x.head.toNat := by omega
      have hpre' : s0.mem ⊨
          (vecDequeGrowWrapMemmoveBsSpec A).pre
            (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) s0 ∗ (F ∗ R) := by
        dsimp only [vecDequeGrowWrapMemmoveBsSpec, F]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hptr, hhead_pos, hhead_lt, hge, hlen_back, hlen_front, hmax8⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1
      refine (vec_deque_grow_wrap_memmove_bs_ok_ext hA).mono_outcome
        (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) (F ∗ R)
        s0 hpc hrun hpre' hsp ?_
      rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [vecDequeGrowWrapMemmoveBsSpec, F] at hpost
        simp only [stackAt_extHookStack_vecDequeGrow, sepExists_sepConj_left,
          sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
        refine ⟨p', BitVec.ofNat 64 (max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat)),
          htr, fun h0 => (hhead0 h0).elim, ?_⟩
        have hpost1 : sf.mem ⊨
            ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
              ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat))) ∗
              ((x.v + 24#64) ↦₆₄ x.cap) ∗
              A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
              (p' ↦ₛ bs_back) ∗
              memRegion (p' + BitVec.ofNat 64 (x.head.toNat * 112))
                ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 112) ∗
              ((p' + BitVec.ofNat 64 ((max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat)) * 112)) ↦ₛ bs_front) ∗
              chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
              chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat))) ∗
            (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗
              memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
        have hpost2 := Satisfies.mono
          (sepConj_mono_left (vecDequeAt_wrap_memmove_of_post A x.v x.cap p' x.head x.xs
            hlen hhead_pos hhead_lt hge hbs_back hbs_front hmax hp'))
          hpost1
        simpa only [sepConj_assoc] using hpost2
      · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
          (by simpa only [vecDequeGrowWrapMemmoveBsSpec, sepConj_assoc] using hpost)⟩)
      · exact (allowPanic_not_exited hpost).elim
      · exact (allowPanic_not_exited hpost).elim

theorem vec_deque_grow_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    ChainProofs.VecDequeGrowOkX img A ext :=
  subroutine_ok_inImage img (vec_deque_grow_spec_ok_ext hA)

theorem vec_deque_grow_ok_x_tripleRatchetExterns {img : Obj.Image} (C : Crypto) {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    ChainProofs.VecDequeGrowOkX img A (tripleRatchetExterns C ctl abs) :=
  vec_deque_grow_ok_x (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)

/-! ## Relocatable Contracts (Block 353) -/

private def growOneChainEpochBsMemSpec (A : RustAlloc) (m : Memory) : Spec GrowGhost :=
  { growOneChainEpochBsSpec A with
    pre := fun (v, cap, ptr, bs) s =>
      ⌜s.mem = m ∧ s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * 112 ∧ ptr ≠ 0#64 ∧
        max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp
       else A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 112 - bs.length)) ∗
      A.pool ∗ stackAt s.sp growOneStack }

private theorem lscall_grow_one_chain_epoch [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {m : Memory}
    (hgrow : subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochBsSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (lsmpl.base 356) (growOneChainEpochBsMemSpec A m) := by
  refine subroutine_ok_mono
    (lscall_blk_cl (callerProg := (blkPC_353).rebase (blkPl_353).base H) hgrow hcl)
    (fun (v, cap, ptr, bs) R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [growOneChainEpochBsMemSpec, withMemEq, growOneChainEpochBsSpec, growOneStrideBsSpec] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hpure⟩, hmem⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpure, hmem⟩

private theorem intro_withLsCodeLoaded {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

/-- Block 353 meets `withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec A)`. -/
theorem vec_deque_grow_nonwrap_bs_placed_ok_of_grow [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hgrow : subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochBsSpec A))) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec A)) := by
  unfold withLsCodeLoaded
  simp only [vecDequeGrowNonwrapBsSpec, stackAt_vecDequeGrow, sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, len, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hule := vec_deque_nonwrap_ule (cap := cap) (head := head) (len := len) (by omega)
  apply SepWPp.of_sepWP (mid := lsmpl.base 356)
  wp_steps_lscl (lsmpl.base 356)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ len) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (lscall_grow_one_chain_epoch hgrow ‹_›)
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := (blkPl_353).base + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      ‹_›, ‹_›, by omega⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsMemSpec, growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

theorem vec_deque_grow_nonwrap_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec A)) :=
  vec_deque_grow_nonwrap_bs_placed_ok_of_grow
    (grow_one_chain_epoch_bs_placed_ok h_panic hshim halloc hrealloc)

theorem vec_deque_grow_empty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowEmptySpec A)) := by
  have h := vec_deque_grow_nonwrap_bs_placed_ok h_panic hshim halloc hrealloc
  refine subroutine_ok_outcome_intro fun ⟨d, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec A)).pre (d, 0#64, ptr, 0#64, 0#64, []) s0 ∗ R := by
    simp only [vecDequeGrowEmptySpec, vecDequeGrowNonwrapBsSpec,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      List.length_nil, Nat.le_refl, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, trivial, hpre.1.2, trivial, by decide⟩, hpre.2⟩
  refine h.mono_outcome (d, 0#64, ptr, 0#64, 0#64, []) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have h0 : max (2 * (0#64 : BitVec 64).toNat) 4 = 4 := rfl
    simp only [vecDequeGrowEmptySpec, vecDequeGrowNonwrapBsSpec, h0,
      Nat.sub_zero, List.length_nil, BitVec.add_zero, pointsToBytes_nil, emp_sepConj,
      sepExists_sepConj_left, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact hpost
  · exact Or.inr hfail

set_option maxHeartbeats 800000 in
/-- Block 353 meets `withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec A)`. -/
theorem vec_deque_grow_wrap_memcpy_bs_placed_ok_of_grow [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hgrow : subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochBsSpec A)))
    (hmc : subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (lsρ spqrMemcpySym) sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec A)) := by
  unfold withLsCodeLoaded
  simp only [vecDequeGrowWrapMemcpyBsSpec, stackAt_vecDequeGrow, sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, bs_back, bs_front⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hhead_pos : 0 < head.toNat := ‹_›
  have hhead_lt : head.toNat < cap.toNat := ‹_›
  have hbranch : head.toNat < cap.toNat - head.toNat := ‹_›
  have hbs_back : bs_back.length = head.toNat * 112 := ‹_›
  have hbs_front : bs_front.length = (cap.toNat - head.toNat) * 112 := ‹_›
  have hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hcap_ne : cap ≠ 0#64 := by
    intro h0; rw [h0] at hhead_lt; change head.toNat < 0 at hhead_lt; omega
  have hbs_len : (bs_back ++ bs_front).length = cap.toNat * 112 := by
    rw [List.length_append, hbs_back, hbs_front]; omega
  have hule1 := vec_deque_wrap_ule_false (cap := cap) hhead_pos
  have hule2 := vec_deque_memcpy_branch hhead_lt hbranch
  have hult3 := vec_deque_memcpy_fit hhead_lt hmax
  have hsub_head : cap - (cap - head) = head := by bv_arith
  have hshift_head : (head <<< 7 - head <<< 4).toNat = head.toNat * 112 :=
    shift_128_sub_16_toNat (by omega)
  apply SepWPp.of_sepWP (mid := lsmpl.base 356)
  wp_steps_lscl (lsmpl.base 356)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs_back ++ bs_front))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (lscall_grow_one_chain_epoch hgrow ‹_›)
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := (blkPl_353).base + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by omega, ‹_›, hmax⟩
    (by simp only [wp_norm, arm64_norm, Nat.sub_self, memRegion_zero,
          ite_false, sepConj_emp, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsMemSpec, growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  have hmadd_cap : p' + cap * 112#64 = p' + BitVec.ofNat 64 (cap.toNat * 112) :=
    madd_112_eq p' cap (by omega)
  have hsplit_bs : (p' ↦ₛ (bs_back ++ bs_front)) =
      (p' ↦ₛ bs_back) ∗ ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) := by
    rw [pointsToBytes_append, hbs_back]
  have hsplit_reg :
      memRegion (p' + BitVec.ofNat 64 (bs_back ++ bs_front).length)
        (max (2 * cap.toNat) 4 * 112 - (bs_back ++ bs_front).length) =
      memRegion (p' + BitVec.ofNat 64 (cap.toNat * 112)) bs_back.length ∗
        memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
          ((max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112) := by
    rw [hbs_len, hbs_back]
    have hlen_eq : max (2 * cap.toNat) 4 * 112 - cap.toNat * 112 =
        head.toNat * 112 + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112 := by
      have : max (2 * cap.toNat) 4 - cap.toNat =
          head.toNat + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) := by omega
      calc max (2 * cap.toNat) 4 * 112 - cap.toNat * 112
          = (max (2 * cap.toNat) 4 - cap.toNat) * 112 := (Nat.sub_mul _ _ 112).symm
        _ = (head.toNat + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat))) * 112 := by rw [this]
        _ = head.toNat * 112 + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112 :=
          Nat.add_mul _ _ 112
    have hoff : p' + BitVec.ofNat 64 (cap.toNat * 112) + BitVec.ofNat 64 (head.toNat * 112) =
        p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    rw [hlen_eq, memRegion_split (p' + BitVec.ofNat 64 (cap.toNat * 112)) (head.toNat * 112) _ (by omega), hoff]
  rw [hsplit_bs, hsplit_reg]
  apply SepWPp.of_sepWP (mid := lsρ spqrMemcpySym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (p' + BitVec.ofNat 64 (cap.toNat * 112), p', bs_back))
    (F := (d ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) ∗
      memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
        ((max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) growOneStack ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hmc
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := s0.readReg64 .x30)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *]⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ h => (not_satisfies_false_sepConj (sepConj_assoc _ _ _ ▸ h)).elim)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [sessionMemcpyRegionSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_hx0f, htrf⟩ => ?_
  have htr_sf : sf.trace = s0.trace := by
    rw [htrf]; simp only [wp_norm, arm64_norm, *]
  have hsp_sf : sf.sp = s0.sp := by
    rw [hspf]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩ := hcsf
  apply SepWPp.of_sepWP_ret
  have hreg_back : (p' ↦ₛ bs_back) ⊢ memRegion p' (head.toNat * 112) := by
    rw [← hbs_back]
    exact pointsToBytes_entails_memRegion p' bs_back
  have hcomb_fb :
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) ∗
        ((p' + BitVec.ofNat 64 (cap.toNat * 112)) ↦ₛ bs_back) =
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) := by
    rw [pointsToBytes_append, hbs_front]
    have hoff : p' + BitVec.ofNat 64 (head.toNat * 112) +
        BitVec.ofNat 64 ((cap.toNat - head.toNat) * 112) =
        p' + BitVec.ofNat 64 (cap.toNat * 112) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
      congr 2; omega
    rw [hoff]
  apply SepWP.fold hreg_back (by sep_focus)
  apply SepWP.fold (Entails.of_eq hcomb_fb) (by sep_focus)
  wp_done

theorem vec_deque_grow_wrap_memcpy_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec A)) :=
  vec_deque_grow_wrap_memcpy_bs_placed_ok_of_grow
    (grow_one_chain_epoch_bs_placed_ok h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmc)

set_option maxHeartbeats 800000 in
/-- Block 353 meets `withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec A)`. -/
theorem vec_deque_grow_wrap_memmove_bs_placed_ok_of_grow [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hgrow : subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochBsSpec A)))
    (hmm : subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (lsρ spqrMemmoveSym) (sessionMemmoveSpec growOneStack)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec A)) := by
  unfold withLsCodeLoaded
  simp only [vecDequeGrowWrapMemmoveBsSpec, stackAt_vecDequeGrow, sepExists_sepConj_right]
  have hmm_fe := session_memmove_front_to_end_ok hmm
  wpp_init x s0
  obtain ⟨d, cap, ptr, head, bs_back, bs_front⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hhead_pos : 0 < head.toNat := ‹_›
  have hhead_lt : head.toNat < cap.toNat := ‹_›
  have hbranch : cap.toNat - head.toNat ≤ head.toNat := ‹_›
  have hbs_back : bs_back.length = head.toNat * 112 := ‹_›
  have hbs_front : bs_front.length = (cap.toNat - head.toNat) * 112 := ‹_›
  have hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hcap_ne : cap ≠ 0#64 := by
    intro h0; rw [h0] at hhead_lt; change head.toNat < 0 at hhead_lt; omega
  have hbs_len : (bs_back ++ bs_front).length = cap.toNat * 112 := by
    rw [List.length_append, hbs_back, hbs_front]; omega
  have hule1 := vec_deque_wrap_ule_false (cap := cap) hhead_pos
  have hule2 := vec_deque_memmove_branch hhead_lt hbranch
  have hsub_head : cap - (cap - head) = head := by bv_arith
  have hnc : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hch : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have hle_nc : cap - head ≤ BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
    rw [BitVec.le_def, hch, hnc]; omega
  have hsub_newHead :
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) - (cap - head) =
        BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hle_nc, hnc, hch,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift_front : ((cap - head) <<< 7 - (cap - head) <<< 4).toNat =
      (cap.toNat - head.toNat) * 112 := by
    rw [← hch]
    exact shift_128_sub_16_toNat (by omega)
  apply SepWPp.of_sepWP (mid := lsmpl.base 356)
  wp_steps_lscl (lsmpl.base 356)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (d, cap, ptr, bs_back ++ bs_front))
    (F := ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (lscall_grow_one_chain_epoch hgrow ‹_›)
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := (blkPl_353).base + 24#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by omega, ‹_›, hmax⟩
    (by simp only [wp_norm, arm64_norm, Nat.sub_self, memRegion_zero,
          ite_false, sepConj_emp, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ hm => allowPanic_frame id hm)
    fun sm hpcm hrunm hspm hcsm => ?_
  have hsp_sm : sm.sp = s0.sp - 32#64 := by
    rw [hspm]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregsm⟩ := hcsm
  have hx19 : sm.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20 : sm.readReg64 (Reg.gpr 20#5) = cap := by
    rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
  dsimp only [growOneChainEpochBsMemSpec, growOneChainEpochBsSpec, growOneStrideBsSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun p' => ?_
  refine SepWPp.pure_elim fun htrace => ?_
  refine SepWPp.pure_elim fun ⟨hp', halign⟩ => ?_
  have htr_sm : sm.trace = s0.trace := by
    rw [htrace]; simp only [wp_norm, arm64_norm, *]
  have hmadd_head : p' + head * 112#64 = p' + BitVec.ofNat 64 (head.toNat * 112) :=
    madd_112_eq p' head (by omega)
  have hmadd_newHead :
      p' + BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112#64 =
        p' + BitVec.ofNat 64 (head.toNat * 112) +
          BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - cap.toNat) * 112) := by
    have h1 := madd_112_eq p' (BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat))) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 2; omega
  have hsplit_bs : (p' ↦ₛ (bs_back ++ bs_front)) =
      (p' ↦ₛ bs_back) ∗ ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) := by
    rw [pointsToBytes_append, hbs_back]
  have hreg_eq :
      memRegion (p' + BitVec.ofNat 64 (bs_back ++ bs_front).length)
        (max (2 * cap.toNat) 4 * 112 - (bs_back ++ bs_front).length) =
      memRegion (p' + BitVec.ofNat 64 (head.toNat * 112) + BitVec.ofNat 64 bs_front.length)
        ((max (2 * cap.toNat) 4 - cap.toNat) * 112) := by
    rw [hbs_len, hbs_front, ← Nat.sub_mul, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 3; omega
  rw [hsplit_bs, hreg_eq]
  apply SepWPp.of_sepWP (mid := lsρ spqrMemmoveSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame
    (x := (p' + BitVec.ofNat 64 (head.toNat * 112), bs_front,
           (max (2 * cap.toNat) 4 - cap.toNat) * 112))
    (F := (d ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      (p' ↦ₛ bs_back) ∗ A.pool ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    hmm_fe
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := (blkPl_353).base + 136#64)
    (by simp only [wp_norm, arm64_norm, *])
    rfl
    ⟨by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by dsimp only; omega⟩
    (by simp only [wp_norm, arm64_norm, *]; ac_rfl)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ h => (not_satisfies_false_sepConj (sepConj_assoc _ _ _ ▸ h)).elim)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [sessionMemmoveFrontToEndSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_hx0f, htrf⟩ => ?_
  have htr_sf : sf.trace = s0.trace := by
    rw [htrf]; simp only [wp_norm, arm64_norm, *]
  have hsp_sf : sf.sp = s0.sp - 32#64 := by
    rw [hspf]; simp only [wp_norm, arm64_norm, *]
  obtain ⟨hx19f_eq, hx20f_eq, hx21f_eq, hx22f_eq, hx23f_eq, hx24f_eq, hx25f_eq, hx26f_eq, hx27f_eq, hx28f_eq, hx29f_eq, hvregsf⟩ := hcsf
  have hx19f : sf.readReg64 (Reg.gpr 19#5) = d := by
    rw [hx19f_eq]; simp only [wp_norm, arm64_norm, *]
  have hx20f : sf.readReg64 (Reg.gpr 20#5) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) := by
    rw [hx20f_eq]; simp only [wp_norm, arm64_norm, *]
  have hx29f : sf.readReg64 (Reg.gpr 29#5) = s0.sp - 32#64 := by
    change sf.readReg64 Reg.fp = s0.sp - 32#64
    rw [hx29f_eq]; simp only [wp_norm, arm64_norm, *]
  have hoff_nh :
      p' + BitVec.ofNat 64 (head.toNat * 112) +
        BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - cap.toNat) * 112) =
      p' + BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 2; omega
  rw [hoff_nh]
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

theorem vec_deque_grow_wrap_memmove_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmm : HookSat H spqrMemmoveSym (sessionMemmoveSpec growOneStack)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec A)) :=
  vec_deque_grow_wrap_memmove_bs_placed_ok_of_grow
    (grow_one_chain_epoch_bs_placed_ok h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmm)

/-- Block 353 meets `withLsCodeLoaded lsmpl (ChainProofs.vecDequeGrowSpec A)`. -/
theorem vec_deque_grow_spec_placed_ok_of_branches [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64}
    (h_nonwrap : subroutine_ok P addr (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec A)))
    (h_memcpy : subroutine_ok P addr (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec A)))
    (h_memmove : subroutine_ok P addr (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (ChainProofs.vecDequeGrowSpec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hsp => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre0
  dsimp only [withLsCodeLoaded, ChainProofs.vecDequeGrowSpec, ChainProofs.newCapChainEpoch] at hpre ⊢
  simp only [stackAt_extHookStack_vecDequeGrow, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hmax⟩, hmem⟩
  have hmax8 : max (2 * x.cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by
    change max (2 * x.cap.toNat) 4 * 112 < 2 ^ 63 at hmax
    omega
  by_cases hhead0 : x.head = 0#64
  · rw [hhead0] at hmem
    have hmem1 := Satisfies.mono
      (sepConj_mono_left (vecDequeAt_head_zero_entails_bytes A x.v x.cap x.ptr x.xs hlen)) hmem
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hmem1
    rcases hmem1 with ⟨bs, ⟨hbs, hbs_len, hptr⟩, hmem1⟩
    let F := chainEpochHeaps A x.xs ∗ memRegion (s0.sp - 16384#64) 12144
    have hpre' : s0.mem ⊨
        (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec A)).pre (x.v, x.cap, x.ptr, 0#64, x.cap, bs) s0 ∗ (F ∗ R) := by
      refine intro_withLsCodeLoaded hcl0 ?_
      dsimp only [vecDequeGrowNonwrapBsSpec, F]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, by omega, hptr, by change 0 + x.cap.toNat ≤ x.cap.toNat; omega, hmax8⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1
    refine h_nonwrap.mono_outcome (x.v, x.cap, x.ptr, 0#64, x.cap, bs) (F ∗ R)
      s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, vecDequeGrowNonwrapBsSpec, F] at hpost
      simp only [stackAt_extHookStack_vecDequeGrow, sepExists_sepConj_left,
        sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
      refine ⟨p', 0#64, htr, fun _ => rfl, ?_⟩
      have hpost1 : sf.mem ⊨
          ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
            ((x.v + 16#64) ↦₆₄ 0#64) ∗ ((x.v + 24#64) ↦₆₄ x.cap) ∗
            A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
            (p' ↦ₛ bs) ∗
            memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * x.cap.toNat) 4 * 112 - bs.length) ∗
            chainEpochHeaps A x.xs) ∗
          (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗
            memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      have hpost2 := Satisfies.mono
        (sepConj_mono_left (vecDequeAt_head_zero_of_post A x.v x.cap p' x.xs hlen hbs hmax hp'))
        hpost1
      simpa only [sepConj_assoc] using hpost2
    · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
        (by simpa only [withLsCodeLoaded, vecDequeGrowNonwrapBsSpec, sepConj_assoc] using hpost)⟩)
    · exact (allowPanic_not_exited hpost).elim
    · exact (allowPanic_not_exited hpost).elim
  · have hhead_pos : 0 < x.head.toNat := by
      refine Nat.pos_of_ne_zero fun h0 => hhead0 ?_
      exact BitVec.eq_of_toNat_eq h0
    have hmem1 := Satisfies.mono
      (sepConj_mono_left (vecDequeAt_wrap_entails_bytes A x.v x.cap x.ptr x.head x.xs hlen hhead_pos))
      hmem
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hmem1
    rcases hmem1 with ⟨bs_back, bs_front,
      ⟨hhead_lt, hptr, hbs_back, hbs_front, hlen_back, hlen_front⟩, hmem1⟩
    let F := chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
      chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat)) ∗
      memRegion (s0.sp - 16384#64) 12144
    by_cases hcmp : x.head.toNat < x.cap.toNat - x.head.toNat
    · have hpre' : s0.mem ⊨
          (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec A)).pre
            (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) s0 ∗ (F ∗ R) := by
        refine intro_withLsCodeLoaded hcl0 ?_
        dsimp only [vecDequeGrowWrapMemcpyBsSpec, F]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hptr, hhead_pos, hhead_lt, hcmp, hlen_back, hlen_front, hmax8⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1
      refine h_memcpy.mono_outcome
        (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) (F ∗ R)
        s0 hpc hrun hpre' hsp ?_
      rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withLsCodeLoaded, vecDequeGrowWrapMemcpyBsSpec, F] at hpost
        simp only [stackAt_extHookStack_vecDequeGrow, sepExists_sepConj_left,
          sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
        refine ⟨p', x.head, htr, fun h0 => (hhead0 h0).elim, ?_⟩
        have hpost1 : sf.mem ⊨
            ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
              ((x.v + 16#64) ↦₆₄ x.head) ∗ ((x.v + 24#64) ↦₆₄ x.cap) ∗
              A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
              memRegion p' (x.head.toNat * 112) ∗
              ((p' + BitVec.ofNat 64 (x.head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
              memRegion (p' + BitVec.ofNat 64 ((x.cap.toNat + x.head.toNat) * 112))
                ((max (2 * x.cap.toNat) 4 - (x.cap.toNat + x.head.toNat)) * 112) ∗
              chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
              chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat))) ∗
            (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗
              memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
        have hpost2 := Satisfies.mono
          (sepConj_mono_left (vecDequeAt_wrap_memcpy_of_post A x.v x.cap p' x.head x.xs
            hlen hhead_pos hcmp hbs_back hbs_front hmax hp'))
          hpost1
        simpa only [sepConj_assoc] using hpost2
      · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
          (by simpa only [withLsCodeLoaded, vecDequeGrowWrapMemcpyBsSpec, sepConj_assoc] using hpost)⟩)
      · exact (allowPanic_not_exited hpost).elim
      · exact (allowPanic_not_exited hpost).elim
    · have hge : x.cap.toNat - x.head.toNat ≤ x.head.toNat := by omega
      have hpre' : s0.mem ⊨
          (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec A)).pre
            (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) s0 ∗ (F ∗ R) := by
        refine intro_withLsCodeLoaded hcl0 ?_
        dsimp only [vecDequeGrowWrapMemmoveBsSpec, F]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hptr, hhead_pos, hhead_lt, hge, hlen_back, hlen_front, hmax8⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem1
      refine h_memmove.mono_outcome
        (x.v, x.cap, x.ptr, x.head, bs_back, bs_front) (F ∗ R)
        s0 hpc hrun hpre' hsp ?_
      rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withLsCodeLoaded, vecDequeGrowWrapMemmoveBsSpec, F] at hpost
        simp only [stackAt_extHookStack_vecDequeGrow, sepExists_sepConj_left,
          sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨p', htr, ⟨hp', _⟩, hpost⟩
        refine ⟨p', BitVec.ofNat 64 (max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat)),
          htr, fun h0 => (hhead0 h0).elim, ?_⟩
        have hpost1 : sf.mem ⊨
            ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
              ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat))) ∗
              ((x.v + 24#64) ↦₆₄ x.cap) ∗
              A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
              (p' ↦ₛ bs_back) ∗
              memRegion (p' + BitVec.ofNat 64 (x.head.toNat * 112))
                ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 112) ∗
              ((p' + BitVec.ofNat 64 ((max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat)) * 112)) ↦ₛ bs_front) ∗
              chainEpochHeaps A (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
              chainEpochHeaps A (x.xs.take (x.cap.toNat - x.head.toNat))) ∗
            (A.pool ∗ stackAt s0.sp vecDequeGrowStack ∗
              memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
        have hpost2 := Satisfies.mono
          (sepConj_mono_left (vecDequeAt_wrap_memmove_of_post A x.v x.cap p' x.head x.xs
            hlen hhead_pos hhead_lt hge hbs_back hbs_front hmax hp'))
          hpost1
        simpa only [sepConj_assoc] using hpost2
      · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id
          (by simpa only [withLsCodeLoaded, vecDequeGrowWrapMemmoveBsSpec, sepConj_assoc] using hpost)⟩)
      · exact (allowPanic_not_exited hpost).elim
      · exact (allowPanic_not_exited hpost).elim

theorem vec_deque_grow_spec_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hmm : HookSat H spqrMemmoveSym (sessionMemmoveSpec growOneStack)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (ChainProofs.vecDequeGrowSpec A)) :=
  vec_deque_grow_spec_placed_ok_of_branches
    (vec_deque_grow_nonwrap_bs_placed_ok h_panic hshim halloc hrealloc)
    (vec_deque_grow_wrap_memcpy_bs_placed_ok h_panic hshim halloc hrealloc hmc)
    (vec_deque_grow_wrap_memmove_bs_placed_ok h_panic hshim halloc hrealloc hmm)

end CryptoVerification.SpqrV1.Alloc

