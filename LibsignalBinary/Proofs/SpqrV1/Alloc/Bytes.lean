/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `BytesMut::reserve_inner` and `Bytes::from(Vec<u8>)`

Verifies `<bytes::bytes_mut::BytesMut>::reserve_inner` (`0x3fc88`) on `KIND_VEC` buffers
(showing `KIND_ARC` is excluded by `bytesMutIsKindVec`) and
`<bytes::bytes::Bytes as From<Vec<u8>>>::from` (`0x423cc`) on `tripleRatchetProgAtExt b ext`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalSessionRepr
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev bytesMutReserveInnerName : String :=
  "<bytes::bytes_mut::BytesMut>::reserve_inner"

@[simp, arm64_norm] theorem bytesMutReserveInner_fnOff :
    libsignalSessionCode.fnOff bytesMutReserveInnerName = 0x3fd6c :=
  libsignalSessionCode_fnOff_0x3fd6c

/-- Instruction-fetch tactic for `[k0, k0 + len)` inside `BytesMut::reserve_inner` (`0x3fc88`). -/
macro "reserve_inner_fetches_range " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrAllocBin $b $H $hfn 0x3fd6c $k0 $len)

/-!
## `KIND_ARC` Exclusion in `BytesMut::reserve_inner`

In `BytesMut`, bit 0 of the fourth word `data` (`[bm + 0x18]`) distinguishes shared
`KIND_ARC = 0` buffers (`Shared` refcount at `data + 0x20`) from uniquely owned
`KIND_VEC = 1` buffers (`v_off = data >>> 5 = 0#64`). At `+0x028 (tbnz w20, #0x0, 0x3fd10)`,
`bytesMutIsKindVec data` unconditionally branches past the `KIND_ARC` path.
-/

/-- Shared (`KIND_ARC = 0`) `BytesMut` tag: bit 0 of `data` is `0`. -/
def bytesMutIsKindArc (data : BitVec 64) : Prop :=
  data.getLsbD 0 = false

/-- Uniquely owned `Vec`-backed (`KIND_VEC = 1`) `BytesMut` tag with zero prefix offset (`data >>> 5 = 0#64`). -/
def bytesMutIsKindVec (data : BitVec 64) : Prop :=
  data.getLsbD 0 = true ∧ data >>> 5 = 0#64

private theorem setWidth32_and_one_bne_zero (data : BitVec 64) :
    (data.setWidth 32 &&& 1#32 != 0#32) = data.getLsbD 0 := by
  cases h0 : data.getLsbD 0
  · have heq : data.setWidth 32 &&& 1#32 = 0#32 := by
      ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_setWidth, BitVec.getElem_zero]
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [← BitVec.getLsbD_eq_getElem, h0, Bool.false_and]
      · have h1 : (1#32 : BitVec 32)[i] = false := by
          rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
          rcases i with _ | i
          · omega
          · simp [Nat.testBit_succ]
        rw [h1, Bool.and_false]
    rw [heq]; rfl
  · have heq : data.setWidth 32 &&& 1#32 = 1#32 := by
      ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_setWidth]
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [← BitVec.getLsbD_eq_getElem, h0, Bool.true_and]
      · have h1 : (1#32 : BitVec 32)[i] = false := by
          rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
          rcases i with _ | i
          · omega
          · simp [Nat.testBit_succ]
        rw [h1, Bool.and_false]
    rw [heq]; rfl

/-- The `tbnz w20, #0x0, 0x3fd10` test at `+0x028` falls through to `KIND_ARC` iff `bytesMutIsKindArc data`. -/
theorem bytesMut_reserve_inner_kind_arc_iff (data : BitVec 64) :
    ((data.setWidth 32 &&& 1#32 != 0#32) = false) ↔ bytesMutIsKindArc data := by
  unfold bytesMutIsKindArc
  rw [setWidth32_and_one_bne_zero]

/-- `bytesMutIsKindVec data` excludes `bytesMutIsKindArc` and takes the `+0x088` branch. -/
theorem bytesMut_reserve_inner_kind_arc_excluded {data : BitVec 64}
    (hvec : bytesMutIsKindVec data) :
    ¬ bytesMutIsKindArc data ∧ (data.setWidth 32 &&& 1#32 != 0#32) = true := by
  obtain ⟨hbit0, _⟩ := hvec
  unfold bytesMutIsKindArc
  rw [setWidth32_and_one_bne_zero, hbit0]
  decide

/-- Every `bytesMutDataWord orig_len` constructed by `BytesMut::with_capacity` satisfies `bytesMutIsKindVec`. -/
theorem bytesMutDataWord_isKindVec (orig_len : BitVec 64) :
    bytesMutIsKindVec (bytesMutDataWord orig_len) :=
  ⟨bytesMutDataWord_getLsbD_zero orig_len, bytesMutDataWord_lsr5 orig_len⟩

/-! ## `BytesMut::reserve_inner` Specification and Proof -/

/-- Stack budget of `BytesMut::reserve_inner`: 96-byte frame plus `doReserveStack`. -/
abbrev bytesMutReserveInnerStack : Nat := doReserveStack + 96

private theorem stackAt_bytesMutReserveInner (sp : BitVec 64) :
    stackAt sp bytesMutReserveInnerStack =
      stackAt (sp - 96#64) doReserveStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4208 12 (by decide)
  change stackAt sp bytesMutReserveInnerStack =
    stackAt (sp - 96#64) doReserveStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

structure BytesMutReserveInnerGhost where
  bm         : BitVec 64
  cap        : BitVec 64
  ptr        : BitVec 64
  data       : BitVec 64
  bs         : List (BitVec 8)
  additional : Nat

/-- Specification of `<bytes::bytes_mut::BytesMut>::reserve_inner` (`0x3fc88`) on a `KIND_VEC` buffer
(`x2 = 1#64`): reallocates the backing buffer to `reserveCap x.cap.toNat x.bs.length x.additional`,
preserving `x.bs` and returning `x0 = 1#64` (or panicking on OOM). -/
def bytesMutReserveInnerSpec (A : RustAlloc) : Spec BytesMutReserveInnerGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.bm ∧
      s.readReg64 .x1 = BitVec.ofNat 64 x.additional ∧
      s.readReg64 .x2 = 1#64 ∧
      bytesMutIsKindVec x.data ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧
      x.cap.toNat - x.bs.length < x.additional ∧
      reserveCap x.cap.toNat x.bs.length x.additional ≤ 2 ^ 63 - 1⌝ ∗
    (x.bm ↦₆₄ x.ptr) ∗ ((x.bm + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
    ((x.bm + 16#64) ↦₆₄ x.cap) ∗ ((x.bm + 24#64) ↦₆₄ x.data) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp bytesMutReserveInnerStack
  post x s0 sf :=
    ⌜sf.readReg64 .x0 = 1#64 ∧ sf.trace = s0.trace⌝ ∗
    (∃∗ p',
      ⌜p' ≠ 0#64⌝ ∗
      (x.bm ↦₆₄ p') ∗ ((x.bm + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((x.bm + 16#64) ↦₆₄ BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) ∗
      ((x.bm + 24#64) ↦₆₄ x.data) ∗
      A.live p' (reserveCap x.cap.toNat x.bs.length x.additional) 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (reserveCap x.cap.toNat x.bs.length x.additional - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp bytesMutReserveInnerStack
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem do_reserve_4_at_reserve_inner {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr bytesMutReserveInnerName + 18446744073709549736#64)
      (doReserve1RawSpec A) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr bytesMutReserveInnerName =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve4Name + 1880#64 :=
    Program.fnAddr_rel (name := doReserve4Name)
      libsignalSessionCode_fnOff_0x3f614 libsignalSessionCode_fnOff_0x3fd6c (k := 1880) (by decide)
  have heq : (tripleRatchetProgAtExt b ext).fnAddr bytesMutReserveInnerName + 18446744073709549736#64 =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve4Name := by
    rw [hrel, BitVec.add_assoc,
      (by decide : (1880#64 : BitVec 64) + 18446744073709549736#64 = 0#64), BitVec.add_zero]
  rw [heq]
  exact do_reserve_4_raw1_ok_ext hA

private theorem reserve_inner_sub_no_underflow {cap : BitVec 64} {len : Nat}
    (hlen : len ≤ cap.toNat) :
    cap.ult (BitVec.ofNat 64 len) = false := by
  have hlt : len < 2 ^ 64 := lt_of_le_of_lt hlen cap.isLt
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, decide_eq_false_iff_not]
  omega

private theorem reserve_inner_rem_ult_add {cap : BitVec 64} {len additional : Nat}
    (hlen : len ≤ cap.toNat) (hlt : cap.toNat - len < additional)
    (hmax : reserveCap cap.toNat len additional ≤ 2 ^ 63 - 1) :
    (cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 additional) = true := by
  have hmax' : len + additional ≤ 2 ^ 63 - 1 := by
    unfold reserveCap at hmax; omega
  have hlen_lt : len < 2 ^ 64 := by omega
  have hadd_lt : additional < 2 ^ 64 := by omega
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
    · simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
      exact hlen
  simp only [BitVec.ult, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hadd_lt, decide_eq_true_eq]
  exact hlt

@[local arm64_norm, local simp]
private theorem bitvec_ult_self (w : BitVec 64) : w.ult w = false :=
  ProofLib.bitvec_ult_self w

@[local arm64_norm, local simp]
private theorem bitvec_ult_zero (w : BitVec 64) : w.ult 0#64 = false := by
  simp [BitVec.ult]

set_option maxHeartbeats 800000 in
/-- `BytesMut::reserve_inner` meets `bytesMutReserveInnerSpec A` on `tripleRatchetProgAtExt b ext`. -/
theorem bytes_mut_reserve_inner_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr bytesMutReserveInnerName)
      (bytesMutReserveInnerSpec A) := by
  simp only [bytesMutReserveInnerSpec, stackAt_bytesMutReserveInner, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff bytesMutReserveInnerName = 0x3fd6c :=
    libsignalSessionCode_fnOff_0x3fd6c
  have hdo_res := do_reserve_4_at_reserve_inner hA
  reserve_inner_fetches_range b (Rust.withPanics ext) hfn 0 44
  reserve_inner_fetches_range b (Rust.withPanics ext) hfn 136 40
  reserve_inner_fetches_range b (Rust.withPanics ext) hfn 224 68
  reserve_inner_fetches_range b (Rust.withPanics ext) hfn 540 28
  reserve_inner_fetches_range b (Rust.withPanics ext) hfn 760 36
  dsimp only [tripleRatchetProgAtExt] at hdo_res ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr bytesMutReserveInnerName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨bm, cap, ptr, data, bs, additional⟩ := x
  dsimp only at *
  obtain ⟨hbit0, hlsr5⟩ := ‹bytesMutIsKindVec data›
  have hbit0_32 : (data.setWidth 32 &&& 1#32 != 0#32) = true :=
    (bytesMut_reserve_inner_kind_arc_excluded ⟨hbit0, hlsr5⟩).2
  have hsub_ok : cap.ult (BitVec.ofNat 64 bs.length) = false :=
    reserve_inner_sub_no_underflow ‹bs.length ≤ cap.toNat›
  have hrem_lt : (cap - BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 additional) = true :=
    reserve_inner_rem_ult_add ‹bs.length ≤ cap.toNat› ‹cap.toNat - bs.length < additional› ‹_›
  have hmax : reserveCap cap.toNat bs.length additional ≤ 2 ^ 63 - 1 := ‹_›
  have hlen_lt : bs.length < 2 ^ 64 := by unfold reserveCap at hmax; omega
  have hadd_lt : additional < 2 ^ 64 := by unfold reserveCap at hmax; omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
  have hadd_toNat : (BitVec.ofNat 64 additional).toNat = additional := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hadd_lt]
  have hsp88_16 : (s0.sp - 88#64) + 8#64 = s0.sp - 80#64 := by bv_omega
  apply SepWPp.of_sepWP (mid := entry + 18446744073709549736#64)
  wp_steps
  wp_if hlen0 <;> {
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.call_frame
      (x := { v := s0.sp - 88#64, cap := cap, ptr := ptr, bs := bs, additional := additional })
      (F := (bm ↦₆₄ ptr) ∗ ((bm + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((bm + 16#64) ↦₆₄ cap) ∗ ((bm + 24#64) ↦₆₄ data) ∗
        ((s0.sp - 96#64) ↦₆₄ v_stk) ∗ ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_stk_7) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      hdo_res
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (ret_pc := entry + 776#64)
      (by simp only [wp_norm, arm64_norm, *])
      rfl
      ⟨by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       ‹_›, ‹_›, by change reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63; omega⟩
      (by dsimp only [doReserve1RawSpec]; rw [hsp88_16]; simp only [wp_norm, arm64_norm, *]; ac_rfl)
      (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (fun sf _ hm => allowPanic_frame id hm)
      fun sm hpcm hrunm hspm hcsm => ?_
    have hsp_sm : sm.sp = s0.sp - 96#64 := by
      rw [hspm]; simp only [wp_norm, arm64_norm, *]
    obtain ⟨hx19_eq, hx20_eq, hx21_eq, hx22_eq, hx23_eq, hx24_eq, hx25_eq, hx26_eq, hx27_eq, hx28_eq, hx29_eq, hvregs_eq⟩ := hcsm
    have hx19 : sm.readReg64 (Reg.gpr 19#5) = bm := by
      rw [hx19_eq]; simp only [wp_norm, arm64_norm, *]
    have hx20 : sm.readReg64 (Reg.gpr 20#5) = data := by
      rw [hx20_eq]; simp only [wp_norm, arm64_norm, *]
    have hx21 : sm.readReg64 (Reg.gpr 21#5) = 0#64 := by
      rw [hx21_eq]; simp only [wp_norm, arm64_norm, *]
    have hx22 : sm.readReg64 (Reg.gpr 22#5) = cap := by
      rw [hx22_eq]; simp only [wp_norm, arm64_norm, *]
    have hx29 : sm.readReg64 (Reg.gpr 29#5) = s0.sp - 64#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 64#64
      rw [hx29_eq]; simp only [wp_norm, arm64_norm, *]
    dsimp only [doReserve1RawSpec]
    rw [hsp88_16]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun p' => ?_
    refine SepWPp.pure_elim fun htrace => ?_
    refine SepWPp.pure_elim fun hp' => ?_
    have htr_sm : sm.trace = s0.trace := by
      rw [htrace]; simp only [wp_norm, arm64_norm, *]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  }

/-! ## `Bytes::from(Vec<u8>)` -/

/-- `Bytes::from(Vec<u8>)` meets `bytesFromVecSpec A b` when `(b &&& 0xfff#64) = 0#64`. -/
theorem bytes_from_vec_base_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hb : (b &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr bytesFromVecName)
      (bytesFromVecSpec A b) :=
  bytesFromVec_base_ok_ext hb

/-- `Bytes::from(Vec<u8>)` meets `(bytesFromVecSpec A b).inImage img`. -/
theorem bytes_from_vec_ok_ext {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} :
    BytesFromVecOkExt img b A ext :=
  bytesFromVecOk_ext

end CryptoVerification.SpqrV1.Alloc
