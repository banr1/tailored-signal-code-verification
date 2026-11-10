/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecDecode
import ProofLib.SepLogic.WPp

/-!
# Shared `Vec<u8>::append_elements` and `RawVecInner::try_allocate_in` Callees

Proves `subroutine_ok` on `tripleRatchetProgAt` for the fast paths of
`<alloc::vec::Vec<u8>>::append_elements` (`0x1af54` and `0x7655c`, `len + bs.length ≤ cap`) and for
`<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (`0x764a0`).
-/

@[expose] public section

set_option autoImplicit false

open ProofLib.Variant
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Arithmetic and Memory Helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]
  omega

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_tryAllocateIn (sp : BitVec 64) :
    stackAt sp finishGrowStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 4096 6 (by decide)

private theorem hi_append_eq_false {cap len n : Nat}
    (hle : len + n ≤ cap) (hcap : cap < 2 ^ 64) :
    (BitVec.ofNat 64 cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 n) = false := by
  have hlen : len < 2 ^ 64 := by omega
  have hn : n < 2 ^ 64 := by omega
  have hsub : (BitVec.ofNat 64 cap - BitVec.ofNat 64 len).toNat = cap - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hlen]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hlen]
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  omega

private theorem ofNat_beq_zero_eq_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

/-! ## `<alloc::vec::Vec<u8>>::append_elements [local#1]` (`0x1af54`) -/

abbrev vecAppendElementsSym : String :=
  "<alloc::vec::Vec<u8>>::append_elements"

/-- Fast-path contract for `<Vec<u8>>::append_elements` (`0x1af54`) when `cap = 192`,
`len = 128`, and `bs.length = 32` (`192 - 128 = 64 ≥ 32`). -/
def pqxdhVecAppendElementsFastSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (vecHdr, vecPtr, srcPtr, bs) s =>
    ⌜s.readReg64 .x0 = vecHdr ∧ s.readReg64 .x1 = srcPtr ∧
      s.readReg64 .x2 = 32#64 ∧ bs.length = 32⌝ ∗
    (vecHdr ↦₆₄ 192#64) ∗ ((vecHdr + 8#64) ↦₆₄ vecPtr) ∗ ((vecHdr + 16#64) ↦₆₄ 128#64) ∗
    memRegion (vecPtr + 128#64) bs.length ∗ (srcPtr ↦ₛ bs) ∗
    cells (s.sp - 48#64) 6
  post := fun (vecHdr, vecPtr, srcPtr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (vecHdr ↦₆₄ 192#64) ∗ ((vecHdr + 8#64) ↦₆₄ vecPtr) ∗ ((vecHdr + 16#64) ↦₆₄ 160#64) ∗
    ((vecPtr + 128#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗
    cells (s0.sp - 48#64) 6

theorem vecAppendElements_fast_ok_trap {b : BitVec 64} {C : Crypto}
    {absHooks : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr vecAppendElementsSym)
      pqxdhVecAppendElementsFastSpec := by
  unfold pqxdhVecAppendElementsFastSpec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff vecAppendElementsSym = 0x1af54 :=
    libsignalSessionCode_fnOff_0x1af54
  have hmemcpy := framelessMemcpy_ok_at_trap (b := b) (C := C) (abs := absHooks)
      (name := vecAppendElementsSym) (k := num% (ls_off% "memcpy" - 0x1af54))
    (by rw [hfn, (ls_stub% "memcpy")])
  dsimp only [framelessMemcpySpec] at hmemcpy
  code_fetches CryptoVerification.libsignalSessionCode vecAppendElements b
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x1af54 88
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨vecHdr, vecPtr, srcPtr, bs⟩ := x
  dsimp only at *
  subst h_1 h_2
  wp_steps
  rw [← h]
  wp_call hmemcpy (vecPtr + 128#64, s0.readReg64 (.gpr 1#5), bs)
  simp only [h] at *
  wp_steps
  wp_done

theorem vecAppendElements_fast_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr vecAppendElementsSym)
      pqxdhVecAppendElementsFastSpec := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap vecAppendElements_fast_ok_trap

/-! ## General Fast-Path `<alloc::vec::Vec<u8>>::append_elements` -/

abbrev vecAppendElements2Sym : String := vecAppendElementsSym

/-- Ghost state for a general fast-path `<Vec<u8>>::append_elements` call
(`len + bs.length ≤ cap`). -/
structure VecAppendFastCall where
  vecHdr : BitVec 64
  vecPtr : BitVec 64
  srcPtr : BitVec 64
  cap    : Nat
  len    : Nat
  bs     : List (BitVec 8)

/-- General fast-path contract for `<Vec<u8>>::append_elements` (`len + bs.length ≤ cap`,
`cap < 2^64`). Covers both `bs = []` (`cbz` taken, skipping `memcpy`) and `bs ≠ []` (`memcpy`). -/
def vecAppendElementsGenFastSpec : Spec VecAppendFastCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.vecHdr ∧ s.readReg64 .x1 = x.srcPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧
      x.len + x.bs.length ≤ x.cap ∧ x.cap < 2 ^ 64⌝ ∗
    (x.vecHdr ↦₆₄ BitVec.ofNat 64 x.cap) ∗
    ((x.vecHdr + 8#64) ↦₆₄ x.vecPtr) ∗
    ((x.vecHdr + 16#64) ↦₆₄ BitVec.ofNat 64 x.len) ∗
    memRegion (x.vecPtr + BitVec.ofNat 64 x.len) x.bs.length ∗
    (x.srcPtr ↦ₛ x.bs) ∗
    cells (s.sp - 48#64) 6
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (x.vecHdr ↦₆₄ BitVec.ofNat 64 x.cap) ∗
    ((x.vecHdr + 8#64) ↦₆₄ x.vecPtr) ∗
    ((x.vecHdr + 16#64) ↦₆₄ BitVec.ofNat 64 (x.len + x.bs.length)) ∗
    ((x.vecPtr + BitVec.ofNat 64 x.len) ↦ₛ x.bs) ∗
    (x.srcPtr ↦ₛ x.bs) ∗
    cells (s0.sp - 48#64) 6

theorem vecAppendElements1_gen_fast_ok_trap {b : BitVec 64} {C : Crypto}
    {absHooks : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr vecAppendElementsSym)
      vecAppendElementsGenFastSpec := by
  unfold vecAppendElementsGenFastSpec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff vecAppendElementsSym = 0x1af54 :=
    libsignalSessionCode_fnOff_0x1af54
  have hmemcpy := framelessMemcpy_ok_at_trap (b := b) (C := C) (abs := absHooks)
      (name := vecAppendElementsSym) (k := num% (ls_off% "memcpy" - 0x1af54))
    (by rw [hfn, (ls_stub% "memcpy")])
  dsimp only [framelessMemcpySpec] at hmemcpy
  code_fetches CryptoVerification.libsignalSessionCode vecAppendElements b
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x1af54 88
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨vecHdr, vecPtr, srcPtr, cap, len, bs⟩ := x
  dsimp only at *
  have hle : len + bs.length ≤ cap := ‹len + bs.length ≤ cap›
  have hcap : cap < 2 ^ 64 := ‹cap < 2 ^ 64›
  have hhi := hi_append_eq_false hle hcap
  cases bs with
  | nil =>
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat,
      memRegion_zero, pointsToBytes_nil] at *
    wp_steps
    wp_done
  | cons b0 bs' =>
    have hpos : 0 < (b0 :: bs').length := by simp
    have hlt : (b0 :: bs').length < 2 ^ 64 := by omega
    have hcbz := ofNat_beq_zero_eq_false hpos hlt
    wp_steps
    wp_call hmemcpy (vecPtr + BitVec.ofNat 64 len, s0.readReg64 (.gpr 1#5), b0 :: bs')
    wp_steps
    wp_done

theorem vecAppendElements1_gen_fast_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr vecAppendElementsSym)
      vecAppendElementsGenFastSpec := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap vecAppendElements1_gen_fast_ok_trap

theorem vecAppendElements2_gen_fast_ok_trap {b : BitVec 64} {C : Crypto}
    {absHooks : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr vecAppendElements2Sym)
      vecAppendElementsGenFastSpec :=
  vecAppendElements1_gen_fast_ok_trap

theorem vecAppendElements2_gen_fast_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr vecAppendElements2Sym)
      vecAppendElementsGenFastSpec :=
  vecAppendElements1_gen_fast_ok

/-! ## `<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (`0x764a0`) -/

abbrev tryAllocateIn2Sym : String :=
  "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]"

structure TryAllocateInCall where
  /-- Result pointer `x0` (24-byte `Result<RawVecInner, TryReserveError>`). -/
  out    : BitVec 64
  /-- Requested capacity `x1` in elements. -/
  new    : BitVec 64
  /-- Element alignment `x2` in bytes. -/
  align  : BitVec 64
  /-- Element stride `x3` in bytes. -/
  stride : BitVec 64

/-- Contract for `<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` when
`0 < new.toNat`, `0 < stride.toNat`, and `LayoutOk (new.toNat * stride.toNat) align.toNat`.
- On `Ok` (`tag = 0#64`): writes `0#64` at `out + 0`, `new` at `out + 8`, and `p'` at `out + 16`,
  yielding `A.live p' (new * stride) align ∗ memRegion p' (new * stride)`.
- On `Err` (`tag = 1#64`): writes `1#64` at `out + 0`, `align` at `out + 8`, and `new * stride`
  at `out + 16`, appending `allocFailedEvent` to `sf.trace`. -/
def tryAllocateInSpec (A : RustAlloc) : Spec TryAllocateInCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp finishGrowStack
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗
      (if tag = 1#64 then
        ((x.out + 8#64) ↦₆₄ x.align) ∗
        ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
        ⌜p' = 0#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ((x.out + 8#64) ↦₆₄ x.new) ∗
        ((x.out + 16#64) ↦₆₄ p') ∗
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗
          memRegion p' (x.new.toNat * x.stride.toNat)) ∗
      A.pool ∗ stackAt s0.sp finishGrowStack

theorem tryAllocateIn2_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr tryAllocateIn2Sym)
      (tryAllocateInSpec A) := by
  unfold tryAllocateInSpec
  simp only [memRegion_24, stackAt_tryAllocateIn, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff tryAllocateIn2Sym =
      (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")
  have hshim := noAllocShim_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := tryAllocateIn2Sym)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_trap (b := b) (C := C) hA
    (name := tryAllocateIn2Sym)
    (k := num% (ls_off% "__rustc::__rust_alloc" -
      (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]")))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  dsimp only [noAllocShimSpec] at hshim
  code_fetches CryptoVerification.libsignalSessionCode tryAllocateIn2 b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]") 188
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, new, align, stride⟩ := x
  dsimp only at *
  rcases h with ⟨hsz_pos, hpow, hbound⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat * stride.toNat, align.toNat)
  wp_steps
  wp_if hoom
  · have hoom0 : sf_1.readReg64 Reg.x0 = 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat hlt64
    simp only [hoom0, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 0#64
    simp only [ite_true, hmul_bv]
    wp_done
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done

theorem tryAllocateIn2_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr tryAllocateIn2Sym)
      (tryAllocateInSpec A) := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (tryAllocateIn2_ok_trap hA)

end CryptoVerification.E2E.Pqxdh.Shared
