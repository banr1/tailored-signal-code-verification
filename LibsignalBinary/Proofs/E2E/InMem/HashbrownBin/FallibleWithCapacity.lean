/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<RawTableInner>::fallible_with_capacity::<Global>` (`0x01798`)

Proves `fallibleWithCapacity4_ok` against `fallibleWithCapacity4Spec A`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace FallibleWithCapacity

theorem sepWP_exists_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : α → SepProp} {post : Arm64.State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : Arm64.State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem trace_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

/-- No-op shim spec that records trace preservation. -/
def hashbrownShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

theorem hashbrownShim_hookOk : HookOk hookNoop hashbrownShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [hashbrownShimSpec, hookNoop, retHook, id_eq, trace_setPC_pre,
    satisfies_pure_sepConj, emp_sepConj] at hpre ⊢
  exact ⟨trivial, hpre⟩

/-- `memset(ptr = x0, c = w1, len = x2)` region-only spec with trace preservation. -/
def hashbrownMemsetRegionSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := memsetRegionSpec.pre
  post := fun (ptr, c, len) s0 sf =>
    ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c)

theorem hashbrownMemset_region_trace_ok : HookOk hookMemset hashbrownMemsetRegionSpec := by
  refine HookOk.of_trace hookMemset_region_ok fun _ _ _ ht hpost => ?_
  simp only [memsetRegionSpec, hashbrownMemsetRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

/-- `memcpy(dst = x0, src = x1, len = x2)` region-only spec with trace preservation. -/
def hashbrownMemcpyRegionSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := memcpyRegionSpec.pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

theorem hashbrownMemcpy_region_trace_ok : HookOk hookMemcpy hashbrownMemcpyRegionSpec := by
  refine HookOk.of_trace hookMemcpy_region_ok fun _ _ _ ht hpost => ?_
  simp only [memcpyRegionSpec, hashbrownMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

/-- A stub `hname` mapped to `some Rust.panicked` in `H` evaluates to `some Rust.panicked`
at `fnAddr name + k` of `P.rebase b H`. -/
theorem panic_at_hook_raw {P : Program} {b : BitVec 64}
    {H : String → Option (Arm64.State → Arm64.State)} {name hname : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (P.rebase 0 X).hookAtOff? stub = X hname)
    (hp : H hname = some Rust.panicked) :
    (P.rebase b H).externAt?
      ((P.rebase b H).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked := by
  rw [Program.externAt?_fnAddr_add hfn hk hs, hstub, hp]

theorem hashbrown_shim_ok_at {A : RustAlloc} {b : BitVec 64} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2")) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr name + BitVec.ofNat 64 k)
      hashbrownShimSpec :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    ⟨hookNoop, hHooks.shim, hashbrownShim_hookOk⟩

theorem hashbrown_allocNW_ok_at {A : RustAlloc} {b : BitVec 64} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "__rustc::__rust_alloc")) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustAllocNWSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_alloc")
    hHooks.allocNW

theorem hashbrown_memset_region_ok_at {A : RustAlloc} {b : BitVec 64} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "memset")) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr name + BitVec.ofNat 64 k)
      hashbrownMemsetRegionSpec :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "memset")
    ⟨hookMemset, hHooks.memset, hashbrownMemset_region_trace_ok⟩

theorem hashbrown_panic_at_fallibilityAllocErr {A : RustAlloc} {b : BitVec 64} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "<hashbrown::raw::Fallibility>::alloc_err#1")) :
    (RebasedProg b ext).externAt?
      ((RebasedProg b ext).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_hook_raw hfn hk (by decide) (ls_hook% "<hashbrown::raw::Fallibility>::alloc_err#1")
    hHooks.fallibilityAllocErr

/-! ## Stack and Memory Splitting Helpers for `fallible_with_capacity` -/

theorem stackAt_fallibleWithCapacity (sp : BitVec 64) :
    stackAt sp fallibleWithCapacityStack =
      memRegion (sp - 4224#64) 64 ∗
        stackAt (sp - 64#64) allocHookStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := stackAt_split_bottom sp 4160 64 (by decide)
  have h2 := stackAt_split_cells sp 4096 8 (by decide)
  change stackAt sp fallibleWithCapacityStack = memRegion (sp - 4224#64) 64 ∗ stackAt sp 4160 at h1
  change stackAt sp 4160 = stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8, ← sepConj_assoc]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        (a ↦₆₄ u3) ∗ ((a + 8#64) ↦₆₄ u2) ∗ ((a + 16#64) ↦₆₄ u1) ∗ ((a + 24#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 24 (by decide),
    memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_4_stride_eq_arrayAt (ptr : BitVec 64) (stride : Nat) (h : stride ≤ 0x1000) :
    memRegion ptr (4 * stride) =
      arrayAt (fun _ a => memRegion a stride) stride ptr (List.range 4).reverse := by
  have h1 := memRegion_split ptr stride (3 * stride) (by omega)
  have h2 := memRegion_split (ptr + BitVec.ofNat 64 stride) stride (2 * stride) (by omega)
  have h3 := memRegion_split
    (ptr + BitVec.ofNat 64 stride + BitVec.ofNat 64 stride) stride stride (by omega)
  rw [show 4 * stride = stride + 3 * stride by omega, h1,
      show 3 * stride = stride + 2 * stride by omega, h2,
      show 2 * stride = stride + stride by omega, h3]
  change _ =
    memRegion ptr stride ∗
      (memRegion (ptr + BitVec.ofNat 64 stride) stride ∗
        (memRegion (ptr + BitVec.ofNat 64 stride + BitVec.ofNat 64 stride) stride ∗
          (memRegion (ptr + BitVec.ofNat 64 stride + BitVec.ofNat 64 stride + BitVec.ofNat 64 stride) stride ∗ emp)))
  rw [sepConj_emp]

theorem allocFailedIn_of_eq {s0 sf : Arm64.State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

/-! ## Arithmetic Helpers for `fallible_with_capacity` -/

theorem cap_beq_zero_eq_false {cap : BitVec 64} (h : 1 ≤ cap.toNat) :
    (cap == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  rw [heq] at h
  contradiction

theorem cap_ule_15_eq_false {cap : BitVec 64} (h : cap.toNat < 4) :
    (15#64).ule cap = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
  change ¬ (15 ≤ cap.toNat)
  omega

theorem cap_ult_4_eq_true {cap : BitVec 64} (h : cap.toNat < 4) :
    cap.ult 4#64 = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  exact h

theorem umulh_4_eq_zero {s : BitVec 64} (h : s.toNat ≤ 4096) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 s * 4#128) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth]
  have h1 : (4#128 : BitVec 128).toNat = 4 := rfl
  have h2 : s.toNat < 2 ^ 128 := by omega
  have h3 : s.toNat * 4 < 2 ^ 128 := by omega
  rw [h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : s.toNat * 4 / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

theorem mul_4_toNat {s : BitVec 64} (h : s.toNat ≤ 4096) :
    (s * 4#64).toNat = 4 * s.toNat := by
  rw [BitVec.toNat_mul]
  have h4 : (4#64 : BitVec 64).toNat = 4 := rfl
  rw [h4, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

theorem conditionHolds_hi_addsPState64_eq_false {x y : BitVec 64}
    (h : x.toNat + y.toNat < 2 ^ 64) :
    ConditionHolds CondCode.HI (addsPState64 x y) = false := by
  have hcs : ConditionHolds CondCode.CS (addsPState64 x y) = false := by
    rw [conditionHolds_cs_addsPState64, BitVec.ult_eq_decide, decide_eq_false_iff_not,
      BitVec.toNat_add, Nat.mod_eq_of_lt h]
    omega
  unfold ConditionHolds addsPState64 at hcs ⊢
  simp only [Bool.and_eq_false_imp]
  intro hc
  rw [hc] at hcs
  contradiction

theorem and_mask8_eq_shift (y : BitVec 64) :
    y &&& bv% (2 ^ 64 - 8) = (y >>> 3) <<< 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : ∀ k : Fin 64,
      (bv% (2 ^ 64 - 8) : BitVec 64).getLsbD k.val = !(decide (k.val < 3)) := by decide
  rw [BitVec.getLsbD_and, hm ⟨i, hi⟩, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h3 : i < 3
  · simp [h3]
  · have h3sub : 3 + (i - 3) = i := by omega
    simp [h3, hi, h3sub]

theorem align8_mul_4 {s : BitVec 64} (h : s.toNat ≤ 4096) (h8 : s.toNat % 8 = 0) :
    (s * 4#64 + 7#64) &&& bv% (2 ^ 64 - 8) = s * 4#64 := by
  rw [and_mask8_eq_shift]
  apply BitVec.eq_of_toNat_eq
  have hm := mul_4_toNat h
  have hy : (s * 4#64 + 7#64).toNat = 4 * s.toNat + 7 := by
    rw [BitVec.toNat_add, hm]
    have h7 : (7#64 : BitVec 64).toNat = 7 := rfl
    rw [h7, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, hy, hm,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (((4 * s.toNat + 7) / 8) * 8) % 2 ^ 64 = 4 * s.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem alloc_size_cs_eq_false {s : BitVec 64} (h : s.toNat ≤ 4096) :
    (12#64 + s * 4#64).ult 12#64 = false := by
  have hm := mul_4_toNat h
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, hm]
  have h12 : (12#64 : BitVec 64).toNat = 12 := rfl
  rw [h12, Nat.mod_eq_of_lt (by omega)]
  omega

theorem alloc_size_hi_eq_false {s : BitVec 64} (h : s.toNat ≤ 4096) :
    (9223372036854775800#64).ult (12#64 + s * 4#64) = false := by
  have hm := mul_4_toNat h
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, hm]
  have h12 : (12#64 : BitVec 64).toNat = 12 := rfl
  have hmax : (9223372036854775800#64 : BitVec 64).toNat = 9223372036854775800 := rfl
  rw [h12, hmax, Nat.mod_eq_of_lt (by omega)]
  omega

theorem alloc_size_beq_zero_eq_false {s : BitVec 64} (h : s.toNat ≤ 4096) :
    (12#64 + s * 4#64 == 0#64) = false := by
  have hm := mul_4_toNat h
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, hm] at ht
  have h12 : (12#64 : BitVec 64).toNat = 12 := rfl
  rw [h12, Nat.mod_eq_of_lt (by omega)] at ht
  change 12 + 4 * s.toNat = 0 at ht
  omega

theorem fold_rawTableInner4EmptyAt (A : RustAlloc) (stride : Nat) (sret ptr : BitVec 64)
    (hstride_pos : 0 < stride) (hstride_le : stride ≤ 4096) (hstride_align : stride % 8 = 0)
    (hptr_align : ptr.toNat % 8 = 0) (hptr_lt : ptr.toNat + (4 * stride + 12) < 2 ^ 64) :
    let ctrl := ptr + BitVec.ofNat 64 (4 * stride)
    (sret ↦₆₄ ctrl) ∗
    ((sret + 8#64) ↦₆₄ 3#64) ∗
    ((sret + 16#64) ↦₆₄ 3#64) ∗
    ((sret + 24#64) ↦₆₄ 0#64) ∗
    A.live ptr (4 * stride + 12) 8 ∗
    (ctrl ↦ₛ List.replicate 12 0xff#8) ∗
    memRegion ptr (4 * stride) ⊢
    rawTableInner4EmptyAt A stride sret := by
  intro ctrl
  unfold rawTableInner4EmptyAt
  refine Entails.sepExists_right ctrl ?_
  have hctrl_toNat : ctrl.toNat = ptr.toNat + 4 * stride := by
    change (ptr + BitVec.ofNat 64 (4 * stride)).toNat = ptr.toNat + 4 * stride
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hctrl_ne : ctrl ≠ 0#64 := by
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [hctrl_toNat] at ht
    change ptr.toNat + 4 * stride = 0 at ht
    omega
  have hctrl_align : ctrl.toNat % 8 = 0 := by omega
  have hctrl_ge : 4 * stride ≤ ctrl.toNat := by omega
  have hctrl_lt : ctrl.toNat + 12 < 2 ^ 64 := by omega
  have hsub : ctrl - BitVec.ofNat 64 (4 * stride) = ptr := by
    change ptr + BitVec.ofNat 64 (4 * stride) - BitVec.ofNat 64 (4 * stride) = ptr
    exact BitVec.add_sub_cancel ptr (BitVec.ofNat 64 (4 * stride))
  refine Entails.pure_right ⟨hctrl_ne, hctrl_align, hctrl_ge, hctrl_lt⟩ ?_
  rw [hsub, ← memRegion_4_stride_eq_arrayAt ptr stride hstride_le]
  exact Entails.refl _

end FallibleWithCapacity

open FallibleWithCapacity

#arm64_check_no_rfl_state_lemmas

theorem fallibleWithCapacity4_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr fallibleWithCapacityName)
      (fallibleWithCapacity4Spec A) := by
  simp only [fallibleWithCapacity4Spec, stackAt_fallibleWithCapacity, memRegion_32_cells]
  have hfn : libsignalSessionCode.fnOff fallibleWithCapacityName = num% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>") := fallibleWithCapacity_fnOff
  have hshim := hashbrown_shim_ok_at (b := b) hHooks hfn (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>")) (by decide)
  have halloc := hashbrown_allocNW_ok_at (b := b) hHooks hfn (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>")) (by decide)
  have hmemset := hashbrown_memset_region_ok_at (b := b) hHooks hfn (k := num% (ls_off% "memset" - ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>")) (by decide)
  have hpanic := hashbrown_panic_at_fallibilityAllocErr (b := b) hHooks hfn (k := num% (ls_off% "<hashbrown::raw::Fallibility>::alloc_err#1" - ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>")) (by decide)
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>")) 412
  dsimp only [RebasedProg] at hshim halloc hmemset hpanic ⊢
  clear hfn hHooks
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr fallibleWithCapacityName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨sret, stride, capacity⟩ := x
  dsimp only at *
  have hcap0 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = false := cap_beq_zero_eq_false (by omega)
  have hcap15 : (15#64).ule (s0.readReg64 (Reg.gpr 2#5)) = false := cap_ule_15_eq_false (by omega)
  have hcap4 : (s0.readReg64 (Reg.gpr 2#5)).ult 4#64 = true := cap_ult_4_eq_true (by omega)
  have humulh : BitVec.truncate 64 ((BitVec.zeroExtend 128 (s0.readReg64 (Reg.gpr 1#5)) * 4#128) >>> 64) = 0#64 :=
    umulh_4_eq_zero (by omega)
  have hmul4 : (s0.readReg64 (Reg.gpr 1#5) * 4#64).toNat = 4 * stride := by
    rw [mul_4_toNat (by omega), h_2]
  have hhi8 : ConditionHolds CondCode.HI (addsPState64 (s0.readReg64 (Reg.gpr 1#5) * 4#64) 8#64) = false :=
    conditionHolds_hi_addsPState64_eq_false
      (by change (s0.readReg64 (Reg.gpr 1#5) * 4#64).toNat + 8 < 2 ^ 64; omega)
  have halign8 : (s0.readReg64 (Reg.gpr 1#5) * 4#64 + 7#64) &&& bv% (2 ^ 64 - 8) =
      s0.readReg64 (Reg.gpr 1#5) * 4#64 :=
    align8_mul_4 (by omega) (by omega)
  have hcs_sz : (12#64 + s0.readReg64 (Reg.gpr 1#5) * 4#64).ult 12#64 = false :=
    alloc_size_cs_eq_false (by omega)
  have hhi_sz : (9223372036854775800#64).ult (12#64 + s0.readReg64 (Reg.gpr 1#5) * 4#64) = false :=
    alloc_size_hi_eq_false (by omega)
  have hcbz_sz : (12#64 + s0.readReg64 (Reg.gpr 1#5) * 4#64 == 0#64) = false :=
    alloc_size_beq_zero_eq_false (by omega)
  have hsz_toNat : (12#64 + s0.readReg64 (Reg.gpr 1#5) * 4#64).toNat = 4 * stride + 12 := by
    rw [BitVec.toNat_add, hmul4]
    have h12 : (12#64 : BitVec 64).toNat = 12 := rfl
    rw [h12, Nat.mod_eq_of_lt (by omega)]
    omega
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (240))
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · have hoom0 : sf_1.readReg64 (Reg.gpr 0#5) = 0 := hoom
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hoom
    wp_simp_pre only [hoom0, ite_true, sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<hashbrown::raw::Fallibility>::alloc_err#1" - ls_off% "<hashbrown::raw::RawTableInner>::fallible_with_capacity::<alloc::alloc::Global>"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0 := hoom
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    wp_simp_pre only [hoom0, ite_false, sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun ⟨hptr_align, hptr_lt, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    rw [memRegion_split (sf_1.readReg64 (Reg.gpr 0#5)) (4 * stride) 12 (by omega)]
    wp_steps
    have hmul4_bv : s0.readReg64 (Reg.gpr 1#5) * 4#64 = BitVec.ofNat 64 (4 * stride) := by
      apply BitVec.eq_of_toNat_eq
      rw [hmul4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hmul4_bv]
    wp_apply
    wp_steps
    have hfold :=
      fold_rawTableInner4EmptyAt A stride sret (sf_1.readReg64 (Reg.gpr 0#5)) h_7 h_8 h hptr_align hptr_lt
    dsimp only at hfold
    refine SepWP.fold hfold (by sep_focus) ?_
    wp_done
end CryptoVerification.E2E.InMem.HashbrownBin
