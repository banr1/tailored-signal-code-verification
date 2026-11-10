/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Process.OracleEq
public import ProofLib.StdStartup.MemOps
public import VerifiedLibraries.Musl.Proofs.MemsetSymCommon
public import VerifiedLibraries.Musl.Proofs.MemmoveProof
public import LibsignalBinary.Heap.Iface
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux -- proof-setup: allow-public-import
import ProofLib.BV.Bits

/-!
# Region-Local `memmove` Code Verification & `.text.b_pre` Hull (`HooksDehook.MemmoveCode`)

Card **M-a1** (`memmove` `a1` code-side contract over the single `239`-word / `956`-byte `.text.b_pre`
hull, mirroring `HooksDehook.MemsetCode`, `HooksDehook.MemcpyCode`, and `HooksDehook.BcmpCode`):

1. **State preservation (`MemmoveStatePreserved` & `stdMemmoveSpec`):**
   `abbrev MemmoveStatePreserved := MemsetStatePreserved` (`rfl`-identical to
   `Memmove.MemmoveStatePreserved` and `MemcpyCode.MemcpyStatePreserved`), giving definitional
   `SpecStripSInvariant keep masterMemmoveSpec`. Exports permission-carrying `stdMemmoveSpec`
   (`ProcessFieldsPreserved s0 sf`, `rfl`-identical to `StdStatePreserved s0 sf`) so
   `MemmoveGhost` recovers `VmPreserved` across `stripS keep`, plus
   `MemmoveStatePreserved.toAllocCallPreserved` and `linkedCallHook_oracle_eq`.
2. **Frameless zero-stack `masterMemmoveSpec` & `K`-narrowing (`memmoveSpecK`):**
   Zero stack bytes, gated by `MemmoveArithBound base buf` (`base.toNat + buf.length ≤ 2 ^ 64 ∧
   buf.length < 2 ^ 63`), updating `base ↦ₛ buf` to `base ↦ₛ ProofLib.listMove buf dst src len`
   with `x0 = base + BitVec.ofNat 64 dst` and `onPanic = onExit = onOom = ⌜False⌝`.
3. **Contiguous `239`-word (`956`-byte) `.text.b_pre` hull (`bPreHullWords`):**
   Under stock `libc.a` layout (`D-C2f = 2C`), `.text.b_pre` at `m` places `memcpy` at `+0` (`99`
   words), `1` pad word (`bPrePadWord = 0#32`) at `+396`, `memset` at `+400` (`bPreMemsetByteOff`,
   `65` words), and `memmove` at `+660` (`bPreMemmoveByteOff`, `74` words patched with `b memcpy`
   at `-764` B = `-191` words). Proves slice extraction, `branchInRange_bPreHull`, and single-`P_sub`
   `subroutine_ok` at `m + bPreMemmoveByteOff` (polymorphic in `padWord : BitVec 32`).
4. **`W`-free fallback (`hookMemmove`) & bounded consumer `HookOk` lifts:**
   Proves `hookMemmove` (`State → State`, `W`-free) and `hookMemmoveOf_masterMemmove_ok`, and lifts
   `HookOk f masterMemmoveSpec` (+ `K`, `withVmPreserved`, `withAlloc`) to `libcMemmoveBoundedSpec`,
   `sessionMemmoveBoundedSpec`, `keepsFs (sessionMemmoveBoundedSpec _)`,
   `sessionMemmoveBoundedBudgetSpec`, `sessionMemmoveBoundedAcpSpec`, and
   `withAllocVmPreserved (sessionMemmoveBoundedSpec _)` (including `stk = 0` for
   `SpqrSendCoinsPlacedInstBudget:333`, where `0` is `hookStack = 0`, not `len = 0`). Unbounded
   specs omitting `MemmoveArithBound` are intentionally not lifted without `A.block_valid`.
5. **C4 Hook-Shape Return-to-`lr` Lemmas (`TrapRetHook` & `linkedCallHook`):**
   Proves `TrapRetHook L` (`rfl`-identical to `MemsetLrTrap.Blk21TrapHook L`) for standard hooks
   and `linkedCallHook` (`trapRetHook_linkedCallHook_of_hookOk_and_lr` covers the cross-block
   `keep L = false` case).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib.StdStartup (StdStatePreserved)
open VerifiedLibraries.Musl (
  memmoveLibcaCalls memmoveLibcaWords memmoveSpec memcpySymWords memsetWordsSym
  moveBytes_eq_listMove
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionMemmoveSpec)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved hookMemmove_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux (sessionMemmoveAcpSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (
  MemmoveArithBound libcMemmoveBoundedSpec sessionMemmoveBoundedSpec
  sessionMemmoveBoundedBudgetSpec memcpyTailVm_ok_of_masterMemcpyVm_ok
  memmove_masterVm_patchCalls_ok vmPreserved_of_processFieldsPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
  keepFsTrace linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  masterMemcpySpec hookOk_map_frame_pureAbort
  stdMemcpy_pre_of_masterMemcpy_pre stdMemcpyRO_pre_of_masterMemcpy_pre
  subroutine_ok_stdMemcpy_of_hasWords subroutine_ok_stdMemcpyRO_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)

/-! ## 1. Master `memmove` Specification, `stdMemmoveSpec`, & `SpecStripSInvariant` -/

/-- Reuse `MemsetStatePreserved` (`fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`,
    `physMemAvail`) via `abbrev` so `MemmoveStatePreserved` is definitionally (`rfl`) identical to
    `MemsetStatePreserved`, `MemcpyStatePreserved`, and `Memmove.MemmoveStatePreserved`. -/
abbrev MemmoveStatePreserved (s0 sf : State) : Prop :=
  MemsetStatePreserved s0 sf

/-- `ProofLib.StdStartup.StdStatePreserved` and `ProofLib.ProcessFieldsPreserved` are definitionally
    (`rfl`) identical (the 7 `MemsetStatePreserved` fields plus pointwise `mem.perm`). -/
theorem stdStatePreserved_eq_processFieldsPreserved (s0 sf : State) :
    StdStatePreserved s0 sf = ProcessFieldsPreserved s0 sf := rfl

theorem memmoveStatePreserved_eq_memmoveBridge (s0 sf : State) :
    MemmoveStatePreserved s0 sf =
      LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.MemmoveStatePreserved s0 sf := rfl

theorem MemmoveStatePreserved.refl (s : State) : MemmoveStatePreserved s s :=
  MemsetStatePreserved.refl s

theorem MemmoveStatePreserved.trans {s0 s1 s2 : State}
    (h01 : MemmoveStatePreserved s0 s1) (h12 : MemmoveStatePreserved s1 s2) :
    MemmoveStatePreserved s0 s2 :=
  LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.MemmoveStatePreserved.trans h01 h12

theorem MemmoveStatePreserved.of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : MemmoveStatePreserved s0 sf :=
  MemsetStatePreserved.of_stdStatePreserved h

theorem MemmoveStatePreserved.of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : MemmoveStatePreserved s0 sf :=
  MemsetStatePreserved.of_stdStatePreserved h

theorem MemmoveStatePreserved.toAllocCallPreserved {s0 sf : State}
    (h : MemmoveStatePreserved s0 sf) (horc : sf.oracle = s0.oracle)
    (hsym : sf.symtab = s0.symtab) : AllocCallPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2.1, horc, hsym⟩

/-- Reconstruct full `ProcessFieldsPreserved s0 sf` (= `StdStatePreserved s0 sf`) from
    `MemmoveStatePreserved s0 sf` and `VmPreserved s0 sf`. -/
theorem processFieldsPreserved_of_memmoveState_and_vm {s0 sf : State}
    (hmsp : MemmoveStatePreserved s0 sf) (hvm : VmPreserved s0 sf) :
    ProcessFieldsPreserved s0 sf :=
  ⟨hmsp.1, hmsp.2.1, hmsp.2.2.1, hmsp.2.2.2.1, hmsp.2.2.2.2.1,
   hmsp.2.2.2.2.2.1, hmsp.2.2.2.2.2.2, hvm.2.2.1⟩

/-- Master separation-logic contract for `void *memmove(void *dst, const void *src, size_t len)`:
    frameless leaf (zero stack bytes), gated by `MemmoveArithBound base buf`
    (`base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63`), returning `x0 = base + dst`,
    updating `base ↦ₛ buf` to `base ↦ₛ ProofLib.listMove buf dst src len`, preserving
    `MemmoveStatePreserved s0 sf`, and never panicking, exiting, or OOMing. -/
@[expose] def masterMemmoveSpec :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := fun (base, buf, dst, src, len) s0 =>
    ⌜MemmoveArithBound base buf ∧
      s0.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧
      s0.readReg64 .x1 = base + BitVec.ofNat 64 src ∧
      (s0.readReg64 .x2).toNat = len ∧
      dst + len ≤ buf.length ∧
      src + len ≤ buf.length⌝ ∗
    (base ↦ₛ buf)
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ MemmoveStatePreserved s0 sf⌝ ∗
    (base ↦ₛ ProofLib.listMove buf dst src len)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Permission-carrying process contract for `memmove`: identical `.pre` to `masterMemmoveSpec`,
    carrying full `ProcessFieldsPreserved s0 sf` (`rfl`-identical to `StdStatePreserved s0 sf`,
    including pointwise `sf.mem.perm a = s0.mem.perm a`) so `HooksDehook.MemmoveGhost` recovers
    `VmPreserved` across `stripS keep`. -/
@[expose] def stdMemmoveSpec :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := masterMemmoveSpec.pre
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ ProcessFieldsPreserved s0 sf⌝ ∗
    (base ↦ₛ ProofLib.listMove buf dst src len)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem stdMemmove_pre_eq : stdMemmoveSpec.pre = masterMemmoveSpec.pre := rfl

/-- `K`-route precondition narrowing: conjoins `⌜keep (s.readReg64 .lr) = false⌝` to `spec.pre`,
    leaving `post`, `onPanic`, `onExit`, and `onOom` unchanged (`rfl`-identical to
    `MemsetCode.memsetSpecK` and `Memmove.memmoveSpecK`). -/
@[expose] def memmoveSpecK (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre x s }

theorem masterMemmoveSpec_stripSInvariant (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterMemmoveSpec where
  pre_eq := fun ⟨_, _, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem masterMemmoveSpecK_stripSInvariant (keep keep' : BitVec 64 → Bool) :
    SpecStripSInvariant keep (memmoveSpecK keep' masterMemmoveSpec) where
  pre_eq := fun ⟨_, _, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem masterMemmoveSpec_preservesFsTrace : SpecPreservesFsTrace masterMemmoveSpec := by
  intro ⟨base, buf, dst, src, len⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [masterMemmoveSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨_, hmsp⟩, _⟩ := hpost
    exact ⟨hmsp.1, FsTraced.of_eq hmsp.2.1 (congrArg FsState.files hmsp.1)⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem masterMemmoveSpecK_preservesFsTrace (keep : BitVec 64 → Bool) :
    SpecPreservesFsTrace (memmoveSpecK keep masterMemmoveSpec) :=
  masterMemmoveSpec_preservesFsTrace

theorem masterMemmoveSpec_pre_setPC (x : BitVec 64 × List (BitVec 8) × Nat × Nat × Nat)
    (s : State) (pc : BitVec 64) :
    masterMemmoveSpec.pre x (s.setPC pc) = masterMemmoveSpec.pre x s := by
  cases x; cases s; rfl

theorem masterMemmoveSpecK_pre_setPC (keep : BitVec 64 → Bool)
    (x : BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) (s : State) (pc : BitVec 64) :
    (memmoveSpecK keep masterMemmoveSpec).pre x (s.setPC pc) =
      (memmoveSpecK keep masterMemmoveSpec).pre x s := by
  cases x; cases s; rfl

theorem masterMemmoveSpec_outcome_setPC
    (x : BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (hout : SubroutineOutcome masterMemmoveSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterMemmoveSpec x R s0 sf := by
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨c, he_st, he⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨hret, ⟨hcc.1, by cases s0; exact hcc.2⟩, ?_⟩
    have hpeq : masterMemmoveSpec.post x (s0.setPC pc) sf = masterMemmoveSpec.post x s0 sf := by
      cases x; cases s0; rfl
    rwa [hpeq] at hpost
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem masterMemmoveSpecK_outcome_setPC (keep : BitVec 64 → Bool)
    (x : BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (hout : SubroutineOutcome (memmoveSpecK keep masterMemmoveSpec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (memmoveSpecK keep masterMemmoveSpec) x R s0 sf :=
  masterMemmoveSpec_outcome_setPC x R s0 sf pc hout

/-! ## 2. Contiguous 956 B `.text.b_pre` Hull (`bPreHullWords`) & Region-Local `subroutine_ok` -/

/-- Default 4-byte section-alignment pad word (`0#32` = `udf #0`) between `99`-word `memcpy.lo`
    (`396` B) and 16-byte-aligned `65`-word `memset.lo` (`260` B) in `.text.b_pre :text_b =0`. -/
@[expose] def bPrePadWord : BitVec 32 := 0#32

/-- Byte offset (`400#64`) of `memset` (`+400`, after `99` words of `memcpy` + `1` pad word)
    inside the contiguous `.text.b_pre` hull. -/
@[expose] def bPreMemsetByteOff : BitVec 64 :=
  BitVec.ofNat 64 (4 * (memcpySymWords.length + 1))

/-- Byte offset (`660#64`) of `memmove` (`+660`, after `99` words of `memcpy` + `1` pad word +
    `65` words of `memset`) inside the contiguous `.text.b_pre` hull. -/
@[expose] def bPreMemmoveByteOff : BitVec 64 :=
  BitVec.ofNat 64 (4 * (memcpySymWords.length + 1 + memsetWordsSym.length))

theorem bPreMemsetByteOff_eq : bPreMemsetByteOff = 400#64 := rfl

theorem bPreMemmoveByteOff_eq : bPreMemmoveByteOff = 660#64 := rfl

/-- Contiguous `239`-word (`956`-byte) `.text.b_pre` word list matching stock `libc.a` layout
    (`D-C2f = 2C`):
    - `memcpySymWords` (`99` words = `396` B) at `m`,
    - `[padWord]` (`1` word = `4` B, defaulting to `bPrePadWord = 0#32`) at `m + 396`,
    - `memsetWordsSym` (`65` words = `260` B) at `m + bPreMemsetByteOff`, and
    - `memmoveLibcaWords` (`74` words = `296` B, patched with `resolve`) at `m + bPreMemmoveByteOff`.
    All region-local `subroutine_ok` theorems below are polymorphic in `padWord : BitVec 32`. -/
@[expose] def bPreHullWords (m : BitVec 64)
    (resolve : String → BitVec 64 := fun _ => m)
    (padWord : BitVec 32 := bPrePadWord) : List (BitVec 32) :=
  (memcpySymWords ++ [padWord] ++ memsetWordsSym) ++
    Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords (m + bPreMemmoveByteOff) resolve

theorem bPreHullWords_length (m : BitVec 64)
    (resolve : String → BitVec 64 := fun _ => m)
    (padWord : BitVec 32 := bPrePadWord) :
    (bPreHullWords m resolve padWord).length = 239 := by
  simp [bPreHullWords, Obj.patchCalls]
  decide

private theorem hookFree_mono_subrange {prog : Program} {off len subOff subLen : Nat}
    (hf : prog.hookFree off len) (hlo : off ≤ subOff) (hhi : subOff + subLen ≤ off + len) :
    prog.hookFree subOff subLen := by
  unfold Program.hookFree at hf ⊢
  rcases hf with ⟨hst, hsym⟩
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at hst ⊢
    intro ⟨n, o⟩ hmem
    have h := hst ⟨n, o⟩ hmem
    by_cases hsub : subOff ≤ o ∧ o < subOff + subLen
    · have hbig : off ≤ o ∧ o < off + len := ⟨by omega, by omega⟩
      simp [hsub, hbig] at h ⊢
      exact h
    · simp
      exact Or.inl (by omega)
  · rw [List.all_eq_true] at hsym ⊢
    intro ⟨n, o⟩ hmem
    have h := hsym ⟨n, o⟩ hmem
    by_cases hsub : subOff ≤ o ∧ o < subOff + subLen
    · have hbig : off ≤ o ∧ o < off + len := ⟨by omega, by omega⟩
      simp [hsub, hbig] at h ⊢
      exact h
    · simp
      exact Or.inl (by omega)

/-- Left slice of `hasWords` over `ws1 ++ ws2` at the base address `m`. -/
theorem hasWords_append_left {prog : Program} {m : BitVec 64} {ws1 ws2 : List (BitVec 32)}
    (h : prog.hasWords m (ws1 ++ ws2)) :
    prog.hasWords m ws1 := by
  unfold Program.hasWords Program.hasWordsOff at h ⊢
  rcases h with ⟨hfit, hread, hfree⟩
  rw [List.length_append] at hfit hfree
  refine ⟨by omega, fun i hi => ?_, hookFree_mono_subrange hfree (Nat.le_refl _) (by omega)⟩
  have hi' : i < (ws1 ++ ws2).length := by rw [List.length_append]; omega
  rw [hread i hi', List.getElem_append_left hi]

/-- Right slice of `hasWords` over `ws1 ++ ws2` at `m + BitVec.ofNat 64 (4 * ws1.length)` whenever
    `ws2` is non-empty (`0 < ws2.length` ensures `off + 4 * ws1.length < 2 ^ 64` from `h.1`). -/
theorem hasWords_append_right {prog : Program} {m : BitVec 64} {ws1 ws2 : List (BitVec 32)}
    (h : prog.hasWords m (ws1 ++ ws2)) (hpos : 0 < ws2.length) :
    prog.hasWords (m + BitVec.ofNat 64 (4 * ws1.length)) ws2 := by
  unfold Program.hasWords Program.hasWordsOff at h ⊢
  rcases h with ⟨hfit, hread, hfree⟩
  rw [List.length_append] at hfit hfree
  have hk_lt : (m - prog.base).toNat + 4 * ws1.length < 2 ^ 64 := by omega
  have hoff_eq : ((m + BitVec.ofNat 64 (4 * ws1.length)) - prog.base).toNat =
      (m - prog.base).toNat + 4 * ws1.length := by
    have hbv : (m + BitVec.ofNat 64 (4 * ws1.length)) - prog.base =
        (m - prog.base) + BitVec.ofNat 64 (4 * ws1.length) := by bv_omega
    rw [hbv, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 4 * ws1.length < 2 ^ 64), Nat.mod_eq_of_lt hk_lt]
  rw [hoff_eq]
  refine ⟨by omega, fun i hi => ?_, hookFree_mono_subrange hfree (by omega) (by omega)⟩
  have hidx : (m - prog.base).toNat + 4 * ws1.length + 4 * i =
      (m - prog.base).toNat + 4 * (ws1.length + i) := by omega
  have hi' : ws1.length + i < (ws1 ++ ws2).length := by rw [List.length_append]; omega
  rw [hidx, hread (ws1.length + i) hi', List.getElem_append_right (Nat.le_add_right ws1.length i)]
  simp only [Nat.add_sub_cancel_left]

/-- Extract the `memcpy` (`+0`, `99` words) slice at `m` from a `239`-word `bPreHullWords` witness. -/
theorem bPreHull_hasWords_memcpy {prog : Program} {m : BitVec 64}
    {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hhull : prog.hasWords m (bPreHullWords m resolve padWord)) :
    prog.hasWords m memcpySymWords :=
  hasWords_append_left (hasWords_append_left (hasWords_append_left hhull))

/-- Extract the `memset` (`+400`, `65` words) slice at `m + bPreMemsetByteOff` from a `239`-word
    `bPreHullWords` witness. -/
theorem bPreHull_hasWords_memset {prog : Program} {m : BitVec 64}
    {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hhull : prog.hasWords m (bPreHullWords m resolve padWord)) :
    prog.hasWords (m + bPreMemsetByteOff) memsetWordsSym := by
  have hpre : prog.hasWords m ((memcpySymWords ++ [padWord]) ++ memsetWordsSym) :=
    hasWords_append_left hhull
  have hlen : (memcpySymWords ++ [padWord]).length = memcpySymWords.length + 1 := by simp
  have hms := hasWords_append_right hpre (by decide : 0 < memsetWordsSym.length)
  rwa [hlen] at hms

/-- Extract the `memmove` (`+660`, `74` patched words) slice at `m + bPreMemmoveByteOff` from a
    `239`-word `bPreHullWords` witness. -/
theorem bPreHull_hasWords_memmove {prog : Program} {m : BitVec 64}
    {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hhull : prog.hasWords m (bPreHullWords m resolve padWord)) :
    prog.hasWords (m + bPreMemmoveByteOff)
      (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords (m + bPreMemmoveByteOff) resolve) := by
  have hlen : (memcpySymWords ++ [padWord] ++ memsetWordsSym).length =
      memcpySymWords.length + 1 + memsetWordsSym.length := by simp; omega
  have hmm := hasWords_append_right hhull (by simp [Obj.patchCalls]; decide)
  rwa [hlen] at hmm

/-- The `-764`-byte (`-191`-word) branch from `(m + bPreMemmoveByteOff) + reloc_call_off% memmoveLibcaCalls "memcpy"`
    back to `m` (`resolve "memcpy" = m`) is in `Obj.BranchInRange` unconditionally for every `m : BitVec 64`. -/
theorem branchInRange_bPreHull (m : BitVec 64) {resolve : String → BitVec 64}
    (hres : resolve "memcpy" = m := by rfl) :
    Obj.BranchInRange
      ((m + bPreMemmoveByteOff) + reloc_call_off% memmoveLibcaCalls "memcpy")
      (resolve "memcpy") := by
  have hoff : (reloc_call_off% memmoveLibcaCalls "memcpy") = 104#64 := rfl
  have hd :
      resolve "memcpy" - ((m + bPreMemmoveByteOff) + reloc_call_off% memmoveLibcaCalls "memcpy") =
        -764#64 := by
    rw [hres, bPreMemmoveByteOff_eq, hoff]
    bv_omega
  unfold Obj.BranchInRange
  rw [hd]
  decide

private theorem wordToBytesLE_concat (w : BitVec 32) :
    w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  bv_bits

private theorem drop_flatMap_wordToBytesLE (words : List (BitVec 32)) (i : Nat) :
    (words.flatMap Program.wordToBytesLE).drop (4 * i) =
      (words.drop i).flatMap Program.wordToBytesLE := by
  induction words generalizing i with
  | nil => simp
  | cons _ ws ih =>
    cases i with
    | zero => rfl
    | succ k =>
      have hmul : 4 * (k + 1) = 4 + 4 * k := by omega
      rw [List.flatMap_cons, hmul, ← List.drop_drop]
      simp only [Program.wordToBytesLE, List.cons_append, List.nil_append,
        List.drop_succ_cons, List.drop_zero]
      exact ih k

private theorem readWordOff_ofWords_mul4 (base : BitVec 64) (words : List (BitVec 32)) (i : Nat) :
    (Program.ofWords base words).readWordOff (4 * i) = words[i]? := by
  unfold Program.readWordOff Program.ofWords
  have hmod : ¬(4 * i % 4 ≠ 0) := by omega
  simp only [hmod, ↓reduceIte, drop_flatMap_wordToBytesLE]
  have hget : words[i]? = (words.drop i)[0]? := by simp [List.getElem?_drop]
  rw [hget]
  cases words.drop i with
  | nil => simp
  | cons w _ => simp [Program.wordToBytesLE, wordToBytesLE_concat]

/-- `pureWordsProg m (bPreHullWords m resolve padWord)` holds the `239`-word `.text.b_pre` hull at `m`. -/
theorem pureWordsProg_bPreHull_hasWords (m : BitVec 64)
    (resolve : String → BitVec 64 := fun _ => m)
    (padWord : BitVec 32 := bPrePadWord) :
    (pureWordsProg m (bPreHullWords m resolve padWord)).hasWords m
      (bPreHullWords m resolve padWord) := by
  refine pureWordsProg_hasWords (by rw [bPreHullWords_length m resolve padWord]; decide)
    (List.all_eq_true.mpr fun i _ => ?_)
  have h1 := readWordOff_ofWords_mul4 m (bPreHullWords m resolve padWord) i
  simp [pureWordsProg, h1]


/-- Region-local `subroutine_ok` for `withVmPreserved masterMemcpySpec` on any hook-free `P_sub`
    holding `memcpySymWords`. -/
theorem subroutine_ok_masterMemcpyVm_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry memcpySymWords) :
    subroutine_ok P_sub entry (withVmPreserved masterMemcpySpec) := by
  refine subroutine_ok_outcome_intro fun ⟨ro, dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  cases ro
  · have hpre' := stdMemcpy_pre_of_masterMemcpy_pre hpre
    refine (subroutine_ok_stdMemcpy_of_hasWords hsub_no hwords).mono_outcome
      (dst, src, bs) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | hpan | hex)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [ProofLib.StdStartup.stdMemcpySpec, withVmPreserved, masterMemcpySpec,
        VerifiedLibraries.Musl.memcpySrc, cond] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨vmPreserved_of_processFieldsPreserved hq.1.2, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq.1.1, MemcpyCode.MemcpyStatePreserved.of_stdStatePreserved hq.1.2⟩, by
        rw [← sepConj_assoc]; exact hq.2⟩
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)
  · have hpre' := stdMemcpyRO_pre_of_masterMemcpy_pre hpre
    refine (subroutine_ok_stdMemcpyRO_of_hasWords hsub_no hwords).mono_outcome
      (dst, src, bs) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | hpan | hex)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [ProofLib.StdStartup.stdMemcpyROSpec, withVmPreserved, masterMemcpySpec,
        VerifiedLibraries.Musl.memcpySrc, cond] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨vmPreserved_of_processFieldsPreserved hq.1.2, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq.1.1, MemcpyCode.MemcpyStatePreserved.of_stdStatePreserved hq.1.2⟩, by
        rw [← sepConj_assoc]; exact hq.2⟩
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)

/-- Region-local `subroutine_ok` for permission-carrying `stdMemmoveSpec` (`ProcessFieldsPreserved`)
    at `m + bPreMemmoveByteOff` on any hook-free `P_sub` holding the `239`-word `bPreHullWords`
    hull at `m` (`resolve "memcpy" = m`). -/
theorem subroutine_ok_bPreHull_stdMemmove_of_hasWords
    {P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    subroutine_ok P_sub (m + bPreMemmoveByteOff) stdMemmoveSpec := by
  have hmc_vm : subroutine_ok P_sub (resolve "memcpy") (withVmPreserved masterMemcpySpec) := by
    rw [hres]
    exact subroutine_ok_masterMemcpyVm_of_hasWords hsub_no (bPreHull_hasWords_memcpy hhull)
  have hmm_vm :=
    memmove_masterVm_patchCalls_ok
      (branchInRange_bPreHull m hres)
      (bPreHull_hasWords_memmove hhull)
      hsub_no
      (memcpyTailVm_ok_of_masterMemcpyVm_ok hmc_vm)
  refine subroutine_ok_map hmm_vm ?_
  rintro ⟨base, buf, dst, src, len⟩ R s0 hpre
  dsimp only [stdMemmoveSpec, masterMemmoveSpec, MemmoveArithBound] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨⟨hwrap, hsmall⟩, hx0, hx1, hx2, hdst, hsrc⟩, hmem⟩
  refine ⟨(base + BitVec.ofNat 64 dst, base + BitVec.ofNat 64 src, s0.readReg64 .x2,
      base, buf, dst, src), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.masterMemmoveVmSpec,
      LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.withVmPreserved,
      LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.masterMemmoveSpec,
      memmoveSpec, CType.InteriorPtr, CType.SizeT, CType.scalarTy, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, by omega, by omega, hwrap, hsmall, Satisfies.of_eq hmem⟩
  · dsimp only [LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.masterMemmoveVmSpec,
      LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.withVmPreserved,
      LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.masterMemmoveSpec,
      memmoveSpec, CType.InteriorPtr] at hpost
    dsimp only [stdMemmoveSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, hx2,
      moveBytes_eq_listMove] at hpost ⊢
    exact ⟨⟨hpost.2.2.1, processFieldsPreserved_of_memmoveState_and_vm hpost.2.1 hpost.1⟩,
      Satisfies.of_eq hpost.2.2.2⟩

/-- Region-local `subroutine_ok` for `masterMemmoveSpec` at `m + bPreMemmoveByteOff` on any
    hook-free `P_sub` holding the `239`-word `bPreHullWords` hull at `m` (`resolve "memcpy" = m`). -/
theorem subroutine_ok_bPreHull_masterMemmove_of_hasWords
    {P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    subroutine_ok P_sub (m + bPreMemmoveByteOff) masterMemmoveSpec := by
  refine subroutine_ok_mono (subroutine_ok_bPreHull_stdMemmove_of_hasWords hsub_no hhull hres)
    (fun _ _ _ hp => hp)
    (fun ⟨base, buf, dst, src, len⟩ R s0 sf hq => ?_)
  dsimp only [stdMemmoveSpec, masterMemmoveSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, MemmoveStatePreserved.of_processFieldsPreserved hq.1.2⟩, hq.2⟩

/-- Region-local `subroutine_ok` for `withVmPreserved masterMemmoveSpec` at `m + bPreMemmoveByteOff`
    on any hook-free `P_sub` holding the `239`-word `bPreHullWords` hull at `m`. -/
theorem subroutine_ok_bPreHull_masterMemmoveVm_of_hasWords
    {P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    subroutine_ok P_sub (m + bPreMemmoveByteOff) (withVmPreserved masterMemmoveSpec) := by
  refine subroutine_ok_mono (subroutine_ok_bPreHull_stdMemmove_of_hasWords hsub_no hhull hres)
    (fun _ _ _ hp => hp)
    (fun ⟨base, buf, dst, src, len⟩ R s0 sf hq => ?_)
  dsimp only [stdMemmoveSpec, withVmPreserved, masterMemmoveSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨vmPreserved_of_processFieldsPreserved hq.1.2, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hq.1.1, MemmoveStatePreserved.of_processFieldsPreserved hq.1.2⟩, hq.2⟩

/-- Region-local `subroutine_ok` for `memmoveSpecK keep masterMemmoveSpec` at
    `m + bPreMemmoveByteOff` on any hook-free `P_sub` holding `bPreHullWords` at `m`. -/
theorem subroutine_ok_bPreHull_masterMemmoveK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl) :
    subroutine_ok P_sub (m + bPreMemmoveByteOff) (memmoveSpecK keep masterMemmoveSpec) := by
  refine subroutine_ok_mono (subroutine_ok_bPreHull_masterMemmove_of_hasWords hsub_no hhull hres)
    (fun _ _ _ hp => ?_)
    (fun _ _ _ _ hq => hq)
  dsimp only [memmoveSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Concrete single-`P_sub` `.text.b_pre` hull witness satisfying `stdMemmoveSpec`. -/
theorem pureWordsProg_bPreHull_stdMemmove_ok (m : BitVec 64)
    {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hres : resolve "memcpy" = m := by rfl) :
    subroutine_ok (pureWordsProg m (bPreHullWords m resolve padWord))
      (m + bPreMemmoveByteOff) stdMemmoveSpec :=
  subroutine_ok_bPreHull_stdMemmove_of_hasWords
    (pureWordsProg_externAt_none m _) (pureWordsProg_bPreHull_hasWords m resolve padWord) hres

/-- Concrete single-`P_sub` `.text.b_pre` hull witness satisfying `masterMemmoveSpec`. -/
theorem pureWordsProg_bPreHull_masterMemmove_ok (m : BitVec 64)
    {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hres : resolve "memcpy" = m := by rfl) :
    subroutine_ok (pureWordsProg m (bPreHullWords m resolve padWord))
      (m + bPreMemmoveByteOff) masterMemmoveSpec :=
  subroutine_ok_bPreHull_masterMemmove_of_hasWords
    (pureWordsProg_externAt_none m _) (pureWordsProg_bPreHull_hasWords m resolve padWord) hres

/-- Concrete single-`P_sub` `.text.b_pre` hull witness satisfying `withVmPreserved masterMemmoveSpec`. -/
theorem pureWordsProg_bPreHull_masterMemmoveVm_ok (m : BitVec 64)
    {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hres : resolve "memcpy" = m := by rfl) :
    subroutine_ok (pureWordsProg m (bPreHullWords m resolve padWord))
      (m + bPreMemmoveByteOff) (withVmPreserved masterMemmoveSpec) :=
  subroutine_ok_bPreHull_masterMemmoveVm_of_hasWords
    (pureWordsProg_externAt_none m _) (pureWordsProg_bPreHull_hasWords m resolve padWord) hres

/-- Concrete single-`P_sub` `.text.b_pre` hull witness satisfying `memmoveSpecK keep masterMemmoveSpec`. -/
theorem pureWordsProg_bPreHull_masterMemmoveK_ok (keep : BitVec 64 → Bool) (m : BitVec 64)
    {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hres : resolve "memcpy" = m := by rfl) :
    subroutine_ok (pureWordsProg m (bPreHullWords m resolve padWord))
      (m + bPreMemmoveByteOff) (memmoveSpecK keep masterMemmoveSpec) :=
  subroutine_ok_bPreHull_masterMemmoveK_of_hasWords keep
    (pureWordsProg_externAt_none m _) (pureWordsProg_bPreHull_hasWords m resolve padWord) hres

/-! ## 3. `W`-Free Fallback `hookMemmove` & Generic `hookMemmoveOf` Soundness -/

theorem hookMemmove_processFieldsPreserved (s : State) :
    ProcessFieldsPreserved s (hookMemmove s) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun a => ?_⟩
  simp [hookMemmove, hookMemcpy, retHook, State.setPC, State.setMem]

theorem hookMemmove_oracle_eq (s : State) : (hookMemmove s).oracle = s.oracle := rfl

theorem hookMemmove_symtab_eq (s : State) : (hookMemmove s).symtab = s.symtab := rfl

theorem hookMemmove_allocCallPreserved (s : State) :
    AllocCallPreserved s (hookMemmove s) :=
  (MemmoveStatePreserved.of_processFieldsPreserved (hookMemmove_processFieldsPreserved s)).toAllocCallPreserved
    rfl rfl

theorem keepFsTrace_hookMemmove_eq (s : State) :
    keepFsTrace hookMemmove s = hookMemmove s := by
  unfold keepFsTrace
  cases s
  rfl

/-- Generic `W`-independent `masterMemmoveSpec` soundness (Template F3): any `f : State → State`
    satisfying `HookOk f (ProofLib.libcMemmoveSpec 0)` and preserving `MemmoveStatePreserved`
    satisfies `HookOk f masterMemmoveSpec`. -/
theorem hookMemmoveOf_masterMemmove_ok {f : State → State}
    (hlib : HookOk f (ProofLib.libcMemmoveSpec 0))
    (hst : ∀ s : State, MemmoveStatePreserved s (f s)) :
    HookOk f masterMemmoveSpec := by
  refine hookOk_map_frame_pureAbort id (fun _ _ => emp) hlib
    (fun ⟨base, buf, dst, src, len⟩ s0 => ?_)
    (fun ⟨base, buf, dst, src, len⟩ s0 sf hsf _ => ?_)
  · dsimp only [masterMemmoveSpec, ProofLib.libcMemmoveSpec, id, stackAt]
    rw [memRegion_zero, sepConj_emp, sepConj_emp]
    exact Entails.pure_left fun ⟨_, hx0, hx1, hx2, hdst, hsrc⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2, hdst, hsrc⟩ (Entails.refl _)
  · subst hsf
    dsimp only [ProofLib.libcMemmoveSpec, masterMemmoveSpec, id, stackAt]
    rw [memRegion_zero, sepConj_emp, sepConj_emp]
    exact Entails.pure_left fun hx0 =>
      Entails.pure_right ⟨hx0, hst s0⟩ (Entails.refl _)

/-- `K`-narrowed counterpart of `hookMemmoveOf_masterMemmove_ok`. -/
theorem hookMemmoveOf_masterMemmoveK_ok (keep : BitVec 64 → Bool) {f : State → State}
    (hlib : HookOk f (ProofLib.libcMemmoveSpec 0))
    (hst : ∀ s : State, MemmoveStatePreserved s (f s)) :
    HookOk f (memmoveSpecK keep masterMemmoveSpec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [memmoveSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hookMemmoveOf_masterMemmove_ok hlib hst x R s0 hrun hpre.2 hsp

/-- Fixed `W`-free `hookMemmove` satisfies `masterMemmoveSpec`. -/
theorem hookMemmove_masterMemmove_ok : HookOk hookMemmove masterMemmoveSpec :=
  hookMemmoveOf_masterMemmove_ok (ProofLib.hookMemmove_ok 0)
    (fun s => MemmoveStatePreserved.of_processFieldsPreserved (hookMemmove_processFieldsPreserved s))

/-- Fixed `W`-free `hookMemmove` satisfies permission-carrying `stdMemmoveSpec`. -/
theorem hookMemmove_stdMemmove_ok : HookOk hookMemmove stdMemmoveSpec := by
  refine hookOk_map_frame_pureAbort id (fun _ _ => emp) (ProofLib.hookMemmove_ok 0)
    (fun ⟨base, buf, dst, src, len⟩ s0 => ?_)
    (fun ⟨base, buf, dst, src, len⟩ s0 sf hsf _ => ?_)
  · dsimp only [stdMemmoveSpec, masterMemmoveSpec, ProofLib.libcMemmoveSpec, id, stackAt]
    rw [memRegion_zero, sepConj_emp, sepConj_emp]
    exact Entails.pure_left fun ⟨_, hx0, hx1, hx2, hdst, hsrc⟩ =>
      Entails.pure_right ⟨hx0, hx1, hx2, hdst, hsrc⟩ (Entails.refl _)
  · subst hsf
    dsimp only [ProofLib.libcMemmoveSpec, stdMemmoveSpec, id, stackAt]
    rw [memRegion_zero, sepConj_emp, sepConj_emp]
    exact Entails.pure_left fun hx0 =>
      Entails.pure_right ⟨hx0, hookMemmove_processFieldsPreserved s0⟩ (Entails.refl _)

/-- Fixed `W`-free `hookMemmove` satisfies `withVmPreserved masterMemmoveSpec`. -/
theorem hookMemmove_masterMemmoveVm_ok : HookOk hookMemmove (withVmPreserved masterMemmoveSpec) :=
  hookOk_withVmPreserved hookMemmove_masterMemmove_ok hookMemmove_vmPreserved

/-- Fixed `W`-free `hookMemmove` satisfies `memmoveSpecK keep masterMemmoveSpec` for any `keep`. -/
theorem hookMemmove_masterMemmoveK_ok (keep : BitVec 64 → Bool) :
    HookOk hookMemmove (memmoveSpecK keep masterMemmoveSpec) :=
  hookMemmoveOf_masterMemmoveK_ok keep (ProofLib.hookMemmove_ok 0)
    (fun s => MemmoveStatePreserved.of_processFieldsPreserved (hookMemmove_processFieldsPreserved s))

/-! ## 4. Generic `HookOk` Consequence Lifts from `masterMemmoveSpec` -/

/-- Any `HookOk f spec` weakens to `HookOk f (memmoveSpecK keep spec)`. -/
theorem hookOk_memmoveSpecK_of_plain (keep : BitVec 64 → Bool) {α : Type} {f : State → State}
    {spec : Spec α} (hh : HookOk f spec) :
    HookOk f (memmoveSpecK keep spec) :=
  MemcpyCode.hookOk_memcpySpecK_of_plain keep hh

/-- Lift a ghost-reindexing frame/consequence derivation across `memmoveSpecK keep`. -/
theorem hookOk_memmoveSpecK_map_frame_pureAbort (keep : BitVec 64 → Bool)
    {α β : Type} {f : State → State} {base : Spec α} {target : Spec β}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk f (memmoveSpecK keep base))
    (hpre : ∀ y s0, target.pre y s0 ⊢ base.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, sf = f s0 → sf.symtab = s0.symtab →
      base.post (g y) s0 sf ∗ F y s0 ⊢ target.post y s0 sf)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (memmoveSpecK keep target) :=
  MemcpyCode.hookOk_memcpySpecK_map_frame_pureAbort keep g F hh hpre hpost hpan hex hoom

/-- Bounded (`MemmoveArithBound`) counterpart of `VecDequeGrowBudgetAux.sessionMemmoveAcpSpec`:
    same `AllocCallPreserved ∧ VmPreserved` postcondition, gated by `MemmoveArithBound base buf`
    in `.pre` so real `libc.a` `memmove` satisfies it (`VecDequeGrowBudget` / `AddChunkCl1PlacedBudget`
    / `SpqrChainPlacedInstBudget:1389`). -/
@[expose] def sessionMemmoveBoundedAcpSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  { sessionMemmoveAcpSpec hookStack with
    pre := (sessionMemmoveBoundedSpec hookStack).pre }

private theorem bounded_pre_entails_master (stk : Nat)
    (x : BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) (s0 : State) :
    (libcMemmoveBoundedSpec stk).pre x s0 ⊢ masterMemmoveSpec.pre x s0 ∗ stackAt s0.sp stk := by
  rcases x with ⟨base, buf, dst, src, len⟩
  dsimp only [libcMemmoveBoundedSpec, ProofLib.libcMemmoveSpec, masterMemmoveSpec]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun hbound =>
    Entails.pure_left fun ⟨hx0, hx1, hx2, hdst, hsrc⟩ =>
      Entails.pure_right ⟨hbound, hx0, hx1, hx2, hdst, hsrc⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemmoveSpec` to `HookOk f (libcMemmoveBoundedSpec stk)`. -/
theorem hookOk_libcMemmoveBounded_of_master {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (stk : Nat := extHookStack) :
    HookOk f (libcMemmoveBoundedSpec stk) := by
  refine hookOk_map_frame_pureAbort id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf _ _ => ?_)
  dsimp only [masterMemmoveSpec, libcMemmoveBoundedSpec, ProofLib.libcMemmoveSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- `K`-narrowed counterpart of `hookOk_libcMemmoveBounded_of_master`. -/
theorem hookOk_libcMemmoveBoundedK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memmoveSpecK keep masterMemmoveSpec)) (stk : Nat := extHookStack) :
    HookOk f (memmoveSpecK keep (libcMemmoveBoundedSpec stk)) := by
  refine hookOk_memmoveSpecK_map_frame_pureAbort keep id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf _ _ => ?_)
  dsimp only [masterMemmoveSpec, libcMemmoveBoundedSpec, ProofLib.libcMemmoveSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, _⟩ => Entails.pure_right hx0 (Entails.refl _)

/-- Lift `HookOk f masterMemmoveSpec` + pointwise `VmPreserved` to
    `HookOk f (withVmPreserved (libcMemmoveBoundedSpec stk))`. -/
theorem hookOk_withVmPreserved_libcMemmoveBounded_of_master {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    (stk : Nat := extHookStack) :
    HookOk f (withVmPreserved (libcMemmoveBoundedSpec stk)) :=
  hookOk_withVmPreserved (hookOk_libcMemmoveBounded_of_master hh stk) hvm

/-- Lift `HookOk f masterMemmoveSpec` to `HookOk f (sessionMemmoveBoundedSpec stk)`. -/
theorem hookOk_sessionMemmoveBounded_of_master {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (stk : Nat := extHookStack) :
    HookOk f (sessionMemmoveBoundedSpec stk) := by
  refine hookOk_map_frame_pureAbort id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf _ _ => ?_)
  dsimp only [masterMemmoveSpec, sessionMemmoveBoundedSpec, sessionMemmoveSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hmsp⟩ => Entails.pure_right ⟨hx0, hmsp.2.1⟩ (Entails.refl _)

/-- `K`-narrowed counterpart of `hookOk_sessionMemmoveBounded_of_master`. -/
theorem hookOk_sessionMemmoveBoundedK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memmoveSpecK keep masterMemmoveSpec)) (stk : Nat := extHookStack) :
    HookOk f (memmoveSpecK keep (sessionMemmoveBoundedSpec stk)) := by
  refine hookOk_memmoveSpecK_map_frame_pureAbort keep id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf _ _ => ?_)
  dsimp only [masterMemmoveSpec, sessionMemmoveBoundedSpec, sessionMemmoveSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hmsp⟩ => Entails.pure_right ⟨hx0, hmsp.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemmoveSpec` to `HookOk f (keepsFs (sessionMemmoveBoundedSpec stk))`. -/
theorem hookOk_sessionMemmoveBounded_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (stk : Nat := extHookStack) :
    HookOk f (keepsFs (sessionMemmoveBoundedSpec stk)) := by
  refine hookOk_map_frame_pureAbort id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf _ _ => ?_)
  dsimp only [masterMemmoveSpec, keepsFs, sessionMemmoveBoundedSpec, sessionMemmoveSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hmsp⟩ =>
    Entails.pure_right hmsp.1 (Entails.pure_right ⟨hx0, hmsp.2.1⟩ (Entails.refl _))

/-- `K`-narrowed counterpart of `hookOk_sessionMemmoveBounded_keepsFs_of_master`. -/
theorem hookOk_sessionMemmoveBounded_keepsFsK_of_master (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (memmoveSpecK keep masterMemmoveSpec)) (stk : Nat := extHookStack) :
    HookOk f (memmoveSpecK keep (keepsFs (sessionMemmoveBoundedSpec stk))) := by
  refine hookOk_memmoveSpecK_map_frame_pureAbort keep id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf _ _ => ?_)
  dsimp only [masterMemmoveSpec, keepsFs, sessionMemmoveBoundedSpec, sessionMemmoveSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hmsp⟩ =>
    Entails.pure_right hmsp.1 (Entails.pure_right ⟨hx0, hmsp.2.1⟩ (Entails.refl _))

/-- Lift `HookOk f masterMemmoveSpec` + pointwise `VmPreserved` to
    `HookOk f (sessionMemmoveBoundedBudgetSpec stk)`. -/
theorem hookOk_sessionMemmoveBoundedBudget_of_master {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    (stk : Nat := extHookStack) :
    HookOk f (sessionMemmoveBoundedBudgetSpec stk) :=
  hookOk_withVmPreserved (hookOk_sessionMemmoveBounded_of_master hh stk) hvm

/-- `K`-narrowed counterpart of `hookOk_sessionMemmoveBoundedBudget_of_master`. -/
theorem hookOk_sessionMemmoveBoundedBudgetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memmoveSpecK keep masterMemmoveSpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) (stk : Nat := extHookStack) :
    HookOk f (memmoveSpecK keep (sessionMemmoveBoundedBudgetSpec stk)) :=
  hookOk_withVmPreserved (hookOk_sessionMemmoveBoundedK_of_master keep hh stk) hvm

/-- Lift `HookOk f masterMemmoveSpec` + pointwise `VmPreserved` + `oracle` preservation to
    `HookOk f (sessionMemmoveBoundedAcpSpec stk)` (`AllocCallPreserved ∧ VmPreserved`). -/
theorem hookOk_sessionMemmoveBoundedAcp_of_master {f : State → State}
    (hh : HookOk f masterMemmoveSpec)
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle)
    (stk : Nat := 4096) :
    HookOk f (sessionMemmoveBoundedAcpSpec stk) := by
  refine hookOk_map_frame_pureAbort id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf hsf hsym => ?_)
  subst hsf
  dsimp only [masterMemmoveSpec, sessionMemmoveBoundedAcpSpec, sessionMemmoveAcpSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hmsp⟩ =>
    Entails.pure_right ⟨hx0, hmsp.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- `K`-narrowed counterpart of `hookOk_sessionMemmoveBoundedAcp_of_master`. -/
theorem hookOk_sessionMemmoveBoundedAcpK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memmoveSpecK keep masterMemmoveSpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle)
    (stk : Nat := 4096) :
    HookOk f (memmoveSpecK keep (sessionMemmoveBoundedAcpSpec stk)) := by
  refine hookOk_memmoveSpecK_map_frame_pureAbort keep id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf hsf hsym => ?_)
  subst hsf
  dsimp only [masterMemmoveSpec, sessionMemmoveBoundedAcpSpec, sessionMemmoveAcpSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hmsp⟩ =>
    Entails.pure_right ⟨hx0, hmsp.toAllocCallPreserved (horc s0) hsym, hvm s0⟩ (Entails.refl _)

/-- Lift `HookOk f masterMemmoveSpec` + pointwise `VmPreserved` + `oracle` preservation to
    `HookOk f (withAllocVmPreserved (sessionMemmoveBoundedSpec stk))`
    (covering `stk = 0` for `SpqrSendCoinsPlacedInstBudget:333` as well as general `stk`). -/
theorem hookOk_allocVmPreserved_sessionMemmoveBounded_of_master {f : State → State}
    (hh : HookOk f masterMemmoveSpec)
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle)
    (stk : Nat := 0) :
    HookOk f (withAllocVmPreserved (sessionMemmoveBoundedSpec stk)) := by
  refine hookOk_map_frame_pureAbort id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf hsf hsym => ?_)
  subst hsf
  dsimp only [masterMemmoveSpec, withAllocVmPreserved, sessionMemmoveBoundedSpec,
    sessionMemmoveSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hmsp⟩ =>
    Entails.pure_right ⟨hmsp.toAllocCallPreserved (horc s0) hsym, hvm s0⟩
      (Entails.pure_right ⟨hx0, hmsp.2.1⟩ (Entails.refl _))

/-- `K`-narrowed counterpart of `hookOk_allocVmPreserved_sessionMemmoveBounded_of_master`. -/
theorem hookOk_allocVmPreserved_sessionMemmoveBoundedK_of_master (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (memmoveSpecK keep masterMemmoveSpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle)
    (stk : Nat := 0) :
    HookOk f (memmoveSpecK keep (withAllocVmPreserved (sessionMemmoveBoundedSpec stk))) := by
  refine hookOk_memmoveSpecK_map_frame_pureAbort keep id (fun _ s0 => stackAt s0.sp stk) hh
    (bounded_pre_entails_master stk) (fun ⟨base, buf, dst, src, len⟩ s0 sf hsf hsym => ?_)
  subst hsf
  dsimp only [masterMemmoveSpec, withAllocVmPreserved, sessionMemmoveBoundedSpec,
    sessionMemmoveSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hmsp⟩ =>
    Entails.pure_right ⟨hmsp.toAllocCallPreserved (horc s0) hsym, hvm s0⟩
      (Entails.pure_right ⟨hx0, hmsp.2.1⟩ (Entails.refl _))

/-- `hookMemmove` satisfies `sessionMemmoveBoundedAcpSpec stk`. -/
theorem hookMemmove_sessionBoundedAcp_ok (stk : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveBoundedAcpSpec stk) :=
  hookOk_sessionMemmoveBoundedAcp_of_master
    hookMemmove_masterMemmove_ok hookMemmove_vmPreserved hookMemmove_oracle_eq stk

/-- `hookMemmove` satisfies `withAllocVmPreserved (sessionMemmoveBoundedSpec stk)`. -/
theorem hookMemmove_allocVmPreserved_sessionBounded_ok (stk : Nat := 0) :
    HookOk hookMemmove (withAllocVmPreserved (sessionMemmoveBoundedSpec stk)) :=
  hookOk_allocVmPreserved_sessionMemmoveBounded_of_master
    hookMemmove_masterMemmove_ok hookMemmove_vmPreserved hookMemmove_oracle_eq stk

/-- Weaken `HookSat H name (sessionMemmoveAcpSpec stk)` to
    `HookSat H name (sessionMemmoveBoundedAcpSpec stk)`. -/
theorem hookSat_sessionMemmoveBoundedAcp_of_unbounded
    {H : String → Option (State → State)} {name : String} (stk : Nat := 4096)
    (h : HookSat H name (sessionMemmoveAcpSpec stk)) :
    HookSat H name (sessionMemmoveBoundedAcpSpec stk) := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  dsimp only [sessionMemmoveBoundedAcpSpec, sessionMemmoveBoundedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hok x R s0 hrun hpre.2 hsp

/-- Weaken `HookSat H name (withAllocVmPreserved (sessionMemmoveSpec stk))` to
    `HookSat H name (withAllocVmPreserved (sessionMemmoveBoundedSpec stk))`. -/
theorem hookSat_allocVmBounded_of_unbounded
    {H : String → Option (State → State)} {name : String} (stk : Nat := 0)
    (h : HookSat H name (withAllocVmPreserved (sessionMemmoveSpec stk))) :
    HookSat H name (withAllocVmPreserved (sessionMemmoveBoundedSpec stk)) := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  dsimp only [withAllocVmPreserved, sessionMemmoveBoundedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hok x R s0 hrun hpre.2 hsp

/-- Lift `HookOk f masterMemmoveSpec` + pointwise `VmPreserved` across `withAlloc A lim` on
    `masterMemmoveSpec`. -/
theorem hookOk_withAlloc_masterMemmove_of_master {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f (withAlloc (M := M) A lim masterMemmoveSpec) :=
  hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved hh hvm)

/-- Lift `HookOk f masterMemmoveSpec` + `VmPreserved` to `withAlloc A lim (withVmPreserved masterMemmoveSpec)`. -/
theorem hookOk_withAlloc_masterMemmoveVm_of_master {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f (withAlloc (M := M) A lim (withVmPreserved masterMemmoveSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim (hookOk_withVmPreserved hh hvm)

/-- Lift `HookOk f masterMemmoveSpec` + `VmPreserved` to `withAlloc A lim (libcMemmoveBoundedSpec stk)`. -/
theorem hookOk_withAlloc_libcMemmoveBounded_of_master {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    (stk : Nat := extHookStack) :
    HookOk f (withAlloc (M := M) A lim (libcMemmoveBoundedSpec stk)) :=
  hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved_libcMemmoveBounded_of_master hh hvm stk)

/-- Lift `HookOk f masterMemmoveSpec` + `VmPreserved` to `withAlloc A lim (sessionMemmoveBoundedSpec stk)`. -/
theorem hookOk_withAlloc_sessionMemmoveBounded_of_master {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    (stk : Nat := extHookStack) :
    HookOk f (withAlloc (M := M) A lim (sessionMemmoveBoundedSpec stk)) :=
  hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hookOk_sessionMemmoveBounded_of_master hh stk) hvm)

/-- Lift `HookOk f masterMemmoveSpec` + `VmPreserved` to `withAlloc A lim (sessionMemmoveBoundedBudgetSpec stk)`. -/
theorem hookOk_withAlloc_sessionMemmoveBoundedBudget_of_master {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    (stk : Nat := extHookStack) :
    HookOk f (withAlloc (M := M) A lim (sessionMemmoveBoundedBudgetSpec stk)) :=
  hookOk_withAlloc_withVmPreserved A lim (hookOk_withVmPreserved (hookOk_sessionMemmoveBounded_of_master hh stk) hvm)

/-- Lift `HookOk f masterMemmoveSpec` + `VmPreserved` + `oracle` to `withAlloc A lim (sessionMemmoveBoundedAcpSpec stk)`. -/
theorem hookOk_withAlloc_sessionMemmoveBoundedAcp_of_master {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) (stk : Nat := 4096) :
    HookOk f (withAlloc (M := M) A lim (sessionMemmoveBoundedAcpSpec stk)) :=
  hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hookOk_sessionMemmoveBoundedAcp_of_master hh hvm horc stk) hvm)

/-- Lift `HookOk f masterMemmoveSpec` + `VmPreserved` + `oracle` to `withAlloc A lim (withAllocVmPreserved (sessionMemmoveBoundedSpec stk))`. -/
theorem hookOk_withAlloc_allocVmPreserved_sessionMemmoveBounded_of_master {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State}
    (hh : HookOk f masterMemmoveSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    (horc : ∀ s : State, (f s).oracle = s.oracle) (stk : Nat := 0) :
    HookOk f (withAlloc (M := M) A lim (withAllocVmPreserved (sessionMemmoveBoundedSpec stk))) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (hookOk_withVmPreserved (hookOk_allocVmPreserved_sessionMemmoveBounded_of_master hh hvm horc stk) hvm)

theorem memmoveSpecK_keepsFs (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    keepsFs (memmoveSpecK keep spec) = memmoveSpecK keep (keepsFs spec) := rfl

theorem memmoveSpecK_withVmPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withVmPreserved (memmoveSpecK keep spec) = memmoveSpecK keep (withVmPreserved spec) := rfl

/-! ## 5. C4 Hook-Shape Return-to-`lr` & `oracle` Lemmas (`TrapRetHook` & `linkedCallHook`) -/

/-- One step of a `Syscall.standard` program whose extern hooks preserve `State.oracle`
    preserves `State.oracle`. -/
theorem Step.oracle_eq_of_standard_hooks {prog : Program} (hsvc : prog.svc = Syscall.standard)
    (hext : ∀ pc f, prog.externAt? pc = some f → ∀ s : State, (f s).oracle = s.oracle)
    {s s' : State} (h : Step prog s s') :
    s'.oracle = s.oracle := by
  cases h with
  | exec _ _ => exact evalInst_oracle_of_standard hsvc _ _
  | halt_unmapped _ _ _ => rfl
  | extern _ he _ _ => exact hext _ _ he _
  | extern_fault _ _ _ => rfl

/-- Multi-step `State.oracle` preservation under `Syscall.standard` and `oracle`-preserving
    extern hooks. -/
theorem Steps.oracle_eq_of_standard_hooks {prog : Program} (hsvc : prog.svc = Syscall.standard)
    (hext : ∀ pc f, prog.externAt? pc = some f → ∀ s : State, (f s).oracle = s.oracle)
    {s0 sf : State} (h : Steps prog s0 sf) :
    sf.oracle = s0.oracle := by
  induction h with
  | refl _ => rfl
  | step h1 _ ih => exact ih.trans (Step.oracle_eq_of_standard_hooks hsvc hext h1)

/-- Generic `State.oracle` preservation for any `linkedCallHook` ghost when `P_real.svc = Syscall.standard`,
    `P_real`'s remaining extern hooks preserve `State.oracle`, and `fallback` preserves `State.oracle`
    (discharging the `horc` hypothesis of `MemmoveStatePreserved.toAllocCallPreserved` and the
    `sessionMemmoveBoundedAcpSpec` / `withAllocVmPreserved` lifts). -/
theorem linkedCallHook_oracle_eq {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hext_orc : ∀ pc f, P_real.externAt? pc = some f → ∀ s : State, (f s).oracle = s.oracle)
    (hfb_orc : ∀ s : State, (fallback s).oracle = s.oracle)
    (s0 : State) :
    (linkedCallHook keep P_real P_sub entryTarget spec fallback s0).oracle = s0.oracle := by
  classical
  unfold linkedCallHook
  split
  · split
    · rename_i hReal
      have hsteps := (Classical.choose_spec hReal.2.2.2).1.toSteps
      have horc := Steps.oracle_eq_of_standard_hooks hsvc_real hext_orc hsteps
      have hpc_orc : (s0.setPC entryTarget).oracle = s0.oracle := by cases s0; rfl
      exact horc.trans hpc_orc
    · change (fallback s0).oracle = s0.oracle
      exact hfb_orc s0
  · rfl

/-- Hook-level return-to-`lr` / `x30`-preservation shape (`rfl`-identical to
    `MemsetLrTrap.Blk21TrapHook L f`, `MemcpyLrTrap.Blk20TrapHook L f`, and
    `TrapSafeWords.TrapHook L f`): on any `.Running` state `w` with `w.readReg64 .lr = L`,
    `f w` either transitions to `.Exception _` or stays `.Running` at `pc = L` with `lr = L`. -/
@[expose] def TrapRetHook (L : BitVec 64) (f : State → State) : Prop :=
  ∀ w : State, w.status = .Running → w.readReg64 .lr = L →
    (∃ msg, (f w).status = .Exception msg) ∨
    ((f w).status = .Running ∧ (f w).pc = L ∧ (f w).readReg64 .lr = L)

theorem trapRetHook_retHook {L : BitVec 64} {g : State → State}
    (hg : ∀ w : State, (g w).status = w.status ∧ (g w).readReg64 .lr = w.readReg64 .lr) :
    TrapRetHook L (retHook g) := by
  intro w hrun hlr
  obtain ⟨hst, hlr_g⟩ := hg w
  refine Or.inr ⟨?_, hlr, ?_⟩
  · simpa [retHook, State.setPC] using hst.trans hrun
  · simpa [retHook, State.readReg64_setPC] using hlr_g.trans hlr

theorem trapRetHook_keepFsTrace {L : BitVec 64} {f : State → State}
    (hf : TrapRetHook L f) : TrapRetHook L (keepFsTrace f) := by
  intro w hrun hlr
  rcases hf w hrun hlr with ⟨msg, hex⟩ | ⟨hr, hpc, hlr'⟩
  · exact Or.inl ⟨msg, hex⟩
  · exact Or.inr ⟨hr, hpc, by cases f w; exact hlr'⟩

theorem trapRetHook_hookMemset (L : BitVec 64) : TrapRetHook L hookMemset :=
  fun _w hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

theorem trapRetHook_hookMemcpy (L : BitVec 64) : TrapRetHook L hookMemcpy :=
  fun _w hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

theorem trapRetHook_hookMemmove (L : BitVec 64) : TrapRetHook L hookMemmove :=
  fun _w hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

theorem trapRetHook_hookNoop (L : BitVec 64) : TrapRetHook L hookNoop :=
  fun _w hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

/-- Unconditional `.Running` return-PC lemma for `linkedCallHook`: whenever `fallback` returns to
    `w.readReg64 .lr` on `.Running` outcomes, any `.Running` output of `linkedCallHook` has
    `pc = w.readReg64 .lr` and `sp = w.sp` (for arbitrary `keep` and `w`, with zero `HookOk`
    assumptions). -/
theorem linkedCallHook_running_returns_to_lr {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hfb : ∀ w : State, w.status = .Running → (fallback w).status = .Running →
      (fallback w).pc = w.readReg64 .lr ∧ (fallback w).sp = w.sp)
    {w : State} (hrun_w : w.status = .Running)
    (hrun_out : (linkedCallHook keep P_real P_sub entryTarget spec fallback w).status = .Running) :
    (linkedCallHook keep P_real P_sub entryTarget spec fallback w).pc = w.readReg64 .lr ∧
      (linkedCallHook keep P_real P_sub entryTarget spec fallback w).sp = w.sp := by
  classical
  unfold linkedCallHook at hrun_out ⊢
  by_cases hAct : ActiveRealPre spec w
  · simp only [hAct, ↓reduceDIte] at hrun_out ⊢
    by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget w
    · simp only [hReal, ↓reduceDIte] at hrun_out ⊢
      have hstop := (Classical.choose_spec hReal.2.2.2).2.1
      rcases hstop with ⟨hpc, hsp, _⟩ | hp | ⟨_, he⟩ | ho
      · exact ⟨hpc, hsp⟩
      · rw [hp] at hrun_out; cases hrun_out
      · rw [he] at hrun_out; cases hrun_out
      · rw [ho] at hrun_out; cases hrun_out
    · simp only [hReal, ↓reduceDIte] at hrun_out ⊢
      have hfb_run : (fallback w).status = .Running := hrun_out
      obtain ⟨hpc, hsp⟩ := hfb w hrun_w hfb_run
      exact ⟨hpc, by cases fallback w; exact hsp⟩
  · simp only [hAct, ↓reduceDIte] at hrun_out
    cases hrun_out

/-- `linkedCallHook` `TrapRetHook L` when `keep L = true` (shared `.text.b_pre` union `keep`). -/
theorem trapRetHook_linkedCallHook_of_keepLr {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State} {L : BitVec 64}
    (hkeepL : keep L = true) (hfb : TrapRetHook L fallback) :
    TrapRetHook L (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w hrun hlr
  unfold linkedCallHook
  by_cases hAct : ActiveRealPre spec w
  · have hnoReal : ¬ ActiveRealRun keep P_real P_sub entryTarget w := by
      intro hR
      have hfalse := hR.2.1
      rw [hlr, hkeepL] at hfalse
      exact Bool.noConfusion hfalse
    simp only [hAct, hnoReal, ↓reduceDIte]
    exact trapRetHook_keepFsTrace hfb w hrun hlr
  · exact Or.inl ⟨"ghost-hook precondition violated", by simp [hAct]⟩

/-- `linkedCallHook` `TrapRetHook L` whenever `spec.pre` excludes `lr = L` (`K`-narrowed specs). -/
theorem trapRetHook_linkedCallHook_of_not_pre {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State} {L : BitVec 64}
    (hnoPre : ∀ w : State, w.readReg64 .lr = L → ¬ ActiveRealPre spec w) :
    TrapRetHook L (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w _ hlr
  have hnp := hnoPre w hlr
  exact Or.inl ⟨"ghost-hook precondition violated", by unfold linkedCallHook; simp [hnp]⟩

/-- `K`-narrowed `memmoveSpecK keep'` corollary of `trapRetHook_linkedCallHook_of_not_pre`. -/
theorem trapRetHook_linkedCallHook_memmoveSpecK {α : Type}
    {keep keep' : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State} {L : BitVec 64} (hkeepL : keep' L = true) :
    TrapRetHook L
      (linkedCallHook keep P_real P_sub entryTarget (memmoveSpecK keep' spec) fallback) := by
  refine trapRetHook_linkedCallHook_of_not_pre fun w hlr ⟨_, _, x, R, hpre⟩ => ?_
  dsimp only [memmoveSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hfalse := hpre.1
  rw [hlr, hkeepL] at hfalse
  exact Bool.noConfusion hfalse

/-- Universal-`L` `TrapRetHook L` lemma for `linkedCallHook` covering the cross-block `keep L = false`
    case (e.g. `L` inside `memmove` with `keepMemcpyBlk20 L = false`), given non-aborting `HookOk`
    and leaf `lr`-preservation. -/
theorem trapRetHook_linkedCallHook_of_hookOk_and_lr {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State} {L : BitVec 64}
    (hOk : HookOk (linkedCallHook keep P_real P_sub entryTarget spec fallback) spec)
    (hfb : TrapRetHook L fallback)
    (hreal_lr : ∀ w sf : State, w.status = .Running → w.readReg64 .lr = L → ExecFrozen w.mem →
      keep L = false → P_sub.CodeLoaded (stripExecOutside keep w.mem) →
      StepsUntil P_real (SubroutineStop w) (w.setPC entryTarget) sf → Returned w sf →
      sf.readReg64 .lr = L)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    TrapRetHook L (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w hrun hlr
  by_cases hAct : ActiveRealPre spec w
  · by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget w
    · obtain ⟨_, hsp, x, R, hpre⟩ := id hAct
      obtain ⟨_, _, hout⟩ := hOk x R w hrun hpre hsp
      rcases hout with ⟨hret, _, _⟩ | ⟨_, hp_sat⟩ | ⟨code, _, he_sat⟩ | ⟨_, ho_sat⟩
      · have heq :
            linkedCallHook keep P_real P_sub entryTarget spec fallback w =
              Classical.choose hReal.2.2.2 := by
          unfold linkedCallHook
          simp [hAct, hReal]
        have hret_choose : Returned w (Classical.choose hReal.2.2.2) := heq ▸ hret
        have hchoose := Classical.choose_spec hReal.2.2.2
        have hlr_sf : (Classical.choose hReal.2.2.2).readReg64 .lr = L :=
          hreal_lr w (Classical.choose hReal.2.2.2) hrun hlr hReal.1
            (hlr ▸ hReal.2.1) hReal.2.2.1 hchoose.1 hret_choose
        exact Or.inr ⟨hret.2.2, hret.1.trans hlr, heq ▸ hlr_sf⟩
      · rw [hpan x w _, satisfies_pure_sepConj] at hp_sat
        exact False.elim hp_sat.1
      · rw [hex x code w _, satisfies_pure_sepConj] at he_sat
        exact False.elim he_sat.1
      · rw [hoom x w _, satisfies_pure_sepConj] at ho_sat
        exact False.elim ho_sat.1
    · unfold linkedCallHook
      simp only [hAct, hReal, ↓reduceDIte]
      exact trapRetHook_keepFsTrace hfb w hrun hlr
  · exact Or.inl ⟨"ghost-hook precondition violated", by unfold linkedCallHook; simp [hAct]⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode
