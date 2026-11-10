/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import VerifiedLibraries.Musl.Proofs.MemcmpProof
public import LibsignalBinary.Heap.Iface
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.CommonBudget -- proof-setup: allow-public-import

/-!
# Region-Local `bcmp` / `memcmp` Code Verification & Master Spec (`HooksDehook.BcmpCode`)

Card **L1-a1** (`bcmp` de-hook pilot, mirroring `HooksDehook.MemsetCode` and `HooksDehook.MemcpyCode`):

1. **State preservation (`BcmpStatePreserved` & permission-carrying `stdBcmpSpec` / `stdMemcmpSpec`):**
   - `abbrev BcmpStatePreserved := MemsetStatePreserved` (the 7 memory-permission-independent
     process/VM fields `fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`, `physMemAvail`),
     so `SpecStripSInvariant keepR masterBcmpSpec` in card `L1-b` (`HooksDehook.BcmpGhost`) holds
     definitionally (`cases s0; cases sf; rfl`).
   - Alongside `masterBcmpSpec` / `masterMemcmpSpec`, exports permission-carrying process specs
     `stdBcmpSpec` and `stdMemcmpSpec` (same `.pre`, carrying full `ProcessFieldsPreserved s0 sf`,
     which is `rfl`-identical to `ProofLib.StdStartup.StdStatePreserved s0 sf` via
     `stdStatePreserved_eq_processFieldsPreserved`) so `HooksDehook.BcmpGhost` recovers
     `VmPreserved` across `stripS keepR` on the real-code branch.
2. **Frameless zero-stack master spec (`masterBcmpSpec`), byte-difference companion
   (`masterMemcmpSpec`), and `K`-narrowing (`bcmpSpecK`):**
   `masterBcmpSpec` equals `DirSpecs.cliBcmpSpec` minus `stackAt s.sp extHookStack`, strengthened
   with `sf.vregs = s0.vregs` and `BcmpStatePreserved s0 sf` (`onPanic = onExit = onOom = ⌜False⌝`).
   Both `bcmp` (`1` word `b memcmp`) and `memcmp` (`13` scalar `ldrb`/`subs` words) are frameless
   leaves touching zero stack bytes and zero SIMD/FP registers.
3. **Contiguous 56-byte `memcmp ++ bcmp` hull (`bcmpHullWords`) & region-local `subroutine_ok`:**
   Matches stock `libc.a` layout (`memcmp` `13` words = `52` B at `m`, followed contiguously at
   `m + 52#64` by `bcmp` = `1` word `b memcmp`, `14` words = `56` B total in a single `P_sub`):
   - `hasWords` splitting (`hasWords_append_left`, `hasWords_append_right`), unconditional
     `branchInRange_bcmp_hull`, and `pureWordsProg_bcmpHull_hasWords`;
   - single-`P_sub` hull `subroutine_ok` at `m + 52#64` for `stdMemcmpSpec`, `stdBcmpSpec`,
     `masterMemcmpSpec`, `masterBcmpSpec`, and their `K` forms, plus concrete `pureWordsProg`
     instances (`pureWordsProg_bcmpHull_stdBcmp_ok`, `pureWordsProg_bcmpHull_masterBcmp_ok`,
     `pureWordsProg_bcmpHull_masterBcmpK_ok`).
4. **Stock code-identity status (`L1-a2` at the C2 cutover):**
   Per GK6c, there is **no** trusted placed-library entry for libc strings; code identity for the
   `memcmp ++ bcmp` hull comes from the untrusted `a2` card plus `K3(b)` at the C2 cutover.
5. **`W`-independent fallback (`hookBcmpFallback`) & `HookOk` lifts to all 4 consumer specs:**
   `hookBcmpOf_masterBcmp_ok` (+ `K`) generalizes over any `g` satisfying `bcmp_ok`, with both the
   `W`-independent `hookBcmpFallback := cliBcmpHook canonicalBcmp` instance (`canonicalBcmp` =
   `(memcmpBytes a b).zeroExtend 64`, for ghost hooks fixed before `∀ W`) and `hookBcmp_masterBcmp_ok W`
   as 1-line corollaries; §4 lifts `HookOk f masterBcmpSpec` (+ `K`) to all four stack-carrying
   consumer contracts (`CliExt.bcmpSpec`, `DirSpecs.cliBcmpSpec`, `HooksE.bcmpVregsSpec`,
   `HooksE.e2eBcmpSpec`), with `withVmPreserved` / `withAlloc` ghost-hook lifts proved in `BcmpGhost`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved)
open VerifiedLibraries.Musl (bcmpWords bcmpCalls memcmpLibcaWords memcmpBytes memcmpBytes_eq_zero_iff)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt_false bytesAt_true)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (CliHooks cliBcmpHook)
open CryptoVerification.SignalSession.Cli (CliBcmpCall cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (bytesAt_readBytes)
open CryptoVerification.SignalSession.CliExt (bcmpSpec)
open CryptoVerification.E2E.HooksE (bcmpVregsSpec e2eBcmpSpec)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved cliBcmpHook_vmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp (
  bcmpMemVregsROSpec cliBcmpStackSpec memcmpLibca_memVregsRO_codeAt_ok
)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (MemsetStatePreserved)

/-! ## 1. Master `bcmp` Specification & Wrappers -/

/-- Reuse `MemsetStatePreserved` (`fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`,
    `physMemAvail`) via `abbrev` so `BcmpStatePreserved` is `rfl`-identical to
    `MemsetStatePreserved` and `MemcpyStatePreserved`. -/
abbrev BcmpStatePreserved (s0 sf : State) : Prop :=
  MemsetStatePreserved s0 sf

/-- `ProofLib.StdStartup.StdStatePreserved` and `ProofLib.ProcessFieldsPreserved` are definitionally
    (`rfl`) identical (the 7 `MemsetStatePreserved` fields plus pointwise `mem.perm`). -/
theorem stdStatePreserved_eq_processFieldsPreserved (s0 sf : State) :
    StdStatePreserved s0 sf = ProcessFieldsPreserved s0 sf := rfl

theorem BcmpStatePreserved.refl (s : State) : BcmpStatePreserved s s :=
  MemsetStatePreserved.refl s

theorem BcmpStatePreserved.of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : BcmpStatePreserved s0 sf :=
  MemsetStatePreserved.of_stdStatePreserved h

theorem BcmpStatePreserved.of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : BcmpStatePreserved s0 sf :=
  MemsetStatePreserved.of_stdStatePreserved h

theorem BcmpStatePreserved.toAllocCallPreserved {s0 sf : State}
    (h : BcmpStatePreserved s0 sf) (horc : sf.oracle = s0.oracle)
    (hsym : sf.symtab = s0.symtab) : AllocCallPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2.1, horc, hsym⟩

/-- Master separation-logic contract for `bcmp(a = x0, b = x1, n = x2)` (`DirSpecs.cliBcmpSpec`
    minus `stackAt s.sp extHookStack`, strengthened with `sf.vregs = s0.vregs` and
    `BcmpStatePreserved s0 sf`, and `onPanic = onExit = onOom = ⌜False⌝`): requires zero stack
    bytes, preserves both input slices (`CryptoVerification.SpqrV1.ChainProofs.bytesAt`, owned `↦ₛ` or read-only `↦ᵣ`
    independently on each side), sets `w0 = 0 ↔ bsA = bsB`, leaves `vregs` unchanged, and preserves
    `BcmpStatePreserved`. -/
@[expose] def masterBcmpSpec : Spec CliBcmpCall where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.a ∧ s0.readReg64 .x1 = x.b ∧
      (s0.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧
      sf.vregs = s0.vregs ∧
      BcmpStatePreserved s0 sf⌝ ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Stronger exact-byte-difference companion spec for the real `bcmp` (`b memcmp`) + `memcmp`
    bytes (`sf.readReg32 .x0 = memcmpBytes x.bsA x.bsB`). -/
@[expose] def masterMemcmpSpec : Spec CliBcmpCall where
  pre := masterBcmpSpec.pre
  post := fun x s0 sf =>
    ⌜sf.readReg32 .x0 = memcmpBytes x.bsA x.bsB ∧
      sf.vregs = s0.vregs ∧
      BcmpStatePreserved s0 sf⌝ ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Permission-carrying process contract for `bcmp(a = x0, b = x1, n = x2)`: identical `.pre` to
    `masterBcmpSpec`, carrying full `ProcessFieldsPreserved s0 sf` (`rfl`-identical to
    `StdStatePreserved s0 sf`, including pointwise `sf.mem.perm a = s0.mem.perm a`) so
    `HooksDehook.BcmpGhost` recovers `VmPreserved` across `stripS keepR`. -/
@[expose] def stdBcmpSpec : Spec CliBcmpCall where
  pre := masterBcmpSpec.pre
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧
      sf.vregs = s0.vregs ∧
      ProcessFieldsPreserved s0 sf⌝ ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Permission-carrying exact-byte-difference process contract (`memcmpBytes`) with full
    `ProcessFieldsPreserved s0 sf` (= `StdStatePreserved s0 sf`) and `.pre = masterBcmpSpec.pre`. -/
@[expose] def stdMemcmpSpec : Spec CliBcmpCall where
  pre := masterBcmpSpec.pre
  post := fun x s0 sf =>
    ⌜sf.readReg32 .x0 = memcmpBytes x.bsA x.bsB ∧
      sf.vregs = s0.vregs ∧
      ProcessFieldsPreserved s0 sf⌝ ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem stdBcmp_pre_eq : stdBcmpSpec.pre = masterBcmpSpec.pre := rfl

theorem stdMemcmp_pre_eq : stdMemcmpSpec.pre = masterBcmpSpec.pre := rfl

/-- `K`-route precondition narrowing: conjoins `⌜keep (s.readReg64 .lr) = false⌝` to `spec.pre`,
    leaving `post`, `onPanic`, `onExit`, and `onOom` unchanged (mirrors `memsetSpecK`). -/
@[expose] def bcmpSpecK (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre x s }

/-! ## 2. Contiguous 56 B `memcmp ++ bcmp` Hull & Region-Local `subroutine_ok` -/

/-- Byte size (`52#64`) of `memcmpLibcaWords` (`13` words), i.e. the offset of `bcmp` inside the
    contiguous `memcmp ++ bcmp` stock `libc.a` hull. -/
@[expose] def memcmpByteLen : BitVec 64 :=
  BitVec.ofNat 64 (4 * memcmpLibcaWords.length)

theorem memcmpByteLen_eq : memcmpByteLen = 52#64 := rfl

/-- Contiguous `14`-word (`56`-byte) `memcmp ++ bcmp` word list matching stock `libc.a` layout:
    `memcmpLibcaWords` (`13` words = `52` B) at `m`, followed immediately at `m + 52#64`
    (`= m + memcmpByteLen`) by `bcmp` (`1` word `b memcmp`, patched with `resolve`). -/
@[expose] def bcmpHullWords (m : BitVec 64) (resolve : String → BitVec 64 := fun _ => m) :
    List (BitVec 32) :=
  memcmpLibcaWords ++ Obj.patchCalls bcmpCalls bcmpWords (m + memcmpByteLen) resolve

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

/-- Extract the `memcmp` (`+0`, `13` words) slice from a 56 B `bcmpHullWords` witness. -/
theorem bcmpHull_hasWords_memcmp {prog : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    (hhull : prog.hasWords m (bcmpHullWords m resolve)) :
    prog.hasWords m memcmpLibcaWords :=
  hasWords_append_left hhull

/-- Extract the `bcmp` (`+52`, `1` word `b memcmp`) slice at `m + memcmpByteLen` (`= m + 52#64`)
    from a 56 B `bcmpHullWords` witness. -/
theorem bcmpHull_hasWords_bcmp {prog : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    (hhull : prog.hasWords m (bcmpHullWords m resolve)) :
    prog.hasWords (m + memcmpByteLen)
      (Obj.patchCalls bcmpCalls bcmpWords (m + memcmpByteLen) resolve) := by
  refine hasWords_append_right hhull ?_
  simp [Obj.patchCalls, bcmpWords]

/-- The `-52`-byte branch from `m + memcmpByteLen` (`+52`) back to `m` (`resolve "memcmp" = m`) is
    in `Obj.BranchInRange` unconditionally for every `m : BitVec 64`. -/
theorem branchInRange_bcmp_hull (m : BitVec 64) {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m := by rfl) :
    Obj.BranchInRange ((m + memcmpByteLen) + 0#64) (resolve "memcmp") := by
  have hd : resolve "memcmp" - ((m + memcmpByteLen) + 0#64) = -52#64 := by
    rw [hres, memcmpByteLen_eq]
    bv_omega
  unfold Obj.BranchInRange
  rw [hd]
  decide

/-- `pureWordsProg base words` holds `words` at `base` whenever `4 * words.length ≤ 2 ^ 64`. -/
theorem pureWordsProg_hasWords_of_fit (base : BitVec 64) (words : List (BitVec 32))
    (hlen : 4 * words.length ≤ 2 ^ 64) :
    (pureWordsProg base words).hasWords base words := by
  unfold Program.hasWords Program.hasWordsOff
  have hsub : (base - (pureWordsProg base words).base).toNat = 0 := by
    change (base - base).toNat = 0
    simp
  rw [hsub]
  refine ⟨by omega, fun i hi => ?_, rfl, rfl⟩
  rw [Nat.zero_add, Program.readWordOff_eq_some_iff _ _ _ (by omega)]
  have h r (hr : r < 4) := Program.getElem?_flatMap_wordToBytesLE words i r hi hr
  refine ⟨?_, h 1 (by omega), h 2 (by omega), h 3 (by omega)⟩
  have h0 := h 0 (by omega)
  simp only [Nat.add_zero, Nat.mul_zero] at h0
  exact h0

/-- `pureWordsProg base memcmpLibcaWords` holds `memcmpLibcaWords` (`13` words) at `base`. -/
theorem pureWordsProg_memcmp_hasWords (base : BitVec 64) :
    (pureWordsProg base memcmpLibcaWords).hasWords base memcmpLibcaWords :=
  pureWordsProg_hasWords_of_fit base memcmpLibcaWords (by decide)

/-- `pureWordsProg base (Obj.patchCalls bcmpCalls bcmpWords base resolve)` holds the relocation-patched
    `bcmp` word (`1` word `b memcmp`) at `base` for any `base` and `resolve`. -/
theorem pureWordsProg_bcmp_hasWords (base : BitVec 64) (resolve : String → BitVec 64) :
    (pureWordsProg base (Obj.patchCalls bcmpCalls bcmpWords base resolve)).hasWords base
      (Obj.patchCalls bcmpCalls bcmpWords base resolve) := by
  refine pureWordsProg_hasWords_of_fit base _ ?_
  have hlen : (Obj.patchCalls bcmpCalls bcmpWords base resolve).length = 1 := by
    simp [Obj.patchCalls, bcmpCalls, bcmpWords]
  omega

/-- `pureWordsProg m (bcmpHullWords m resolve)` holds the full 14-word (`56`-byte) `memcmp ++ bcmp`
    hull at `m` for every `m` and `resolve`. -/
theorem pureWordsProg_bcmpHull_hasWords (m : BitVec 64)
    (resolve : String → BitVec 64 := fun _ => m) :
    (pureWordsProg m (bcmpHullWords m resolve)).hasWords m (bcmpHullWords m resolve) := by
  refine pureWordsProg_hasWords_of_fit m _ ?_
  have hlen : (bcmpHullWords m resolve).length = 14 := by
    simp [bcmpHullWords, Obj.patchCalls, memcmpLibcaWords, bcmpWords]
  omega

/-- `pureWordsProg base words` has no external hooks (`externAt? pc = none`). -/
theorem pureWordsProg_externAt_none (base : BitVec 64) (words : List (BitVec 32))
    (pc : BitVec 64) :
    (pureWordsProg base words).externAt? pc = none := by
  unfold Program.externAt? pureWordsProg Program.ofWords
  rfl

private theorem pureWordsProg_noSvcMsr_memcmp (base : BitVec 64) :
    (pureWordsProg base memcmpLibcaWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 memcmpLibcaWords) rfl (by prove_all_instrs)

private def masterMemcmpCoreSpec : Spec CliBcmpCall where
  pre := masterBcmpSpec.pre
  post := fun x s0 sf =>
    ⌜sf.readReg32 .x0 = memcmpBytes x.bsA x.bsB ∧ sf.vregs = s0.vregs⌝ ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗
      CryptoVerification.SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem chainBytesAt_to_ro {m : Memory} {ro : Bool} {p : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ CryptoVerification.SpqrV1.ChainProofs.bytesAt ro p bs ∗ R) :
    m ⊨ (p ↦ᵣ bs) ∗ R := by
  cases ro
  · rw [bytesAt_false] at h
    exact Satisfies.pointsToBytes_to_ro h
  · rwa [bytesAt_true] at h

private theorem bcmpMemVregsRO_simulates_masterMemcmpCore :
    SpecSimulates bcmpMemVregsROSpec masterMemcmpCoreSpec := by
  refine SpecSimulates.of_map ?_
  intro x R s0 hpre
  dsimp only [masterMemcmpCoreSpec, masterBcmpSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hmem_a : s0.mem ⊨ (x.a ↦ᵣ x.bsA) ∗ (CryptoVerification.SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB ∗ R) :=
    chainBytesAt_to_ro (by simpa only [sepConj_assoc] using hmem)
  have hmem_ab : s0.mem ⊨ (x.b ↦ᵣ x.bsB) ∗ ((x.a ↦ᵣ x.bsA) ∗ R) :=
    chainBytesAt_to_ro (Satisfies.of_eq hmem_a)
  refine ⟨(x.a, x.b, s0.readReg64 .x2, x.bsA, x.bsB), R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [bcmpMemVregsROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, rfl, hx2, by omega⟩, Satisfies.of_eq hmem_ab⟩
  · dsimp only [bcmpMemVregsROSpec] at hpost
    dsimp only [masterMemcmpCoreSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hret, hmem_eq, hvregs⟩, _⟩
    rw [hmem_eq]
    exact ⟨⟨hret, hvregs⟩, by simpa only [sepConj_assoc] using hmem⟩

private theorem bcmp_tail_ok {α : Type} {P_sub : Program} {bcmpEntry : BitVec 64}
    {resolve : String → BitVec 64} {spec : Spec α}
    (hrange : Obj.BranchInRange (bcmpEntry + 0#64) (resolve "memcmp"))
    (hbcmp : P_sub.hasWords bcmpEntry (Obj.patchCalls bcmpCalls bcmpWords bcmpEntry resolve))
    (hcallee : subroutine_ok P_sub (resolve "memcmp") spec)
    (hpre_pc : ∀ x s, spec.pre x (s.setPC (resolve "memcmp")) = spec.pre x s)
    (hpost_pc : ∀ x s sf, spec.post x (s.setPC (resolve "memcmp")) sf = spec.post x s sf)
    (hpanic : ∀ x s sf, spec.onPanic x s sf = ⌜False⌝)
    (hexit : ∀ x c s sf, spec.onExit x c s sf = ⌜False⌝)
    (hoom : ∀ x s sf, spec.onOom x (s.setPC (resolve "memcmp")) sf = spec.onOom x s sf) :
    subroutine_ok P_sub bcmpEntry spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hf := Obj.fetch_patchCalls_b (r := (0, "memcmp")) hbcmp rfl rfl (by decide) (by decide)
    hrange
  simp only [BitVec.add_zero, ← hpc] at hf
  apply reaches_outcome_step hrun hf
  dsimp only [Program.evalInst, execInstWithSvc]
  rw [show s0.pc + (resolve "memcmp" - s0.pc) = resolve "memcmp" by bv_omega]
  exact reaches_outcome_of_reaches_pc
    (reaches_pc_tailcall_subroutine hcallee x x rfl hrun rfl rfl (CalleeSavedPreserved.rfl s0)
      (by rw [hpre_pc]; exact hpre) (fun sf _ _ _ _ hq => hpost_pc x s0 sf ▸ hq) hsp
      (fun _ _ hp => by rw [hpanic] at hp; exact not_satisfies_false_sepConj hp)
      (fun _ _ _ he => by rw [hexit] at he; exact not_satisfies_false_sepConj he)
      (fun sf _ ho => hoom x s0 sf ▸ ho))
    (fun _ _ ho => ho)

/-- Single-block region-local `subroutine_ok` for `stdMemcmpSpec` (carrying full
    `ProcessFieldsPreserved s0 sf` = `StdStatePreserved s0 sf`) on any hook-free `P_sub`
    holding `memcmpLibcaWords` (`13` words) at `m`. -/
theorem subroutine_ok_memcmp_stdMemcmp_of_hasWords {P_sub : Program} {m : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m memcmpLibcaWords) :
    subroutine_ok P_sub m stdMemcmpSpec := by
  have hpure := bcmpMemVregsRO_simulates_masterMemcmpCore.subroutine_ok
    (memcmpLibca_memVregsRO_codeAt_ok _ m (pureWordsProg_memcmp_hasWords m))
  have hlift := subroutine_ok_lift_pureWords_process hpure
    (pureWordsProg_noSvcMsr_memcmp m) hwords hsub_no
    (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)
  refine subroutine_ok_map hlift (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [masterMemcmpCoreSpec, stdMemcmpSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩

/-- Single-block region-local `subroutine_ok` for `stdBcmpSpec` (carrying full
    `ProcessFieldsPreserved s0 sf` = `StdStatePreserved s0 sf`) on any hook-free `P_sub`
    holding `memcmpLibcaWords` (`13` words) at `m`. -/
theorem subroutine_ok_memcmp_stdBcmp_of_hasWords {P_sub : Program} {m : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m memcmpLibcaWords) :
    subroutine_ok P_sub m stdBcmpSpec := by
  refine subroutine_ok_map (subroutine_ok_memcmp_stdMemcmp_of_hasWords hsub_no hwords)
    (fun x R s0 hpre => ?_)
  have hlen : x.bsB.length = x.bsA.length := by
    dsimp only [stdBcmpSpec, masterBcmpSpec] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.2.2.2
  refine ⟨x, R, hpre, fun sf hpost => ?_⟩
  dsimp only [stdMemcmpSpec, stdBcmpSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  refine ⟨⟨?_, hpost.1.2.1, hpost.1.2.2⟩, hpost.2⟩
  change sf.readReg32 .x0 = 0#32 ↔ x.bsA = x.bsB
  rw [hpost.1.1]
  exact memcmpBytes_eq_zero_iff hlen.symm

/-- Single-block region-local `subroutine_ok` for `masterMemcmpSpec` on any hook-free `P_sub`
    holding `memcmpLibcaWords` (`13` words) at `m`. -/
theorem subroutine_ok_memcmp_masterMemcmp_of_hasWords {P_sub : Program} {m : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m memcmpLibcaWords) :
    subroutine_ok P_sub m masterMemcmpSpec := by
  refine subroutine_ok_map (subroutine_ok_memcmp_stdMemcmp_of_hasWords hsub_no hwords)
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [stdMemcmpSpec, masterMemcmpSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.1, hpost.1.2.1, BcmpStatePreserved.of_processFieldsPreserved hpost.1.2.2⟩, hpost.2⟩

/-- Single-block region-local `subroutine_ok` for `bcmpSpecK keep masterMemcmpSpec` on any
    hook-free `P_sub` holding `memcmpLibcaWords`. -/
theorem subroutine_ok_memcmp_masterMemcmpK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {m : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m memcmpLibcaWords) :
    subroutine_ok P_sub m (bcmpSpecK keep masterMemcmpSpec) := by
  refine subroutine_ok_mono (subroutine_ok_memcmp_masterMemcmp_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [bcmpSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Single-block region-local `subroutine_ok` for `masterBcmpSpec` on any hook-free `P_sub`
    holding `memcmpLibcaWords` (`13` words) at `m`. -/
theorem subroutine_ok_memcmp_masterBcmp_of_hasWords {P_sub : Program} {m : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m memcmpLibcaWords) :
    subroutine_ok P_sub m masterBcmpSpec := by
  refine subroutine_ok_map (subroutine_ok_memcmp_stdBcmp_of_hasWords hsub_no hwords)
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [stdBcmpSpec, masterBcmpSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.1, hpost.1.2.1, BcmpStatePreserved.of_processFieldsPreserved hpost.1.2.2⟩, hpost.2⟩

/-- Single-block region-local `subroutine_ok` for `bcmpSpecK keep masterBcmpSpec` on any
    hook-free `P_sub` holding `memcmpLibcaWords`. -/
theorem subroutine_ok_memcmp_masterBcmpK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {m : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m memcmpLibcaWords) :
    subroutine_ok P_sub m (bcmpSpecK keep masterBcmpSpec) := by
  refine subroutine_ok_mono (subroutine_ok_memcmp_masterBcmp_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [bcmpSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

private theorem subroutine_ok_twoBlocks_stdMemcmp {P_sub : Program}
    {bcmpEntry : BitVec 64} {resolve : String → BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hrange : Obj.BranchInRange (bcmpEntry + 0#64) (resolve "memcmp"))
    (hbcmp : P_sub.hasWords bcmpEntry (Obj.patchCalls bcmpCalls bcmpWords bcmpEntry resolve))
    (hmemcmp : P_sub.hasWords (resolve "memcmp") memcmpLibcaWords) :
    subroutine_ok P_sub bcmpEntry stdMemcmpSpec :=
  bcmp_tail_ok hrange hbcmp
    (subroutine_ok_memcmp_stdMemcmp_of_hasWords hsub_no hmemcmp)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

private theorem subroutine_ok_twoBlocks_stdBcmp {P_sub : Program}
    {bcmpEntry : BitVec 64} {resolve : String → BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hrange : Obj.BranchInRange (bcmpEntry + 0#64) (resolve "memcmp"))
    (hbcmp : P_sub.hasWords bcmpEntry (Obj.patchCalls bcmpCalls bcmpWords bcmpEntry resolve))
    (hmemcmp : P_sub.hasWords (resolve "memcmp") memcmpLibcaWords) :
    subroutine_ok P_sub bcmpEntry stdBcmpSpec :=
  bcmp_tail_ok hrange hbcmp
    (subroutine_ok_memcmp_stdBcmp_of_hasWords hsub_no hmemcmp)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

/-- Contiguous 56 B hull `subroutine_ok` for `stdMemcmpSpec` (full `ProcessFieldsPreserved`) on a
    single hook-free `P_sub` holding `bcmpHullWords m resolve` (`memcmp ++ bcmp`) at `m`, entered
    at `m + memcmpByteLen` (`= m + 52#64`). -/
theorem subroutine_ok_hull_stdMemcmp_of_hasWords {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    subroutine_ok P_sub (m + memcmpByteLen) stdMemcmpSpec :=
  subroutine_ok_twoBlocks_stdMemcmp hsub_no
    (branchInRange_bcmp_hull m hres)
    (bcmpHull_hasWords_bcmp hhull)
    (hres ▸ bcmpHull_hasWords_memcmp hhull)

/-- Contiguous 56 B hull `subroutine_ok` for `stdBcmpSpec` (full `ProcessFieldsPreserved`) on a
    single hook-free `P_sub` holding `bcmpHullWords m resolve` (`memcmp ++ bcmp`) at `m`, entered
    at `m + memcmpByteLen` (`= m + 52#64`). -/
theorem subroutine_ok_hull_stdBcmp_of_hasWords {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    subroutine_ok P_sub (m + memcmpByteLen) stdBcmpSpec :=
  subroutine_ok_twoBlocks_stdBcmp hsub_no
    (branchInRange_bcmp_hull m hres)
    (bcmpHull_hasWords_bcmp hhull)
    (hres ▸ bcmpHull_hasWords_memcmp hhull)

/-- Contiguous 56 B hull `subroutine_ok` for `masterMemcmpSpec` on a single hook-free `P_sub`
    holding `bcmpHullWords m resolve` at `m`, entered at `m + memcmpByteLen` (`= m + 52#64`). -/
theorem subroutine_ok_hull_masterMemcmp_of_hasWords {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    subroutine_ok P_sub (m + memcmpByteLen) masterMemcmpSpec := by
  refine subroutine_ok_map (subroutine_ok_hull_stdMemcmp_of_hasWords hsub_no hhull hres)
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [stdMemcmpSpec, masterMemcmpSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.1, hpost.1.2.1, BcmpStatePreserved.of_processFieldsPreserved hpost.1.2.2⟩, hpost.2⟩

/-- Contiguous 56 B hull `subroutine_ok` for `bcmpSpecK keep masterMemcmpSpec` on a single
    hook-free `P_sub` holding `bcmpHullWords m resolve` at `m`. -/
theorem subroutine_ok_hull_masterMemcmpK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    subroutine_ok P_sub (m + memcmpByteLen) (bcmpSpecK keep masterMemcmpSpec) := by
  refine subroutine_ok_mono (subroutine_ok_hull_masterMemcmp_of_hasWords hsub_no hhull hres)
    (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [bcmpSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Contiguous 56 B hull `subroutine_ok` for `masterBcmpSpec` on a single hook-free `P_sub`
    holding `bcmpHullWords m resolve` at `m`, entered at `m + memcmpByteLen` (`= m + 52#64`). -/
theorem subroutine_ok_hull_masterBcmp_of_hasWords {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    subroutine_ok P_sub (m + memcmpByteLen) masterBcmpSpec := by
  refine subroutine_ok_map (subroutine_ok_hull_stdBcmp_of_hasWords hsub_no hhull hres)
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [stdBcmpSpec, masterBcmpSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.1, hpost.1.2.1, BcmpStatePreserved.of_processFieldsPreserved hpost.1.2.2⟩, hpost.2⟩

/-- Contiguous 56 B hull `subroutine_ok` for `bcmpSpecK keep masterBcmpSpec` on a single
    hook-free `P_sub` holding `bcmpHullWords m resolve` at `m`. -/
theorem subroutine_ok_hull_masterBcmpK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    subroutine_ok P_sub (m + memcmpByteLen) (bcmpSpecK keep masterBcmpSpec) := by
  refine subroutine_ok_mono (subroutine_ok_hull_masterBcmp_of_hasWords hsub_no hhull hres)
    (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [bcmpSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Concrete 56 B hull `pureWordsProg m (bcmpHullWords m)` satisfying `stdMemcmpSpec` at
    `m + memcmpByteLen` (`= m + 52#64`). -/
theorem pureWordsProg_bcmpHull_stdMemcmp_ok (m : BitVec 64) :
    subroutine_ok (pureWordsProg m (bcmpHullWords m)) (m + memcmpByteLen) stdMemcmpSpec :=
  subroutine_ok_hull_stdMemcmp_of_hasWords
    (pureWordsProg_externAt_none m (bcmpHullWords m))
    (pureWordsProg_bcmpHull_hasWords m)

/-- Concrete 56 B hull `pureWordsProg m (bcmpHullWords m)` satisfying `stdBcmpSpec` at
    `m + memcmpByteLen` (`= m + 52#64`). -/
theorem pureWordsProg_bcmpHull_stdBcmp_ok (m : BitVec 64) :
    subroutine_ok (pureWordsProg m (bcmpHullWords m)) (m + memcmpByteLen) stdBcmpSpec :=
  subroutine_ok_hull_stdBcmp_of_hasWords
    (pureWordsProg_externAt_none m (bcmpHullWords m))
    (pureWordsProg_bcmpHull_hasWords m)

/-- Concrete 56 B hull `pureWordsProg m (bcmpHullWords m)` satisfying `masterMemcmpSpec` at
    `m + memcmpByteLen` (`= m + 52#64`). -/
theorem pureWordsProg_bcmpHull_masterMemcmp_ok (m : BitVec 64) :
    subroutine_ok (pureWordsProg m (bcmpHullWords m)) (m + memcmpByteLen) masterMemcmpSpec :=
  subroutine_ok_hull_masterMemcmp_of_hasWords
    (pureWordsProg_externAt_none m (bcmpHullWords m))
    (pureWordsProg_bcmpHull_hasWords m)

/-- Concrete 56 B hull `pureWordsProg m (bcmpHullWords m)` satisfying `masterBcmpSpec` at
    `m + memcmpByteLen` (`= m + 52#64`). -/
theorem pureWordsProg_bcmpHull_masterBcmp_ok (m : BitVec 64) :
    subroutine_ok (pureWordsProg m (bcmpHullWords m)) (m + memcmpByteLen) masterBcmpSpec :=
  subroutine_ok_hull_masterBcmp_of_hasWords
    (pureWordsProg_externAt_none m (bcmpHullWords m))
    (pureWordsProg_bcmpHull_hasWords m)

/-- Concrete 56 B hull `pureWordsProg m (bcmpHullWords m)` satisfying
    `bcmpSpecK keep masterBcmpSpec` at `m + memcmpByteLen` (`= m + 52#64`). -/
theorem pureWordsProg_bcmpHull_masterBcmpK_ok (keep : BitVec 64 → Bool) (m : BitVec 64) :
    subroutine_ok (pureWordsProg m (bcmpHullWords m)) (m + memcmpByteLen)
      (bcmpSpecK keep masterBcmpSpec) :=
  subroutine_ok_hull_masterBcmpK_of_hasWords keep
    (pureWordsProg_externAt_none m (bcmpHullWords m))
    (pureWordsProg_bcmpHull_hasWords m)

/-- Concrete 1-block `pureWordsProg base memcmpLibcaWords` instance satisfying `masterBcmpSpec`. -/
theorem pureWordsProg_memcmp_masterBcmp_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base memcmpLibcaWords) base masterBcmpSpec :=
  subroutine_ok_memcmp_masterBcmp_of_hasWords
    (pureWordsProg_externAt_none base memcmpLibcaWords)
    (pureWordsProg_memcmp_hasWords base)

/-- Concrete 1-block `pureWordsProg base memcmpLibcaWords` instance satisfying
    `bcmpSpecK keep masterBcmpSpec`. -/
theorem pureWordsProg_memcmp_masterBcmpK_ok (keep : BitVec 64 → Bool) (base : BitVec 64) :
    subroutine_ok (pureWordsProg base memcmpLibcaWords) base (bcmpSpecK keep masterBcmpSpec) :=
  subroutine_ok_memcmp_masterBcmpK_of_hasWords keep
    (pureWordsProg_externAt_none base memcmpLibcaWords)
    (pureWordsProg_memcmp_hasWords base)

/-! ## 3. `W`-Independent Fallback Soundness for `masterBcmpSpec` -/

/-- Generalized fallback soundness: `cliBcmpHook g` satisfies `masterBcmpSpec` for any comparison
    function `g` whose low 32 bits vanish iff equal-length byte lists match (`W`-independent). -/
theorem hookBcmpOf_masterBcmp_ok
    (g : List (BitVec 8) → List (BitVec 8) → BitVec 64)
    (hg : ∀ bsA bsB, bsA.length = bsB.length → ((g bsA bsB).setWidth 32 = 0#32 ↔ bsA = bsB)) :
    HookOk (cliBcmpHook g) masterBcmpSpec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [masterBcmpSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hlenA : x.bsA.length ≤ 2 ^ 64 := by
    have := (s0.readReg64 .x2).isLt
    omega
  have hreadA := bytesAt_readBytes hmem hlenA
  have hmemB : s0.mem ⊨ CryptoVerification.SpqrV1.ChainProofs.bytesAt x.bRo x.b x.bsB ∗
      (CryptoVerification.SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (CryptoVerification.SpqrV1.ChainProofs.bytesAt x.aRo x.a x.bsA),
      sepConj_assoc] at hmem
  have hreadB := bytesAt_readBytes hmemB (by omega)
  rw [hlen] at hreadB
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [masterBcmpSpec, cliBcmpHook, retHook]
  rw [hx0, hx1, hx2, hreadA, hreadB]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hg x.bsA x.bsB hlen.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hmem⟩

/-- `K`-narrowed generalized fallback soundness (`W`-independent). -/
theorem hookBcmpOf_masterBcmpK_ok (keep : BitVec 64 → Bool)
    (g : List (BitVec 8) → List (BitVec 8) → BitVec 64)
    (hg : ∀ bsA bsB, bsA.length = bsB.length → ((g bsA bsB).setWidth 32 = 0#32 ↔ bsA = bsB)) :
    HookOk (cliBcmpHook g) (bcmpSpecK keep masterBcmpSpec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [bcmpSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hookBcmpOf_masterBcmp_ok g hg x R s0 hrun hpre.2 hsp

/-- Fixed `W`-independent byte comparator `(memcmpBytes bsA bsB).zeroExtend 64` for `bcmp` ghost
    hooks (which must be fixed before `∀ W : CliHooks` in `GhostRowReplayOn`). -/
@[expose] def canonicalBcmp (bsA bsB : List (BitVec 8)) : BitVec 64 :=
  (memcmpBytes bsA bsB).zeroExtend 64

theorem canonicalBcmp_ok (bsA bsB : List (BitVec 8)) (hlen : bsA.length = bsB.length) :
    (canonicalBcmp bsA bsB).setWidth 32 = 0#32 ↔ bsA = bsB := by
  unfold canonicalBcmp
  have htrunc : ((memcmpBytes bsA bsB).zeroExtend 64).setWidth 32 = memcmpBytes bsA bsB := by
    bv_omega
  rw [htrunc]
  exact memcmpBytes_eq_zero_iff hlen

/-- Fixed `W`-independent fallback hook `cliBcmpHook canonicalBcmp` for `bcmpGhostFn`. -/
@[expose] def hookBcmpFallback : State → State :=
  cliBcmpHook canonicalBcmp

/-- `hookBcmpFallback` satisfies `masterBcmpSpec` unconditionally (no `W : CliHooks` binder). -/
theorem hookBcmpFallback_masterBcmp_ok :
    HookOk hookBcmpFallback masterBcmpSpec :=
  hookBcmpOf_masterBcmp_ok canonicalBcmp canonicalBcmp_ok

/-- `hookBcmpFallback` satisfies `bcmpSpecK keep masterBcmpSpec` unconditionally. -/
theorem hookBcmpFallback_masterBcmpK_ok (keep : BitVec 64 → Bool) :
    HookOk hookBcmpFallback (bcmpSpecK keep masterBcmpSpec) :=
  hookBcmpOf_masterBcmpK_ok keep canonicalBcmp canonicalBcmp_ok

/-- `hookBcmpFallback` preserves `VmPreserved` for every state `s`. -/
theorem hookBcmpFallback_vmPreserved (s : State) :
    VmPreserved s (hookBcmpFallback s) :=
  cliBcmpHook_vmPreserved canonicalBcmp s

/-- Corollary: `cliBcmpHook W.bcmp` satisfies `masterBcmpSpec` for every `W : CliHooks`. -/
theorem hookBcmp_masterBcmp_ok (W : CliHooks) :
    HookOk (cliBcmpHook W.bcmp) masterBcmpSpec :=
  hookBcmpOf_masterBcmp_ok W.bcmp W.bcmp_ok

/-- Corollary: `cliBcmpHook W.bcmp` satisfies `bcmpSpecK keep masterBcmpSpec` for every `W`. -/
theorem hookBcmp_masterBcmpK_ok (keep : BitVec 64 → Bool) (W : CliHooks) :
    HookOk (cliBcmpHook W.bcmp) (bcmpSpecK keep masterBcmpSpec) :=
  hookBcmpOf_masterBcmpK_ok keep W.bcmp W.bcmp_ok

/-! ## 4. Generic `HookOk` Consequence Lifts from `masterBcmpSpec` -/

/-- General non-aborting ghost-reindexing frame/consequence lemma for `HookOk` (mirrors
    `MemcpyCode.hookOk_map_frame_pureAbort`). -/
theorem hookOk_map_frame_pureAbort {α β : Type} {f : State → State}
    {base : Spec α} {target : Spec β}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk f base)
    (hpre : ∀ y s0, target.pre y s0 ⊢ base.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, sf = f s0 → sf.symtab = s0.symtab →
      base.post (g y) s0 sf ∗ F y s0 ⊢ target.post y s0 sf)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f target := by
  intro y R s0 hrun hp hsp
  have hp' : s0.mem ⊨ base.pre (g y) s0 ∗ (F y s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre y s0)) hp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) (F y s0 ∗ R) s0 hrun hp' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp_sat⟩ | ⟨code, _, he_sat⟩ | ⟨_, ho_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost y s0 (f s0) rfl hsym)) hq
  · rw [hpan (g y) s0 (f s0), satisfies_pure_sepConj] at hp_sat
    exact False.elim hp_sat.1
  · rw [hex (g y) code s0 (f s0), satisfies_pure_sepConj] at he_sat
    exact False.elim he_sat.1
  · rw [hoom (g y) s0 (f s0), satisfies_pure_sepConj] at ho_sat
    exact False.elim ho_sat.1

/-- Any `HookOk f spec` weakens to `HookOk f (bcmpSpecK keep spec)`. -/
theorem hookOk_bcmpSpecK_of_plain (keep : BitVec 64 → Bool) {α : Type} {f : State → State}
    {spec : Spec α} (hh : HookOk f spec) :
    HookOk f (bcmpSpecK keep spec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [bcmpSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hh x R s0 hrun hpre.2 hsp

/-- Lift a ghost-reindexing frame/consequence derivation across `bcmpSpecK keep`. -/
theorem hookOk_bcmpSpecK_map_frame_pureAbort (keep : BitVec 64 → Bool)
    {α β : Type} {f : State → State} {base : Spec α} {target : Spec β}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk f (bcmpSpecK keep base))
    (hpre : ∀ y s0, target.pre y s0 ⊢ base.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, sf = f s0 → sf.symtab = s0.symtab →
      base.post (g y) s0 sf ∗ F y s0 ⊢ target.post y s0 sf)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (bcmpSpecK keep target) := by
  refine hookOk_map_frame_pureAbort g F hh
    (fun y s0 => ?_)
    (fun y s0 sf hsf hsym => hpost y s0 sf hsf hsym)
    (fun x s0 sf => hpan x s0 sf)
    (fun x code s0 sf => hex x code s0 sf)
    (fun x s0 sf => hoom x s0 sf)
  dsimp only [bcmpSpecK]
  rw [sepConj_assoc]
  exact Entails.pure_left fun hlr => Entails.pure_right hlr (hpre y s0)

/-- Weaken `HookOk f masterMemcmpSpec` (`w0 = memcmpBytes bsA bsB`) to `HookOk f masterBcmpSpec`
    (`w0 = 0 ↔ bsA = bsB`). -/
theorem hookOk_masterBcmp_of_masterMemcmp {f : State → State}
    (hh : HookOk f masterMemcmpSpec) :
    HookOk f masterBcmpSpec := by
  intro x R s0 hrun hpre hsp
  have hlen : x.bsB.length = x.bsA.length := by
    dsimp only [masterBcmpSpec] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.2.2.2
  obtain ⟨hkf, hsym, hout⟩ := hh x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [masterMemcmpSpec, masterBcmpSpec] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨⟨?_, hq.1.2.1, hq.1.2.2⟩, hq.2⟩
    change (f s0).readReg32 .x0 = 0#32 ↔ x.bsA = x.bsB
    rw [hq.1.1]
    exact memcmpBytes_eq_zero_iff hlen.symm
  · dsimp only [masterMemcmpSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [masterMemcmpSpec] at he; rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [masterMemcmpSpec] at ho; rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1

/-- Weaken `HookOk f (bcmpSpecK keep masterMemcmpSpec)` to
    `HookOk f (bcmpSpecK keep masterBcmpSpec)`. -/
theorem hookOk_masterBcmpK_of_masterMemcmp (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterMemcmpSpec)) :
    HookOk f (bcmpSpecK keep masterBcmpSpec) := by
  intro x R s0 hrun hpre hsp
  have hlen : x.bsB.length = x.bsA.length := by
    dsimp only [bcmpSpecK, masterBcmpSpec] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.2.1.2.2.2
  obtain ⟨hkf, hsym, hout⟩ := hh x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [bcmpSpecK, masterMemcmpSpec, masterBcmpSpec] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨⟨?_, hq.1.2.1, hq.1.2.2⟩, hq.2⟩
    change (f s0).readReg32 .x0 = 0#32 ↔ x.bsA = x.bsB
    rw [hq.1.1]
    exact memcmpBytes_eq_zero_iff hlen.symm
  · dsimp only [bcmpSpecK, masterMemcmpSpec] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [bcmpSpecK, masterMemcmpSpec] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [bcmpSpecK, masterMemcmpSpec] at ho
    rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1

/-- Consumer 1 (`DirSpecs.cliBcmpSpec`): lift `HookOk f masterBcmpSpec` to
    `HookOk f DirSpecs.cliBcmpSpec` (framing `stackAt s0.sp extHookStack`). -/
theorem hookOk_dirCliBcmp_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) :
    HookOk f cliBcmpSpec := by
  refine hookOk_map_frame_pureAbort id (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun x s0 => by
      dsimp only [cliBcmpSpec, masterBcmpSpec, id]
      simp only [sepConj_assoc]
      exact Entails.refl _)
    (fun x s0 sf _ _ => ?_)
  dsimp only [masterBcmpSpec, cliBcmpSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hret, _hvregs, hst⟩ =>
    Entails.pure_right ⟨hret, hst.2.1⟩ (Entails.refl _)

/-- Consumer 1 (`K`-narrowed `DirSpecs.cliBcmpSpec`): lift
    `HookOk f (bcmpSpecK keep masterBcmpSpec)` to `HookOk f (bcmpSpecK keep DirSpecs.cliBcmpSpec)`. -/
theorem hookOk_dirCliBcmpK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) :
    HookOk f (bcmpSpecK keep cliBcmpSpec) := by
  refine hookOk_bcmpSpecK_map_frame_pureAbort keep id (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun x s0 => by
      dsimp only [cliBcmpSpec, masterBcmpSpec, id]
      simp only [sepConj_assoc]
      exact Entails.refl _)
    (fun x s0 sf _ _ => ?_)
  dsimp only [masterBcmpSpec, cliBcmpSpec, id]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun ⟨hret, _hvregs, hst⟩ =>
    Entails.pure_right ⟨hret, hst.2.1⟩ (Entails.refl _)

/-- Stack-parametric Consumer 2 (`cliBcmpStackSpec stk`): lift `HookOk f masterBcmpSpec` to
    `HookOk f (cliBcmpStackSpec stk)` for any `stk : Nat`. -/
theorem hookOk_cliBcmpStack_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) (stk : Nat := extHookStack) :
    HookOk f (cliBcmpStackSpec stk) := by
  refine hookOk_map_frame_pureAbort
    (fun y => ⟨y.a, y.aRo, y.bsA, y.b, y.bRo, y.bsB⟩)
    (fun _ s0 => stackAt s0.sp stk) hh
    (fun y s0 => by
      dsimp only [cliBcmpStackSpec, masterBcmpSpec]
      cases y.aRo <;> cases y.bRo <;>
        simp only [LibsignalBinary.Proofs.HookDischarge.Libc.Common.bytesAt,
          bytesAt_false, bytesAt_true, sepConj_assoc] <;>
        exact Entails.refl _)
    (fun y s0 sf _ _ => ?_)
  dsimp only [masterBcmpSpec, cliBcmpStackSpec]
  cases y.aRo <;> cases y.bRo <;>
    simp only [LibsignalBinary.Proofs.HookDischarge.Libc.Common.bytesAt,
      bytesAt_false, bytesAt_true, sepConj_assoc] <;>
    exact Entails.pure_left fun ⟨hret, _hvregs, hst⟩ =>
      Entails.pure_right ⟨hret, hst.2.1⟩ (Entails.refl _)

/-- Stack-parametric Consumer 2 (`K`-narrowed `cliBcmpStackSpec stk`): lift
    `HookOk f (bcmpSpecK keep masterBcmpSpec)` to `HookOk f (bcmpSpecK keep (cliBcmpStackSpec stk))`. -/
theorem hookOk_cliBcmpStackK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) (stk : Nat := extHookStack) :
    HookOk f (bcmpSpecK keep (cliBcmpStackSpec stk)) := by
  refine hookOk_bcmpSpecK_map_frame_pureAbort keep
    (fun y => ⟨y.a, y.aRo, y.bsA, y.b, y.bRo, y.bsB⟩)
    (fun _ s0 => stackAt s0.sp stk) hh
    (fun y s0 => by
      dsimp only [cliBcmpStackSpec, masterBcmpSpec]
      cases y.aRo <;> cases y.bRo <;>
        simp only [LibsignalBinary.Proofs.HookDischarge.Libc.Common.bytesAt,
          bytesAt_false, bytesAt_true, sepConj_assoc] <;>
        exact Entails.refl _)
    (fun y s0 sf _ _ => ?_)
  dsimp only [masterBcmpSpec, cliBcmpStackSpec]
  cases y.aRo <;> cases y.bRo <;>
    simp only [LibsignalBinary.Proofs.HookDischarge.Libc.Common.bytesAt,
      bytesAt_false, bytesAt_true, sepConj_assoc] <;>
    exact Entails.pure_left fun ⟨hret, _hvregs, hst⟩ =>
      Entails.pure_right ⟨hret, hst.2.1⟩ (Entails.refl _)

/-- Consumer 2 (`CliExt.bcmpSpec` = `cliBcmpStackSpec extHookStack`): lift
    `HookOk f masterBcmpSpec` to `HookOk f CliExt.bcmpSpec`. -/
theorem hookOk_cliExtBcmp_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) :
    HookOk f bcmpSpec :=
  hookOk_cliBcmpStack_of_master hh extHookStack

/-- Consumer 2 (`K`-narrowed `CliExt.bcmpSpec`): lift
    `HookOk f (bcmpSpecK keep masterBcmpSpec)` to `HookOk f (bcmpSpecK keep CliExt.bcmpSpec)`. -/
theorem hookOk_cliExtBcmpK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) :
    HookOk f (bcmpSpecK keep bcmpSpec) :=
  hookOk_cliBcmpStackK_of_master keep hh extHookStack

/-- Consumer 3 (`HooksE.bcmpVregsSpec`): lift `HookOk f masterBcmpSpec` to
    `HookOk f HooksE.bcmpVregsSpec` (`aRo = false`, `bRo = false`, retaining `sf.vregs = s0.vregs`). -/
theorem hookOk_bcmpVregs_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) :
    HookOk f bcmpVregsSpec := by
  refine hookOk_map_frame_pureAbort
    (fun y => ⟨y.a, false, y.bsA, y.b, false, y.bsB⟩)
    (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun y s0 => by
      dsimp only [bcmpVregsSpec, masterBcmpSpec]
      simp only [bytesAt_false, sepConj_assoc]
      exact Entails.refl _)
    (fun y s0 sf _ _ => ?_)
  dsimp only [masterBcmpSpec, bcmpVregsSpec]
  simp only [bytesAt_false, sepConj_assoc]
  exact Entails.pure_left fun ⟨hret, hvregs, hst⟩ =>
    Entails.pure_right ⟨hret, hvregs, hst.2.1⟩ (Entails.refl _)

/-- Consumer 3 (`K`-narrowed `HooksE.bcmpVregsSpec`): lift
    `HookOk f (bcmpSpecK keep masterBcmpSpec)` to `HookOk f (bcmpSpecK keep HooksE.bcmpVregsSpec)`. -/
theorem hookOk_bcmpVregsK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) :
    HookOk f (bcmpSpecK keep bcmpVregsSpec) := by
  refine hookOk_bcmpSpecK_map_frame_pureAbort keep
    (fun y => ⟨y.a, false, y.bsA, y.b, false, y.bsB⟩)
    (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun y s0 => by
      dsimp only [bcmpVregsSpec, masterBcmpSpec]
      simp only [bytesAt_false, sepConj_assoc]
      exact Entails.refl _)
    (fun y s0 sf _ _ => ?_)
  dsimp only [masterBcmpSpec, bcmpVregsSpec]
  simp only [bytesAt_false, sepConj_assoc]
  exact Entails.pure_left fun ⟨hret, hvregs, hst⟩ =>
    Entails.pure_right ⟨hret, hvregs, hst.2.1⟩ (Entails.refl _)

/-- Consumer 4 (`HooksE.e2eBcmpSpec`): lift `HookOk f masterBcmpSpec` to
    `HookOk f HooksE.e2eBcmpSpec`. -/
theorem hookOk_e2eBcmp_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) :
    HookOk f e2eBcmpSpec := by
  refine hookOk_map_frame_pureAbort
    (fun y => ⟨y.a, false, y.bsA, y.b, false, y.bsB⟩)
    (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun y s0 => by
      dsimp only [e2eBcmpSpec, masterBcmpSpec]
      simp only [bytesAt_false, sepConj_assoc]
      exact Entails.refl _)
    (fun y s0 sf _ _ => ?_)
  dsimp only [masterBcmpSpec, e2eBcmpSpec]
  simp only [bytesAt_false, sepConj_assoc]
  exact Entails.pure_left fun ⟨hret, _hvregs, hst⟩ =>
    Entails.pure_right ⟨hret, hst.2.1⟩ (Entails.refl _)

/-- Consumer 4 (`K`-narrowed `HooksE.e2eBcmpSpec`): lift
    `HookOk f (bcmpSpecK keep masterBcmpSpec)` to `HookOk f (bcmpSpecK keep HooksE.e2eBcmpSpec)`. -/
theorem hookOk_e2eBcmpK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) :
    HookOk f (bcmpSpecK keep e2eBcmpSpec) := by
  refine hookOk_bcmpSpecK_map_frame_pureAbort keep
    (fun y => ⟨y.a, false, y.bsA, y.b, false, y.bsB⟩)
    (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun y s0 => by
      dsimp only [e2eBcmpSpec, masterBcmpSpec]
      simp only [bytesAt_false, sepConj_assoc]
      exact Entails.refl _)
    (fun y s0 sf _ _ => ?_)
  dsimp only [masterBcmpSpec, e2eBcmpSpec]
  simp only [bytesAt_false, sepConj_assoc]
  exact Entails.pure_left fun ⟨hret, _hvregs, hst⟩ =>
    Entails.pure_right ⟨hret, hst.2.1⟩ (Entails.refl _)

/-- `bcmpSpecK keep` commutes definitionally with `.keepsFs`, `withVmPreserved`, and
    `withOomPoolPreserved` (which only touch `post`). -/
theorem bcmpSpecK_keepsFs (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    (bcmpSpecK keep spec).keepsFs = bcmpSpecK keep spec.keepsFs := rfl

theorem bcmpSpecK_withVmPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withVmPreserved (bcmpSpecK keep spec) = bcmpSpecK keep (withVmPreserved spec) := rfl

theorem bcmpSpecK_withOomPoolPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withOomPoolPreserved (bcmpSpecK keep spec) =
      bcmpSpecK keep (withOomPoolPreserved spec) := rfl

theorem bcmpSpecK_hooksEBcmpVregsBudget (keep : BitVec 64 → Bool) :
    withVmPreserved (bcmpSpecK keep bcmpVregsSpec) =
      bcmpSpecK keep LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.bcmpVregsSpec := rfl

theorem bcmpSpecK_hooksEE2eBcmpBudget (keep : BitVec 64 → Bool) :
    withVmPreserved (bcmpSpecK keep e2eBcmpSpec) =
      bcmpSpecK keep LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.e2eBcmpSpec := rfl

/-- Consumer 1 (`withVmPreserved DirSpecs.cliBcmpSpec`): lift `HookOk f masterBcmpSpec` +
    pointwise `VmPreserved`. -/
theorem hookOk_dirCliBcmp_vmPreserved_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved cliBcmpSpec) :=
  hookOk_withVmPreserved (hookOk_dirCliBcmp_of_master hh) hvm

theorem hookOk_dirCliBcmpK_vmPreserved_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (bcmpSpecK keep (withVmPreserved cliBcmpSpec)) :=
  bcmpSpecK_withVmPreserved keep cliBcmpSpec ▸
    hookOk_withVmPreserved (hookOk_dirCliBcmpK_of_master keep hh) hvm

/-- Consumer 2 (`withVmPreserved (cliBcmpStackSpec stk)` and `withVmPreserved CliExt.bcmpSpec`):
    lift `HookOk f masterBcmpSpec` + pointwise `VmPreserved`. -/
theorem hookOk_cliBcmpStack_vmPreserved_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) (hvm : ∀ s, VmPreserved s (f s)) (stk : Nat) :
    HookOk f (withVmPreserved (cliBcmpStackSpec stk)) :=
  hookOk_withVmPreserved (hookOk_cliBcmpStack_of_master hh stk) hvm

theorem hookOk_cliBcmpStackK_vmPreserved_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) (hvm : ∀ s, VmPreserved s (f s)) (stk : Nat) :
    HookOk f (bcmpSpecK keep (withVmPreserved (cliBcmpStackSpec stk))) :=
  bcmpSpecK_withVmPreserved keep (cliBcmpStackSpec stk) ▸
    hookOk_withVmPreserved (hookOk_cliBcmpStackK_of_master keep hh stk) hvm

theorem hookOk_cliExtBcmp_vmPreserved_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved bcmpSpec) :=
  hookOk_withVmPreserved (hookOk_cliExtBcmp_of_master hh) hvm

theorem hookOk_cliExtBcmpK_vmPreserved_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (bcmpSpecK keep (withVmPreserved bcmpSpec)) :=
  bcmpSpecK_withVmPreserved keep bcmpSpec ▸
    hookOk_withVmPreserved (hookOk_cliExtBcmpK_of_master keep hh) hvm

/-- Consumer 3 (`HooksE.CommonBudget.bcmpVregsSpec := withVmPreserved HooksE.bcmpVregsSpec`):
    lift `HookOk f masterBcmpSpec` + pointwise `VmPreserved`. -/
theorem hookOk_bcmpVregsBudget_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.bcmpVregsSpec :=
  hookOk_withVmPreserved (hookOk_bcmpVregs_of_master hh) hvm

theorem hookOk_bcmpVregsBudgetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (bcmpSpecK keep LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.bcmpVregsSpec) :=
  bcmpSpecK_hooksEBcmpVregsBudget keep ▸
    hookOk_withVmPreserved (hookOk_bcmpVregsK_of_master keep hh) hvm

/-- Consumer 4 (`HooksE.CommonBudget.e2eBcmpSpec := withVmPreserved HooksE.e2eBcmpSpec`):
    lift `HookOk f masterBcmpSpec` + pointwise `VmPreserved`. -/
theorem hookOk_e2eBcmpBudget_of_master {f : State → State}
    (hh : HookOk f masterBcmpSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.e2eBcmpSpec :=
  hookOk_withVmPreserved (hookOk_e2eBcmp_of_master hh) hvm

theorem hookOk_e2eBcmpBudgetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (bcmpSpecK keep masterBcmpSpec)) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (bcmpSpecK keep LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.e2eBcmpSpec) :=
  bcmpSpecK_hooksEE2eBcmpBudget keep ▸
    hookOk_withVmPreserved (hookOk_e2eBcmpK_of_master keep hh) hvm

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode
