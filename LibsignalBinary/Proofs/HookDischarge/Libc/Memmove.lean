/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.MemmoveProof
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Common.SharedHelpers -- proof-setup: allow-public-import
import ProofLib.BV.Bits

/-!
# Byte-Exact `memmove` Hook Discharge (`LibsignalBinary.Proofs.HookDischarge.Libc.Memmove`)

Byte-exact discharge of `memmove` against the `74` AArch64 words (`296` bytes) of
`rustc 1.98.1`'s `aarch64-unknown-linux-musl/lib/self-contained/libc.a` `memmove.lo`
(`VerifiedLibraries.Musl.memmoveLibcaWords`, patched at `+0x68` via
`Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve`).

## Design & Contracts
1. **`MemmoveArithBound` (`C_ARITH_BOUND`):**
   `base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63` (the buffer does not wrap the
   64-bit address space and fits in signed `isize::MAX`, required by C `memmove`'s pointer/size
   comparisons and discharged at heap call sites from `RustAlloc.block_valid`).
2. **Explicit `memcpy` tail-call hypothesis (`memcpyTailSpec` / `memcpyTailVmSpec`):**
   On disjoint ranges (`dst ≠ src` and `BitVec.ule (src - n - dst) (-(n <<< 1)) = true`),
   `memmove.lo` tail-calls `memcpy` via `b memcpy` at `+0x68`. We parameterize the real-bytes
   theorems over `subroutine_ok prog (resolve "memcpy") memcpyTailSpec` (or `memcpyTailVmSpec`),
   where `memcpyTailSpec` specializes `masterMemcpySpec` (`Cli/HooksDehook/MemcpyCode.lean`) to
   `ro = false` (`Common.bytesAt false = memcpySrc false` and
   `MemmoveStatePreserved = MemcpyStatePreserved` by `rfl`, bridged via
   `memcpyTail_ok_of_masterMemcpy_ok` / `memcpyTailVm_ok_of_masterMemcpyVm_ok`).
3. **Ideal hook (`toSat`) & `HookSat` weakening:**
   `hookMemmove` (`abbrev` of `hookMemcpy` in `ProofLib/Hoare/LibcHooks.lean`) satisfies
   `masterMemmoveVmSpec`, `libcMemmoveBoundedSpec`, `sessionMemmoveBoundedSpec`, and
   `sessionMemmoveBoundedBudgetSpec`, so `*Sat` consumer siblings instantiate immediately
   from today's `cliHookTablePlaced` and weaken from unbounded `HookSat` witnesses.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.Libc.Memmove

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open VerifiedLibraries.Musl
  (memmoveLibcaWords memmoveLibcaCalls memmoveSpec moveBytes moveBytes_eq_listMove
   memcpySpec MemmoveFetch memmoveFetch_of_patchCalls memmove_patchCalls_ok
   memmove_reaches_of_sepWP memmove_ret memmove_fwd_entry memmove_bwd_entry
   disjoint_of_sub_ule mm_fwd_safe_of_not_ule mm_bwd_safe_of_ule mm_offset_eq_of_ptr_eq
   pointsToBytes_split_disjoint MmExit mmSet)
open CryptoVerification.LibsignalTripleRatchet (sessionMemmoveSpec extHookStack)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
  (MemcpyStatePreserved masterMemcpySpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common
  (keepsFs bytesAt subroutine_ok_drop_keepsFs)

/-! ## 1. Arithmetic Bound, State Preservation, and `memmove` / `memcpy` Specifications -/

/-- `C_ARITH_BOUND` precondition from `VerifiedLibraries.Musl.memmoveSpec`:
    `base + buf.length` does not wrap `2 ^ 64` and `buf.length < 2 ^ 63` (`isize::MAX + 1`). -/
@[expose] def MemmoveArithBound (base : BitVec 64) (buf : List (BitVec 8)) : Prop :=
  base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63

/-- Process/OS state fields preserved across `memmove` and its `+0x68` `memcpy` tail-call.
    Definitionally equal (`rfl`) to `MemcpyStatePreserved` in `Cli/HooksDehook/MemcpyCode.lean`. -/
@[expose] def MemmoveStatePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
    sf.trace = s0.trace ∧
    sf.tpidrEl0 = s0.tpidrEl0 ∧
    sf.sigActions = s0.sigActions ∧
    sf.brk = s0.brk ∧
    sf.brkStart = s0.brkStart ∧
    sf.physMemAvail = s0.physMemAvail

theorem MemmoveStatePreserved.refl (s : State) : MemmoveStatePreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MemmoveStatePreserved.trans {s0 s1 s2 : State}
    (h01 : MemmoveStatePreserved s0 s1) (h12 : MemmoveStatePreserved s1 s2) :
    MemmoveStatePreserved s0 s2 :=
  ⟨h12.1.trans h01.1,
   h12.2.1.trans h01.2.1,
   h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1,
   h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem MemmoveStatePreserved.of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : MemmoveStatePreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- Conjoin `⌜VmPreserved s0 sf⌝` to `spec.post` (definitionally equal to
    `LibsignalBinary.Heap.SpecBudget.withVmPreserved`). -/
@[expose] def withVmPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-- Explicit contract required of `resolve "memcpy"` at `memmove`'s `+0x68` tail-call.
    Definitionally equal (`rfl`) to `masterMemcpySpec` in `Cli/HooksDehook/MemcpyCode.lean`. -/
@[expose] def memcpyTailSpec :
    Spec (Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (ro, dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗
      bytesAt ro src bs
  post := fun (ro, dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ MemmoveStatePreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗
      bytesAt ro src bs
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- `VmPreserved`-strengthened counterpart of `memcpyTailSpec` (`withVmPreserved masterMemcpySpec`). -/
@[expose] def memcpyTailVmSpec :
    Spec (Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved memcpyTailSpec

/-- `MemmoveStatePreserved` is definitionally equal (`rfl`) to `MemcpyStatePreserved`. -/
theorem memmoveStatePreserved_eq_memcpyStatePreserved :
    @MemmoveStatePreserved = @MemcpyStatePreserved := rfl

/-- `masterMemcpySpec` (`Cli/HooksDehook/MemcpyCode.lean`) directly discharges `memcpyTailSpec`
    (used at `ro = false` for `memmove`'s `+0x68` `b memcpy` tail-call). -/
theorem memcpyTail_ok_of_masterMemcpy_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry masterMemcpySpec) :
    subroutine_ok prog entry memcpyTailSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨ro, dst, src, bs⟩ R s0 hpre
  refine ⟨(ro, dst, src, bs), R, ?_, fun sf hpost => ?_⟩
  · cases ro <;> exact hpre
  · cases ro <;> exact hpost

/-- `SpecBudget.withVmPreserved masterMemcpySpec` directly discharges `memcpyTailVmSpec`. -/
theorem memcpyTailVm_ok_of_masterMemcpyVm_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved masterMemcpySpec)) :
    subroutine_ok prog entry memcpyTailVmSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨ro, dst, src, bs⟩ R s0 hpre
  refine ⟨(ro, dst, src, bs), R, ?_, fun sf hpost => ?_⟩
  · cases ro <;> exact hpre
  · cases ro <;> exact hpost

/-- `VerifiedLibraries.Musl.memmoveSpec` strengthened with `MemmoveStatePreserved s0 sf`. -/
@[expose] def masterMemmoveSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat) :=
  { memmoveSpec with
    post := fun x s0 sf => ⌜MemmoveStatePreserved s0 sf⌝ ∗ memmoveSpec.post x s0 sf }

/-- `masterMemmoveSpec` strengthened with `VmPreserved s0 sf`. -/
@[expose] def masterMemmoveVmSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat) :=
  withVmPreserved masterMemmoveSpec

/-- `K`-route precondition narrowing: conjoins `⌜keep (s.readReg64 .lr) = false⌝` to `spec.pre`. -/
@[expose] def memmoveSpecK (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre x s }

/-- `ProofLib.libcMemmoveSpec` augmented with `MemmoveArithBound base buf` (`C_ARITH_BOUND`). -/
@[expose] def libcMemmoveBoundedSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  { ProofLib.libcMemmoveSpec hookStack with
    pre := fun (base, buf, dst, src, len) s0 =>
      ⌜MemmoveArithBound base buf⌝ ∗
        (ProofLib.libcMemmoveSpec hookStack).pre (base, buf, dst, src, len) s0 }

/-- `sessionMemmoveSpec` augmented with `MemmoveArithBound base buf` (`C_ARITH_BOUND`). -/
@[expose] def sessionMemmoveBoundedSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  { sessionMemmoveSpec hookStack with
    pre := fun (base, buf, dst, src, len) s0 =>
      ⌜MemmoveArithBound base buf⌝ ∗
        (sessionMemmoveSpec hookStack).pre (base, buf, dst, src, len) s0 }

/-- Budget-threaded `sessionMemmoveBudgetSpec` augmented with `MemmoveArithBound base buf`
    (`C_ARITH_BOUND`). Consumer spec for the budget CMK `*Sat` sibling chain. -/
@[expose] def sessionMemmoveBoundedBudgetSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  { sessionMemmoveBudgetSpec hookStack with
    pre := fun (base, buf, dst, src, len) s0 =>
      ⌜MemmoveArithBound base buf⌝ ∗
        (sessionMemmoveBudgetSpec hookStack).pre (base, buf, dst, src, len) s0 }

theorem sessionMemmoveBoundedBudgetSpec_eq_withVmPreserved (hookStack : Nat := extHookStack) :
    sessionMemmoveBoundedBudgetSpec hookStack =
      withVmPreserved (sessionMemmoveBoundedSpec hookStack) := rfl

/-! ## 2. Pure-Words `hasWords` and Opcode-Exclusion Witnesses for Patched `memmove.lo` -/

private theorem wordToBytesLE_concat (w : BitVec 32) :
    let b0 := w.extractLsb' 0 8
    let b1 := w.extractLsb' 8 8
    let b2 := w.extractLsb' 16 8
    let b3 := w.extractLsb' 24 8
    b3 ++ b2 ++ b1 ++ b0 = w := by
  dsimp only
  bv_bits

private theorem drop_flatMap_wordToBytesLE (words : List (BitVec 32)) (i : Nat) :
    (words.flatMap Program.wordToBytesLE).drop (4 * i) =
      (words.drop i).flatMap Program.wordToBytesLE := by
  induction words generalizing i with
  | nil => simp
  | cons w ws ih =>
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
  have hget : words[i]? = (words.drop i)[0]? := by
    simp [List.getElem?_drop]
  rw [hget]
  cases h : words.drop i with
  | nil => simp
  | cons w ws =>
    simp [Program.wordToBytesLE, wordToBytesLE_concat]

open Arm64.Process (pureWordsProg pureWordsProg_hasWords)

private theorem pureWordsProg_hasWords_any (base : BitVec 64) (words : List (BitVec 32))
    (hbound : 4 * words.length ≤ 2 ^ 64) :
    (pureWordsProg base words).hasWords base words := by
  refine pureWordsProg_hasWords hbound (List.all_eq_true.mpr fun i _ => ?_)
  have h1 : (pureWordsProg base words).readWordOff (4 * i) = words[i]? :=
    readWordOff_ofWords_mul4 base words i
  simp [h1]

private theorem bytesAllWords_flatMap_wordToBytesLE (pw : BitVec 32 → Bool) :
    ∀ words : List (BitVec 32),
      bytesAllWords pw (words.flatMap Program.wordToBytesLE) = words.all pw
  | [] => rfl
  | w :: ws => by
    simp only [List.flatMap_cons, Program.wordToBytesLE, List.cons_append, List.nil_append,
      bytesAllWords, wordToBytesLE_concat, List.all_cons,
      bytesAllWords_flatMap_wordToBytesLE pw ws]

private theorem pureWordsProg_allInstrs_iff (base : BitVec 64) (words : List (BitVec 32))
    (p : Instr → Bool) :
    (pureWordsProg base words).allInstrs p = words.all (instrPredOnWord p) := by
  unfold pureWordsProg Program.ofWords Program.allInstrs Program.allWords
  exact bytesAllWords_flatMap_wordToBytesLE (instrPredOnWord p) words

private theorem memmoveLibcaWords_noSvcMsr :
    memmoveLibcaWords.all (instrPredOnWord (fun i => !i.isSvc && !i.isMsrTpidrEl0)) = true := by
  decide +kernel

private theorem memmoveCalls_find_other :
    ∀ j < 74, j ≠ 26 → memmoveLibcaCalls.find? (·.1 == 4 * j) = none := by
  decide +kernel

private theorem patched_memmove_length (entry : BitVec 64) (resolve : String → BitVec 64) :
    (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve).length = 74 := by
  rw [Obj.patchCalls, List.length_mapIdx]
  rfl

private theorem patchCalls_getElem? (calls : List (Nat × String)) (ws : List (BitVec 32))
    (entry : BitVec 64) (resolve : String → BitVec 64) (j : Nat) :
    (Obj.patchCalls calls ws entry resolve)[j]? =
      (ws[j]?).map fun w =>
        match calls.find? (·.1 == 4 * j) with
        | some (_, sym) => Obj.branchWord w (entry + BitVec.ofNat 64 (4 * j)) (resolve sym)
        | none => w := by
  unfold Obj.patchCalls
  rw [List.getElem?_mapIdx]
  cases ws[j]? <;> simp only [Option.map]
  rcases calls.find? (·.1 == 4 * j) with _ | ⟨_, sym⟩ <;> rfl

private theorem patched_memmove_noSvcMsr (entry : BitVec 64) (resolve : String → BitVec 64)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy")) :
    (pureWordsProg entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve)).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true := by
  rw [pureWordsProg_allInstrs_iff, List.all_eq_true]
  intro w hw
  obtain ⟨j, hj, hw_eq⟩ := List.getElem_of_mem hw
  have hj? : (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve)[j]? = some w :=
    (List.getElem?_eq_getElem hj).trans (congrArg some hw_eq)
  have hj74 : j < 74 := by rw [patched_memmove_length] at hj; exact hj
  clear hj hw_eq hw
  by_cases h26 : j = 26
  · subst h26
    have hfind : memmoveLibcaCalls.find? (·.1 == 4 * 26) = some (104, "memcpy") := rfl
    have hbase26 : memmoveLibcaWords[26]? = some 0x14000000#32 := rfl
    rw [patchCalls_getElem?, hbase26, hfind] at hj?
    dsimp only [Option.map] at hj?
    injection hj? with hw_b
    rw [← hw_b]
    have hdec := Obj.decode_branchWord_b (w := 0x14000000#32)
      (place := entry + reloc_call_off% memmoveLibcaCalls "memcpy") (target := resolve "memcpy") (by decide) hrange
    unfold instrPredOnWord
    rw [hdec]
    rfl
  · rw [patchCalls_getElem?, memmoveCalls_find_other j hj74 h26] at hj?
    cases hmw : memmoveLibcaWords[j]? with
    | none => rw [hmw] at hj?; cases hj?
    | some w0 =>
      rw [hmw] at hj?
      dsimp only [Option.map] at hj?
      injection hj? with hw0
      rw [← hw0]
      obtain ⟨hj_orig, rfl⟩ := List.getElem?_eq_some_iff.mp hmw
      exact List.all_eq_true.mp memmoveLibcaWords_noSvcMsr _ (List.getElem_mem hj_orig)


/-! ## 3. Real-Bytes `subroutine_ok` Proofs on Patched `memmoveLibcaWords` -/

theorem vmPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩,
   h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2,
   LibsignalBinary.Heap.FdsHiFrame.of_fs_eq h.1⟩

private def MemmoveLocalCase (dst src n : BitVec 64) : Prop :=
  (dst == src) = true ∨ BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = false

private def memmoveLocalSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat) :=
  { memmoveSpec with
    pre := fun (dst, src, n, base, buf, d, o) s0 =>
      ⌜MemmoveLocalCase dst src n⌝ ∗ memmoveSpec.pre (dst, src, n, base, buf, d, o) s0 }

private theorem mm_listMove_self_local {buf : List (BitVec 8)} {d len : Nat} :
    ProofLib.listMove buf d d len = buf := by
  simp [ProofLib.listMove, ← List.drop_drop, List.take_append_drop]

section LocalStepping

attribute [local irreducible] Program.fetch Program.externAt?

private theorem memmoveLocal_core_reaches (prog0 : Program) (entry mc : BitVec 64)
    (hf : MemmoveFetch prog0 entry mc)
    {dst src n base : BitVec 64} {buf : List (BitVec 8)} {d o : Nat}
    (s0 : State) (R : SepProp) (Post : State → Prop)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src) (hx2 : s0.readReg64 .x2 = n)
    (hcase : MemmoveLocalCase dst src n)
    (hdst : dst = base + BitVec.ofNat 64 d) (hsrc : src = base + BitVec.ofNat 64 o)
    (hd_le : d + n.toNat ≤ buf.length) (ho_le : o + n.toNat ≤ buf.length)
    (hbase_le : base.toNat + buf.length ≤ 2 ^ 64) (hbuf_lt : buf.length < 2 ^ 63)
    (hmem0 : s0.mem ⊨ (base ↦ₛ buf) ∗ R)
    (h_local : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      MmExit s0 dst sf → sf.mem ⊨ (base ↦ₛ ProofLib.listMove buf d o n.toNat) ∗ R → Post sf) :
    reaches_pc prog0 (s0.readReg64 .lr) s0 Post := by
  obtain ⟨hc, hf_b⟩ := hf
  have ⟨hcA, _⟩ := hc
  have hx2n : n = BitVec.ofNat 64 n.toNat := by simp
  have h_ret := fun (heq : (dst == src) = true) (s : State) hpc'
      (hrun' : s.status = .Running) (hmem' : s.mem = s0.mem) (hx7' : s.readReg64 .x7 = dst)
      (hsp' : s.sp = s0.sp) (hlr' : s.readReg64 .lr = s0.readReg64 .lr)
      (hcs' : CalleeSavedPreserved s0 s) => show reaches_pc prog0 (s0.readReg64 .lr) s Post by
    have hdo : d = o :=
      mm_offset_eq_of_ptr_eq hd_le ho_le hbuf_lt (hdst.symm.trans ((beq_iff_eq.mp heq).trans hsrc))
    have hself : buf = ProofLib.listMove buf d o n.toNat := hdo ▸ mm_listMove_self_local.symm
    refine memmove_reaches_of_sepWP
      (memmove_ret prog0 entry hc s0 s base buf _ dst hself
        hpc' hrun' hx7' hsp' hlr' hcs') ?_ h_local
    rwa [hmem']
  have h_fwd := fun (hcmp : BitVec.ule src dst = false) (s : State) hpc'
      (hrun' : s.status = .Running) (hmem' : s.mem = s0.mem)
      (hx7' : s.readReg64 .x7 = dst) (hx0' : s.readReg64 .x0 = dst) (hx4' : s.readReg64 .x4 = src)
      (hx2' : s.readReg64 .x2 = n) (hx3' : s.readReg64 .x3 = n) (hx5' : s.readReg64 .x5 = src - n)
      (hsp' : s.sp = s0.sp) (hlr' : s.readReg64 .lr = s0.readReg64 .lr)
      (hcs' : CalleeSavedPreserved s0 s) => show reaches_pc prog0 (s0.readReg64 .lr) s Post by
    refine memmove_reaches_of_sepWP
      (memmove_fwd_entry (hc := hc) (hd := hd_le) (ho := ho_le) (hbuf := hbuf_lt)
        (hfwd := mm_fwd_safe_of_not_ule hdst hsrc hd_le ho_le hbase_le hbuf_lt hcmp)
        (hrun := hrun') (hx7 := hx7'.trans hdst) (hsp := hsp') (hlr := hlr') (hcs := hcs')
        (hpc := hpc') (hx0 := hx0'.trans hdst) (hx4 := hx4'.trans hsrc) (hx2 := hx2'.trans hx2n)
        (hx3 := hx3'.trans hx2n)
        (hx5 := hx5'.trans (by rw [hsrc, ← hx2n]))) ?_
      (fun sf h1 h2 hex hm => h_local sf h1 h2 (hdst.symm ▸ hex) hm)
    rwa [VerifiedLibraries.Musl.mm_mmSet_empty, hmem']
  have h_bwd := fun (hcmp : BitVec.ule src dst = true) (s : State) hpc'
      (hrun' : s.status = .Running) (hmem' : s.mem = s0.mem)
      (hx7' : s.readReg64 .x7 = dst) (hx4' : s.readReg64 .x4 = src) (hx3' : s.readReg64 .x3 = n)
      (hsp' : s.sp = s0.sp) (hlr' : s.readReg64 .lr = s0.readReg64 .lr)
      (hcs' : CalleeSavedPreserved s0 s) => show reaches_pc prog0 (s0.readReg64 .lr) s Post by
    refine memmove_reaches_of_sepWP
      (memmove_bwd_entry (hc := hc) (hd := hd_le) (ho := ho_le) (hbuf := hbuf_lt)
        (hbwd := mm_bwd_safe_of_ule hdst hsrc hd_le ho_le hbase_le hbuf_lt hcmp)
        (hrun := hrun') (hx7 := hx7'.trans hdst) (hx4 := hx4'.trans hsrc) (hsp := hsp')
        (hlr := hlr') (hcs := hcs')
        (hpc := hpc') (hx3 := hx3'.trans hx2n)) ?_
      (fun sf h1 h2 hex hm => h_local sf h1 h2 (hdst.symm ▸ hex) hm)
    rwa [VerifiedLibraries.Musl.mm_mmSet_empty, hmem']
  clear hdst hsrc h_local hmem0 hx2n
  by_cases heq : (dst == src) = true
  · iterate 5 arm64_step
  have heq_f : (dst == src) = false := Bool.eq_false_iff.mpr heq
  by_cases hule : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = true
  · exfalso
    rcases hcase with h1 | h2
    · rw [heq_f] at h1; contradiction
    · rw [hule] at h2; contradiction
  have hule_f : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = false :=
    Bool.eq_false_iff.mpr hule
  by_cases hcs : BitVec.ule src dst = true
  · iterate 14 arm64_step
  · have hcs_f : BitVec.ule src dst = false := Bool.eq_false_iff.mpr hcs
    iterate 14 arm64_step

private theorem memmoveLocal_fetch_ok (prog0 : Program) (entry mc : BitVec 64)
    (hf : MemmoveFetch prog0 entry mc) :
    subroutine_ok prog0 entry memmoveLocalSpec := by
  apply subroutine_ok_outcome_intro
  intro ⟨dst, src, n, base, buf, d, o⟩ R s0 hpc hrun hpre _hal
  refine reaches_outcome_of_reaches_pc (oom := fun _ => False) ?_
  dsimp only [memmoveLocalSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcase, hpre0⟩ := hpre
  obtain ⟨⟨hx0, hx1, hx2, hdst, hsrc, ⟨hd_le, ho_le⟩, ⟨hbase_le, hbuf_lt⟩⟩, hmem0⟩ :=
    VerifiedLibraries.Musl.memmove_pre_extract hpre0
  refine memmoveLocal_core_reaches prog0 entry mc hf s0 R
    (SubroutinePost memmoveLocalSpec (dst, src, n, base, buf, d, o) R s0)
    hpc hrun hx0 hx1 hx2 hcase hdst hsrc hd_le ho_le hbase_le hbuf_lt hmem0 ?_
  intro sf _hpc_f _hrun_f ⟨hx0_f, hsp_f, hcs_f⟩ hmem_f
  exact ⟨VerifiedLibraries.Musl.memmove_post_of_moved (src := src) (s0 := s0) hmem_f hx0_f,
    hsp_f, hcs_f⟩

private theorem memmove_disjoint_step_to_tailcall (prog : Program) (entry mc dst src n : BitVec 64)
    (hcA : prog.hasCode entry VerifiedLibraries.Musl.memmoveWordsA)
    (hf_b : prog.fetch (entry + reloc_call_off% memmoveLibcaCalls "memcpy") =
      some (.b (mc - (entry + reloc_call_off% memmoveLibcaCalls "memcpy"))))
    (s0 : State) (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src) (hx2 : s0.readReg64 .x2 = n)
    (heq_f : (dst == src) = false)
    (hule : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = true)
    (hL : prog.CodeLoaded s0.mem) :
    ∃ sc : State,
      Steps prog s0 sc ∧
      sc.pc = mc ∧ sc.status = .Running ∧
      sc.readReg64 .x0 = dst ∧ sc.readReg64 .x1 = src ∧ sc.readReg64 .x2 = n ∧
      sc.mem = s0.mem ∧ sc.sp = s0.sp ∧ sc.symtab = s0.symtab ∧
      sc.readReg64 .lr = s0.readReg64 .lr ∧ CalleeSavedPreserved s0 sc ∧
      MemmoveStatePreserved s0 sc ∧ VmPreserved s0 sc := by
  let Post : State → Prop := fun sc =>
    sc.pc = mc ∧ sc.status = .Running ∧
      sc.readReg64 .x0 = dst ∧ sc.readReg64 .x1 = src ∧ sc.readReg64 .x2 = n ∧
      sc.mem = s0.mem ∧ sc.sp = s0.sp ∧ sc.symtab = s0.symtab ∧
      sc.readReg64 .lr = s0.readReg64 .lr ∧ CalleeSavedPreserved s0 sc ∧
      MemmoveStatePreserved s0 sc ∧ VmPreserved s0 sc
  have h_done : ∀ sc : State,
      sc.pc = mc → sc.status = .Running →
      sc.readReg64 .x0 = dst → sc.readReg64 .x1 = src → sc.readReg64 .x2 = n →
      sc.mem = s0.mem → sc.sp = s0.sp → sc.symtab = s0.symtab →
      sc.readReg64 .lr = s0.readReg64 .lr → CalleeSavedPreserved s0 sc →
      MemmoveStatePreserved s0 sc → VmPreserved s0 sc →
      reaches_pc prog mc sc Post := by
    intro sc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    exact fun _ => ⟨sc, Steps.refl sc, Or.inl ⟨h1, h2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩
  have hr : reaches_pc prog mc s0 Post := by
    iterate 11 arm64_step
    apply h_done
    · simp [arm64_norm]
    · simp [arm64_norm, hrun]
    · simp [arm64_norm, hx0]
    · simp [arm64_norm, hx1]
    · simp [arm64_norm, hx2]
    · rfl
    · simp [arm64_norm]
    · rfl
    · simp [arm64_norm]
    · simp (config := { decide := true }) only [arm64_norm]
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  rcases hr hL with ⟨sc, hsteps_sc, ⟨_, _, hprops⟩ | ⟨_, hfalse⟩⟩
  · exact ⟨sc, hsteps_sc, hprops⟩
  · exact False.elim hfalse

end LocalStepping

private theorem memmoveLocal_pureWords_ok (entry : BitVec 64) (resolve : String → BitVec 64)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy")) :
    subroutine_ok
      (pureWordsProg entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
      entry memmoveLocalSpec := by
  have hw0 := pureWordsProg_hasWords_any entry
    (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve)
    (by rw [patched_memmove_length]; decide)
  exact memmoveLocal_fetch_ok _ entry (resolve "memcpy") (memmoveFetch_of_patchCalls hrange hw0)

private theorem memmoveLocal_process_patchCalls_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog entry
      { memmoveLocalSpec with
        post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ memmoveLocalSpec.post x s0 sf } :=
  subroutine_ok_lift_pureWords_process
    (memmoveLocal_pureWords_ok entry resolve hrange)
    (patched_memmove_noSvcMsr entry resolve hrange)
    hwords h_no_ext
    (h_ne := by intro h; have := congrArg List.length h; rw [patched_memmove_length] at this; cases this)
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `masterMemmoveVmSpec` (`memmoveSpec` +
    `MemmoveStatePreserved` + `VmPreserved`) whenever `resolve "memcpy"` satisfies
    `memcpyTailVmSpec` (`withVmPreserved masterMemcpySpec`) and `prog` has no unfreezeable
    functional extern hooks. -/
theorem memmove_masterVm_patchCalls_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy") memcpyTailVmSpec) :
    subroutine_ok prog entry masterMemmoveVmSpec := by
  have hloc := memmoveLocal_process_patchCalls_ok hrange hwords h_no_ext
  have hf := memmoveFetch_of_patchCalls hrange hwords
  obtain ⟨⟨hcA, _⟩, hf_b⟩ := hf
  apply subroutine_ok.of_codeLoaded
  intro ⟨dst, src, n, base, buf, d, o⟩ R s0 hpc hrun hpre hsp hL
  by_cases hcase : MemmoveLocalCase dst src n
  · have hpre_loc : s0.mem ⊨ memmoveLocalSpec.pre (dst, src, n, base, buf, d, o) s0 ∗ R := by
      dsimp only [memmoveLocalSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcase, hpre⟩
    refine hloc.mono_outcome (dst, src, n, base, buf, d, o) R s0 hpc hrun hpre_loc hsp
      fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [masterMemmoveVmSpec, withVmPreserved, masterMemmoveSpec, memmoveLocalSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨hpf, hpost0⟩ := hpost
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨vmPreserved_of_processFieldsPreserved hpf, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨MemmoveStatePreserved.of_processFieldsPreserved hpf, hpost0⟩
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  · have heq_f : (dst == src) = false := by
      cases h : dst == src
      · rfl
      · exact False.elim (hcase (Or.inl h))
    have hule : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = true := by
      cases h : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat)))
      · exact False.elim (hcase (Or.inr h))
      · rfl
    obtain ⟨⟨hx0, hx1, hx2, hdst, hsrc, ⟨hd_le, ho_le⟩, ⟨hbase_le, hbuf_lt⟩⟩, hmem0⟩ :=
      VerifiedLibraries.Musl.memmove_pre_extract hpre
    have hdisj : d + n.toNat ≤ o ∨ o + n.toNat ≤ d :=
      disjoint_of_sub_ule hdst hsrc hd_le ho_le hbase_le hbuf_lt hule
    obtain ⟨Frame, hsplit, hjoin⟩ :=
      pointsToBytes_split_disjoint base buf d o n.toNat hd_le ho_le hdisj
    obtain ⟨sc, hsteps_sc, hpc_c, hrun_c, hx0_c, hx1_c, hx2_c, hmem_c, hsp_c, _hsym_c,
      hlr_c, hcs_c, hmsp_c, hvm_c⟩ :=
      memmove_disjoint_step_to_tailcall prog entry (resolve "memcpy") dst src n
        hcA hf_b s0 hpc hrun hx0 hx1 hx2 heq_f hule hL
    let bs_src := (buf.drop o).take n.toNat
    have hbs_len : bs_src.length = n.toNat := by
      dsimp [bs_src]; rw [List.length_take, List.length_drop]; omega
    have hpre_mc : sc.mem ⊨
        memcpyTailVmSpec.pre (false, dst, src, bs_src) sc ∗ (Frame ∗ R) := by
      dsimp only [memcpyTailVmSpec, withVmPreserved, memcpyTailSpec, bytesAt]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_c, hx1_c, by rw [hx2_c, hbs_len]⟩, ?_⟩
      rw [hmem_c, hbs_len, hdst, hsrc]
      have h1 := Satisfies.mono (sepConj_mono_left hsplit) hmem0
      simpa [bs_src, sepConj_assoc] using h1
    refine reaches_outcome_steps hsteps_sc ?_
    refine reaches_outcome_of_reaches_pc (oom := fun _ => False) ?_
    refine reaches_pc_tailcall_subroutine hmemcpy
      (false, dst, src, bs_src) (dst, src, n, base, buf, d, o)
      hpc_c hrun_c hlr_c hsp_c hcs_c hpre_mc
      (fun sf _hpc_f _hrun_f _hsp_f _hcs_f hpost_mc => ?_) hsp
    dsimp only [memcpyTailVmSpec, withVmPreserved, memcpyTailSpec, bytesAt] at hpost_mc
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost_mc
    obtain ⟨hvm_f, ⟨hx0_f, hmsp_f⟩, hmem_f⟩ := hpost_mc
    dsimp only [masterMemmoveVmSpec, withVmPreserved, masterMemmoveSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm_c.trans hvm_f, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hmsp_c.trans hmsp_f, ?_⟩
    have hmem_rejoined : sf.mem ⊨ (base ↦ₛ ProofLib.listMove buf d o n.toNat) ∗ R := by
      rw [← moveBytes_eq_listMove, ← hjoin]
      simpa [bs_src, hdst, hsrc, sepConj_assoc] using hmem_f
    exact VerifiedLibraries.Musl.memmove_post_of_moved (src := src) (s0 := s0)
      hmem_rejoined hx0_f

/-- Patched `libc.a` `memmove` (`74` words) satisfies `masterMemmoveSpec` (`memmoveSpec` +
    `MemmoveStatePreserved`) whenever `resolve "memcpy"` satisfies `memcpyTailSpec`
    (`masterMemcpySpec`) and `prog` has no unfreezeable functional extern hooks. -/
theorem memmove_master_patchCalls_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy") memcpyTailSpec) :
    subroutine_ok prog entry masterMemmoveSpec := by
  have hloc := memmoveLocal_process_patchCalls_ok hrange hwords h_no_ext
  have hf := memmoveFetch_of_patchCalls hrange hwords
  obtain ⟨⟨hcA, _⟩, hf_b⟩ := hf
  apply subroutine_ok.of_codeLoaded
  intro ⟨dst, src, n, base, buf, d, o⟩ R s0 hpc hrun hpre hsp hL
  by_cases hcase : MemmoveLocalCase dst src n
  · have hpre_loc : s0.mem ⊨ memmoveLocalSpec.pre (dst, src, n, base, buf, d, o) s0 ∗ R := by
      dsimp only [memmoveLocalSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcase, hpre⟩
    refine hloc.mono_outcome (dst, src, n, base, buf, d, o) R s0 hpc hrun hpre_loc hsp
      fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [masterMemmoveSpec, memmoveLocalSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨MemmoveStatePreserved.of_processFieldsPreserved hpost.1, hpost.2⟩
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  · have heq_f : (dst == src) = false := by
      cases h : dst == src
      · rfl
      · exact False.elim (hcase (Or.inl h))
    have hule : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat))) = true := by
      cases h : BitVec.ule (src - n - dst) (-(n <<< (1 : Nat)))
      · exact False.elim (hcase (Or.inr h))
      · rfl
    obtain ⟨⟨hx0, hx1, hx2, hdst, hsrc, ⟨hd_le, ho_le⟩, ⟨hbase_le, hbuf_lt⟩⟩, hmem0⟩ :=
      VerifiedLibraries.Musl.memmove_pre_extract hpre
    have hdisj : d + n.toNat ≤ o ∨ o + n.toNat ≤ d :=
      disjoint_of_sub_ule hdst hsrc hd_le ho_le hbase_le hbuf_lt hule
    obtain ⟨Frame, hsplit, hjoin⟩ :=
      pointsToBytes_split_disjoint base buf d o n.toNat hd_le ho_le hdisj
    obtain ⟨sc, hsteps_sc, hpc_c, hrun_c, hx0_c, hx1_c, hx2_c, hmem_c, hsp_c, _hsym_c,
      hlr_c, hcs_c, hmsp_c, _hvm_c⟩ :=
      memmove_disjoint_step_to_tailcall prog entry (resolve "memcpy") dst src n
        hcA hf_b s0 hpc hrun hx0 hx1 hx2 heq_f hule hL
    let bs_src := (buf.drop o).take n.toNat
    have hbs_len : bs_src.length = n.toNat := by
      dsimp [bs_src]; rw [List.length_take, List.length_drop]; omega
    have hpre_mc : sc.mem ⊨
        memcpyTailSpec.pre (false, dst, src, bs_src) sc ∗ (Frame ∗ R) := by
      dsimp only [memcpyTailSpec, bytesAt]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_c, hx1_c, by rw [hx2_c, hbs_len]⟩, ?_⟩
      rw [hmem_c, hbs_len, hdst, hsrc]
      have h1 := Satisfies.mono (sepConj_mono_left hsplit) hmem0
      simpa [bs_src, sepConj_assoc] using h1
    refine reaches_outcome_steps hsteps_sc ?_
    refine reaches_outcome_of_reaches_pc (oom := fun _ => False) ?_
    refine reaches_pc_tailcall_subroutine hmemcpy
      (false, dst, src, bs_src) (dst, src, n, base, buf, d, o)
      hpc_c hrun_c hlr_c hsp_c hcs_c hpre_mc
      (fun sf _hpc_f _hrun_f _hsp_f _hcs_f hpost_mc => ?_) hsp
    dsimp only [memcpyTailSpec, bytesAt] at hpost_mc
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost_mc
    obtain ⟨⟨hx0_f, hmsp_f⟩, hmem_f⟩ := hpost_mc
    dsimp only [masterMemmoveSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hmsp_c.trans hmsp_f, ?_⟩
    have hmem_rejoined : sf.mem ⊨ (base ↦ₛ ProofLib.listMove buf d o n.toNat) ∗ R := by
      rw [← moveBytes_eq_listMove, ← hjoin]
      simpa [bs_src, hdst, hsrc, sepConj_assoc] using hmem_f
    exact VerifiedLibraries.Musl.memmove_post_of_moved (src := src) (s0 := s0)
      hmem_rejoined hx0_f

/-! ## 4. CLI & `ProofLib` Bounded Contract Bridges on Patched `memmoveLibcaWords` -/

/-- `VerifiedLibraries.Musl.memmoveSpec` directly implies `libcMemmoveBoundedSpec hookStack`. -/
theorem libcMemmoveBounded_ok_of_memmove_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry memmoveSpec) :
    subroutine_ok prog entry (libcMemmoveBoundedSpec hookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨base, buf, dst, src, len⟩ R s0 hpre
  dsimp only [libcMemmoveBoundedSpec, MemmoveArithBound, ProofLib.libcMemmoveSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hwrap, hsmall⟩, ⟨hx0, hx1, hx2, hdst, hsrc⟩, hmem⟩
  refine ⟨(base + BitVec.ofNat 64 dst, base + BitVec.ofNat 64 src, s0.readReg64 .x2,
      base, buf, dst, src), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memmoveSpec, CType.InteriorPtr, CType.SizeT, CType.scalarTy,
      CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, by omega, by omega, hwrap, hsmall, Satisfies.of_eq hmem⟩
  · dsimp only [memmoveSpec, CType.InteriorPtr] at hpost
    dsimp only [libcMemmoveBoundedSpec, ProofLib.libcMemmoveSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, hx2,
      moveBytes_eq_listMove] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

/-- `masterMemmoveSpec` implies `keepsFs (sessionMemmoveBoundedSpec hookStack)`. -/
theorem sessionMemmoveBounded_keepsFs_ok_of_master {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry masterMemmoveSpec) :
    subroutine_ok prog entry (keepsFs (sessionMemmoveBoundedSpec hookStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨base, buf, dst, src, len⟩ R s0 hpre
  dsimp only [keepsFs, sessionMemmoveBoundedSpec, MemmoveArithBound, sessionMemmoveSpec,
    ProofLib.libcMemmoveSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hwrap, hsmall⟩, ⟨hx0, hx1, hx2, hdst, hsrc⟩, hmem⟩
  refine ⟨(base + BitVec.ofNat 64 dst, base + BitVec.ofNat 64 src, s0.readReg64 .x2,
      base, buf, dst, src), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [masterMemmoveSpec, memmoveSpec, CType.InteriorPtr, CType.SizeT, CType.scalarTy,
      CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, by omega, by omega, hwrap, hsmall, Satisfies.of_eq hmem⟩
  · dsimp only [masterMemmoveSpec, memmoveSpec, CType.InteriorPtr] at hpost
    dsimp only [keepsFs, sessionMemmoveBoundedSpec, sessionMemmoveSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, hx2,
      moveBytes_eq_listMove] at hpost ⊢
    exact ⟨hpost.1.1, ⟨hpost.2.1, hpost.1.2.1⟩, Satisfies.of_eq hpost.2.2⟩

/-- `masterMemmoveSpec` implies `sessionMemmoveBoundedSpec hookStack`. -/
theorem sessionMemmoveBounded_ok_of_master {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry masterMemmoveSpec) :
    subroutine_ok prog entry (sessionMemmoveBoundedSpec hookStack) :=
  subroutine_ok_drop_keepsFs (sessionMemmoveBounded_keepsFs_ok_of_master hookStack h)

/-- `masterMemmoveVmSpec` implies `keepsFs (sessionMemmoveBoundedBudgetSpec hookStack)`. -/
theorem sessionMemmoveBoundedBudget_keepsFs_ok_of_masterVm {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry masterMemmoveVmSpec) :
    subroutine_ok prog entry (keepsFs (sessionMemmoveBoundedBudgetSpec hookStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨base, buf, dst, src, len⟩ R s0 hpre
  dsimp only [keepsFs, sessionMemmoveBoundedBudgetSpec, sessionMemmoveBudgetSpec,
    MemmoveArithBound, sessionMemmoveSpec, ProofLib.libcMemmoveSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hwrap, hsmall⟩, ⟨hx0, hx1, hx2, hdst, hsrc⟩, hmem⟩
  refine ⟨(base + BitVec.ofNat 64 dst, base + BitVec.ofNat 64 src, s0.readReg64 .x2,
      base, buf, dst, src), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [masterMemmoveVmSpec, withVmPreserved, masterMemmoveSpec, memmoveSpec,
      CType.InteriorPtr, CType.SizeT, CType.scalarTy, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, by omega, by omega, hwrap, hsmall, Satisfies.of_eq hmem⟩
  · dsimp only [masterMemmoveVmSpec, withVmPreserved, masterMemmoveSpec, memmoveSpec,
      CType.InteriorPtr] at hpost
    dsimp only [keepsFs, sessionMemmoveBoundedBudgetSpec, sessionMemmoveBudgetSpec,
      sessionMemmoveSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, hx2,
      moveBytes_eq_listMove] at hpost ⊢
    exact ⟨hpost.2.1.1, hpost.1, ⟨hpost.2.2.1, hpost.2.1.2.1⟩, Satisfies.of_eq hpost.2.2.2⟩

/-- `masterMemmoveVmSpec` implies `sessionMemmoveBoundedBudgetSpec hookStack`. -/
theorem sessionMemmoveBoundedBudget_ok_of_masterVm {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry masterMemmoveVmSpec) :
    subroutine_ok prog entry (sessionMemmoveBoundedBudgetSpec hookStack) :=
  subroutine_ok_drop_keepsFs (sessionMemmoveBoundedBudget_keepsFs_ok_of_masterVm hookStack h)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `libcMemmoveBoundedSpec hookStack`
    whenever `resolve "memcpy"` satisfies `VerifiedLibraries.Musl.memcpySpec`. -/
theorem memmove_patchCalls_bounded_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64} (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (hmemcpy : subroutine_ok prog (resolve "memcpy") memcpySpec) :
    subroutine_ok prog entry (libcMemmoveBoundedSpec hookStack) :=
  libcMemmoveBounded_ok_of_memmove_ok hookStack
    (memmove_patchCalls_ok prog entry resolve hrange hwords hmemcpy)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `sessionMemmoveBoundedSpec hookStack`
    under `memcpyTailSpec` (`masterMemcpySpec`) at `resolve "memcpy"`. -/
theorem memmove_sessionBounded_patchCalls_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64} (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy") memcpyTailSpec) :
    subroutine_ok prog entry (sessionMemmoveBoundedSpec hookStack) :=
  sessionMemmoveBounded_ok_of_master hookStack
    (memmove_master_patchCalls_ok hrange hwords h_no_ext hmemcpy)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `keepsFs (sessionMemmoveBoundedSpec hookStack)`
    under `memcpyTailSpec` (`masterMemcpySpec`) at `resolve "memcpy"`. -/
theorem memmove_sessionBounded_keepsFs_patchCalls_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64} (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy") memcpyTailSpec) :
    subroutine_ok prog entry (keepsFs (sessionMemmoveBoundedSpec hookStack)) :=
  sessionMemmoveBounded_keepsFs_ok_of_master hookStack
    (memmove_master_patchCalls_ok hrange hwords h_no_ext hmemcpy)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `sessionMemmoveBoundedBudgetSpec hookStack`
    under `memcpyTailVmSpec` (`withVmPreserved masterMemcpySpec`) at `resolve "memcpy"`. -/
theorem memmove_sessionBoundedBudget_patchCalls_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64} (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy") memcpyTailVmSpec) :
    subroutine_ok prog entry (sessionMemmoveBoundedBudgetSpec hookStack) :=
  sessionMemmoveBoundedBudget_ok_of_masterVm hookStack
    (memmove_masterVm_patchCalls_ok hrange hwords h_no_ext hmemcpy)

/-- Patched `libc.a` `memmove` (`74` words) satisfies
    `keepsFs (sessionMemmoveBoundedBudgetSpec hookStack)` under `memcpyTailVmSpec` at
    `resolve "memcpy"`. -/
theorem memmove_sessionBoundedBudget_keepsFs_patchCalls_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64} (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy") memcpyTailVmSpec) :
    subroutine_ok prog entry (keepsFs (sessionMemmoveBoundedBudgetSpec hookStack)) :=
  sessionMemmoveBoundedBudget_keepsFs_ok_of_masterVm hookStack
    (memmove_masterVm_patchCalls_ok hrange hwords h_no_ext hmemcpy)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `masterMemmoveSpec` directly from
    `subroutine_ok prog (resolve "memcpy") masterMemcpySpec` (`ro = false`). -/
theorem memmove_master_of_masterMemcpy_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy") masterMemcpySpec) :
    subroutine_ok prog entry masterMemmoveSpec :=
  memmove_master_patchCalls_ok hrange hwords h_no_ext (memcpyTail_ok_of_masterMemcpy_ok hmemcpy)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `masterMemmoveVmSpec` directly from
    `subroutine_ok prog (resolve "memcpy") (SpecBudget.withVmPreserved masterMemcpySpec)`. -/
theorem memmove_masterVm_of_masterMemcpyVm_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy")
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved masterMemcpySpec)) :
    subroutine_ok prog entry masterMemmoveVmSpec :=
  memmove_masterVm_patchCalls_ok hrange hwords h_no_ext
    (memcpyTailVm_ok_of_masterMemcpyVm_ok hmemcpy)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `sessionMemmoveBoundedSpec hookStack`
    directly from `subroutine_ok prog (resolve "memcpy") masterMemcpySpec`. -/
theorem memmove_sessionBounded_of_masterMemcpy_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64} (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy") masterMemcpySpec) :
    subroutine_ok prog entry (sessionMemmoveBoundedSpec hookStack) :=
  memmove_sessionBounded_patchCalls_ok hookStack hrange hwords h_no_ext
    (memcpyTail_ok_of_masterMemcpy_ok hmemcpy)

/-- Patched `libc.a` `memmove` (`74` words) satisfies `sessionMemmoveBoundedBudgetSpec hookStack`
    directly from `subroutine_ok prog (resolve "memcpy") (SpecBudget.withVmPreserved masterMemcpySpec)`. -/
theorem memmove_sessionBoundedBudget_of_masterMemcpyVm_ok {prog : Program} {entry : BitVec 64}
    {resolve : String → BitVec 64} (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (entry + reloc_call_off% memmoveLibcaCalls "memcpy") (resolve "memcpy"))
    (hwords : prog.hasWords entry (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords entry resolve))
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hmemcpy : subroutine_ok prog (resolve "memcpy")
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved masterMemcpySpec)) :
    subroutine_ok prog entry (sessionMemmoveBoundedBudgetSpec hookStack) :=
  memmove_sessionBoundedBudget_patchCalls_ok hookStack hrange hwords h_no_ext
    (memcpyTailVm_ok_of_masterMemcpyVm_ok hmemcpy)

/-! ## 5. Ideal `hookMemmove` (`toSat` / `HookOk`) & `HookSat` Weakening Lemmas -/

private theorem hookMemmove_processFieldsPreserved (s : State) :
    ProcessFieldsPreserved s (hookMemmove s) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun a => ?_⟩
  simp [hookMemmove, hookMemcpy, retHook, State.setPC, State.setMem]

/-- Ideal `hookMemmove` satisfies `libcMemmoveBoundedSpec hookStack`. -/
theorem hookMemmove_bounded_ok (hookStack : Nat := extHookStack) :
    HookOk hookMemmove (libcMemmoveBoundedSpec hookStack) := by
  intro ⟨base, buf, dst, src, len⟩ R s0 hrun hpre hsp
  dsimp only [libcMemmoveBoundedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ProofLib.hookMemmove_ok hookStack (base, buf, dst, src, len) R s0 hrun hpre.2 hsp

/-- Ideal `hookMemmove` satisfies `sessionMemmoveBoundedSpec hookStack`. -/
theorem hookMemmove_sessionBounded_ok (hookStack : Nat := extHookStack) :
    HookOk hookMemmove (sessionMemmoveBoundedSpec hookStack) := by
  intro ⟨base, buf, dst, src, len⟩ R s0 hrun hpre hsp
  dsimp only [sessionMemmoveBoundedSpec, sessionMemmoveSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hok := ProofLib.hookMemmove_ok hookStack (base, buf, dst, src, len) R s0 hrun hpre.2 hsp
  rcases hok with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [ProofLib.libcMemmoveSpec] at hpost
    dsimp only [sessionMemmoveBoundedSpec, sessionMemmoveSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1, (hookMemmove_processFieldsPreserved s0).2.1⟩, hpost.2⟩
  · right; exact hrest

/-- Ideal `hookMemmove` satisfies `sessionMemmoveBoundedBudgetSpec hookStack` (`toSat` witness). -/
theorem hookMemmove_sessionBoundedBudget_ok (hookStack : Nat := extHookStack) :
    HookOk hookMemmove (sessionMemmoveBoundedBudgetSpec hookStack) := by
  intro x R s0 hrun hpre hsp
  dsimp only [sessionMemmoveBoundedBudgetSpec, sessionMemmoveBudgetSpec] at hpre
  have hok := hookMemmove_sessionBounded_ok hookStack x R s0 hrun hpre hsp
  rcases hok with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemmoveBoundedBudgetSpec, sessionMemmoveBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨vmPreserved_of_processFieldsPreserved (hookMemmove_processFieldsPreserved s0), hpost⟩
  · right; exact hrest

/-- Any exact `hooks name = some hookMemmove` entry satisfies
    `HookSat hooks name (sessionMemmoveBoundedBudgetSpec hookStack)` (`toSat`). -/
theorem hookSat_sessionMemmoveBoundedBudget_of_exact
    {hooks : String → Option (State → State)} {name : String}
    (hookStack : Nat := extHookStack)
    (h : hooks name = some hookMemmove) :
    HookSat hooks name (sessionMemmoveBoundedBudgetSpec hookStack) :=
  ⟨hookMemmove, h, hookMemmove_sessionBoundedBudget_ok hookStack⟩

/-- Weaken `HookSat hooks name (ProofLib.libcMemmoveSpec hookStack)` to
    `HookSat hooks name (libcMemmoveBoundedSpec hookStack)`. -/
theorem hookSat_libcMemmoveBounded_of_unbounded
    {hooks : String → Option (State → State)} {name : String}
    (hookStack : Nat := extHookStack)
    (h : HookSat hooks name (ProofLib.libcMemmoveSpec hookStack)) :
    HookSat hooks name (libcMemmoveBoundedSpec hookStack) := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  dsimp only [libcMemmoveBoundedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hsat x R s0 hrun hpre.2 hsp

/-- Weaken `HookSat hooks name (sessionMemmoveSpec hookStack)` to
    `HookSat hooks name (sessionMemmoveBoundedSpec hookStack)`. -/
theorem hookSat_sessionMemmoveBounded_of_unbounded
    {hooks : String → Option (State → State)} {name : String}
    (hookStack : Nat := extHookStack)
    (h : HookSat hooks name (sessionMemmoveSpec hookStack)) :
    HookSat hooks name (sessionMemmoveBoundedSpec hookStack) := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  dsimp only [sessionMemmoveBoundedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hsat x R s0 hrun hpre.2 hsp

/-- Weaken `HookSat hooks name (sessionMemmoveBudgetSpec hookStack)` to
    `HookSat hooks name (sessionMemmoveBoundedBudgetSpec hookStack)`. -/
theorem hookSat_sessionMemmoveBoundedBudget_of_unbounded
    {hooks : String → Option (State → State)} {name : String}
    (hookStack : Nat := extHookStack)
    (h : HookSat hooks name (sessionMemmoveBudgetSpec hookStack)) :
    HookSat hooks name (sessionMemmoveBoundedBudgetSpec hookStack) := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  dsimp only [sessionMemmoveBoundedBudgetSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hsat x R s0 hrun hpre.2 hsp

end LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
