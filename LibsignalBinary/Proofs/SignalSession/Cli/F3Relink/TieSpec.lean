/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.ProgramReflection
public import ProofLib.Process.FastParse
public import ProofLib.Placed.Multi
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.RustStd.Proofs.MallocngBridge
public import LibsignalBinary.Heap.Fine.AllocZeroedHelpersFine

/-!
# Re-Linked ELF Kernel-Tie and Branch-Stub Validators

Layout-parametric validators and soundness theorems for the re-linked CLI ELF: linear-time
`.img.text` byte comparison modulo `--branch-stubs` words (`f3BytesEq8`, `f3CheckTextWordsFrom`),
structural `WordTree` verification of `ProgContainsMultiLib` (`progContainsMultiLib_of_wordTree`),
co-located `rdl_shim.S` validation (`F3Seg5ShimBundle`), and 1-instruction `Instr.b` branch-stub
execution lifting (`steps_of_loaded_b_stub`).
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec

open Arm64
open Arm64.Obj (CodeBlock HoldsBytes MultiPlacedLib MultiPlacement subroutine_ok_toPureMem_outcome)
open Arm64.Process (ElfImage ProcessInputs fastDrop fastDrop_eq_drop)
open ProofLib
open ProofLib.ProgramReflection (WordTree)
open ProofLib.StdStartup (hasInstrs hasInstrs_of_wordTree)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMultiLib ProgContainsMallocng)
open VerifiedLibraries.RustStd (
  MallocngCEntryAddrs RustStdRdlShimCode
  checkShimInstrsAt checkRustStdRdlShimCode rustStdRdlShimCode_of_wordTree
)
open LibsignalBinary.Heap (RustAllocAddrs)
open LibsignalBinary.Heap.Fine (
  rdlAllocZeroedInstrs checkRdlAllocZeroedCode rdlAllocZeroedCode_of_wordTree
)

/-! ## Byte Comparison and `--branch-stubs` Tail Validator -/

/-- Byte equality via `Nat.beq`. -/
def f3ByteBeq (a b : BitVec 8) : Bool :=
  Nat.beq a.toNat b.toNat

theorem f3ByteBeq_true_iff (a b : BitVec 8) : f3ByteBeq a b = true ↔ a = b := by
  unfold f3ByteBeq
  rw [Nat.beq_eq]
  exact ⟨BitVec.eq_of_toNat_eq, congrArg BitVec.toNat⟩

def f3BytesEq1 : Nat → List (BitVec 8) → List (BitVec 8) → Bool
  | 0, _, _ => true
  | n + 1, a :: xs, b :: ys => Bool.and (f3ByteBeq a b) (f3BytesEq1 n xs ys)
  | _ + 1, _, _ => false

theorem f3BytesEq1_getElem_eq :
    ∀ (n : Nat) (xs ys : List (BitVec 8)),
      f3BytesEq1 n xs ys = true →
      ∀ (k : Nat), k < n → xs[k]? = ys[k]? ∧ k < xs.length ∧ k < ys.length
  | 0, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ + 1, [], _, h, _, _ => by simp [f3BytesEq1] at h
  | _ + 1, _ :: _, [], h, _, _ => by simp [f3BytesEq1] at h
  | n + 1, a :: xs, b :: ys, h, 0, _ => by
    simp only [f3BytesEq1, Bool.and_eq_true, f3ByteBeq_true_iff] at h
    simp [h.1]
  | n + 1, a :: xs, b :: ys, h, k + 1, hk => by
    simp only [f3BytesEq1, Bool.and_eq_true] at h
    have ih := f3BytesEq1_getElem_eq n xs ys h.2 k (Nat.lt_of_succ_lt_succ hk)
    refine ⟨?_, Nat.succ_lt_succ ih.2.1, Nat.succ_lt_succ ih.2.2⟩
    simpa using ih.1

def f3StepByteEq (xs ys : List (BitVec 8))
    (k : List (BitVec 8) → List (BitVec 8) → Bool) : Bool :=
  List.casesOn xs false fun a xs' =>
  List.casesOn ys false fun b ys' =>
  Bool.casesOn (f3ByteBeq a b) false (k xs' ys')

theorem f3StepByteEq_eq (n : Nat) (k : List (BitVec 8) → List (BitVec 8) → Bool)
    (hk : ∀ xs' ys', k xs' ys' = f3BytesEq1 n xs' ys') (xs ys : List (BitVec 8)) :
    f3StepByteEq xs ys k = f3BytesEq1 (n + 1) xs ys := by
  cases xs with
  | nil => cases ys <;> rfl
  | cons a xs' =>
    cases ys with
    | nil => rfl
    | cons b ys' =>
      simp only [f3StepByteEq, f3BytesEq1]
      rw [hk xs' ys']
      cases f3ByteBeq a b <;> rfl

/-- Tail-recursive 8-byte block comparison for linear-time kernel reduction. -/
def f3BytesEq8 : Nat → List (BitVec 8) → List (BitVec 8) → Bool
  | 0, _, _ => true
  | q + 1, xs, ys =>
    f3StepByteEq xs ys fun xs1 ys1 =>
    f3StepByteEq xs1 ys1 fun xs2 ys2 =>
    f3StepByteEq xs2 ys2 fun xs3 ys3 =>
    f3StepByteEq xs3 ys3 fun xs4 ys4 =>
    f3StepByteEq xs4 ys4 fun xs5 ys5 =>
    f3StepByteEq xs5 ys5 fun xs6 ys6 =>
    f3StepByteEq xs6 ys6 fun xs7 ys7 =>
    f3StepByteEq xs7 ys7 fun xs8 ys8 =>
    f3BytesEq8 q xs8 ys8

theorem f3BytesEq8_eq_f3BytesEq1 :
    ∀ (q : Nat) (xs ys : List (BitVec 8)),
      f3BytesEq8 q xs ys = f3BytesEq1 (q * 8) xs ys
  | 0, _, _ => rfl
  | q + 1, xs, ys => by
    have h1 := f3StepByteEq_eq (q * 8) (f3BytesEq8 q) (f3BytesEq8_eq_f3BytesEq1 q)
    have h2 := f3StepByteEq_eq (q * 8 + 1) _ h1
    have h3 := f3StepByteEq_eq (q * 8 + 2) _ h2
    have h4 := f3StepByteEq_eq (q * 8 + 3) _ h3
    have h5 := f3StepByteEq_eq (q * 8 + 4) _ h4
    have h6 := f3StepByteEq_eq (q * 8 + 5) _ h5
    have h7 := f3StepByteEq_eq (q * 8 + 6) _ h6
    have h8 := f3StepByteEq_eq (q * 8 + 7) _ h7 xs ys
    have hmul : q * 8 + 7 + 1 = (q + 1) * 8 := by omega
    rw [hmul] at h8
    simpa only [f3BytesEq8] using h8

/-- Whether byte offset `k` from `textBase` falls inside a 4-byte stub word of `stubSpec`. -/
def isF3BranchStubByteOff (stubSpec : List (Nat × BitVec 64)) (k : Nat) : Bool :=
  stubSpec.any fun (off, _) => Nat.ble off k && !Nat.ble (off + 4) k

/-- Expected branch-stub target at word-aligned byte offset `off` from `textBase`, if any. -/
def f3BranchStubTarget? (stubSpec : List (Nat × BitVec 64)) (off : Nat) : Option (BitVec 64) :=
  (stubSpec.find? fun (o, _) => o == off).map Prod.snd

/-- Check that every `(off, tgt) ∈ stubSpec` is 4-byte aligned, lies in the `[headOff, headOff + 4 * tailWords)`
    tail window without 64-bit wraparound from `textBase`, and is uniquely returned by `f3BranchStubTarget?`. -/
def f3StubSpecValid (stubSpec : List (Nat × BitVec 64)) (textBase : BitVec 64)
    (headOff tailWords : Nat) : Bool :=
  (headOff % 4 == 0) &&
  stubSpec.all fun (off, tgt) =>
    (off % 4 == 0) &&
    Nat.ble headOff off &&
    !Nat.ble (headOff + 4 * tailWords) off &&
    Nat.ble (textBase.toNat + off + 4) 18446744073709551616 &&
    (f3BranchStubTarget? stubSpec off == some tgt)

/-- Check `rem` 4-byte words starting at byte offset `off`:
    - if `f3BranchStubTarget? stubSpec off = some tgt`, `xs`'s 4 bytes decode via `Arm64.decode` to
      `Instr.b (tgt - (textBase + BitVec.ofNat 64 off))` and `ys`'s 4 bytes are `0, 0, 0, 0`;
    - otherwise `xs`'s 4 bytes equal `ys`'s 4 bytes. -/
def f3CheckTextWordsFrom (stubSpec : List (Nat × BitVec 64)) (textBase : BitVec 64) :
    Nat → Nat → List (BitVec 8) → List (BitVec 8) → Bool
  | _, 0, _, _ => true
  | off, rem + 1, x0 :: x1 :: x2 :: x3 :: xs, y0 :: y1 :: y2 :: y3 :: ys =>
    let okWord :=
      match f3BranchStubTarget? stubSpec off with
      | some tgt =>
        let w : BitVec 32 := x3 ++ x2 ++ x1 ++ x0
        let pc : BitVec 64 := textBase + BitVec.ofNat 64 off
        (Arm64.decode w == some (.b (tgt - pc))) &&
        f3ByteBeq y0 0#8 && f3ByteBeq y1 0#8 && f3ByteBeq y2 0#8 && f3ByteBeq y3 0#8
      | none =>
        f3ByteBeq x0 y0 && f3ByteBeq x1 y1 && f3ByteBeq x2 y2 && f3ByteBeq x3 y3
    Bool.casesOn okWord false (f3CheckTextWordsFrom stubSpec textBase (off + 4) rem xs ys)
  | _, _ + 1, _, _ => false

theorem f3CheckTextWordsFrom_nonStub_byte {stubSpec : List (Nat × BitVec 64)} {textBase : BitVec 64} :
    ∀ (off rem : Nat) (xs ys : List (BitVec 8)),
      f3CheckTextWordsFrom stubSpec textBase off rem xs ys = true →
      ∀ (j : Nat), j < 4 * rem →
        f3BranchStubTarget? stubSpec (off + 4 * (j / 4)) = none →
        xs[j]? = ys[j]? ∧ j < xs.length ∧ j < ys.length
  | _, 0, _, _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | off, rem + 1, [], _, h, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, [_], _, h, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, [_, _], _, h, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, [_, _, _], _, h, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, _ :: _ :: _ :: _ :: _, [], h, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, _ :: _ :: _ :: _ :: _, [_], h, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, _ :: _ :: _ :: _ :: _, [_, _], h, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, _ :: _ :: _ :: _ :: _, [_, _, _], h, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, x0 :: x1 :: x2 :: x3 :: xs, y0 :: y1 :: y2 :: y3 :: ys, h, j, hj, hns => by
    unfold f3CheckTextWordsFrom at h
    dsimp only at h
    by_cases hj4 : j < 4
    · have hdiv : j / 4 = 0 := Nat.div_eq_of_lt hj4
      rw [hdiv, Nat.mul_zero, Nat.add_zero] at hns
      rw [hns] at h
      dsimp only at h
      cases hok : (f3ByteBeq x0 y0 && f3ByteBeq x1 y1 && f3ByteBeq x2 y2 && f3ByteBeq x3 y3) with
      | false => rw [hok] at h; simp at h
      | true =>
        simp only [Bool.and_eq_true, f3ByteBeq_true_iff] at hok
        rcases hok with ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩
        subst e0; subst e1; subst e2; subst e3
        have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;> simp
    · cases hok :
          (match f3BranchStubTarget? stubSpec off with
           | some tgt =>
             (Arm64.decode (x3 ++ x2 ++ x1 ++ x0) == some (Instr.b (tgt - (textBase + BitVec.ofNat 64 off)))) &&
             f3ByteBeq y0 0#8 && f3ByteBeq y1 0#8 && f3ByteBeq y2 0#8 && f3ByteBeq y3 0#8
           | none =>
             f3ByteBeq x0 y0 && f3ByteBeq x1 y1 && f3ByteBeq x2 y2 && f3ByteBeq x3 y3) with
      | false => rw [hok] at h; simp at h
      | true =>
        rw [hok] at h
        dsimp only at h
        have hdiv : j / 4 = (j - 4) / 4 + 1 := by omega
        have hoff_eq : off + 4 * (j / 4) = (off + 4) + 4 * ((j - 4) / 4) := by omega
        rw [hoff_eq] at hns
        have ih := f3CheckTextWordsFrom_nonStub_byte (off + 4) rem xs ys h (j - 4) (by omega) hns
        have hj_eq : j = (j - 4) + 4 := by omega
        rw [hj_eq]
        refine ⟨?_, by simp; omega, by simp; omega⟩
        simpa using ih.1

theorem f3CheckTextWordsFrom_stub_word {stubSpec : List (Nat × BitVec 64)} {textBase : BitVec 64} :
    ∀ (off rem : Nat) (xs ys : List (BitVec 8)),
      f3CheckTextWordsFrom stubSpec textBase off rem xs ys = true →
      ∀ (wIdx : Nat) (tgt : BitVec 64), wIdx < rem →
        f3BranchStubTarget? stubSpec (off + 4 * wIdx) = some tgt →
        ∃ b0 b1 b2 b3,
          xs.drop (4 * wIdx) = b0 :: b1 :: b2 :: b3 :: xs.drop (4 * (wIdx + 1)) ∧
          ys.drop (4 * wIdx) = 0#8 :: 0#8 :: 0#8 :: 0#8 :: ys.drop (4 * (wIdx + 1)) ∧
          Arm64.decode (b3 ++ b2 ++ b1 ++ b0) =
            some (.b (tgt - (textBase + BitVec.ofNat 64 (off + 4 * wIdx))))
  | _, 0, _, _, _, _, _, hw, _ => absurd hw (Nat.not_lt_zero _)
  | off, rem + 1, [], _, h, _, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, [_], _, h, _, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, [_, _], _, h, _, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, [_, _, _], _, h, _, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, _ :: _ :: _ :: _ :: _, [], h, _, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, _ :: _ :: _ :: _ :: _, [_], h, _, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, _ :: _ :: _ :: _ :: _, [_, _], h, _, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, _ :: _ :: _ :: _ :: _, [_, _, _], h, _, _, _, _ => by simp [f3CheckTextWordsFrom] at h
  | off, rem + 1, x0 :: x1 :: x2 :: x3 :: xs, y0 :: y1 :: y2 :: y3 :: ys, h, 0, tgt, _, hst => by
    unfold f3CheckTextWordsFrom at h
    rw [Nat.mul_zero, Nat.add_zero] at hst
    dsimp only at h
    rw [hst] at h
    dsimp only at h
    cases hok :
        ((Arm64.decode (x3 ++ x2 ++ x1 ++ x0) == some (Instr.b (tgt - (textBase + BitVec.ofNat 64 off)))) &&
         f3ByteBeq y0 0#8 && f3ByteBeq y1 0#8 && f3ByteBeq y2 0#8 && f3ByteBeq y3 0#8) with
    | false => rw [hok] at h; simp at h
    | true =>
      simp only [Bool.and_eq_true, beq_iff_eq, f3ByteBeq_true_iff] at hok
      rcases hok with ⟨⟨⟨⟨hdec, hy0⟩, hy1⟩, hy2⟩, hy3⟩
      subst hy0; subst hy1; subst hy2; subst hy3
      refine ⟨x0, x1, x2, x3, rfl, rfl, ?_⟩
      simpa using hdec
  | off, rem + 1, x0 :: x1 :: x2 :: x3 :: xs, y0 :: y1 :: y2 :: y3 :: ys, h, wIdx + 1, tgt, hw, hst => by
    unfold f3CheckTextWordsFrom at h
    dsimp only at h
    cases hok :
        (match f3BranchStubTarget? stubSpec off with
         | some tgt' =>
           (Arm64.decode (x3 ++ x2 ++ x1 ++ x0) == some (Instr.b (tgt' - (textBase + BitVec.ofNat 64 off)))) &&
           f3ByteBeq y0 0#8 && f3ByteBeq y1 0#8 && f3ByteBeq y2 0#8 && f3ByteBeq y3 0#8
         | none =>
           f3ByteBeq x0 y0 && f3ByteBeq x1 y1 && f3ByteBeq x2 y2 && f3ByteBeq x3 y3) with
    | false => rw [hok] at h; simp at h
    | true =>
      rw [hok] at h
      dsimp only at h
      have hoff_eq : off + 4 * (wIdx + 1) = (off + 4) + 4 * wIdx := by omega
      rw [hoff_eq] at hst
      obtain ⟨b0, b1, b2, b3, hxs, hys, hdec⟩ :=
        f3CheckTextWordsFrom_stub_word (off + 4) rem xs ys h wIdx tgt (Nat.lt_of_succ_lt_succ hw) hst
      refine ⟨b0, b1, b2, b3, ?_, ?_, ?_⟩
      · simpa [Nat.mul_add] using hxs
      · simpa [Nat.mul_add] using hys
      · rwa [hoff_eq]

theorem f3BranchStubTarget?_none_of_not_isF3BranchStubByteOff :
    ∀ (stubSpec : List (Nat × BitVec 64)) {k : Nat},
      (stubSpec.all fun (o, _) => o % 4 == 0) = true →
      isF3BranchStubByteOff stubSpec k = false →
      f3BranchStubTarget? stubSpec (4 * (k / 4)) = none
  | [], _, _, _ => rfl
  | (o, tgt) :: rest, k, hall, hnot => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
    simp only [isF3BranchStubByteOff, List.any_cons, Bool.or_eq_false_iff] at hnot
    have hnot_in : ¬ (o ≤ k ∧ k < o + 4) := by
      rintro ⟨hlo, hhi⟩
      have h1 : Nat.ble o k = true := Nat.ble_eq.mpr hlo
      have h2 : Nat.ble (o + 4) k = false := by
        cases hb : Nat.ble (o + 4) k with
        | false => rfl
        | true => have := Nat.le_of_ble_eq_true hb; omega
      rw [h1, h2] at hnot
      simp at hnot
    have ho4 := hall.1
    have hne : (o == 4 * (k / 4)) = false := beq_eq_false_iff_ne.mpr (by omega)
    unfold f3BranchStubTarget?
    simp only [List.find?_cons, hne]
    exact f3BranchStubTarget?_none_of_not_isF3BranchStubByteOff rest hall.2 hnot.2

/-- Parametric non-stub byte-equality theorem for `.img.text` (`headBlocks * 8 + 4 * tailWords` B). -/
theorem f3TextNonStubBytes_eq {stubSpec : List (Nat × BitVec 64)} {textBase : BitVec 64}
    {headBlocks tailWords : Nat} {segBytes refCode : List (BitVec 8)}
    (hStubAl : (stubSpec.all fun (o, _) => o % 4 == 0) = true)
    (hlenRef : refCode.length = headBlocks * 8 + 4 * tailWords)
    (hHead : f3BytesEq8 headBlocks segBytes refCode = true)
    (hTail : f3CheckTextWordsFrom stubSpec textBase (headBlocks * 8) tailWords
      (fastDrop (headBlocks * 8) segBytes) (fastDrop (headBlocks * 8) refCode) = true) :
    ∀ (k : Nat) (hk : k < headBlocks * 8 + 4 * tailWords),
      isF3BranchStubByteOff stubSpec k = false →
      ∃ (hkSeg : k < segBytes.length),
        segBytes[k]'hkSeg = refCode[k]'(by omega) := by
  intro k hk hns
  by_cases hkHead : k < headBlocks * 8
  · have hEq1 : f3BytesEq1 (headBlocks * 8) segBytes refCode = true :=
      (f3BytesEq8_eq_f3BytesEq1 headBlocks segBytes refCode).symm.trans hHead
    have ⟨hget, hkSeg, hkRef⟩ := f3BytesEq1_getElem_eq (headBlocks * 8) segBytes refCode hEq1 k hkHead
    refine ⟨hkSeg, ?_⟩
    rw [List.getElem?_eq_getElem hkSeg, List.getElem?_eq_getElem hkRef] at hget
    exact Option.some.inj hget
  · rw [fastDrop_eq_drop, fastDrop_eq_drop] at hTail
    have hj : k - headBlocks * 8 < 4 * tailWords := by omega
    have hnsOff : f3BranchStubTarget? stubSpec (headBlocks * 8 + 4 * ((k - headBlocks * 8) / 4)) = none := by
      have hmul : headBlocks * 8 + 4 * ((k - headBlocks * 8) / 4) = 4 * (k / 4) := by omega
      rw [hmul]
      exact f3BranchStubTarget?_none_of_not_isF3BranchStubByteOff stubSpec hStubAl hns
    have ⟨hget, hkSegDrop, _⟩ :=
      f3CheckTextWordsFrom_nonStub_byte (headBlocks * 8) tailWords
        (segBytes.drop (headBlocks * 8)) (refCode.drop (headBlocks * 8)) hTail (k - headBlocks * 8) hj hnsOff
    have hkSeg : k < segBytes.length := by simp at hkSegDrop; omega
    have hkRef : k < refCode.length := by omega
    refine ⟨hkSeg, ?_⟩
    have h1 : (segBytes.drop (headBlocks * 8))[k - headBlocks * 8]? = some (segBytes[k]'hkSeg) := by
      rw [List.getElem?_drop, show headBlocks * 8 + (k - headBlocks * 8) = k by omega,
          List.getElem?_eq_getElem hkSeg]
    have h2 : (refCode.drop (headBlocks * 8))[k - headBlocks * 8]? = some (refCode[k]'hkRef) := by
      rw [List.getElem?_drop, show headBlocks * 8 + (k - headBlocks * 8) = k by omega,
          List.getElem?_eq_getElem hkRef]
    rw [h1, h2] at hget
    exact Option.some.inj hget

/-- Loaded-memory corollary: every non-branch-stub byte `k < headBlocks * 8 + 4 * tailWords` in any
    loaded state `s0` of `elf` has `Perm.rx` and reads `refCode[k]`, while every `(off, tgt) ∈ stubSpec`
    has `s0.mem.canExec (textBase + off) 4 = true` and decodes to `Instr.b (tgt - (textBase + off))`. -/
theorem f3LoadedText_matches_mod_branchStubs
    {stubSpec : List (Nat × BitVec 64)} {textBase : BitVec 64} {headBlocks tailWords : Nat}
    {elf : ElfImage} {refCode : List (BitVec 8)} {hseg1 : 1 < elf.segments.length}
    (hValid : f3StubSpecValid stubSpec textBase (headBlocks * 8) tailWords = true)
    (hbrk : ∀ {inputs : ProcessInputs} {s0 : State},
      elf.loadState inputs = .ok s0 →
      HoldsBytes s0.mem textBase (elf.segments[1]'hseg1).bytes (fun _ => Perm.rx))
    (hlenRef : refCode.length = headBlocks * 8 + 4 * tailWords)
    (hHead : f3BytesEq8 headBlocks (elf.segments[1]'hseg1).bytes refCode = true)
    (hTail : f3CheckTextWordsFrom stubSpec textBase (headBlocks * 8) tailWords
      (fastDrop (headBlocks * 8) (elf.segments[1]'hseg1).bytes)
      (fastDrop (headBlocks * 8) refCode) = true)
    {inputs : ProcessInputs} {s0 : State} (hs0 : elf.loadState inputs = .ok s0) :
    (∀ (k : Nat) (hk : k < headBlocks * 8 + 4 * tailWords),
      isF3BranchStubByteOff stubSpec k = false →
      s0.mem.perm (textBase + BitVec.ofNat 64 k) = some Perm.rx ∧
      s0.mem.read8 (textBase + BitVec.ofNat 64 k) = refCode[k]'(by omega)) ∧
    (∀ off tgt, (off, tgt) ∈ stubSpec →
      s0.mem.canExec (textBase + BitVec.ofNat 64 off) 4 = true ∧
      Arm64.decode (s0.mem.read32 (textBase + BitVec.ofNat 64 off)) =
        some (.b (tgt - (textBase + BitVec.ofNat 64 off)))) := by
  have hhb := hbrk hs0
  unfold f3StubSpecValid at hValid
  simp only [Bool.and_eq_true, beq_iff_eq] at hValid
  have hStubAl : (stubSpec.all fun (o, _) => o % 4 == 0) = true := by
    rw [List.all_eq_true]
    intro ⟨o, t⟩ hm
    have hv := List.all_eq_true.mp hValid.2 (o, t) hm
    simp only [Bool.and_eq_true] at hv
    exact hv.1.1.1.1
  refine ⟨fun k hk hns => ?_, fun off tgt hmem => ?_⟩
  · obtain ⟨hkSeg, heq⟩ := f3TextNonStubBytes_eq hStubAl hlenRef hHead hTail k hk hns
    have ⟨hrd, hpm, _⟩ := hhb k hkSeg
    exact ⟨hpm, hrd.trans heq⟩
  · rw [fastDrop_eq_drop, fastDrop_eq_drop] at hTail
    have hv := List.all_eq_true.mp hValid.2 (off, tgt) hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    rcases hv with ⟨⟨⟨⟨hoff4, hge_b⟩, hlt_b⟩, hnw_b⟩, hfind⟩
    have hge : headBlocks * 8 ≤ off := Nat.le_of_ble_eq_true hge_b
    have hlt : off < headBlocks * 8 + 4 * tailWords := by
      cases hb : Nat.ble (headBlocks * 8 + 4 * tailWords) off with
      | false =>
        exact Classical.byContradiction fun h => by
          have hle : headBlocks * 8 + 4 * tailWords ≤ off := by omega
          rw [Nat.ble_eq.mpr hle] at hb; cases hb
      | true => rw [hb] at hlt_b; simp at hlt_b
    have hnw : textBase.toNat + off + 4 ≤ 2 ^ 64 := Nat.le_of_ble_eq_true hnw_b
    let wIdx : Nat := (off - headBlocks * 8) / 4
    have hoff_eq : off = headBlocks * 8 + 4 * wIdx := by omega
    have hw : wIdx < tailWords := by omega
    rw [hoff_eq] at hfind
    obtain ⟨b0, b1, b2, b3, hxs, _, hdec⟩ :=
      f3CheckTextWordsFrom_stub_word (headBlocks * 8) tailWords
        ((elf.segments[1]'hseg1).bytes.drop (headBlocks * 8)) (refCode.drop (headBlocks * 8))
        hTail wIdx tgt hw hfind
    rw [List.drop_drop] at hxs
    have hdrop_len : 4 ≤ ((elf.segments[1]'hseg1).bytes.drop (headBlocks * 8 + 4 * wIdx)).length := by
      rw [hxs]; simp
    simp only [List.length_drop] at hdrop_len
    have hoff0 : off < (elf.segments[1]'hseg1).bytes.length := by omega
    have hoff1 : off + 1 < (elf.segments[1]'hseg1).bytes.length := by omega
    have hoff2 : off + 2 < (elf.segments[1]'hseg1).bytes.length := by omega
    have hoff3 : off + 3 < (elf.segments[1]'hseg1).bytes.length := by omega
    have hb0 : (elf.segments[1]'hseg1).bytes[off]'hoff0 = b0 := by
      have hget : ((elf.segments[1]'hseg1).bytes.drop (headBlocks * 8 + 4 * wIdx))[0]? = some b0 := by
        rw [hxs]; rfl
      rw [List.getElem?_drop, Nat.add_zero, ← hoff_eq, List.getElem?_eq_getElem hoff0] at hget
      exact Option.some.inj hget
    have hb1 : (elf.segments[1]'hseg1).bytes[off + 1]'hoff1 = b1 := by
      have hget : ((elf.segments[1]'hseg1).bytes.drop (headBlocks * 8 + 4 * wIdx))[1]? = some b1 := by
        rw [hxs]; rfl
      rw [List.getElem?_drop, ← hoff_eq, List.getElem?_eq_getElem hoff1] at hget
      exact Option.some.inj hget
    have hb2 : (elf.segments[1]'hseg1).bytes[off + 2]'hoff2 = b2 := by
      have hget : ((elf.segments[1]'hseg1).bytes.drop (headBlocks * 8 + 4 * wIdx))[2]? = some b2 := by
        rw [hxs]; rfl
      rw [List.getElem?_drop, ← hoff_eq, List.getElem?_eq_getElem hoff2] at hget
      exact Option.some.inj hget
    have hb3 : (elf.segments[1]'hseg1).bytes[off + 3]'hoff3 = b3 := by
      have hget : ((elf.segments[1]'hseg1).bytes.drop (headBlocks * 8 + 4 * wIdx))[3]? = some b3 := by
        rw [hxs]; rfl
      rw [List.getElem?_drop, ← hoff_eq, List.getElem?_eq_getElem hoff3] at hget
      exact Option.some.inj hget
    have hadd1 : textBase + BitVec.ofNat 64 off + 1#64 = textBase + BitVec.ofNat 64 (off + 1) := by bv_omega
    have hadd2 : textBase + BitVec.ofNat 64 off + 2#64 = textBase + BitVec.ofNat 64 (off + 2) := by bv_omega
    have hadd3 : textBase + BitVec.ofNat 64 off + 3#64 = textBase + BitVec.ofNat 64 (off + 3) := by bv_omega
    have r0 : s0.mem.read8 (textBase + BitVec.ofNat 64 off) = b0 := (hhb off hoff0).1.trans hb0
    have r1 : s0.mem.read8 (textBase + BitVec.ofNat 64 off + 1#64) = b1 := by
      rw [hadd1]; exact (hhb (off + 1) hoff1).1.trans hb1
    have r2 : s0.mem.read8 (textBase + BitVec.ofNat 64 off + 2#64) = b2 := by
      rw [hadd2]; exact (hhb (off + 2) hoff2).1.trans hb2
    have r3 : s0.mem.read8 (textBase + BitVec.ofNat 64 off + 3#64) = b3 := by
      rw [hadd3]; exact (hhb (off + 3) hoff3).1.trans hb3
    have p0 : s0.mem.perm (textBase + BitVec.ofNat 64 off) = some Perm.rx := (hhb off hoff0).2.1
    have p1 : s0.mem.perm (textBase + BitVec.ofNat 64 off + 1#64) = some Perm.rx := by
      rw [hadd1]; exact (hhb (off + 1) hoff1).2.1
    have p2 : s0.mem.perm (textBase + BitVec.ofNat 64 off + 2#64) = some Perm.rx := by
      rw [hadd2]; exact (hhb (off + 2) hoff2).2.1
    have p3 : s0.mem.perm (textBase + BitVec.ofNat 64 off + 3#64) = some Perm.rx := by
      rw [hadd3]; exact (hhb (off + 3) hoff3).2.1
    refine ⟨?_, ?_⟩
    · have ha2 : textBase + BitVec.ofNat 64 off + 1#64 + 1#64 =
          textBase + BitVec.ofNat 64 off + 2#64 := by bv_omega
      have ha3 : textBase + BitVec.ofNat 64 off + 2#64 + 1#64 =
          textBase + BitVec.ofNat 64 off + 3#64 := by bv_omega
      simp only [Memory.canExec, Memory.allPerm]
      rw [ha2, ha3, p0, p1, p2, p3]
      rfl
    · unfold Memory.read32
      dsimp only
      rw [BitVec.add_zero, r0, r1, r2, r3, hoff_eq]
      exact hdec

/-! ## Structural `WordTree` Validator for `ProgContainsMultiLib` -/

/-- Structural 4-byte quad verifier against `t : WordTree`. -/
def checkQuadBytesFrom (t : WordTree) : Nat → List (BitVec 8) → Bool
  | _, [] => true
  | qIdx, b0 :: b1 :: b2 :: b3 :: rest =>
    match t.getQuad? qIdx with
    | some (t0, t1, t2, t3) =>
      f3ByteBeq t0 b0 && f3ByteBeq t1 b1 && f3ByteBeq t2 b2 && f3ByteBeq t3 b3 &&
      checkQuadBytesFrom t (qIdx + 1) rest
    | none => false
  | _, _ => false

theorem checkQuadBytesFrom_byte_eq {t : WordTree} {n : Nat} (hwf : t.checkSize? = some n) :
    ∀ (qIdx : Nat) (bs : List (BitVec 8)),
      checkQuadBytesFrom t qIdx bs = true →
      ∀ (k : Nat) (hk : k < bs.length),
        ∃ (hidx : 4 * qIdx + k < t.toBytes.length),
          t.toBytes[4 * qIdx + k]'hidx = bs[k]'hk
  | _, [], _, _, hk => nomatch hk
  | _, [_], h, _, _ => by simp [checkQuadBytesFrom] at h
  | _, [_, _], h, _, _ => by simp [checkQuadBytesFrom] at h
  | _, [_, _, _], h, _, _ => by simp [checkQuadBytesFrom] at h
  | qIdx, b0 :: b1 :: b2 :: b3 :: rest, h, k, hk => by
    unfold checkQuadBytesFrom at h
    cases hget : t.getQuad? qIdx with
    | none => rw [hget] at h; simp at h
    | some q =>
      rcases q with ⟨t0, t1, t2, t3⟩
      rw [hget] at h
      simp only [Bool.and_eq_true, f3ByteBeq_true_iff] at h
      rcases h with ⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, hrest⟩
      obtain ⟨tailBytes, hdrop⟩ := WordTree.toBytes_drop_of_getQuad? hwf hget
      have hlen4 : 4 ≤ (t.toBytes.drop (4 * qIdx)).length := by rw [hdrop]; simp
      simp only [List.length_drop] at hlen4
      by_cases hk4 : k < 4
      · have hidx : 4 * qIdx + k < t.toBytes.length := by omega
        refine ⟨hidx, ?_⟩
        have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl
        · have hg : (t.toBytes.drop (4 * qIdx))[0]? = some t0 := by rw [hdrop]; rfl
          rw [List.getElem?_drop, List.getElem?_eq_getElem hidx] at hg
          exact (Option.some.inj hg).trans e0
        · have hg : (t.toBytes.drop (4 * qIdx))[1]? = some t1 := by rw [hdrop]; rfl
          rw [List.getElem?_drop, List.getElem?_eq_getElem hidx] at hg
          exact (Option.some.inj hg).trans e1
        · have hg : (t.toBytes.drop (4 * qIdx))[2]? = some t2 := by rw [hdrop]; rfl
          rw [List.getElem?_drop, List.getElem?_eq_getElem hidx] at hg
          exact (Option.some.inj hg).trans e2
        · have hg : (t.toBytes.drop (4 * qIdx))[3]? = some t3 := by rw [hdrop]; rfl
          rw [List.getElem?_drop, List.getElem?_eq_getElem hidx] at hg
          exact (Option.some.inj hg).trans e3
      · have hk_rest : k - 4 < rest.length := by simp at hk; omega
        obtain ⟨hidx', heq'⟩ := checkQuadBytesFrom_byte_eq hwf (qIdx + 1) rest hrest (k - 4) hk_rest
        have hidx : 4 * qIdx + k < t.toBytes.length := by omega
        refine ⟨hidx, ?_⟩
        have heq_lhs : t.toBytes[4 * qIdx + k]'hidx = t.toBytes[4 * (qIdx + 1) + (k - 4)]'hidx' := by
          congr 1; omega
        have heq_rhs : (b0 :: b1 :: b2 :: b3 :: rest)[k]'hk = rest[k - 4]'hk_rest := by
          have h1 : (b0 :: b1 :: b2 :: b3 :: rest)[k]? = rest[k - 4]? := by
            obtain ⟨m, hm⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
            rw [hm, Nat.add_sub_cancel]
            rfl
          rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk_rest] at h1
          exact Option.some.inj h1
        rw [heq_lhs, heq_rhs]
        exact heq'

/-- Check that `inner : Program` is a word-aligned byte slice of `outerBase` + `t : WordTree`. -/
def checkProgSliceInWordTree (outerBase : BitVec 64) (t : WordTree) (inner : Program) : Bool :=
  let off := inner.base.toNat - outerBase.toNat
  Nat.ble outerBase.toNat inner.base.toNat &&
  (off % 4 == 0) &&
  checkQuadBytesFrom t (off / 4) inner.code

theorem codeLoaded_of_checkProgSliceInWordTree {outer inner : Program} {t : WordTree} {n : Nat}
    {m : Memory}
    (hcode : outer.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hok : checkProgSliceInWordTree outer.base t inner = true)
    (hCL : outer.CodeLoaded m) :
    inner.CodeLoaded m := by
  dsimp only [checkProgSliceInWordTree] at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  rcases hok with ⟨⟨hle_b, hoff4⟩, hquad⟩
  have hle : outer.base.toNat ≤ inner.base.toNat := Nat.le_of_ble_eq_true hle_b
  let off := inner.base.toNat - outer.base.toNat
  have hal_outer := hCL.aligned
  have hnw_outer := hCL.no_wrap
  refine Program.CodeLoaded.intro (by omega) ?_ (fun k hk => ?_)
  · by_cases hempty : inner.code.length = 0
    · have hib := inner.base.isLt; omega
    · obtain ⟨hidx, _⟩ :=
        checkQuadBytesFrom_byte_eq hwf (off / 4) inner.code hquad (inner.code.length - 1) (by omega)
      have hlen_eq : outer.code.length = t.toBytes.length := congrArg List.length hcode
      omega
  · obtain ⟨hidx_t, hbyte_t⟩ := checkQuadBytesFrom_byte_eq hwf (off / 4) inner.code hquad k hk
    have hoff_mul : 4 * (off / 4) = off := by omega
    have hidx_o : off + k < outer.code.length := by rw [hcode]; omega
    have haddr : outer.base + BitVec.ofNat 64 (off + k) = inner.base + BitVec.ofNat 64 k := by
      have hnw_o := hnw_outer
      bv_omega
    have hbo : outer.code[off + k]'hidx_o = inner.code[k]'hk := by
      have ht1 : outer.code[off + k]? = t.toBytes[4 * (off / 4) + k]? := by
        rw [hcode, hoff_mul]
      rw [List.getElem?_eq_getElem hidx_o, List.getElem?_eq_getElem hidx_t] at ht1
      exact (Option.some.inj ht1).trans hbyte_t
    refine ⟨?_, ?_, ?_⟩
    · rw [← haddr]; exact (hCL.byte_eq (off + k) hidx_o).trans hbo
    · rw [← haddr]; exact hCL.perm_eq (off + k) hidx_o
    · rw [← haddr]; exact hCL.isLazyFree_eq (off + k) hidx_o

/-- Structural recursion over `lib.blocks` verifying every block in `t : WordTree`. -/
def checkMultiBlocksFrom (outerBase : BitVec 64) (t : WordTree)
    (lib : MultiPlacedLib) (mpl : MultiPlacement) : Nat → List CodeBlock → Bool
  | _, [] => true
  | i, _ :: rest =>
    checkProgSliceInWordTree outerBase t (lib.blockProgram mpl i) &&
    checkMultiBlocksFrom outerBase t lib mpl (i + 1) rest

private theorem checkMultiBlocksFrom_get {outer : Program} {t : WordTree} {n : Nat}
    {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hcode : outer.code = t.toBytes) (hwf : t.checkSize? = some n) :
    ∀ (start : Nat) (blks : List CodeBlock),
      checkMultiBlocksFrom outer.base t lib mpl start blks = true →
      ∀ (j : Nat), j < blks.length →
        ∀ (m : Memory), outer.CodeLoaded m →
          (lib.blockProgram mpl (start + j)).CodeLoaded m
  | _, [], _, _, hj, _, _ => nomatch hj
  | start, _ :: rest, h, 0, _, m, hCL => by
    simp only [checkMultiBlocksFrom, Bool.and_eq_true] at h
    rw [Nat.add_zero]
    exact codeLoaded_of_checkProgSliceInWordTree hcode hwf h.1 hCL
  | start, _ :: rest, h, j + 1, hj, m, hCL => by
    simp only [checkMultiBlocksFrom, Bool.and_eq_true] at h
    have ih := checkMultiBlocksFrom_get hcode hwf (start + 1) rest h.2 j
      (Nat.lt_of_succ_lt_succ hj) m hCL
    rwa [show start + 1 + j = start + (j + 1) by omega] at ih

/-- Discharge `ProgContainsMultiLib lib P mpl` via `WordTree` for any hook-free `Syscall.standard` `P`. -/
theorem progContainsMultiLib_of_wordTree {lib : MultiPlacedLib} {P : Program}
    {mpl : MultiPlacement} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hpl : lib.Placeable mpl)
    (hsvc : P.svc = Syscall.standard)
    (hext : ∀ pc, P.externAt? pc = none)
    (hok : checkMultiBlocksFrom P.base t lib mpl 0 lib.blocks = true) :
    ProgContainsMultiLib lib P mpl :=
  ProgContainsMultiLib.of_noExterns hpl hsvc
    (fun m hCL i hi => by
      simpa using checkMultiBlocksFrom_get hcode hwf 0 lib.blocks hok i hi m hCL)
    hext

/-! ## `rdl_shim` Validator (`103` Instructions = `412` B) -/

/-- Complete `103`-instruction (`412` B) code bundle for F3's co-located `rdl_shim.S` in `seg[5]`:
    - `noAllocShimV2`: `1` `ret` (`___rust_no_alloc_shim_is_unstable_v2`),
    - `rdlShims`: `RustStdRdlShimCode` (`66` instructions: `22 + 1 + 43`),
    - `allocZeroedInstrs`: `36` instructions of `__rdl_alloc_zeroed` (`= ___rust_alloc_zeroed`). -/
structure F3Seg5ShimBundle (P : Program)
    (rdlAddrs : RustAllocAddrs)
    (rdlAzAddr noShimV2Addr : BitVec 64)
    (cAddrs : MallocngCEntryAddrs) (callocAddr memcpyAddr memsetAddr : BitVec 64) : Prop where
  noAllocShimV2 : hasInstrs P noShimV2Addr [ .ret .x30 ]
  rdlShims : RustStdRdlShimCode P rdlAddrs.toRustStd cAddrs memcpyAddr
  allocZeroedInstrs :
    hasInstrs P rdlAzAddr
      (rdlAllocZeroedInstrs rdlAzAddr callocAddr cAddrs.posixMemalign memsetAddr)

/-- `WordTree` validator for `F3Seg5ShimBundle`. -/
def checkF3Seg5ShimBundle (imgBase : BitVec 64) (t : WordTree)
    (rdlAddrs : RustAllocAddrs)
    (rdlAzAddr noShimV2Addr : BitVec 64)
    (cAddrs : MallocngCEntryAddrs) (callocAddr memcpyAddr memsetAddr : BitVec 64) : Bool :=
  checkShimInstrsAt imgBase t noShimV2Addr [ .ret .x30 ] &&
  checkRustStdRdlShimCode imgBase t rdlAddrs.toRustStd cAddrs memcpyAddr &&
  checkRdlAllocZeroedCode imgBase t rdlAzAddr callocAddr cAddrs.posixMemalign memsetAddr

theorem f3Seg5ShimBundle_of_wordTree {P : Program} {t : WordTree}
    {rdlAddrs : RustAllocAddrs}
    {rdlAzAddr noShimV2Addr : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr memcpyAddr memsetAddr : BitVec 64}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkF3Seg5ShimBundle P.base t rdlAddrs rdlAzAddr noShimV2Addr
      cAddrs callocAddr memcpyAddr memsetAddr = true) :
    F3Seg5ShimBundle P rdlAddrs rdlAzAddr noShimV2Addr
      cAddrs callocAddr memcpyAddr memsetAddr := by
  unfold checkF3Seg5ShimBundle at hok
  simp only [Bool.and_eq_true] at hok
  rcases hok with ⟨⟨hNoShim, hRdl⟩, hAz⟩
  have hNoShimP : hasInstrs P noShimV2Addr [ .ret .x30 ] := by
    simp only [checkShimInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hNoShim
    exact hasInstrs_of_wordTree n hcode hwf hNoShim.1.1 hNoShim.1.2 hext hovr hNoShim.2
  exact ⟨hNoShimP,
         rustStdRdlShimCode_of_wordTree n hcode hwf hext hovr hRdl,
         rdlAllocZeroedCode_of_wordTree n hcode hwf hext hovr hAz⟩

/-! ## Loaded 1-Hop `Instr.b` Stub Execution Lift -/

/-- Execute a 1-instruction unconditional `Instr.b (rdlAddr - stubAddr)` stub loaded in `s0.mem` at
    `stubAddr` (`P.externAt? stubAddr = none`) followed by a `subroutine_ok P_rx rdlAddr spec`
    callee in `seg[5]` (`P_rx.CodeLoaded s0.mem`), producing `Steps P s0 sf` and
    `SubroutineOutcome spec x R s0 sf` across all four `SubroutineOutcome` branches. -/
theorem steps_of_loaded_b_stub {α : Type} {P P_rx : Program}
    {stubAddr rdlAddr : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok P_rx rdlAddr spec)
    (hrx_svc : P_rx.svc = Syscall.standard)
    (hrx_ext : ∀ pc, P_rx.externAt? pc = none)
    (hp_svc : P.svc = Syscall.standard)
    (hp_stub_ext : P.externAt? stubAddr = none)
    {x : α} {R : SepProp} {s0 : State}
    (hpc : s0.pc = stubAddr)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (halign : stubAddr.toNat % 4 = 0)
    (hexec : s0.mem.canExec stubAddr 4 = true)
    (hdec : Arm64.decode (s0.mem.read32 stubAddr) = some (.b (rdlAddr - stubAddr)))
    (hrx_cl : P_rx.CodeLoaded s0.mem)
    (hhooks : P.HooksUnfetched s0.mem)
    (hpre : s0.mem ⊨ spec.pre x (s0.setPC rdlAddr) ∗ R)
    (hpost_pc : ∀ sf, spec.post x (s0.setPC rdlAddr) sf = spec.post x s0 sf)
    (hp_pc : ∀ sf, spec.onPanic x (s0.setPC rdlAddr) sf = spec.onPanic x s0 sf)
    (he_pc : ∀ c sf, spec.onExit x c (s0.setPC rdlAddr) sf = spec.onExit x c s0 sf)
    (ho_pc : ∀ sf, spec.onOom x (s0.setPC rdlAddr) sf = spec.onOom x s0 sf) :
    ∃ sf, Steps P s0 sf ∧ SubroutineOutcome spec x R s0 sf := by
  have hf0 : P.fetchMem s0.mem s0.pc = some (.b (rdlAddr - stubAddr)) := by
    unfold Program.fetchMem
    rw [hpc, hp_stub_ext]
    simp [halign, hexec, hdec]
  have hstep1 : Step P s0 (s0.setPC rdlAddr) := by
    have hev : P.evalInst (.b (rdlAddr - stubAddr)) s0 = s0.setPC rdlAddr := by
      simp only [Program.evalInst, execInstWithSvc, hpc]
      congr 1
      bv_omega
    rw [← hev]
    exact Step.exec hrun hf0
  let s1 := s0.setPC rdlAddr
  obtain ⟨sf, hsteps_pm, hout1⟩ :=
    subroutine_ok_toPureMem_outcome hok (s0 := s1) rfl hrun hpre hsp hrx_cl
      (fun pc _ _ he _ _ _ => by rw [hrx_ext pc] at he; cases he) hrx_svc
  have hend : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory := by
    rcases hout1 with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, hc, _⟩ | ⟨ho, _⟩
    · exact Or.inl hret.2.2
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc⟩))
    · exact Or.inr (Or.inr (Or.inr ho))
  have hstepsP : Steps P s1 sf :=
    Steps.of_pureMem_outcome hp_svc hhooks (Memory.KeepsFrozen.refl s0.mem) hsteps_pm hend
  refine ⟨sf, Steps.step hstep1 hstepsP, ?_⟩
  rcases hout1 with ⟨hret, hcc, hq⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, ⟨hcc.1, (CalleeSavedPreserved_setPC s0 sf rdlAddr).mp hcc.2⟩, ?_⟩
    dsimp only [s1] at hq
    rwa [hpost_pc sf] at hq
  · refine Or.inr (Or.inl ⟨hp, ?_⟩)
    dsimp only [s1] at hpan
    rwa [hp_pc sf] at hpan
  · refine Or.inr (Or.inr (Or.inl ⟨c, hc, ?_⟩))
    dsimp only [s1] at hex
    rwa [he_pc c sf] at hex
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [s1] at hoom
    rwa [ho_pc sf] at hoom

end LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
