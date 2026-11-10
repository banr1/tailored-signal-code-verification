/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Spec.Hoare
public import ProofLib
public import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf

/-!
# `CodeLoaded (stripExecOutside keep ·)` Monotonicity, `KeepsFrozen` Stability, and Load Base Cases

**Checked by Lean.**

Establishes `CodeLoaded (stripExecOutside keep ·)` invariants for ghost-to-real hook transfer:
1. Characterization (`h2cl_codeLoaded_strip_iff`) and guard-set monotonicity (`h2cl_codeLoaded_mono`).
2. `KeepsFrozen` stability (`h2cl_codeLoaded_keepsFrozen_stable`, `h2cl_invS_F3CodeInv_preserved`).
3. Load-state base cases for `f3TrialRxProg` (`seg[5]`, `[0x49c000, 0x4a2000)`) over
   `hole2_keepSub` and `hole2_keep`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2CodeLoadedInv

open Arm64 ProofLib ProofLib.ProgramReflection
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Heap.Fine (f3RxWordCount)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree_eq f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_keep hole2_keepSub)

/-! ## Guard Sets (`hole2_keepSub ⊆ hole2_keep`) -/

theorem h2cl_keepSub_imp_keep (a : BitVec 64) (h : hole2_keepSub a = true) :
    hole2_keep a = true := by
  unfold hole2_keepSub at h
  unfold hole2_keep
  exact decide_eq_true (Or.inr (of_decide_eq_true h))

theorem h2cl_keepSub_false_of_keep_false {a : BitVec 64} (h : hole2_keep a = false) :
    hole2_keepSub a = false := by
  cases hs : hole2_keepSub a with
  | false => rfl
  | true =>
    have hk := h2cl_keepSub_imp_keep a hs
    rw [h] at hk
    cases hk

/-! ## `stripExecOutside` Characterization and Monotonicity -/

/-- `(stripExecOutside keep m).perm a = some Perm.rx` holds iff `m.perm a = some Perm.rx` and
    `keep a = true` (since `stripPerm false p` clears `x`, contradicting `Perm.rx.x = true`). -/
theorem h2cl_strip_perm_eq_rx_iff (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).perm a = some Perm.rx ↔
      m.perm a = some Perm.rx ∧ keep a = true := by
  rw [ProofLib.strip_perm]
  constructor
  · intro h
    cases hp : m.perm a with
    | none => simp [hp] at h
    | some p =>
      rw [hp] at h
      simp only [Option.map, Option.some.injEq] at h
      cases hk : keep a with
      | false =>
        rw [hk] at h
        rcases p with ⟨r, w, x, lf, an⟩
        cases x <;> simp [ProofLib.stripPerm, Perm.rx] at h
      | true =>
        rw [hk] at h
        simp only [ProofLib.stripPerm, Bool.true_or, ↓reduceIte] at h
        exact ⟨congrArg some h, rfl⟩
  · rintro ⟨hp, hk⟩
    rw [hp, hk]
    rfl

/-- Exact characterization: `P.CodeLoaded (stripExecOutside keep m)` holds iff `P.CodeLoaded m`
    holds and every code byte of `P` lies inside `keep`. -/
theorem h2cl_codeLoaded_strip_iff (keep : BitVec 64 → Bool) (P : Program) (m : Memory) :
    P.CodeLoaded (stripExecOutside keep m) ↔
      P.CodeLoaded m ∧ ∀ i < P.code.length, keep (P.base + BitVec.ofNat 64 i) = true := by
  constructor
  · intro hL
    refine ⟨Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_, fun i hi => ?_⟩
    · have hb := hL.byte_eq i hi
      have hp := (h2cl_strip_perm_eq_rx_iff keep m _).mp (hL.perm_eq i hi)
      have hlf := hL.isLazyFree_eq i hi
      rw [ProofLib.strip_read8] at hb
      rw [ProofLib.strip_isLazyFree] at hlf
      exact ⟨hb, hp.1, hlf⟩
    · exact ((h2cl_strip_perm_eq_rx_iff keep m _).mp (hL.perm_eq i hi)).2
  · rintro ⟨hL, hkeep⟩
    refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
    refine ⟨?_, (h2cl_strip_perm_eq_rx_iff keep m _).mpr ⟨hL.perm_eq i hi, hkeep i hi⟩, ?_⟩
    · rw [ProofLib.strip_read8]
      exact hL.byte_eq i hi
    · rw [ProofLib.strip_isLazyFree]
      exact hL.isLazyFree_eq i hi

theorem h2cl_codeLoaded_of_strip {keep : BitVec 64 → Bool} {P : Program} {m : Memory}
    (hL : P.CodeLoaded (stripExecOutside keep m)) :
    P.CodeLoaded m :=
  ((h2cl_codeLoaded_strip_iff keep P m).mp hL).1

theorem h2cl_codeLoaded_strip_of_keep {keep : BitVec 64 → Bool} {P : Program} {m : Memory}
    (hL : P.CodeLoaded m)
    (hkeep : ∀ i < P.code.length, keep (P.base + BitVec.ofNat 64 i) = true) :
    P.CodeLoaded (stripExecOutside keep m) :=
  (h2cl_codeLoaded_strip_iff keep P m).mpr ⟨hL, hkeep⟩

/-- Unstripped `P.CodeLoaded m` plus code-range inclusion in `keep` implies
`P.CodeLoaded (stripExecOutside keep m)`. -/
theorem h2cl_strip_codeLoaded_of_sub {keep : BitVec 64 → Bool} {P : Program} {m : Memory}
    (hL : P.CodeLoaded m)
    (hsub : ∀ i < P.code.length, keep (P.base + BitVec.ofNat 64 i) = true) :
    P.CodeLoaded (stripExecOutside keep m) :=
  h2cl_codeLoaded_strip_of_keep hL hsub

/-- Widening `K₁` to `K₂` preserves `P.CodeLoaded (stripExecOutside · m)`. -/
theorem h2cl_codeLoaded_mono {P : Program} {K₁ K₂ : BitVec 64 → Bool} {m : Memory}
    (hL : P.CodeLoaded (stripExecOutside K₁ m))
    (hSub : ∀ a : BitVec 64, K₁ a = true → K₂ a = true) :
    P.CodeLoaded (stripExecOutside K₂ m) := by
  obtain ⟨hLm, hk1⟩ := (h2cl_codeLoaded_strip_iff K₁ P m).mp hL
  exact (h2cl_codeLoaded_strip_iff K₂ P m).mpr ⟨hLm, fun i hi => hSub _ (hk1 i hi)⟩

/-! ## `KeepsFrozen` Stability and `Inv` Conjunction Helpers -/

/-- `P_sub.CodeLoaded (stripExecOutside keep ·)` is preserved across `m.KeepsFrozen m'`
(since `Perm.rx` implies `m.Frozen a`). -/
theorem h2cl_codeLoaded_of_keepsFrozen {keep : BitVec 64 → Bool} {P_sub : Program} {m m' : Memory}
    (hL : P_sub.CodeLoaded (stripExecOutside keep m))
    (hkf : m.KeepsFrozen m') :
    P_sub.CodeLoaded (stripExecOutside keep m') := by
  obtain ⟨hLm, hkeep⟩ := (h2cl_codeLoaded_strip_iff keep P_sub m).mp hL
  exact (h2cl_codeLoaded_strip_iff keep P_sub m').mpr ⟨hLm.of_keepsFrozen hkf, hkeep⟩

/-- Curried `KeepsFrozen` stability of `P.CodeLoaded (stripExecOutside keep ·)`. -/
theorem h2cl_codeLoaded_keepsFrozen_stable (keep : BitVec 64 → Bool) (P : Program) :
    ∀ m m' : Memory,
      P.CodeLoaded (stripExecOutside keep m) →
      m.KeepsFrozen m' →
      P.CodeLoaded (stripExecOutside keep m') :=
  fun _ _ hL hkf => h2cl_codeLoaded_of_keepsFrozen hL hkf

/-- 4-premise compatibility wrapper accepting optional `ExecFrozen m` and `no-new-X` hypotheses. -/
theorem h2cl_codeLoaded_of_keepsFrozen_with_execFrozen
    {keep : BitVec 64 → Bool} {P_sub : Program} {m m' : Memory}
    (hL : P_sub.CodeLoaded (stripExecOutside keep m))
    (_hFr : ExecFrozen m)
    (hkf : m.KeepsFrozen m')
    (_hNoNewX : ∀ a : BitVec 64, (m'.perm a).x = true → (m.perm a).x = true) :
    P_sub.CodeLoaded (stripExecOutside keep m') :=
  h2cl_codeLoaded_of_keepsFrozen hL hkf

/-- Unconditional single-step preservation along any `Step P s s'` (via `Step.keepsFrozen`). -/
theorem h2cl_step_codeLoaded {keep : BitVec 64 → Bool} {P P_sub : Program} {s s' : State}
    (hstep : Step P s s')
    (hL : P_sub.CodeLoaded (stripExecOutside keep s.mem)) :
    P_sub.CodeLoaded (stripExecOutside keep s'.mem) :=
  h2cl_codeLoaded_of_keepsFrozen hL hstep.keepsFrozen

/-- Unconditional multi-step preservation along any `Steps P s s'` (via `Steps.keepsFrozen`). -/
theorem h2cl_steps_codeLoaded {keep : BitVec 64 → Bool} {P P_sub : Program} {s s' : State}
    (hsteps : Steps P s s')
    (hL : P_sub.CodeLoaded (stripExecOutside keep s.mem)) :
    P_sub.CodeLoaded (stripExecOutside keep s'.mem) :=
  h2cl_codeLoaded_of_keepsFrozen hL hsteps.keepsFrozen

/-- `F3CodeInv mpl mmpl` is `KeepsFrozen`-stable. -/
theorem h2cl_invS_F3CodeInv_preserved (mpl mmpl : MultiPlacement) :
    ∀ m m' : Memory, F3CodeInv mpl mmpl m → m.KeepsFrozen m' → F3CodeInv mpl mmpl m' :=
  fun _ _ h hkf => h.of_keepsFrozen hkf

/-- Generic conjunction combinator for `KeepsFrozen`-stable memory invariants. -/
theorem h2cl_inv_and_keepsFrozen_stable {Inv₁ Inv₂ : Memory → Prop}
    (h₁ : ∀ m m' : Memory, Inv₁ m → m.KeepsFrozen m' → Inv₁ m')
    (h₂ : ∀ m m' : Memory, Inv₂ m → m.KeepsFrozen m' → Inv₂ m') :
    ∀ m m' : Memory, (Inv₁ m ∧ Inv₂ m) → m.KeepsFrozen m' → (Inv₁ m' ∧ Inv₂ m') :=
  fun m m' ⟨hi1, hi2⟩ hkf => ⟨h₁ m m' hi1 hkf, h₂ m m' hi2 hkf⟩

/-- Existing memory invariant `Inv` conjoined with `P.CodeLoaded (stripExecOutside keep ·)`. -/
def h2cl_WithCodeLoaded (Inv : Memory → Prop) (keep : BitVec 64 → Bool) (P : Program)
    (m : Memory) : Prop :=
  Inv m ∧ P.CodeLoaded (stripExecOutside keep m)

/-- `Inv ∧ P.CodeLoaded (stripExecOutside keep ·)` is `KeepsFrozen`-stable whenever `Inv` is. -/
theorem h2cl_withCodeLoaded_keepsFrozen_stable {Inv : Memory → Prop}
    (keep : BitVec 64 → Bool) (P : Program)
    (hInvStable : ∀ m m' : Memory, Inv m → m.KeepsFrozen m' → Inv m') :
    ∀ m m' : Memory,
      h2cl_WithCodeLoaded Inv keep P m →
      m.KeepsFrozen m' →
      h2cl_WithCodeLoaded Inv keep P m' :=
  h2cl_inv_and_keepsFrozen_stable hInvStable (h2cl_codeLoaded_keepsFrozen_stable keep P)

/-- `CliF3MainOkBridge` `hInvCodeSub` projection for `h2cl_WithCodeLoaded`. -/
theorem h2cl_withCodeLoaded_codeSub {Inv : Memory → Prop}
    (keep : BitVec 64 → Bool) (P : Program) :
    ∀ m : Memory, ExecFrozen m → h2cl_WithCodeLoaded Inv keep P m →
      P.CodeLoaded (stripExecOutside keep m) :=
  fun _ _ h => h.2

/-! ### Per-Hook Guard-Set Stability Instantiations -/

/-- Guard set 1 (`alloc` / `allocZeroed` / `dealloc` / `realloc` / `readFile` / `readStdin`):
    `f3TrialRxProg` over `hole2_keepSub`. -/
theorem h2cl_rxProg_keepSub_keepsFrozen_stable :
    ∀ m m' : Memory,
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m) →
      m.KeepsFrozen m' →
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m') :=
  h2cl_codeLoaded_keepsFrozen_stable hole2_keepSub f3TrialRxProg


/-- Guard set 2 (`stringClone`): `f3TrialRxProg` over `hole2_keep`. -/
theorem h2cl_rxProg_keep_keepsFrozen_stable :
    ∀ m m' : Memory,
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep m) →
      m.KeepsFrozen m' →
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep m') :=
  h2cl_codeLoaded_keepsFrozen_stable hole2_keep f3TrialRxProg


/-! ## Load-State Base Cases -/

private theorem h2cl_toNat_add_ofNat_of_lt {b : BitVec 64} {k : Nat}
    (hlt : b.toNat + k < 18446744073709551616) :
    (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hk : k < 2 ^ 64 := by omega
  have hlt' : b.toNat + k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt']

/-! ### `f3TrialRxProg` (`seg[2]`, `[0x469000, 0x46f000)`) Base Cases -/

private theorem h2cl_rxProg_byte_in_keepSub (i : Nat) (hi : i < f3TrialRxProg.code.length) :
    hole2_keepSub (f3TrialRxProg.base + BitVec.ofNat 64 i) = true := by
  have hbase : f3TrialRxProg.base = f3RxSegBase := f3TrialRxProg_base
  have hbase_nat : f3RxSegBase.toNat = 0x469000 := by decide
  have hlen : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  have hwc : f3RxWordCount = 6144 := rfl
  have ht : (f3TrialRxProg.base + BitVec.ofNat 64 i).toNat =
      f3TrialRxProg.base.toNat + i := by
    apply h2cl_toNat_add_ofNat_of_lt
    rw [hbase, hbase_nat]
    rw [hlen, hwc] at hi
    omega
  unfold hole2_keepSub
  refine decide_eq_true ⟨?_, ?_⟩ <;> (rw [ht, hbase, hbase_nat]; rw [hlen, hwc] at hi; omega)

/-- Equivalence between `hole2_keepSub` and `hole2_keep` for `f3TrialRxProg`. -/
theorem h2cl_rxProg_codeLoaded_keepSub_iff_keep (m : Memory) :
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m) ↔
      f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep m) := by
  constructor
  · exact fun h => h2cl_codeLoaded_mono h h2cl_keepSub_imp_keep
  · intro h
    exact h2cl_codeLoaded_strip_of_keep (h2cl_codeLoaded_of_strip h) h2cl_rxProg_byte_in_keepSub

theorem h2cl_f3CodeInv_rxProg_keepSub {mpl mmpl : MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m) :=
  h2cl_codeLoaded_strip_of_keep hInv.rxCode h2cl_rxProg_byte_in_keepSub

/-- `F3CodeOk mpl mmpl m` implies `f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m)`. -/
theorem h2cl_f3CodeOk_rxProg_keepSub {mpl mmpl : MultiPlacement} {m : Memory}
    (hCO : F3CodeOk mpl mmpl m) :
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m) :=
  h2cl_f3CodeInv_rxProg_keepSub hCO.1


theorem h2cl_f3CodeOk_rxProg_keep {mpl mmpl : MultiPlacement} {m : Memory}
    (hCO : F3CodeOk mpl mmpl m) :
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep m) :=
  h2cl_codeLoaded_mono (h2cl_f3CodeOk_rxProg_keepSub hCO) h2cl_keepSub_imp_keep

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2CodeLoadedInv
