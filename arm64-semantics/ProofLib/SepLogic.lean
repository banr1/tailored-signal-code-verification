/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public import Std.Tactic.BVDecide
public import Arm64
import ProofLib.SepLogic.Model
public import ProofLib.SepLogic.Defs
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.Abi.Aapcs

/-!
# Byte-Granular Separation Logic

Algebraic laws, typed block abstractions, and reflective AC normalization for `SepProp`:
partial byte-granular heaps (`Heap`) and connective laws; typed read-write (`IsBlock`),
duplicable read-only (`IsBlockRO`), exclusive `PROT_NONE` (`IsBlockProtNone`), and lazy-free
(`memRegionLazy`) blocks with `mmap` / `mprotect` / `munmap` / `madvise` permission-transition
lemmas; `O(N log N)` sorted-index AC certificates (`SepTree`, `SepAtomTree`); authoritative
ghost maps (`ghostMapAuth`, `ghostMapElem`); and irreducible sealing with `SepBlock` instances.
-/

namespace ProofLib

open Arm64

@[expose] public section

universe u

/-! ## Partial Byte-Granular Heaps (`Heap`) -/

private theorem satSep_iff {m : Memory} {P Q : SepProp} :
    (m ⊨ P ∗ Q) ↔ ∃ h : Heap, (∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧
      P.holds h₁ ∧ Q.holds h₂) ∧ h.Matches m := by
  simp only [SepProp.satisfies_iff, SepProp.holds_sepConj_iff]

/-- A heap covers `[base, base + len)` when it maps every address in that region to a read-write
    cell. -/
def _root_.Arm64.Heap.CoversRegion (h : Heap) (base : BitVec 64) (len : Nat) : Prop :=
  ∀ a, InRegion base len a → ∃ b, h a = some (.rw b)

namespace Heap

export Arm64.Heap (
  Disjoint.symm Disjoint.of_phys_left Disjoint.of_phys_right
  disjoint_empty_left disjoint_empty_right
  union_empty_left union_empty_right
  union_comm_of_disjoint union_assoc
  disjoint_union_left disjoint_union_right disjoint_singleton_iff
  GhostValid.of_phys GhostValid.empty GhostValid.union
  GhostValid.of_union_left GhostValid.of_union_right
  Matches.of_phys Matches.empty Matches.union Matches.of_union_left Matches.of_union_right
)

theorem ext_phys {h₁ h₂ : Heap}
    (hp : ∀ x, h₁.phys x = h₂.phys x)
    (ha : h₁.auth = h₂.auth := by rfl)
    (hf : h₁.frag = h₂.frag := by rfl)
    (hm : h₁.mapped = h₂.mapped := by rfl) :
    h₁ = h₂ :=
  Heap.ext (funext hp) ha hf hm

theorem Matches.of_agreesOutside {h₁ h₂ : Heap} {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat}
    (hcov : h₁.CoversRegion base len)
    (hdisj : h₁.Disjoint h₂)
    (hag : AgreesOutside m₁ m₂ base len)
    (hm : h₂.Matches m₁) :
    h₂.Matches m₂ := by
  refine ⟨fun a c hc => ?_, hm.2.1, fun a hmap => ?_⟩
  · have hout : OutsideRegion base len a := by
      rw [outsideRegion_iff_not_inRegion]
      intro hin
      obtain ⟨b, hb1⟩ := hcov a hin
      rcases hdisj.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hb1] at h1; contradiction
      · rw [hc] at h2; contradiction
      · rw [hb1] at h1; cases h1
    cases c with
    | rw b =>
      rw [hag.read8_eq hout, hag.perm_eq, hag.isLazyFree_eq hout]
      exact hm.1 a (.rw b) hc
    | ro b =>
      rw [hag.read8_eq hout, hag.perm_eq, hag.isLazyFree_eq hout]
      exact hm.1 a (.ro b) hc
    | protNone b =>
      rw [hag.read8_eq hout, hag.perm_eq, hag.isLazyFree_eq hout]
      exact hm.1 a (.protNone b) hc
    | lazy =>
      rw [hag.perm_eq]
      exact hm.1 a .lazy hc
    | protNoneLazy =>
      rw [hag.perm_eq]
      exact hm.1 a .protNoneLazy hc
  · obtain ⟨hmp, han⟩ := hm.2.2 a hmap
    rw [hag.perm_eq]
    exact ⟨hmp, hag.isAnon_true han⟩

end Heap

/-- Mapping fresh bytes (`brk` growth, `mmap`: `Memory.mapFresh`) preserves every assertion:
    owned bytes are already mapped, and `mapFresh` only maps unmapped bytes. -/
theorem satisfies_mapFresh {P : SepProp} {m : Memory} (h : m ⊨ P) (base : BitVec 64) (len : Nat)
    (p : Perm) : m.mapFresh base len p ⊨ P := by
  obtain ⟨hp, hP, hm⟩ := SepProp.satisfies_iff.mp h
  refine SepProp.satisfies_iff.mpr ⟨hp, hP, fun a c hac => ?_, hm.2.1, fun a hmap => ?_⟩
  · cases c with
    | rw b =>
      obtain ⟨hr, hperm, hlf⟩ := hm.1 a (.rw b) hac
      have hmapped : (m.perm a).mapped = true := by rw [hperm]; rfl
      refine ⟨(Memory.read8_mapFresh ..).trans hr, ?_, ?_⟩
      · simp [Memory.perm_mapFresh, hperm]
      · simp [Memory.isLazyFree_mapFresh, hmapped, hlf]
    | ro b =>
      obtain ⟨hr, hperm, hlf⟩ := hm.1 a (.ro b) hac
      have hmap : (m.perm a).mapped = true := by rcases hp' : m.perm a with _ | q <;> simp_all
      refine ⟨(Memory.read8_mapFresh ..).trans hr, ?_, ?_⟩
      · simp [Memory.perm_mapFresh, hmap, hperm]
      · simp [Memory.isLazyFree_mapFresh, hmap, hlf]
    | protNone b =>
      obtain ⟨hr, hperm, hlf⟩ := hm.1 a (.protNone b) hac
      have hmapped : (m.perm a).mapped = true := by rw [hperm]; rfl
      refine ⟨(Memory.read8_mapFresh ..).trans hr, ?_, ?_⟩
      · simp [Memory.perm_mapFresh, hperm]
      · simp [Memory.isLazyFree_mapFresh, hmapped, hlf]
    | lazy =>
      have hperm := hm.1 a .lazy hac
      simp [Memory.perm_mapFresh, hperm]
    | protNoneLazy =>
      have hperm := hm.1 a .protNoneLazy hac
      simp [Memory.perm_mapFresh, hperm]
  · obtain ⟨hm_a, han_a⟩ := hm.2.2 a hmap
    have hpm : (m.mapFresh base len p).perm a = m.perm a := by
      simp [Memory.perm_mapFresh, hm_a]
    have han : (m.mapFresh base len p).isAnon a = m.isAnon a := by
      simp [Memory.isAnon_mapFresh, hm_a]
    rw [hpm, han]
    exact ⟨hm_a, han_a⟩

/-- If `m'` has the same permissions, `isLazyFree`, `isAnon`, and byte values as `m`, it satisfies
    the same separation-logic assertions. -/
theorem Satisfies.congr_mem {P : SepProp} {m m' : Memory}
    (h_read : ∀ a, m'.read8 a = m.read8 a)
    (h_perm : m'.perm = m.perm)
    (h_lf : m'.isLazyFree = m.isLazyFree)
    (h_anon : m'.isAnon = m.isAnon)
    (h : m ⊨ P) : m' ⊨ P := by
  obtain ⟨hp, hP, hm⟩ := SepProp.satisfies_iff.mp h
  refine SepProp.satisfies_iff.mpr ⟨hp, hP, fun a c hac => ?_, hm.2.1, fun a hmap => ?_⟩
  · cases c with
    | rw b =>
      obtain ⟨hr, hp_a, hlf_a⟩ := hm.1 a (.rw b) hac
      exact ⟨(h_read a).trans hr, (congrFun h_perm a).trans hp_a, (congrFun h_lf a).trans hlf_a⟩
    | ro b =>
      obtain ⟨hr, hp_a, hlf_a⟩ := hm.1 a (.ro b) hac
      exact ⟨(h_read a).trans hr, by rw [congrFun h_perm a]; exact hp_a, (congrFun h_lf a).trans hlf_a⟩
    | protNone b =>
      obtain ⟨hr, hp_a, hlf_a⟩ := hm.1 a (.protNone b) hac
      exact ⟨(h_read a).trans hr, (congrFun h_perm a).trans hp_a, (congrFun h_lf a).trans hlf_a⟩
    | lazy =>
      exact (congrFun h_perm a).trans (hm.1 a .lazy hac)
    | protNoneLazy =>
      exact (congrFun h_perm a).trans (hm.1 a .protNoneLazy hac)
  · rw [congrFun h_perm a, congrFun h_anon a]
    exact hm.2.2 a hmap

/-! ## Algebraic Laws for Separation Logic Connectives -/

export Arm64 (
  Entails.refl Entails.trans Entails.of_eq
  Entails.sepExists_intro Entails.sepExists_right Entails.sepExists_elim
  Entails.pure_left Entails.pure_left_only Entails.pure_right Entails.pure_right_only Entails.top_right
  pure_extract_iff not_satisfies_false_sepConj
  Satisfies.mono Satisfies.of_eq
  bupd_intro bupd_mono bupd_trans bupd_frame_r bupd_frame_l satisfies_bupd
  sepConj_comm sepConj_assoc sepConj_left_comm sepConj_right_comm
  instAssociativeSepConj instCommutativeSepConj
  emp_sepConj sepConj_emp pure_true
  satisfies_emp satisfies_pure
  pure_sepConj sepConj_pure
  satisfies_pure_sepConj satisfies_sepConj_pure satisfies_sepConj_pure_assoc
  sepConj_mono sepConj_mono_left sepConj_mono_right
  sepExists_sepConj_left sepExists_sepConj_right satisfies_sepExists
)

instance : Std.Associative (α := SepProp) (· ∗ ·) := ⟨sepConj_assoc⟩

/-- Extensionality for `SepProp`: two assertions are equal whenever they mutually entail each other
    (`P ⊢ Q` and `Q ⊢ P`). -/
theorem sepProp_eq_of_entails {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  SepProp.ext (funext fun h =>
    propext ⟨SepProp.entails_iff.mp h1 h, SepProp.entails_iff.mp h2 h⟩)

instance : Std.Commutative (α := SepProp) (· ∗ ·) := ⟨sepConj_comm⟩

instance instLawfulIdentitySepConj : Std.LawfulIdentity SepProp.sepConj SepProp.emp where
  left_id := emp_sepConj
  right_id := sepConj_emp

theorem pure_true_sepConj (P : SepProp) : (⌜True⌝ : SepProp) ∗ P = P := by
  rw [pure_true, emp_sepConj]

theorem sepConj_pure_true (P : SepProp) : P ∗ (⌜True⌝ : SepProp) = P := by
  rw [pure_true, sepConj_emp]

theorem pure_sepConj_of_true {φ : Prop} (h : φ) (P : SepProp) : (⌜φ⌝ ∗ P) = P := by
  rw [pure_sepConj]; ext hp; exact ⟨fun ⟨_, b⟩ => b, fun b => ⟨h, b⟩⟩

theorem pure_false_sepConj (P : SepProp) : (⌜False⌝ : SepProp) ∗ P = (⌜False⌝ : SepProp) := by
  rw [pure_sepConj]; ext h
  simp only [SepProp.holds_pure_iff, and_false, false_and]

theorem sepConj_pure_false (P : SepProp) : P ∗ (⌜False⌝ : SepProp) = (⌜False⌝ : SepProp) := by
  rw [sepConj_comm, pure_false_sepConj]

theorem pure_sepConj_congr {φ : Prop} {P Q : SepProp} (h : φ → P = Q) :
    (⌜φ⌝ ∗ P) = (⌜φ⌝ ∗ Q) := by
  rw [pure_sepConj, pure_sepConj]
  ext hp
  exact ⟨fun ⟨a, b⟩ => ⟨a, h a ▸ b⟩, fun ⟨a, b⟩ => ⟨a, (h a).symm ▸ b⟩⟩

@[simp, arm64_norm]
theorem pure_sepConj_pure (φ ψ : Prop) :
    ((⌜φ⌝ : SepProp) ∗ ⌜ψ⌝) = ⌜φ ∧ ψ⌝ := by
  rw [pure_sepConj]
  ext h
  simp only [SepProp.holds_pure_iff]
  exact ⟨fun ⟨hφ, h0, hψ⟩ => ⟨h0, hφ, hψ⟩, fun ⟨h0, hφ, hψ⟩ => ⟨hφ, h0, hψ⟩⟩

@[simp, arm64_norm]
theorem pure_sepConj_pure_assoc (φ ψ : Prop) (Q : SepProp) :
    ((⌜φ⌝ : SepProp) ∗ (⌜ψ⌝ ∗ Q)) = ⌜φ ∧ ψ⌝ ∗ Q := by
  rw [← sepConj_assoc, pure_sepConj_pure]

theorem sepConj_pure_left_comm (P : SepProp) (φ : Prop) (Q : SepProp) :
    P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) :=
  sepConj_left_comm P ⌜φ⌝ Q

theorem Satisfies.sepExists_intro {α : Sort u} {P : α → SepProp} {R : SepProp} {m : Memory}
    (x : α) (h : m ⊨ P x ∗ R) : m ⊨ (∃∗ y, P y) ∗ R :=
  Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro x)) h

theorem Entails.wand_intro {P Q R : SepProp} (h : (P ∗ Q) ⊢ R) : P ⊢ (Q -∗ R) := by
  refine SepProp.entails_iff.mpr fun h₁ hp => SepProp.holds_sepImp_iff.mpr fun h₂ hd hq => ?_
  exact SepProp.entails_iff.mp h (h₁.union h₂)
    (SepProp.holds_sepConj_iff.mpr ⟨h₁, h₂, hd, rfl, hp, hq⟩)

theorem Entails.wand_elim (P Q : SepProp) : (P ∗ (P -∗ Q)) ⊢ Q := by
  refine SepProp.entails_iff.mpr fun h hh => ?_
  obtain ⟨h₁, h₂, hd, rfl, hp, hwand⟩ := SepProp.holds_sepConj_iff.mp hh
  rw [Heap.union_comm_of_disjoint hd]
  exact SepProp.holds_sepImp_iff.mp hwand h₁ hd.symm hp

/-- Magic wand (`-∗`) adjunction: `(P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)`. -/
theorem sepImp_adj (P Q R : SepProp) : ((P ∗ Q) ⊢ R) ↔ (P ⊢ (Q -∗ R)) := by
  refine ⟨Entails.wand_intro, fun h => SepProp.entails_iff.mpr fun _ hh => ?_⟩
  obtain ⟨h₁, h₂, hd, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  exact SepProp.holds_sepImp_iff.mp (SepProp.entails_iff.mp h h₁ hp) h₂ hd hq

/-! ## Region and Stack-Frame Lemmas -/

/-- Any memory `m` that maps `[base, base + len)` read-write and non-`lazyFree` (`m.RW base len`)
    satisfies `memRegion base len`, owning that region with the contents of `m`. -/
theorem satisfies_memRegion (m : Memory) (base : BitVec 64) (len : Nat)
    (hrw : m.RW base len) :
    m ⊨ memRegion base len := by
  refine SepProp.satisfies_iff.mpr ⟨regionHeap base len m, holds_memRegion_iff.mpr ⟨m, rfl⟩,
    Heap.Matches.of_phys rfl rfl fun a c h => ?_⟩
  simp only [regionHeap] at h
  split at h
  · rename_i hin
    injection h with h
    subst h
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)
    exact ⟨rfl, hp, hlf⟩
  · contradiction

/-- Any memory `m` that maps `[base, base + len)` read-write (`m.perm a = some Perm.rw`, even if
    `lazyFree`) satisfies `memRegionLazy base len`. -/
theorem satisfies_memRegionLazy (m : Memory) (base : BitVec 64) (len : Nat)
    (hrw : ∀ a, InRegion base len a → m.perm a = some Perm.rw) :
    m ⊨ memRegionLazy base len := by
  refine SepProp.satisfies_iff.mpr ⟨regionHeapLazy base len, holds_memRegionLazy_iff.mpr rfl,
    Heap.Matches.of_phys rfl rfl fun a c h => ?_⟩
  simp only [regionHeapLazy] at h
  split at h
  · rename_i hin; injection h with h; subst h; exact hrw a hin
  · contradiction

theorem stackFrame16At_def (sp : BitVec 64) :
    stackFrame16At sp =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((sp - 16#64) ↦₆₄ v0) ∗ ((sp - 8#64) ↦₆₄ v1) := rfl

theorem stackFrame32At_def (sp : BitVec 64) :
    stackFrame32At sp =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) := rfl

@[simp, arm64_norm, wp_norm]
theorem stackFrameFor_eq {α : Type} [HasFnFrameBytes α] (src : α) (name : String) (sp : BitVec 64) :
    stackFrameFor src name sp = stackFrameAt sp (fnFrameBytes src name) := rfl

@[simp, arm64_norm, wp_norm]
theorem stackFrameAt_zero (sp : BitVec 64) :
    stackFrameAt sp 0 = emp := rfl

end

public meta section

open Lean Meta in
/-- Reduce `stackFrameAt sp n` for concrete `Nat` literals `n` into `emp` (when `n = 0`),
    prenex-quantified 8-byte stack slots `(sp - n) ↦₆₄ v₀ ∗ ... ∗ (sp - 8) ↦₆₄ v_{n/8 - 1}`
    (when `n > 0` and `n % 8 = 0`), or `memRegion (sp - n) n`. -/
dsimproc [arm64_norm, wp_norm] reduceStackFrameAt (stackFrameAt _ _) := fun e => do
  let e ← instantiateMVars e
  unless e.isAppOfArity ``Arm64.stackFrameAt 2 do
    return .continue
  let spExpr := e.getArg! 0
  let nExpr := e.getArg! 1
  let some n ← (do
      if let some k := nExpr.rawNatLit? then pure (some k)
      else (evalNat nExpr).run)
    | return .continue
  if n == 0 then
    return .done (mkConst ``SepProp.emp)
  else if n % 8 == 0 then
    let slots := n / 8
    let bv64Ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
    let rec buildSlots (idx : Nat) (fvars : Array Expr) : MetaM Expr := do
      if idx < slots then
        let vName := Name.mkSimple s!"v{idx}"
        withLocalDeclD vName bv64Ty fun fv => do
          let inner ← buildSlots (idx + 1) (fvars.push fv)
          let lam ← mkLambdaFVars #[fv] inner
          return mkApp2 (mkConst ``SepProp.sepExists [Level.one]) bv64Ty lam
      else
        let mut body : Option Expr := none
        for k in [:slots] do
          let i := slots - 1 - k
          let offBytes := (slots - i) * 8
          let offBv := toExpr (BitVec.ofNat 64 offBytes)
          let addr ← mkAppM ``HSub.hSub #[spExpr, offBv]
          let cell := mkApp2 (mkConst ``Arm64.pointsTo64) addr fvars[i]!
          body := match body with
            | none => some cell
            | some rest => some (mkApp2 (mkConst ``SepProp.sepConj) cell rest)
        return body.getD (mkConst ``SepProp.emp)
    return .done (← buildSlots 0 #[])
  else
    let offBv := toExpr (BitVec.ofNat 64 n)
    let addr ← mkAppM ``HSub.hSub #[spExpr, offBv]
    return .done (mkApp2 (mkConst ``Arm64.memRegion) addr (mkNatLit n))

end

@[expose] public section

universe u

theorem disjointRegions_of_coversRegion {m : Memory} {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    {P₁ P₂ R : SepProp}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hcov₁ : ∀ {hp : Heap}, P₁ hp → hp.CoversRegion b₁ n₁)
    (hcov₂ : ∀ {hp : Heap}, P₂ hp → hp.CoversRegion b₂ n₂)
    (h : m ⊨ P₁ ∗ (P₂ ∗ R)) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  obtain ⟨_, hh, _⟩ := SepProp.satisfies_iff.mp h
  obtain ⟨h₁, _, hd1, _, hp₁, hh'⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨h₂, _, _, rfl, hp₂, _⟩ := SepProp.holds_sepConj_iff.mp hh'
  have c₁ := hcov₁ hp₁
  have c₂ := hcov₂ hp₂
  have hdisj : ∀ a, ¬(InRegion b₁ n₁ a ∧ InRegion b₂ n₂ a) := by
    intro a ⟨hin1, hin2⟩
    obtain ⟨v1, hv1⟩ := c₁ a hin1
    obtain ⟨v2, hv2⟩ := c₂ a hin2
    rcases hd1.1 a with h1 | h23 | ⟨_, h1, _⟩
    · rw [hv1] at h1; contradiction
    · dsimp [Heap.union] at h23
      rw [hv2] at h23; contradiction
    · rw [hv1] at h1; cases h1
  constructor
  · apply Classical.byContradiction
    intro hlt
    have hin1 : InRegion b₁ n₁ b₂ := by simp only [InRegion]; omega
    have hin2 : InRegion b₂ n₂ b₂ := by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
    exact hdisj b₂ ⟨hin1, hin2⟩
  · apply Classical.byContradiction
    intro hlt
    have hin2 : InRegion b₂ n₂ b₁ := by simp only [InRegion]; omega
    have hin1 : InRegion b₁ n₁ b₁ := by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
    exact hdisj b₁ ⟨hin1, hin2⟩

/-! ## Projections and the Complement Frame -/

theorem Satisfies.of_sep_left {m : Memory} {P Q : SepProp} (h : m ⊨ P ∗ Q) : m ⊨ P := by
  obtain ⟨_, hh, hm⟩ := SepProp.satisfies_iff.mp h
  obtain ⟨h₁, _, _, rfl, hp, _⟩ := SepProp.holds_sepConj_iff.mp hh
  exact SepProp.satisfies_iff.mpr ⟨h₁, hp, Heap.Matches.of_union_left hm⟩

theorem Satisfies.of_sep_right {m : Memory} {P Q : SepProp} (h : m ⊨ P ∗ Q) : m ⊨ Q := by
  obtain ⟨_, hh, hm⟩ := SepProp.satisfies_iff.mp h
  obtain ⟨_, h₂, hd, rfl, _, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  exact SepProp.satisfies_iff.mpr ⟨h₂, hq, Heap.Matches.of_union_right hd hm⟩

/-- Exclusivity / non-aliasing of `pointsTo8`: two `↦₈` assertions at the same address are
    mutually inconsistent. -/
theorem pointsTo8_conflict (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    (a ↦₈ v₁ ∗ a ↦₈ v₂) ⊢ ⌜False⌝ := by
  simp only [SepProp.entails_iff, SepProp.holds_sepConj_iff, holds_pointsTo8_iff]
  rintro _ ⟨h₁, h₂, hd, _, rfl, rfl⟩
  exact absurd rfl ((Heap.disjoint_singleton_iff a a v₁ v₂).mp hd)

/-- Two `PROT_NONE` singleton heaps are disjoint if and only if their addresses are distinct. -/
theorem Heap.disjoint_singletonProtNone_iff (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) :
    (Heap.singletonProtNone a₁ v₁).Disjoint (Heap.singletonProtNone a₂ v₂) ↔ a₁ ≠ a₂ := by
  constructor
  · intro hd heq
    subst heq
    have ha := hd.1 a₁
    simp [Heap.singletonProtNone] at ha
  · intro hne
    refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl,
      fun _ _ _ _ h => (by rcases h with ⟨h1, _⟩ | ⟨_, h2⟩ <;> contradiction),
      fun _ => Or.inl rfl⟩
    by_cases hx1 : x = a₁ <;> simp [Heap.singletonProtNone, hx1, hne]

/-- A `PROT_NONE` singleton heap and a read-write singleton heap are disjoint iff `a₁ ≠ a₂`. -/
theorem Heap.disjoint_singletonProtNone_singleton_iff (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) :
    (Heap.singletonProtNone a₁ v₁).Disjoint (Heap.singleton a₂ v₂) ↔ a₁ ≠ a₂ := by
  constructor
  · intro hd heq
    subst heq
    have ha := hd.1 a₁
    simp [Heap.singletonProtNone, Heap.singleton] at ha
  · intro hne
    refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl,
      fun _ _ _ _ h => (by rcases h with ⟨h1, _⟩ | ⟨_, h2⟩ <;> contradiction),
      fun _ => Or.inl rfl⟩
    by_cases hx1 : x = a₁ <;> simp [Heap.singletonProtNone, Heap.singleton, hx1, hne]

/-- Two separated `↦₈ₙ` assertions occupy distinct addresses (`a₁ ≠ a₂`). -/
theorem pointsTo8ProtNone_disjoint (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) :
    ((a₁ ↦₈ₙ v₁) ∗ (a₂ ↦₈ₙ v₂)) ⊢ ⌜a₁ ≠ a₂⌝ ∗ (a₁ ↦₈ₙ v₁) ∗ (a₂ ↦₈ₙ v₂) := by
  refine SepProp.entails_iff.mpr fun h hh => ?_
  obtain ⟨h₁, h₂, hd, rfl, h1, h2⟩ := SepProp.holds_sepConj_iff.mp hh
  rw [pure_sepConj]
  rw [holds_pointsTo8ProtNone_iff] at h1 h2
  subst h1 h2
  exact ⟨(Heap.disjoint_singletonProtNone_iff a₁ a₂ v₁ v₂).mp hd,
    SepProp.holds_sepConj_iff.mpr ⟨Heap.singletonProtNone a₁ v₁, Heap.singletonProtNone a₂ v₂, hd,
      rfl, holds_pointsTo8ProtNone_iff.mpr rfl, holds_pointsTo8ProtNone_iff.mpr rfl⟩⟩

/-- Exclusivity / non-aliasing of `pointsTo8ProtNone`: two `↦₈ₙ` assertions at the same address
    are mutually inconsistent. -/
theorem pointsTo8ProtNone_conflict (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    ((a ↦₈ₙ v₁) ∗ (a ↦₈ₙ v₂)) ⊢ ⌜False⌝ := by
  simp only [SepProp.entails_iff, SepProp.holds_sepConj_iff, holds_pointsTo8ProtNone_iff]
  rintro _ ⟨h₁, h₂, hd, _, rfl, rfl⟩
  exact absurd rfl ((Heap.disjoint_singletonProtNone_iff a a v₁ v₂).mp hd)

/-- Mutual exclusion between `pointsTo8ProtNone` (`↦₈ₙ`) and `pointsTo8` (`↦₈`) at the same address. -/
theorem pointsTo8ProtNone_pointsTo8_conflict (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    ((a ↦₈ₙ v₁) ∗ (a ↦₈ v₂)) ⊢ ⌜False⌝ := by
  simp only [SepProp.entails_iff, SepProp.holds_sepConj_iff, holds_pointsTo8ProtNone_iff,
    holds_pointsTo8_iff]
  rintro _ ⟨h₁, h₂, hd, _, rfl, rfl⟩
  exact absurd rfl ((Heap.disjoint_singletonProtNone_singleton_iff a a v₁ v₂).mp hd)

/-- Mutual exclusion between `pointsTo8` (`↦₈`) and `pointsTo8ProtNone` (`↦₈ₙ`) at the same address. -/
theorem pointsTo8_pointsTo8ProtNone_conflict (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    ((a ↦₈ v₁) ∗ (a ↦₈ₙ v₂)) ⊢ ⌜False⌝ := by
  rw [sepConj_comm]
  exact pointsTo8ProtNone_pointsTo8_conflict a v₂ v₁

/-- Memory satisfaction of `a ↦₈ₙ v` gives `m.read8 a = v` and `m.perm a = some Perm.protNone`. -/
theorem satisfies_pointsTo8ProtNone {m : Memory} {a : BitVec 64} {v : BitVec 8}
    (hm : m ⊨ (a ↦₈ₙ v)) : m.read8 a = v ∧ m.perm a = some Perm.protNone := by
  rcases SepProp.satisfies_iff.mp hm with ⟨h, hh, hmatch⟩
  rw [holds_pointsTo8ProtNone_iff] at hh; subst hh
  obtain ⟨hr, hp, -⟩ := hmatch.1 a (.protNone v) (by simp [Heap.singletonProtNone])
  exact ⟨hr, hp⟩

/-- Framed preserved-byte and permission extraction from `m ⊨ (a ↦₈ₙ v) ∗ R`. -/
theorem satisfies_pointsTo8ProtNone_frame {m : Memory} {a : BitVec 64} {v : BitVec 8} {R : SepProp}
    (hm : m ⊨ (a ↦₈ₙ v) ∗ R) : m.read8 a = v ∧ m.perm a = some Perm.protNone :=
  satisfies_pointsTo8ProtNone (Satisfies.of_sep_left hm)

/-- Memory satisfaction of a single byte `a ↦₈ v` gives `m.read8 a = v` and `m.perm a = some Perm.rw`. -/
theorem satisfies_pointsTo8 {m : Memory} {a : BitVec 64} {v : BitVec 8}
    (hm : m ⊨ (a ↦₈ v)) : m.read8 a = v ∧ m.perm a = some Perm.rw := by
  rcases SepProp.satisfies_iff.mp hm with ⟨h, hh, hmatch⟩
  rw [holds_pointsTo8_iff] at hh; subst hh
  obtain ⟨hr, hp, -⟩ := hmatch.1 a (.rw v) (by simp [Heap.singleton])
  exact ⟨hr, hp⟩

/-- Framed byte read and permission extraction from `m ⊨ (a ↦₈ v) ∗ R`. -/
theorem satisfies_pointsTo8_frame {m : Memory} {a : BitVec 64} {v : BitVec 8} {R : SepProp}
    (hm : m ⊨ (a ↦₈ v) ∗ R) : m.read8 a = v ∧ m.perm a = some Perm.rw :=
  satisfies_pointsTo8 (Satisfies.of_sep_left hm)

theorem Heap.disjoint_complement (h : Heap) (m : Memory) : h.Disjoint (h.complement m) := by
  refine ⟨fun a => ?_, fun _ _ => Or.inr rfl, fun _ _ => Or.inr rfl, ?_, fun a => ?_⟩
  · dsimp [Heap.complement]
    cases h.phys a with
    | none => exact Or.inl rfl
    | some _ => exact Or.inr (Or.inl rfl)
  · intro _ _ _ _ h'
    rcases h' with ⟨_, h2⟩ | ⟨h1, _⟩
    · cases h2
    · cases h1
  · dsimp [Heap.complement]
    cases h.mapped a <;> simp

theorem Heap.Matches.complement (h : Heap) (m : Memory) : (h.complement m).Matches m := by
  refine ⟨fun a c hc => ?_, Heap.GhostValid.empty, fun a hmap => ?_⟩
  · dsimp [Heap.complement] at hc
    cases h1 : h.phys a with
    | some _ => rw [h1] at hc; contradiction
    | none =>
      rw [h1] at hc
      by_cases hrw : m.perm a = some Perm.rw
      · by_cases hlf : m.isLazyFree a = true
        · simp only [hrw, hlf, ↓reduceIte] at hc
          injection hc with hc; subst hc; exact hrw
        · simp only [Bool.not_eq_true] at hlf
          simp only [hrw, hlf, Bool.false_eq_true, ↓reduceIte] at hc
          injection hc with hc; subst hc; exact ⟨rfl, hrw, hlf⟩
      · by_cases hpn : m.perm a = some Perm.protNone
        · by_cases hlf : m.isLazyFree a = true
          · simp only [hpn, hlf, ↓reduceIte] at hc
            injection hc with hc; subst hc; exact hpn
          · simp only [Bool.not_eq_true] at hlf
            simp only [hpn, hlf, Bool.false_eq_true, ↓reduceIte] at hc
            injection hc with hc; subst hc; exact ⟨rfl, hpn, hlf⟩
        · simp only [hrw, hpn, ↓reduceIte] at hc; contradiction
  · dsimp [Heap.complement] at hmap
    simp only [Bool.and_eq_true] at hmap
    exact ⟨hmap.1.1.2, hmap.2⟩

theorem satisfies_with_complement {m : Memory} {P : SepProp} (h : m ⊨ P) :
    m ⊨ P ∗ complementSep P m := by
  rcases SepProp.satisfies_iff.mp h with ⟨hp, hP, hm⟩
  refine satSep_iff.mpr ⟨hp.union (hp.complement m),
    ⟨hp, hp.complement m, Heap.disjoint_complement hp m, rfl, hP,
      SepProp.holds_complementSep_iff.mpr ⟨hp, hP, hm, rfl⟩⟩, ?_⟩
  exact Heap.Matches.union hm (Heap.Matches.complement hp m)

@[simp, arm64_norm]
theorem pointsToBytes_nil (a : BitVec 64) : (a ↦ₛ []) = emp := pointsToBytes_nil_def a

@[simp, arm64_norm]
theorem pointsToBytes_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ₛ (b :: bs)) = ((a ↦₈ b) ∗ ((a + 1#64) ↦ₛ bs)) := pointsToBytes_cons_def a b bs

@[simp, arm64_norm]
theorem pointsToWords64_nil (a : BitVec 64) : (a ↦₆₄* []) = emp := by rfl

@[simp, arm64_norm]
theorem pointsToWords64_cons (a : BitVec 64) (w : BitVec 64) (ws : List (BitVec 64)) :
    (a ↦₆₄* (w :: ws)) = ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄* ws)) := by rfl

@[simp, arm64_norm]
theorem pointsToBytesRO_nil (a : BitVec 64) : (a ↦ᵣ []) = emp := pointsToBytesRO_nil_def a

@[simp, arm64_norm]
theorem pointsToBytesRO_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ᵣ (b :: bs)) = ((a ↦₈ᵣ b) ∗ ((a + 1#64) ↦ᵣ bs)) := pointsToBytesRO_cons_def a b bs

@[simp, arm64_norm]
theorem pointsToWords64RO_nil (a : BitVec 64) : (a ↦₆₄ᵣ* []) = emp := by rfl

@[simp, arm64_norm]
theorem pointsToWords64RO_cons (a : BitVec 64) (w : BitVec 64) (ws : List (BitVec 64)) :
    (a ↦₆₄ᵣ* (w :: ws)) = ((a ↦₆₄ᵣ w) ∗ ((a + 8#64) ↦₆₄ᵣ* ws)) := by rfl

@[simp, arm64_norm]
theorem pointsToBytesProtNone_nil (a : BitVec 64) : (a ↦ₙ []) = emp :=
  pointsToBytesProtNone_nil_def a

@[simp, arm64_norm]
theorem pointsToBytesProtNone_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ₙ (b :: bs)) = ((a ↦₈ₙ b) ∗ ((a + 1#64) ↦ₙ bs)) :=
  pointsToBytesProtNone_cons_def a b bs

/-! ## Block Atoms (`IsBlock`)

Spatial atoms are modeled uniformly by `IsBlock P base len Φ`, asserting ownership of the
contiguous bytes `[base, base + len)` with contents satisfying `Φ : Memory → Prop`. Reading,
updating, and disjointness reduce to `IsBlock.read`, `IsBlock.update`, and `IsBlock.disjoint`,
with multi-byte atoms composed from `IsBlock.pointsTo8` via `IsBlock.sepConj`,
`IsBlock.sepExists`, and `IsBlock.cast`, and registered as `SepBlock` instances after sealing. -/

/-- `P` owns exactly the bytes `[base, base + len)`, whose contents are described by `Φ`
    (a predicate that only depends on the bytes of the region). -/
structure IsBlock (P : SepProp) (base : BitVec 64) (len : Nat) (Φ : Memory → Prop) : Prop where
  iff : ∀ h : Heap, P h ↔ ∃ m, Φ m ∧ h = regionHeap base len m
  congr : ∀ m m' : Memory, (∀ a, InRegion base len a → m'.read8 a = m.read8 a) → Φ m → Φ m'

namespace IsBlock

variable {P P' Q : SepProp} {b b' : BitVec 64} {n n' : Nat} {Φ Φ' Ψ : Memory → Prop}

theorem regionHeap_matches (b : BitVec 64) (n : Nat) (m : Memory)
    (hrw : m.RW b n) : (regionHeap b n m).Matches m := by
  refine Heap.Matches.of_phys rfl rfl fun a c h => ?_
  simp only [regionHeap] at h
  split at h
  · rename_i hin
    injection h with h
    subst h
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)
    exact ⟨rfl, hp, hlf⟩
  · contradiction

theorem covers (hb : IsBlock P b n Φ) {h : Heap} (hp : P h) : h.CoversRegion b n := by
  obtain ⟨m, -, rfl⟩ := (hb.iff h).mp hp
  intro x hx
  exact ⟨m.read8 x, by simp [regionHeap, hx]⟩

/-- Reading a block: `m ⊨ P ∗ R` implies the content description `Φ m`. -/
theorem read (hb : IsBlock P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R) : Φ m := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨m₀, hΦ, rfl⟩ := (hb.iff _).mp hp
  exact hb.congr m₀ m
    (fun a ha => ((Heap.Matches.of_union_left hm).1 a (.rw (m₀.read8 a)) (by simp [regionHeap, ha])).1) hΦ

/-- Updating a block: after `m` changes to `m'` only inside `[b, b + n)`, the block `P` can be
    replaced by any block `P'` over a prefix `[b, b + n')` of the same region whose description
    `Φ'` holds in `m'` (the bytes `[b + n', b + n)` are given up). -/
theorem update (hb : IsBlock P b n Φ) (hb' : IsBlock P' b n' Φ') (hle : n' ≤ n)
    {m m' : Memory} {R : SepProp}
    (h : m ⊨ P ∗ R) (hag : AgreesOutside m m' b n) (hΦ : Φ' m') : m' ⊨ P' ∗ R := by
  obtain ⟨_, ⟨h₁, hR, hd, rfl, hp, hr⟩, hm⟩ := satSep_iff.mp h
  have hmR : hR.Matches m' :=
    Heap.Matches.of_agreesOutside (hb.covers hp) hd hag (Heap.Matches.of_union_right hd hm)
  have hrw : m'.RW b n' := by
    intro a ha
    obtain ⟨v, hv⟩ := hb.covers hp a (Nat.lt_of_lt_of_le ha hle)
    obtain ⟨-, hpm, hlf⟩ := (Heap.Matches.of_union_left hm).1 a (.rw v) hv
    exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨(congrFun hag.perm_eq a).trans hpm, hag.isLazyFree_false hlf⟩
  refine satSep_iff.mpr ⟨(regionHeap b n' m').union hR,
    ⟨_, hR, Heap.Disjoint.of_phys_left rfl rfl fun x => ?_, rfl, (hb'.iff _).mpr ⟨m', hΦ, rfl⟩, hr⟩,
    Heap.Matches.union (regionHeap_matches b n' m' hrw) hmR⟩
  by_cases hx : InRegion b n' x
  · obtain ⟨v, hv⟩ := hb.covers hp x (Nat.lt_of_lt_of_le hx hle)
    rcases hd.1 x with h1 | h2 | ⟨_, h1, _⟩
    · rw [hv] at h1; contradiction
    · exact Or.inr (Or.inl h2)
    · rw [hv] at h1; cases h1
  · exact Or.inl (by simp [regionHeap, hx])

/-- Every byte of an owned block is mapped read-write. -/
theorem perm_rw (hb : IsBlock P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R)
    {a : BitVec 64} (ha : InRegion b n a) : m.perm a = some Perm.rw := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨v, hv⟩ := hb.covers hp a ha
  exact ((Heap.Matches.of_union_left hm).1 a (.rw v) hv).2.1

/-- Every byte of an owned block has `isLazyFree = false`. -/
theorem isLazyFree_false (hb : IsBlock P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R)
    {a : BitVec 64} (ha : InRegion b n a) : m.isLazyFree a = false := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨v, hv⟩ := hb.covers hp a ha
  exact ((Heap.Matches.of_union_left hm).1 a (.rw v) hv).2.2

/-- Every byte of an owned block has `m.permNoLazy a = some Perm.rw`. -/
theorem permNoLazy_rw (hb : IsBlock P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R)
    {a : BitVec 64} (ha : InRegion b n a) : m.permNoLazy a = some Perm.rw :=
  Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hb.perm_rw h ha, hb.isLazyFree_false h ha⟩

/-- Every owned block satisfies `m.RW b n`. -/
theorem rw (hb : IsBlock P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R) : m.RW b n :=
  fun _ ha => hb.permNoLazy_rw h ha

/-- An owned block is readable. -/
theorem canRead (hb : IsBlock P b n Φ) (hn : n ≤ 2 ^ 64) {m : Memory} {R : SepProp}
    (h : m ⊨ P ∗ R) : m.canRead b n = true := by
  simp only [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff]
  exact ⟨fun i hi => by rw [hb.perm_rw h (inRegion_base_add b n i hi hn)]; rfl,
    fun i hi => hb.isLazyFree_false h (inRegion_base_add b n i hi hn)⟩

/-- An owned block is writable. -/
theorem canWrite (hb : IsBlock P b n Φ) (hn : n ≤ 2 ^ 64) {m : Memory} {R : SepProp}
    (h : m ⊨ P ∗ R) : m.canWrite b n = true := by
  unfold Memory.canWrite
  rw [Memory.allPerm_iff]
  intro i hi
  rw [hb.perm_rw h (inRegion_base_add b n i hi hn)]
  rfl

theorem inRegion_sub_range {b a : BitVec 64} {n k i : Nat}
    (hk : (a - b).toNat + k ≤ n) (hn : n ≤ 2 ^ 64) (hi : i < k) :
    InRegion b n (a + BitVec.ofNat 64 i) := by
  have hi' : i < 2 ^ 64 := by omega
  simp only [InRegion]
  have e : a + BitVec.ofNat 64 i - b = (a - b) + BitVec.ofNat 64 i := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']
  have : (a - b).toNat + i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

/-- A sub-range `[a, a + k)` of an owned block is readable. -/
theorem canRead_sub (hb : IsBlock P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R)
    {a : BitVec 64} {k : Nat} (hk : (a - b).toNat + k ≤ n) (hn : n ≤ 2 ^ 64) :
    m.canRead a k = true := by
  simp only [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff]
  exact ⟨fun i hi => by rw [hb.perm_rw h (inRegion_sub_range hk hn hi)]; rfl,
    fun i hi => hb.isLazyFree_false h (inRegion_sub_range hk hn hi)⟩

/-- A sub-range `[a, a + k)` of an owned block is writable. -/
theorem canWrite_sub (hb : IsBlock P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R)
    {a : BitVec 64} {k : Nat} (hk : (a - b).toNat + k ≤ n) (hn : n ≤ 2 ^ 64) :
    m.canWrite a k = true := by
  unfold Memory.canWrite
  rw [Memory.allPerm_iff]
  intro i hi
  rw [hb.perm_rw h (inRegion_sub_range hk hn hi)]
  rfl

/-- Two separated blocks of positive length occupy disjoint regions. -/
theorem disjoint {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat} {Φ₁ Φ₂ : Memory → Prop}
    (hb₁ : IsBlock P b₁ n₁ Φ₁) (hb₂ : IsBlock Q b₂ n₂ Φ₂) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    {m : Memory} {R : SepProp} (h : m ⊨ P ∗ (Q ∗ R)) : DisjointRegions b₁ n₁ b₂ n₂ :=
  disjointRegions_of_coversRegion hn₁ hn₂ hb₁.covers hb₂.covers h

/-- Re-describe a block (base address up to equality, contents up to equivalence). -/
theorem cast (hb : IsBlock P b n Φ) (hbase : b = b') (hΦ : ∀ m, Φ m ↔ Ψ m) :
    IsBlock P b' n Ψ := by
  subst hbase
  exact ⟨fun h => (hb.iff h).trans (exists_congr fun m => and_congr_left fun _ => hΦ m),
    fun m m' hag h => (hΦ m').mp (hb.congr m m' hag ((hΦ m).mpr h))⟩

theorem inRegion_append {a a' x : BitVec 64} {n k : Nat}
    (ha : a' = a + BitVec.ofNat 64 n) (hnk : n + k ≤ 2 ^ 64) :
    (InRegion a (n + k) x ↔ InRegion a n x ∨ InRegion a' k x) ∧
      ¬ (InRegion a n x ∧ InRegion a' k x) := by
  subst ha
  simp only [InRegion]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · by_cases h' : (x - a).toNat < n
    · exact Or.inl h'
    · exact Or.inr (by bv_arith)
  · rcases h with h | h <;> bv_arith
  · bv_arith

/-- Adjacent blocks `[a, a + n)` and `[a + n, a + n + k)` compose into the block `[a, a + n + k)`. -/
theorem sepConj {a a' : BitVec 64} {k : Nat} {Φ₁ Φ₂ : Memory → Prop}
    (hP : IsBlock P a n Φ₁) (hQ : IsBlock Q a' k Φ₂)
    (ha : a' = a + BitVec.ofNat 64 n) (hnk : n + k ≤ 2 ^ 64) :
    IsBlock (P ∗ Q) a (n + k) (fun m => Φ₁ m ∧ Φ₂ m) := by
  have hs := fun x => inRegion_append (x := x) ha hnk
  refine ⟨fun h => ⟨?_, ?_⟩, fun m m' hag ⟨h₁, h₂⟩ =>
    ⟨hP.congr m m' (fun x hx => hag x ((hs x).1.mpr (Or.inl hx))) h₁,
     hQ.congr m m' (fun x hx => hag x ((hs x).1.mpr (Or.inr hx))) h₂⟩⟩
  · intro hh
    obtain ⟨h₁, h₂, _, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
    obtain ⟨m₁, hΦ₁, rfl⟩ := (hP.iff _).mp hp
    obtain ⟨m₂, hΦ₂, rfl⟩ := (hQ.iff _).mp hq
    let m : Memory := Memory.ofFn fun x => if InRegion a n x then m₁.read8 x else m₂.read8 x
    have hm : ∀ x, m.read8 x = if InRegion a n x then m₁.read8 x else m₂.read8 x :=
      fun _ => Memory.read8_ofFn _ _ _
    refine ⟨m, ⟨hP.congr m₁ m (fun x hx => by simp [hm, hx]) hΦ₁,
      hQ.congr m₂ m (fun x hx => by
        have : ¬InRegion a n x := fun h => (hs x).2 ⟨h, hx⟩
        simp [hm, this]) hΦ₂⟩, ?_⟩
    refine Heap.ext_phys fun x => ?_
    by_cases h₁ : InRegion a n x
    · simp [Heap.union, regionHeap, hm, h₁, (hs x).1.mpr (Or.inl h₁)]
    · by_cases h₂ : InRegion a' k x <;> simp [Heap.union, regionHeap, hm, h₁, h₂, (hs x).1]
  · rintro ⟨m, ⟨hΦ₁, hΦ₂⟩, rfl⟩
    refine SepProp.holds_sepConj_iff.mpr ⟨regionHeap a n m, regionHeap a' k m, Heap.Disjoint.of_phys_left rfl rfl fun x => ?_, ?_,
      (hP.iff _).mpr ⟨m, hΦ₁, rfl⟩, (hQ.iff _).mpr ⟨m, hΦ₂, rfl⟩⟩
    · by_cases h₁ : InRegion a n x
      · have : ¬InRegion a' k x := fun h₂ => (hs x).2 ⟨h₁, h₂⟩
        exact Or.inr (Or.inl (by simp [regionHeap, this]))
      · exact Or.inl (by simp [regionHeap, h₁])
    · refine Heap.ext_phys fun x => ?_
      by_cases h₁ : InRegion a n x
      · simp [Heap.union, regionHeap, h₁, (hs x).1.mpr (Or.inl h₁)]
      · by_cases h₂ : InRegion a' k x <;> simp [Heap.union, regionHeap, h₁, h₂, (hs x).1]

/-- An existential over blocks of the same region is a block. -/
theorem sepExists {α : Sort u} {P : α → SepProp} {Φ : α → Memory → Prop}
    {b : BitVec 64} {n : Nat}
    (h : ∀ x, IsBlock (P x) b n (Φ x)) : IsBlock (∃∗ x, P x) b n (fun m => ∃ x, Φ x m) :=
  ⟨fun hp => SepProp.holds_sepExists_iff.trans
     ⟨fun ⟨x, hx⟩ => let ⟨m, hm, e⟩ := ((h x).iff hp).mp hx; ⟨m, ⟨x, hm⟩, e⟩,
      fun ⟨m, ⟨x, hm⟩, e⟩ => ⟨x, ((h x).iff hp).mpr ⟨m, hm, e⟩⟩⟩,
   fun m m' hag ⟨x, hx⟩ => ⟨x, (h x).congr m m' hag hx⟩⟩

theorem pointsTo8 (a : BitVec 64) (v : BitVec 8) :
    IsBlock (a ↦₈ v) a 1 (fun m => m.read8 a = v) := by
  have hreg : ∀ x, InRegion a 1 x ↔ x = a := fun x => by
    simp only [InRegion]; constructor <;> intro h <;> bv_arith
  refine ⟨fun h => ⟨fun hp => ⟨(default : Memory).write8 a v, Memory.read8_write8_same _ _ _, ?_⟩, ?_⟩,
    fun m m' hag hm => (hag a ((hreg a).mpr rfl)).trans hm⟩
  · have hp : h = Heap.singleton a v := holds_pointsTo8_iff.mp hp
    subst hp
    refine Heap.ext_phys fun x => ?_
    by_cases hx : x = a <;> simp [Heap.singleton, regionHeap, hreg, hx]
  · rintro ⟨m, rfl, rfl⟩
    rw [holds_pointsTo8_iff]
    refine Heap.ext_phys fun x => ?_
    by_cases hx : x = a <;> simp [Heap.singleton, regionHeap, hreg, hx]

theorem regionBlock (b : BitVec 64) (n : Nat) (m₀ : Memory) :
    IsBlock (regionBlock b n m₀) b n (fun m => ∀ x, InRegion b n x → m.read8 x = m₀.read8 x) := by
  refine ⟨fun h => ⟨fun hp => ⟨m₀, fun _ _ => rfl, holds_regionBlock_iff.mp hp⟩, ?_⟩,
    fun m m' hag hm x hx => (hag x hx).trans (hm x hx)⟩
  rintro ⟨m, hm, rfl⟩
  rw [holds_regionBlock_iff]
  refine Heap.ext_phys fun x => ?_
  simp only [regionHeap]
  split <;> simp_all

theorem memRegion (b : BitVec 64) (n : Nat) : IsBlock (memRegion b n) b n (fun _ => True) :=
  ⟨fun _ => holds_memRegion_iff.trans ⟨fun ⟨m, e⟩ => ⟨m, trivial, e⟩, fun ⟨m, _, e⟩ => ⟨m, e⟩⟩,
    fun _ _ _ _ => trivial⟩

theorem pointsTo16 (a : BitVec 64) (v : BitVec 16) :
    IsBlock (a ↦₁₆ v) a 2 (fun m => m.read16 a = v) :=
  ((pointsTo8 _ _).sepConj (pointsTo8 _ _) (by bv_arith) (by decide)).cast (by bv_arith) fun m => by
    simp only [Memory.read16]
    generalize m.read8 (a + 0#64) = x0
    generalize m.read8 (a + 1#64) = x1
    bv_bits

theorem pointsTo32 (a : BitVec 64) (v : BitVec 32) :
    IsBlock (a ↦₃₂ v) a 4 (fun m => m.read32 a = v) :=
  ((pointsTo8 _ _).sepConj ((pointsTo8 _ _).sepConj ((pointsTo8 _ _).sepConj (pointsTo8 _ _)
    (by bv_arith) (by decide)) (by bv_arith) (by decide)) (by bv_arith) (by decide)).cast
    (by bv_arith) fun m => by
    simp only [Memory.read32]
    generalize m.read8 (a + 0#64) = x0
    generalize m.read8 (a + 1#64) = x1
    generalize m.read8 (a + 2#64) = x2
    generalize m.read8 (a + 3#64) = x3
    bv_bits

theorem pointsTo64 (a : BitVec 64) (v : BitVec 64) :
    IsBlock (a ↦₆₄ v) a 8 (fun m => m.read64 a = v) :=
  ((pointsTo8 _ _).sepConj ((pointsTo8 _ _).sepConj ((pointsTo8 _ _).sepConj ((pointsTo8 _ _).sepConj
    ((pointsTo8 _ _).sepConj ((pointsTo8 _ _).sepConj ((pointsTo8 _ _).sepConj (pointsTo8 _ _)
    (by bv_arith) (by decide)) (by bv_arith) (by decide)) (by bv_arith) (by decide))
    (by bv_arith) (by decide)) (by bv_arith) (by decide)) (by bv_arith) (by decide))
    (by bv_arith) (by decide)).cast (by bv_arith) fun m => by
    simp only [Memory.read64]
    generalize m.read8 (a + 0#64) = x0
    generalize m.read8 (a + 1#64) = x1
    generalize m.read8 (a + 2#64) = x2
    generalize m.read8 (a + 3#64) = x3
    generalize m.read8 (a + 4#64) = x4
    generalize m.read8 (a + 5#64) = x5
    generalize m.read8 (a + 6#64) = x6
    generalize m.read8 (a + 7#64) = x7
    bv_bits

theorem pointsTo128 (a : BitVec 64) (v : BitVec 128) :
    IsBlock (a ↦₁₂₈ v) a 16 (fun m => m.read128 a = v) :=
  ((pointsTo64 _ _).sepConj (pointsTo64 _ _) (by bv_arith) (by decide)).cast rfl fun m => by
    simp only [Memory.read128]
    generalize m.read64 a = lo
    generalize m.read64 (a + 8#64) = hi
    bv_bits

theorem stackFrame16At (sp : BitVec 64) : IsBlock (stackFrame16At sp) (sp - 16#64) 16 (fun _ => True) :=
  (sepExists fun _ => sepExists fun _ => (pointsTo64 _ _).sepConj (pointsTo64 _ _)
    (by bv_arith) (by decide)).cast rfl fun _ => ⟨fun _ => trivial, fun _ => ⟨_, _, rfl, rfl⟩⟩

theorem stackFrame32At (sp : BitVec 64) : IsBlock (stackFrame32At sp) (sp - 32#64) 32 (fun _ => True) :=
  (sepExists fun _ => sepExists fun _ => sepExists fun _ => sepExists fun _ =>
    (pointsTo64 _ _).sepConj ((pointsTo64 _ _).sepConj ((pointsTo64 _ _).sepConj (pointsTo64 _ _)
      (by bv_arith) (by decide)) (by bv_arith) (by decide)) (by bv_arith) (by decide)).cast rfl
    fun _ => ⟨fun _ => trivial, fun _ => ⟨_, _, _, _, rfl, rfl, rfl, rfl⟩⟩

/-- Block uniqueness: two blocks over the same region with equivalent descriptions are equal. -/
theorem eq (hP : IsBlock P b n Φ) (hQ : IsBlock Q b n Ψ) (h : ∀ m, Φ m ↔ Ψ m) : P = Q := by
  ext hh
  exact (hP.iff hh).trans
    ((hQ.iff hh).trans (exists_congr fun m => and_congr_left fun _ => (h m).symm)).symm

/-- Entailment between blocks over the same region follows from implication of descriptions. -/
theorem entails (hP : IsBlock P b n Φ) (hQ : IsBlock Q b n Ψ) (h : ∀ m, Φ m → Ψ m) : P ⊢ Q := by
  refine SepProp.entails_iff.mpr fun hh hp => ?_
  obtain ⟨m, hm, e⟩ := (hP.iff hh).mp hp
  exact (hQ.iff hh).mpr ⟨m, h m hm, e⟩

/-- A pure guard in front of a block (the block only needs to exist under the guard). -/
theorem pure_sepConj {φ : Prop} (hP : φ → IsBlock P b n Φ) :
    IsBlock (⌜φ⌝ ∗ P) b n (fun m => φ ∧ Φ m) := by
  rw [ProofLib.pure_sepConj]
  refine ⟨fun h => ⟨fun ⟨hφ, hp⟩ => ?_,
      fun ⟨m, ⟨hφ, hm⟩, e⟩ => ⟨hφ, ((hP hφ).iff h).mpr ⟨m, hm, e⟩⟩⟩,
    fun m m' hag ⟨hφ, hm⟩ => ⟨hφ, (hP hφ).congr m m' hag hm⟩⟩
  obtain ⟨m, hm, e⟩ := ((hP hφ).iff h).mp hp
  exact ⟨m, ⟨hφ, hm⟩, e⟩

/-- `a ↦ₛ bs` owns `[a, a + bs.length)` holding exactly the bytes `bs` (and is unsatisfiable when
    `bs.length > 2^64`, since the bytes would overlap). -/
theorem pointsToBytes (a : BitVec 64) (bs : List (BitVec 8)) :
    IsBlock (a ↦ₛ bs) a bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes a bs.length = bs) := by
  induction bs generalizing a with
  | nil =>
    rw [pointsToBytes_nil]
    have hr : ∀ m, regionHeap a 0 m = Heap.empty := fun m => by
      refine Heap.ext_phys fun x => ?_
      simp [regionHeap, InRegion, Heap.empty]
    refine ⟨fun h => ⟨fun hp => ⟨default, ⟨by simp, by simp⟩, ?_⟩, ?_⟩,
      fun _ _ _ h => h⟩
    · rw [SepProp.holds_emp_iff] at hp; simp [hp, hr]
    · rintro ⟨m, -, rfl⟩; rw [SepProp.holds_emp_iff]; simp [hr]
  | cons x bs ih =>
    rw [pointsToBytes_cons]
    by_cases hlen : bs.length + 1 ≤ 2 ^ 64
    · have hb := (IsBlock.pointsTo8 a x).sepConj (ih (a + 1#64)) (by bv_arith) (by omega)
      have e : 1 + bs.length = (x :: bs).length := by simp; omega
      rw [e] at hb
      refine hb.cast rfl fun m => ?_
      simp only [List.length_cons, Memory.readBytes, List.cons.injEq]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨hlen, h1, h3⟩
      · rintro ⟨-, h1, h3⟩; exact ⟨h1, by omega, h3⟩
    · refine ⟨fun h => ⟨fun hp => ?_, fun ⟨_, ⟨hl, _⟩, _⟩ => by simp at hl; omega⟩,
        fun _ _ _ ⟨hl, _⟩ => by simp at hl; omega⟩
      exfalso
      obtain ⟨h₁, h₂, hd, -, hp₁, hp₂⟩ := SepProp.holds_sepConj_iff.mp hp
      obtain ⟨v1, hv1⟩ := (IsBlock.pointsTo8 a x).covers hp₁ a (by simp [InRegion])
      obtain ⟨v2, hv2⟩ := (ih (a + 1#64)).covers hp₂ a (by simp only [InRegion]; bv_arith)
      rcases hd.1 a with h | h | ⟨_, h, _⟩
      · rw [hv1] at h; contradiction
      · rw [hv2] at h; contradiction
      · rw [hv1] at h; cases h

theorem pointsToBytes_len {a : BitVec 64} {bs : List (BitVec 8)} (h : bs.length = n) :
    IsBlock (a ↦ₛ bs) a n (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes a bs.length = bs) := by
  subst h; exact pointsToBytes a bs

end IsBlock

/-! ## Read-Only Block Atoms (`IsBlockRO`) and Duplicable Read-Only Points-To (`↦ᵣ`) -/

/-- If `P` and `Q` are duplicable (`P ∗ P = P` and `Q ∗ Q = Q`), so is `P ∗ Q`. -/
theorem sepConj_dup {P Q : SepProp} (hP : (P ∗ P) = P) (hQ : (Q ∗ Q) = Q) :
    ((P ∗ Q) ∗ (P ∗ Q)) = (P ∗ Q) := by
  calc
    ((P ∗ Q) ∗ (P ∗ Q)) = P ∗ (Q ∗ (P ∗ Q)) := sepConj_assoc P Q (P ∗ Q)
    _ = P ∗ (P ∗ (Q ∗ Q)) := by rw [sepConj_left_comm Q P Q]
    _ = (P ∗ P) ∗ (Q ∗ Q) := (sepConj_assoc P P (Q ∗ Q)).symm
    _ = P ∗ Q := by rw [hP, hQ]

theorem Heap.union_self (h : Heap) : h.union h = h := by
  apply Heap.ext
  · funext x; dsimp [Heap.union]; cases h.phys x <;> rfl
  · funext γ k; dsimp [Heap.union]; cases h.auth γ k <;> rfl
  · funext γ k; dsimp [Heap.union]; cases h.frag γ k <;> rfl
  · funext x; dsimp [Heap.union]; cases h.mapped x <;> rfl

/-- Single-byte read-only points-to is duplicable (`(a ↦₈ᵣ v) ∗ (a ↦₈ᵣ v) = (a ↦₈ᵣ v)`). -/
@[simp]
theorem pointsTo8RO_dup (a : BitVec 64) (v : BitVec 8) :
    ((a ↦₈ᵣ v) ∗ (a ↦₈ᵣ v)) = (a ↦₈ᵣ v) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, holds_pointsTo8RO_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, rfl, rfl⟩
    exact Heap.union_self (Heap.singletonRO a v)
  · intro hp
    have hp' : h = Heap.singletonRO a v := hp
    subst hp'
    refine ⟨Heap.singletonRO a v, Heap.singletonRO a v, Heap.Disjoint.of_phys_left rfl rfl fun x => ?_,
      (Heap.union_self (Heap.singletonRO a v)).symm, rfl, rfl⟩
    dsimp [Heap.singletonRO]
    by_cases hx : x = a
    · subst hx; simp
    · simp [hx]

/-- 16-bit read-only points-to is duplicable. -/
@[simp]
theorem pointsTo16RO_dup (a : BitVec 64) (v : BitVec 16) :
    ((a ↦₁₆ᵣ v) ∗ (a ↦₁₆ᵣ v)) = (a ↦₁₆ᵣ v) :=
  sepConj_dup (pointsTo8RO_dup _ _) (pointsTo8RO_dup _ _)

/-- 32-bit read-only points-to is duplicable. -/
@[simp]
theorem pointsTo32RO_dup (a : BitVec 64) (v : BitVec 32) :
    ((a ↦₃₂ᵣ v) ∗ (a ↦₃₂ᵣ v)) = (a ↦₃₂ᵣ v) :=
  sepConj_dup (pointsTo8RO_dup _ _)
    (sepConj_dup (pointsTo8RO_dup _ _)
      (sepConj_dup (pointsTo8RO_dup _ _) (pointsTo8RO_dup _ _)))

/-- 64-bit read-only points-to is duplicable. -/
@[simp]
theorem pointsTo64RO_dup (a : BitVec 64) (v : BitVec 64) :
    ((a ↦₆₄ᵣ v) ∗ (a ↦₆₄ᵣ v)) = (a ↦₆₄ᵣ v) :=
  sepConj_dup (pointsTo8RO_dup _ _)
    (sepConj_dup (pointsTo8RO_dup _ _)
      (sepConj_dup (pointsTo8RO_dup _ _)
        (sepConj_dup (pointsTo8RO_dup _ _)
          (sepConj_dup (pointsTo8RO_dup _ _)
            (sepConj_dup (pointsTo8RO_dup _ _)
              (sepConj_dup (pointsTo8RO_dup _ _) (pointsTo8RO_dup _ _)))))))

/-- 128-bit read-only points-to is duplicable. -/
@[simp]
theorem pointsTo128RO_dup (a : BitVec 64) (v : BitVec 128) :
    ((a ↦₁₂₈ᵣ v) ∗ (a ↦₁₂₈ᵣ v)) = (a ↦₁₂₈ᵣ v) :=
  sepConj_dup (pointsTo64RO_dup _ _) (pointsTo64RO_dup _ _)

/-- Contiguous byte-list read-only points-to is duplicable (`(a ↦ᵣ bs) ∗ (a ↦ᵣ bs) = (a ↦ᵣ bs)`). -/
@[simp]
theorem pointsToBytesRO_dup (a : BitVec 64) (bs : List (BitVec 8)) :
    ((a ↦ᵣ bs) ∗ (a ↦ᵣ bs)) = (a ↦ᵣ bs) := by
  induction bs generalizing a with
  | nil => rw [pointsToBytesRO_nil]; exact emp_sepConj emp
  | cons b bs ih =>
    rw [pointsToBytesRO_cons]
    exact sepConj_dup (pointsTo8RO_dup a b) (ih (a + 1#64))

/-- Contiguous 64-bit word-list read-only points-to is duplicable. -/
@[simp]
theorem pointsToWords64RO_dup (a : BitVec 64) (ws : List (BitVec 64)) :
    ((a ↦₆₄ᵣ* ws) ∗ (a ↦₆₄ᵣ* ws)) = (a ↦₆₄ᵣ* ws) := by
  induction ws generalizing a with
  | nil => exact emp_sepConj emp
  | cons w ws ih =>
    rw [pointsToWords64RO_cons]
    exact sepConj_dup (pointsTo64RO_dup a w) (ih (a + 8#64))

/-- `regionBlockRO` is duplicable. -/
@[simp]
theorem regionBlockRO_dup (b : BitVec 64) (n : Nat) (m : Memory) :
    (regionBlockRO b n m ∗ regionBlockRO b n m) = regionBlockRO b n m := by
  ext h
  simp only [SepProp.holds_sepConj_iff, holds_regionBlockRO_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, rfl, rfl⟩
    exact Heap.union_self (regionHeapRO b n m)
  · intro hp
    have hp' : h = regionHeapRO b n m := hp
    subst hp'
    refine ⟨regionHeapRO b n m, regionHeapRO b n m, Heap.Disjoint.of_phys_left rfl rfl fun x => ?_,
      (Heap.union_self (regionHeapRO b n m)).symm, rfl, rfl⟩
    dsimp [regionHeapRO]
    by_cases hx : InRegion b n x
    · simp [hx]
    · simp [hx]

/-- `P` asserts read-only access to the bytes `[base, base + len)`, whose contents are described
    by `Φ` (a predicate that only depends on the bytes of the region). -/
structure IsBlockRO (P : SepProp) (base : BitVec 64) (len : Nat) (Φ : Memory → Prop) : Prop where
  iff : ∀ h : Heap, P h ↔ ∃ m, Φ m ∧ h = regionHeapRO base len m
  congr : ∀ m m' : Memory, (∀ a, InRegion base len a → m'.read8 a = m.read8 a) → Φ m → Φ m'

namespace IsBlockRO

variable {P Q : SepProp} {b b' : BitVec 64} {n : Nat} {Φ Ψ : Memory → Prop}

theorem regionHeapRO_matches (b : BitVec 64) (n : Nat) (m : Memory)
    (hr : m.Readable b n) : (regionHeapRO b n m).Matches m := by
  refine Heap.Matches.of_phys rfl rfl fun a c h => ?_
  simp only [regionHeapRO] at h
  split at h
  · rename_i hin
    injection h with h
    subst h
    obtain ⟨hpr, hlf⟩ := hr a hin
    exact ⟨rfl, hpr, hlf⟩
  · contradiction

/-- Reading a read-only block: `m ⊨ P ∗ R` implies the content description `Φ m`. -/
theorem read (hb : IsBlockRO P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R) : Φ m := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨m₀, hΦ, rfl⟩ := (hb.iff _).mp hp
  exact hb.congr m₀ m
    (fun a ha => ((Heap.Matches.of_union_left hm).1 a (.ro (m₀.read8 a)) (by simp [regionHeapRO, ha])).1) hΦ

/-- Every byte of a read-only block has read permission `(m.perm a).r = true`. -/
theorem perm_r (hb : IsBlockRO P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R)
    {a : BitVec 64} (ha : InRegion b n a) : (m.perm a).r = true := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨m₀, -, rfl⟩ := (hb.iff _).mp hp
  exact ((Heap.Matches.of_union_left hm).1 a (.ro (m₀.read8 a)) (by simp [regionHeapRO, ha])).2.1

/-- Every byte of a read-only block has `isLazyFree = false`. -/
theorem isLazyFree_false (hb : IsBlockRO P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R)
    {a : BitVec 64} (ha : InRegion b n a) : m.isLazyFree a = false := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨m₀, -, rfl⟩ := (hb.iff _).mp hp
  exact ((Heap.Matches.of_union_left hm).1 a (.ro (m₀.read8 a)) (by simp [regionHeapRO, ha])).2.2

/-- A read-only block is readable. -/
theorem canRead (hb : IsBlockRO P b n Φ) (hn : n ≤ 2 ^ 64) {m : Memory} {R : SepProp}
    (h : m ⊨ P ∗ R) : m.canRead b n = true := by
  simp only [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff]
  exact ⟨fun i hi => hb.perm_r h (inRegion_base_add b n i hi hn),
    fun i hi => hb.isLazyFree_false h (inRegion_base_add b n i hi hn)⟩

/-- A sub-range `[a, a + k)` of a read-only block is readable. -/
theorem canRead_sub (hb : IsBlockRO P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R)
    {a : BitVec 64} {k : Nat} (hk : (a - b).toNat + k ≤ n) (hn : n ≤ 2 ^ 64) :
    m.canRead a k = true := by
  simp only [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff]
  exact ⟨fun i hi => hb.perm_r h (IsBlock.inRegion_sub_range hk hn hi),
    fun i hi => hb.isLazyFree_false h (IsBlock.inRegion_sub_range hk hn hi)⟩

/-- Re-describe a read-only block (base address up to equality, contents up to equivalence). -/
theorem cast (hb : IsBlockRO P b n Φ) (hbase : b = b') (hΦ : ∀ m, Φ m ↔ Ψ m) :
    IsBlockRO P b' n Ψ := by
  subst hbase
  exact ⟨fun h => (hb.iff h).trans (exists_congr fun m => and_congr_left fun _ => hΦ m),
    fun m m' hag h => (hΦ m').mp (hb.congr m m' hag ((hΦ m).mpr h))⟩

/-- Adjacent read-only blocks `[a, a + n)` and `[a + n, a + n + k)` compose into `[a, a + n + k)`. -/
theorem sepConj {a a' : BitVec 64} {k : Nat} {Φ₁ Φ₂ : Memory → Prop}
    (hP : IsBlockRO P a n Φ₁) (hQ : IsBlockRO Q a' k Φ₂)
    (ha : a' = a + BitVec.ofNat 64 n) (hnk : n + k ≤ 2 ^ 64) :
    IsBlockRO (P ∗ Q) a (n + k) (fun m => Φ₁ m ∧ Φ₂ m) := by
  have hs := fun x => IsBlock.inRegion_append (x := x) ha hnk
  refine ⟨fun h => ⟨?_, ?_⟩, fun m m' hag ⟨h₁, h₂⟩ =>
    ⟨hP.congr m m' (fun x hx => hag x ((hs x).1.mpr (Or.inl hx))) h₁,
     hQ.congr m m' (fun x hx => hag x ((hs x).1.mpr (Or.inr hx))) h₂⟩⟩
  · intro hh
    obtain ⟨h₁, h₂, _, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
    obtain ⟨m₁, hΦ₁, rfl⟩ := (hP.iff _).mp hp
    obtain ⟨m₂, hΦ₂, rfl⟩ := (hQ.iff _).mp hq
    let m : Memory := Memory.ofFn fun x => if InRegion a n x then m₁.read8 x else m₂.read8 x
    have hm : ∀ x, m.read8 x = if InRegion a n x then m₁.read8 x else m₂.read8 x :=
      fun _ => Memory.read8_ofFn _ _ _
    refine ⟨m, ⟨hP.congr m₁ m (fun x hx => by simp [hm, hx]) hΦ₁,
      hQ.congr m₂ m (fun x hx => by
        have : ¬InRegion a n x := fun h => (hs x).2 ⟨h, hx⟩
        simp [hm, this]) hΦ₂⟩, ?_⟩
    refine Heap.ext_phys fun x => ?_
    by_cases h₁ : InRegion a n x
    · simp [Heap.union, regionHeapRO, hm, h₁, (hs x).1.mpr (Or.inl h₁)]
    · by_cases h₂ : InRegion a' k x <;> simp [Heap.union, regionHeapRO, hm, h₁, h₂, (hs x).1]
  · rintro ⟨m, ⟨hΦ₁, hΦ₂⟩, rfl⟩
    refine SepProp.holds_sepConj_iff.mpr ⟨regionHeapRO a n m, regionHeapRO a' k m, Heap.Disjoint.of_phys_left rfl rfl fun x => ?_, ?_,
      (hP.iff _).mpr ⟨m, hΦ₁, rfl⟩, (hQ.iff _).mpr ⟨m, hΦ₂, rfl⟩⟩
    · by_cases h₁ : InRegion a n x
      · have : ¬InRegion a' k x := fun h₂ => (hs x).2 ⟨h₁, h₂⟩
        exact Or.inr (Or.inl (by simp [regionHeapRO, this]))
      · exact Or.inl (by simp [regionHeapRO, h₁])
    · refine Heap.ext_phys fun x => ?_
      by_cases h₁ : InRegion a n x
      · simp [Heap.union, regionHeapRO, h₁, (hs x).1.mpr (Or.inl h₁)]
      · by_cases h₂ : InRegion a' k x <;> simp [Heap.union, regionHeapRO, h₁, h₂, (hs x).1]

theorem pointsTo8RO (a : BitVec 64) (v : BitVec 8) :
    IsBlockRO (a ↦₈ᵣ v) a 1 (fun m => m.read8 a = v) := by
  have hreg : ∀ x, InRegion a 1 x ↔ x = a := fun x => by
    simp only [InRegion]; constructor <;> intro h <;> bv_arith
  refine ⟨fun h => ⟨fun hp => ⟨(default : Memory).write8 a v, Memory.read8_write8_same _ _ _, ?_⟩, ?_⟩,
    fun m m' hag hm => (hag a ((hreg a).mpr rfl)).trans hm⟩
  · have hp : h = Heap.singletonRO a v := holds_pointsTo8RO_iff.mp hp
    subst hp
    refine Heap.ext_phys fun x => ?_
    by_cases hx : x = a <;> simp [Heap.singletonRO, regionHeapRO, hreg, hx]
  · rintro ⟨m, rfl, rfl⟩
    rw [holds_pointsTo8RO_iff]
    refine Heap.ext_phys fun x => ?_
    by_cases hx : x = a <;> simp [Heap.singletonRO, regionHeapRO, hreg, hx]

theorem regionBlockRO (b : BitVec 64) (n : Nat) (m₀ : Memory) :
    IsBlockRO (regionBlockRO b n m₀) b n (fun m => ∀ x, InRegion b n x → m.read8 x = m₀.read8 x) := by
  refine ⟨fun h => ⟨fun hp => ⟨m₀, fun _ _ => rfl, holds_regionBlockRO_iff.mp hp⟩, ?_⟩,
    fun m m' hag hm x hx => (hag x hx).trans (hm x hx)⟩
  rintro ⟨m, hm, rfl⟩
  rw [holds_regionBlockRO_iff]
  refine Heap.ext_phys fun x => ?_
  simp only [regionHeapRO]
  split <;> simp_all

theorem pointsTo16RO (a : BitVec 64) (v : BitVec 16) :
    IsBlockRO (a ↦₁₆ᵣ v) a 2 (fun m => m.read16 a = v) :=
  ((pointsTo8RO _ _).sepConj (pointsTo8RO _ _) (by bv_arith) (by decide)).cast (by bv_arith) fun m => by
    simp only [Memory.read16]
    generalize m.read8 (a + 0#64) = x0
    generalize m.read8 (a + 1#64) = x1
    bv_bits

theorem pointsTo32RO (a : BitVec 64) (v : BitVec 32) :
    IsBlockRO (a ↦₃₂ᵣ v) a 4 (fun m => m.read32 a = v) :=
  ((pointsTo8RO _ _).sepConj ((pointsTo8RO _ _).sepConj ((pointsTo8RO _ _).sepConj (pointsTo8RO _ _)
    (by bv_arith) (by decide)) (by bv_arith) (by decide)) (by bv_arith) (by decide)).cast
    (by bv_arith) fun m => by
    simp only [Memory.read32]
    generalize m.read8 (a + 0#64) = x0
    generalize m.read8 (a + 1#64) = x1
    generalize m.read8 (a + 2#64) = x2
    generalize m.read8 (a + 3#64) = x3
    bv_bits

theorem pointsTo64RO (a : BitVec 64) (v : BitVec 64) :
    IsBlockRO (a ↦₆₄ᵣ v) a 8 (fun m => m.read64 a = v) :=
  ((pointsTo8RO _ _).sepConj ((pointsTo8RO _ _).sepConj ((pointsTo8RO _ _).sepConj ((pointsTo8RO _ _).sepConj
    ((pointsTo8RO _ _).sepConj ((pointsTo8RO _ _).sepConj ((pointsTo8RO _ _).sepConj (pointsTo8RO _ _)
    (by bv_arith) (by decide)) (by bv_arith) (by decide)) (by bv_arith) (by decide))
    (by bv_arith) (by decide)) (by bv_arith) (by decide)) (by bv_arith) (by decide))
    (by bv_arith) (by decide)).cast (by bv_arith) fun m => by
    simp only [Memory.read64]
    generalize m.read8 (a + 0#64) = x0
    generalize m.read8 (a + 1#64) = x1
    generalize m.read8 (a + 2#64) = x2
    generalize m.read8 (a + 3#64) = x3
    generalize m.read8 (a + 4#64) = x4
    generalize m.read8 (a + 5#64) = x5
    generalize m.read8 (a + 6#64) = x6
    generalize m.read8 (a + 7#64) = x7
    bv_bits

theorem pointsTo128RO (a : BitVec 64) (v : BitVec 128) :
    IsBlockRO (a ↦₁₂₈ᵣ v) a 16 (fun m => m.read128 a = v) :=
  ((pointsTo64RO _ _).sepConj (pointsTo64RO _ _) (by bv_arith) (by decide)).cast rfl fun m => by
    simp only [Memory.read128]
    generalize m.read64 a = lo
    generalize m.read64 (a + 8#64) = hi
    bv_bits

theorem pointsToBytesRO (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length ≤ 2 ^ 64) :
    IsBlockRO (a ↦ᵣ bs) a bs.length (fun m => m.readBytes a bs.length = bs) := by
  induction bs generalizing a with
  | nil =>
    rw [pointsToBytesRO_nil]
    have hr : ∀ m, regionHeapRO a 0 m = Heap.empty := fun m => by
      refine Heap.ext_phys fun x => ?_
      simp [regionHeapRO, InRegion, Heap.empty]
    refine ⟨fun h => ⟨fun hp => ⟨default, by simp, ?_⟩, ?_⟩,
      fun _ _ _ h => h⟩
    · rw [SepProp.holds_emp_iff] at hp; simp [hp, hr]
    · rintro ⟨m, -, rfl⟩; rw [SepProp.holds_emp_iff]; simp [hr]
  | cons x bs ih =>
    rw [pointsToBytesRO_cons]
    have hlen' : bs.length ≤ 2 ^ 64 := by simp at hlen; omega
    have hb := (IsBlockRO.pointsTo8RO a x).sepConj (ih (a + 1#64) hlen') (by bv_arith)
      (by simp at hlen; omega)
    have e : 1 + bs.length = (x :: bs).length := by simp; omega
    rw [e] at hb
    refine hb.cast rfl fun m => ?_
    simp only [List.length_cons, Memory.readBytes, List.cons.injEq]

end IsBlockRO

/-- Weakening a read-write block `P` (`IsBlock P b n Φ`) to its read-only counterpart `P_ro`
    (`IsBlockRO P_ro b n Φ`) under `m ⊨ · ∗ R`. -/
theorem IsBlock.toRO {P P_ro : SepProp} {b : BitVec 64} {n : Nat} {Φ : Memory → Prop}
    (hb : IsBlock P b n Φ) (hro : IsBlockRO P_ro b n Φ)
    {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R) : m ⊨ P_ro ∗ R := by
  have hΦ : Φ m := hb.read h
  obtain ⟨_, ⟨h₁, hR, hd, rfl, hp, hr⟩, hm⟩ := satSep_iff.mp h
  have hcov := hb.covers hp
  have hm₁ := Heap.Matches.of_union_left hm
  have hmR := Heap.Matches.of_union_right hd hm
  have hperm_r : m.Readable b n := by
    intro a ha
    obtain ⟨v, hv⟩ := hcov a ha
    obtain ⟨-, hpm, hlf⟩ := hm₁.1 a (.rw v) hv
    exact ⟨by rw [hpm]; rfl, hlf⟩
  refine satSep_iff.mpr ⟨(regionHeapRO b n m).union hR,
    ⟨regionHeapRO b n m, hR, Heap.Disjoint.of_phys_left rfl rfl fun x => ?_, rfl, (hro.iff _).mpr ⟨m, hΦ, rfl⟩, hr⟩,
    Heap.Matches.union (IsBlockRO.regionHeapRO_matches b n m hperm_r) hmR⟩
  by_cases hx : InRegion b n x
  · obtain ⟨v, hv⟩ := hcov x hx
    rcases hd.1 x with h1 | h2 | ⟨_, h1, _⟩
    · rw [hv] at h1; contradiction
    · exact Or.inr (Or.inl h2)
    · rw [hv] at h1; cases h1
  · exact Or.inl (by simp [regionHeapRO, hx])

theorem Satisfies.pointsTo64_to_ro {m : Memory} {a : BitVec 64} {v : BitVec 64} {R : SepProp}
    (h : m ⊨ (a ↦₆₄ v) ∗ R) : m ⊨ (a ↦₆₄ᵣ v) ∗ R :=
  (IsBlock.pointsTo64 a v).toRO (IsBlockRO.pointsTo64RO a v) h

theorem Satisfies.pointsToBytes_to_ro {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ (a ↦ₛ bs) ∗ R) : m ⊨ (a ↦ᵣ bs) ∗ R := by
  have ⟨hlen, _⟩ := (IsBlock.pointsToBytes a bs).read h
  exact ((IsBlock.pointsToBytes a bs).cast rfl
    (fun m' => ⟨fun ⟨_, h2⟩ => h2, fun h2 => ⟨hlen, h2⟩⟩)).toRO
    (IsBlockRO.pointsToBytesRO a bs hlen) h

/-- Introduce any read-only block `P_ro` (`IsBlockRO P_ro base len Φ`) into `m ⊨ P` whenever
    `Φ m` holds and `[base, base + len)` is mapped read-only (`m.RO base len`), without any
    `DisjointRegions` premise. -/
theorem IsBlockRO.intro_of_ro {P_ro P : SepProp} {base : BitVec 64} {len : Nat} {Φ : Memory → Prop}
    (hblk : IsBlockRO P_ro base len Φ)
    {m : Memory} (hro : m.RO base len) (hΦ : Φ m) (hP : m ⊨ P) :
    m ⊨ P_ro ∗ P := by
  obtain ⟨hp, hP_hp, hm⟩ := SepProp.satisfies_iff.mp hP
  have hperm_r : m.Readable base len := by
    intro a ha
    have ⟨hro_a, hlf_a⟩ := hro a ha
    exact ⟨by rw [hro_a]; rfl, hlf_a⟩
  have hm_ro : (regionHeapRO base len m).Matches m :=
    IsBlockRO.regionHeapRO_matches base len m hperm_r
  have hdisj : (regionHeapRO base len m).Disjoint hp := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
    by_cases ha : InRegion base len a
    · cases hpa : hp.phys a with
      | none => exact Or.inr (Or.inl rfl)
      | some c =>
        cases c with
        | rw b =>
          have hrw := (hm.1 a (.rw b) hpa).2.1
          have hro_a := (hro a ha).1
          rw [hrw] at hro_a
          cases hro_a
        | ro b =>
          have hb := (hm.1 a (.ro b) hpa).1
          subst hb
          exact Or.inr (Or.inr ⟨m.read8 a, by simp [regionHeapRO, ha], rfl⟩)
        | protNone b =>
          have hpn := (hm.1 a (.protNone b) hpa).2.1
          have hro_a := (hro a ha).1
          rw [hpn] at hro_a
          cases hro_a
        | lazy =>
          have hrw := hm.1 a .lazy hpa
          have hro_a := (hro a ha).1
          rw [hrw] at hro_a
          cases hro_a
        | protNoneLazy =>
          have hpn := hm.1 a .protNoneLazy hpa
          have hro_a := (hro a ha).1
          rw [hpn] at hro_a
          cases hro_a
    · exact Or.inl (by simp [regionHeapRO, ha])
  exact satSep_iff.mpr ⟨(regionHeapRO base len m).union hp,
    ⟨regionHeapRO base len m, hp, hdisj, rfl, (hblk.iff _).mpr ⟨m, hΦ, rfl⟩, hP_hp⟩,
    Heap.Matches.union hm_ro hm⟩

/-- Introduce `(base ↦ᵣ bs)` onto any assertion `P` satisfied by `m` whenever `[base, base + bs.length)`
    is mapped read-only (`m.RO base bs.length`) and holds bytes `bs` (`m.readBytes base bs.length = bs`). -/
theorem Satisfies.rodata_intro {m : Memory} {base : BitVec 64} {bs : List (BitVec 8)} {P : SepProp}
    (hro : m.RO base bs.length)
    (hread : m.readBytes base bs.length = bs)
    (hlen : bs.length ≤ 2 ^ 64 := by decide)
    (hP : m ⊨ P) :
    m ⊨ (base ↦ᵣ bs) ∗ P :=
  (IsBlockRO.pointsToBytesRO base bs hlen).intro_of_ro hro hread hP

theorem Satisfies.rodata8_intro {m : Memory} {a : BitVec 64} {v : BitVec 8} {P : SepProp}
    (hro : m.RO a 1) (hread : m.read8 a = v) (hP : m ⊨ P) :
    m ⊨ (a ↦₈ᵣ v) ∗ P :=
  (IsBlockRO.pointsTo8RO a v).intro_of_ro hro hread hP

theorem Satisfies.rodata16_intro {m : Memory} {a : BitVec 64} {v : BitVec 16} {P : SepProp}
    (hro : m.RO a 2) (hread : m.read16 a = v) (hP : m ⊨ P) :
    m ⊨ (a ↦₁₆ᵣ v) ∗ P :=
  (IsBlockRO.pointsTo16RO a v).intro_of_ro hro hread hP

theorem Satisfies.rodata64_intro {m : Memory} {a v : BitVec 64} {P : SepProp}
    (hro : m.RO a 8) (hread : m.read64 a = v) (hP : m ⊨ P) :
    m ⊨ (a ↦₆₄ᵣ v) ∗ P :=
  (IsBlockRO.pointsTo64RO a v).intro_of_ro hro hread hP

/-! ## Read-Write Regions (`Memory.RW`) -/

/-- A sub-range `[a, a + k)` of a read-write region `[b, b + n)` is writable. -/
theorem _root_.Arm64.Memory.RW.canWrite_sub {m : Memory} {b : BitVec 64} {n : Nat} (h : m.RW b n)
    {a : BitVec 64} {k : Nat} (hk : (a - b).toNat + k ≤ n) (hn : n ≤ 2 ^ 64) :
    m.canWrite a k = true := by
  unfold Memory.canWrite
  rw [Memory.allPerm_iff]
  intro i hi
  rw [(Memory.permNoLazy_eq_some_rw_iff.mp (h _ (IsBlock.inRegion_sub_range hk hn hi))).1]
  rfl

/-- A sub-range `[a, a + k)` of a read-write region `[b, b + n)` is readable. -/
theorem _root_.Arm64.Memory.RW.canRead_sub {m : Memory} {b : BitVec 64} {n : Nat} (h : m.RW b n)
    {a : BitVec 64} {k : Nat} (hk : (a - b).toNat + k ≤ n) (hn : n ≤ 2 ^ 64) :
    m.canRead a k = true := by
  simp only [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [(Memory.permNoLazy_eq_some_rw_iff.mp (h _ (IsBlock.inRegion_sub_range hk hn hi))).1]; rfl
  · exact (Memory.permNoLazy_eq_some_rw_iff.mp (h _ (IsBlock.inRegion_sub_range hk hn hi))).2

/-- A sub-region `[a, a + k)` of a read-write region `[b, b + n)` is read-write. -/
theorem _root_.Arm64.Memory.RW.sub {m : Memory} {b : BitVec 64} {n : Nat} (h : m.RW b n)
    {a : BitVec 64} {k : Nat} (hk : (a - b).toNat + k ≤ n) : m.RW a k := by
  intro x hx
  apply h
  simp only [InRegion] at hx ⊢
  have e : x - b = (x - a) + (a - b) := by bv_arith
  rw [e, BitVec.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

/-- `Memory.RW` is preserved when permissions are unchanged and non-`lazyFree` bytes stay non-`lazyFree`. -/
theorem _root_.Arm64.Memory.RW.of_perm_eq {m m' : Memory} (hp : m'.perm = m.perm)
    (hlf : ∀ a, m.isLazyFree a = false → m'.isLazyFree a = false)
    {b : BitVec 64} {n : Nat} (h : m.RW b n) : m'.RW b n := by
  intro a ha
  obtain ⟨hpm, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h a ha)
  exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨(congrFun hp a).trans hpm, hlf a hlf_a⟩

/-- `Memory.RW` is preserved across any `AgreesOutside` store transition. -/
theorem _root_.Arm64.Memory.RW.of_agreesOutside {m m' : Memory} {base : BitVec 64} {len : Nat}
    (hag : AgreesOutside m m' base len) {b : BitVec 64} {n : Nat} (h : m.RW b n) : m'.RW b n :=
  h.of_perm_eq hag.perm_eq (fun _ => hag.isLazyFree_false)

/-- `Memory.RW` is preserved across `write64`. -/
theorem _root_.Arm64.Memory.RW.write64 {m : Memory} (addr val : BitVec 64)
    {b : BitVec 64} {n : Nat} (h : m.RW b n) : (m.write64 addr val).RW b n :=
  h.of_perm_eq (Memory.perm_write64 m addr val) (fun _ => Memory.isLazyFree_write64_of_false addr val)

/-- A read-write region is readable. -/
theorem _root_.Arm64.Memory.RW.readable {m : Memory} {b : BitVec 64} {n : Nat} (h : m.RW b n) :
    m.Readable b n := by
  intro a ha
  obtain ⟨hpm, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h a ha)
  exact ⟨by rw [hpm]; rfl, hlf⟩

/-- A sub-region `[a, a + k)` of a read-only region `[b, b + n)` is read-only. -/
theorem _root_.Arm64.Memory.RO.sub {m : Memory} {b : BitVec 64} {n : Nat} (h : m.RO b n)
    {a : BitVec 64} {k : Nat} (hk : (a - b).toNat + k ≤ n) : m.RO a k := by
  intro x hx
  apply h
  simp only [InRegion] at hx ⊢
  have e : x - b = (x - a) + (a - b) := by bv_arith
  rw [e, BitVec.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

/-- A sub-range `[a, a + k)` of a readable region `[b, b + n)` is readable. -/
theorem _root_.Arm64.Memory.Readable.canRead_sub {m : Memory} {b : BitVec 64} {n : Nat}
    (h : m.Readable b n) {a : BitVec 64} {k : Nat} (hk : (a - b).toNat + k ≤ n)
    (hn : n ≤ 2 ^ 64) : m.canRead a k = true := by
  simp only [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff]
  exact ⟨fun i hi => (h _ (IsBlock.inRegion_sub_range hk hn hi)).1,
    fun i hi => (h _ (IsBlock.inRegion_sub_range hk hn hi)).2⟩

/-- `Memory.Readable` is preserved when permissions are unchanged and non-`lazyFree` bytes stay non-`lazyFree`. -/
theorem _root_.Arm64.Memory.Readable.of_perm_eq {m m' : Memory} (hp : m'.perm = m.perm)
    (hlf : ∀ a, m.isLazyFree a = false → m'.isLazyFree a = false)
    {b : BitVec 64} {n : Nat} (h : m.Readable b n) : m'.Readable b n :=
  fun a ha => ⟨by rw [hp]; exact (h a ha).1, hlf a (h a ha).2⟩

theorem _root_.Arm64.Memory.unmapped_of_canMap {m : Memory} {base a : BitVec 64} {len : Nat}
    (h : m.canMap base len = true) (ha : InRegion base len a) :
    (m.perm a).mapped = false := by
  have hi := (Memory.allPerm_iff m (fun p => !p.mapped) base len).1 h (a - base).toNat ha
  have e : base + BitVec.ofNat 64 (a - base).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_arith
  rw [e, Bool.not_eq_true'] at hi
  exact hi

theorem _root_.Arm64.Memory.perm_mapZero_of_canMap {m : Memory} {base a : BitVec 64} {len : Nat}
    (h : m.canMap base len = true) (ha : InRegion base len a) :
    (m.mapZero base len).perm a = some Perm.rw := by
  have ha' : (a - base).toNat < len := ha
  rw [Memory.perm_mapZero, decide_eq_true ha', m.unmapped_of_canMap h ha]
  rfl

theorem _root_.Arm64.Memory.read8_mapZero_of_canMap {m : Memory} {base a : BitVec 64} {len : Nat}
    (h : m.canMap base len = true) (ha : InRegion base len a) :
    (m.mapZero base len).read8 a = 0#8 := by
  have ha' : (a - base).toNat < len := ha
  rw [Memory.read8_mapZero, decide_eq_true ha', m.unmapped_of_canMap h ha]
  rfl

theorem _root_.Arm64.Memory.rw_mapZero_of_canMap {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m.canMap base len = true) :
    (m.mapZero base len).RW base len := by
  intro a ha
  refine Memory.permNoLazy_eq_some_rw_iff.mpr ⟨m.perm_mapZero_of_canMap h ha, ?_⟩
  rw [Memory.isLazyFree_mapZero]
  exact Memory.isLazyFree_eq_false_of_unmapped (m.unmapped_of_canMap h ha)

theorem _root_.Arm64.Memory.canWrite_mapZero_sub {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m.canMap base len = true) {a : BitVec 64} {k : Nat}
    (hk : (a - base).toNat + k ≤ len) (hlen : len ≤ 2 ^ 64) :
    (m.mapZero base len).canWrite a k = true :=
  (m.rw_mapZero_of_canMap h).canWrite_sub hk hlen

theorem _root_.Arm64.Memory.canRead_mapZero_sub {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m.canMap base len = true) {a : BitVec 64} {k : Nat}
    (hk : (a - base).toNat + k ≤ len) (hlen : len ≤ 2 ^ 64) :
    (m.mapZero base len).canRead a k = true :=
  (m.rw_mapZero_of_canMap h).canRead_sub hk hlen

theorem mappedHeap_matches (base : BitVec 64) (len : Nat) (m : Memory)
    (hmap : ∀ a, InRegion base len a → (m.perm a).mapped = true ∧ m.isAnon a = true) :
    (mappedHeap base len).Matches m := by
  refine ⟨fun _ _ h => by contradiction, Heap.GhostValid.of_phys rfl rfl, fun a ha => ?_⟩
  simp only [mappedHeap, decide_eq_true_eq] at ha
  exact hmap a ha

/-- Mapping an unmapped region `[base, base + len)` with `Memory.mapZero` (`mmap`) adds both
    `memRegion base len` and the virtual-address mapping reservation token `memMapped base len`
    alongside any existing assertion `P` (since every byte or mapping token in `P` is already
    mapped in `m`, hence outside the unmapped `[base, base + len)`). -/
theorem Satisfies.mapZero_mapped {P : SepProp} {m : Memory} (h : m ⊨ P) {base : BitVec 64} {len : Nat}
    (hmap : m.canMap base len = true) :
    m.mapZero base len ⊨ memRegion base len ∗ memMapped base len ∗ P := by
  obtain ⟨hp, hP, hm⟩ := SepProp.satisfies_iff.mp h
  let m' := m.mapZero base len
  have hp_out : ∀ a, InRegion base len a → hp.phys a = none ∧ hp.mapped a = false := by
    intro a ha
    have hunm := m.unmapped_of_canMap hmap ha
    refine ⟨?_, ?_⟩
    · cases hpa : hp.phys a with
      | none => rfl
      | some c =>
        exfalso
        cases c with
        | rw v =>
          have hperm := (hm.1 a (.rw v) hpa).2.1
          rw [hperm] at hunm; revert hunm; decide
        | ro v =>
          have hperm := (hm.1 a (.ro v) hpa).2.1
          cases m.perm a <;> simp_all
        | protNone v =>
          have hperm := (hm.1 a (.protNone v) hpa).2.1
          rw [hperm] at hunm; revert hunm; decide
        | lazy =>
          have hperm := hm.1 a .lazy hpa
          rw [hperm] at hunm; revert hunm; decide
        | protNoneLazy =>
          have hperm := hm.1 a .protNoneLazy hpa
          rw [hperm] at hunm; revert hunm; decide
    · cases hma : hp.mapped a with
      | false => rfl
      | true =>
        have hperm := (hm.2.2 a hma).1
        rw [hperm] at hunm; contradiction
  have hdisj_mp : (mappedHeap base len).Disjoint hp := by
    refine ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl,
      fun _ _ _ _ hc => by rcases hc with ⟨h1, _⟩ | ⟨_, h1⟩ <;> contradiction,
      fun a => ?_⟩
    by_cases ha : InRegion base len a
    · exact Or.inr (hp_out a ha).2
    · exact Or.inl (by simp [mappedHeap, ha])
  have hdisj_reg : (regionHeap base len m').Disjoint ((mappedHeap base len).union hp) := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
    by_cases ha : InRegion base len a
    · exact Or.inr (Or.inl (by simp [Heap.union, mappedHeap, (hp_out a ha).1]))
    · exact Or.inl (by simp [regionHeap, ha])
  have hm_reg : (regionHeap base len m').Matches m' :=
    IsBlock.regionHeap_matches base len m' (m.rw_mapZero_of_canMap hmap)
  have hm_map : (mappedHeap base len).Matches m' := by
    refine mappedHeap_matches base len m' fun a ha => ⟨?_, ?_⟩
    · rw [m.perm_mapZero_of_canMap hmap ha]; rfl
    · have ha' : (a - base).toNat < len := ha
      dsimp [m']
      rw [Memory.isAnon_mapZero, decide_eq_true ha', m.unmapped_of_canMap hmap ha]
      rfl
  have hm_hp : hp.Matches m' := by
    refine ⟨fun a c hpa => ?_, hm.2.1, fun a hma => ?_⟩
    · cases c with
      | rw v =>
        obtain ⟨hr, hperm, hlf⟩ := hm.1 a (.rw v) hpa
        have hmapped : (m.perm a).mapped = true := by rw [hperm]; rfl
        exact ⟨by simp [m', Memory.read8_mapZero, hmapped, hr],
          by simp [m', Memory.perm_mapZero, hperm],
          by simp [m', hlf]⟩
      | ro v =>
        obtain ⟨hr, hperm, hlf⟩ := hm.1 a (.ro v) hpa
        have hmapped : (m.perm a).mapped = true := by rcases hp' : m.perm a with _ | q <;> simp_all
        exact ⟨by simp [m', Memory.read8_mapZero, hmapped, hr],
          by simp [m', Memory.perm_mapZero, hmapped, hperm],
          by simp [m', hlf]⟩
      | protNone v =>
        obtain ⟨hr, hperm, hlf⟩ := hm.1 a (.protNone v) hpa
        have hmapped : (m.perm a).mapped = true := by rw [hperm]; rfl
        exact ⟨by simp [m', Memory.read8_mapZero, hmapped, hr],
          by simp [m', Memory.perm_mapZero, hperm],
          by simp [m', hlf]⟩
      | lazy =>
        have hperm := hm.1 a .lazy hpa
        simp [m', Memory.perm_mapZero, hperm]
      | protNoneLazy =>
        have hperm := hm.1 a .protNoneLazy hpa
        simp [m', Memory.perm_mapZero, hperm]
    · obtain ⟨hmapped, hanon⟩ := hm.2.2 a hma
      have hpm : m'.perm a = m.perm a := by simp [m', Memory.perm_mapZero, hmapped]
      have han : m'.isAnon a = m.isAnon a := by simp [m', Memory.isAnon_mapZero, hmapped]
      rw [hpm, han]
      exact ⟨hmapped, hanon⟩
  exact satSep_iff.mpr ⟨(regionHeap base len m').union ((mappedHeap base len).union hp),
    ⟨regionHeap base len m', (mappedHeap base len).union hp, hdisj_reg, rfl, holds_memRegion_iff.mpr ⟨m', rfl⟩,
      SepProp.holds_sepConj_iff.mpr ⟨mappedHeap base len, hp, hdisj_mp, rfl, holds_memMapped_iff.mpr rfl, hP⟩⟩,
    Heap.Matches.union hm_reg (Heap.Matches.union hm_map hm_hp)⟩

/-- Mapping an unmapped region `[base, base + len)` with `Memory.mapZero` (`mmap`) adds a
    separately owned `memRegion base len` alongside any existing assertion `P` (since every
    byte in `P` is already mapped, hence outside the unmapped `[base, base + len)`). -/
theorem Satisfies.mapZero {P : SepProp} {m : Memory} (h : m ⊨ P) {base : BitVec 64} {len : Nat}
    (hmap : m.canMap base len = true) :
    m.mapZero base len ⊨ memRegion base len ∗ P :=
  Satisfies.drop_mid (Satisfies.mapZero_mapped h hmap)

/-- Every read-write region `[base, base + len)` (`len ≤ 2 ^ 64`) satisfies
    `m.allPerm (fun p => !p.frozen) base len = true`. -/
theorem _root_.Arm64.Memory.RW.allPerm_not_frozen {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m.RW base len) (hlen : len ≤ 2 ^ 64) :
    m.allPerm (fun p => !p.frozen) base len = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  have hin : InRegion base len (base + BitVec.ofNat 64 i) := by
    simpa [InRegion] using IsBlock.inRegion_sub_range (a := base) (b := base) (k := len) (n := len)
      (by simp) hlen hi
  rw [(Memory.permNoLazy_eq_some_rw_iff.mp (h _ hin)).1]
  rfl

/-- Every read-write region `[base, base + len)` (`len ≤ 2 ^ 64`) satisfies
    `m.allPerm (·.mapped) base len = true`. -/
theorem _root_.Arm64.Memory.RW.allPerm_mapped {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m.RW base len) (hlen : len ≤ 2 ^ 64) :
    m.allPerm (·.mapped) base len = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  have hin : InRegion base len (base + BitVec.ofNat 64 i) := by
    simpa [InRegion] using IsBlock.inRegion_sub_range (a := base) (b := base) (k := len) (n := len)
      (by simp) hlen hi
  rw [(Memory.permNoLazy_eq_some_rw_iff.mp (h _ hin)).1]
  rfl

/-- Unmapping an owned `memRegion base len` together with its mapping reservation token
    `memMapped base len` via `Memory.unmapNonFrozen` (`munmap`) preserves any separately owned
    assertion `P`. -/
theorem Satisfies.unmapNonFrozen {P : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegion base len ∗ memMapped base len ∗ P) :
    m.unmapNonFrozen base len ⊨ P := by
  obtain ⟨_, ⟨h₁, _, hdisj1, rfl, h1, hrest⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨h₂, hp, hdisj2, rfl, h2, hP⟩ := SepProp.holds_sepConj_iff.mp hrest
  have hcov := (IsBlock.memRegion base len).covers h1
  have h2_eq : h₂ = mappedHeap base len := holds_memMapped_iff.mp h2
  subst h2_eq
  have ⟨_, hd1p⟩ := (Heap.disjoint_union_right hdisj2).mp hdisj1
  have hm_hp := Heap.Matches.of_union_right hdisj2 (Heap.Matches.of_union_right hdisj1 hm)
  refine SepProp.satisfies_iff.mpr ⟨hp, hP, ⟨fun a c hpa => ?_, hm_hp.2.1, fun a hma => ?_⟩⟩
  · have hnot_in : ¬ (a - base).toNat < len := by
      intro hin
      obtain ⟨b, hb1⟩ := hcov a hin
      rcases hd1p.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hb1] at h1; contradiction
      · rw [hpa] at h2; contradiction
      · rw [hb1] at h1; cases h1
    have hr : (m.unmapNonFrozen base len).read8 a = m.read8 a := by
      rw [Memory.read8_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hpm : (m.unmapNonFrozen base len).perm a = m.perm a := by
      rw [Memory.perm_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hlf : (m.unmapNonFrozen base len).isLazyFree a = m.isLazyFree a := by
      rw [Memory.isLazyFree_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hcell := hm_hp.1 a c hpa
    cases c <;> simp only [hr, hpm, hlf] <;> exact hcell
  · have hnot_in : ¬ (a - base).toNat < len := by
      intro hin
      have hin' : InRegion base len a := hin
      rcases hdisj2.2.2.2.2 a with hmap1 | hmap2
      · simp [mappedHeap, hin'] at hmap1
      · rw [hma] at hmap2; contradiction
    have hpm : (m.unmapNonFrozen base len).perm a = m.perm a := by
      rw [Memory.perm_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have han : (m.unmapNonFrozen base len).isAnon a = m.isAnon a := by
      rw [Memory.isAnon_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [hpm, han]
    exact hm_hp.2.2 a hma

@[simp, arm64_norm]
theorem memMapped_zero (base : BitVec 64) : memMapped base 0 = emp := by
  ext h
  simp only [holds_memMapped_iff, SepProp.holds_emp_iff]
  have heq : mappedHeap base 0 = Heap.empty := by
    refine Heap.ext_phys (fun _ => rfl) rfl rfl ?_
    funext x
    simp [mappedHeap, InRegion, Heap.empty]
  rw [heq]

theorem memMapped_split (base : BitVec 64) (n k : Nat) (hnk : n + k ≤ 2 ^ 64) :
    memMapped base (n + k) =
      (memMapped base n ∗ memMapped (base + BitVec.ofNat 64 n) k) := by
  have hs := fun x => IsBlock.inRegion_append (a := base) (n := n) (k := k) (x := x) rfl hnk
  have hdisj : (mappedHeap base n).Disjoint (mappedHeap (base + BitVec.ofNat 64 n) k) := by
    refine ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl,
      fun _ _ _ _ h => (by rcases h with ⟨h1, _⟩ | ⟨_, h1⟩ <;> contradiction),
      fun x => ?_⟩
    by_cases h1 : InRegion base n x
    · have h2 : ¬ InRegion (base + BitVec.ofNat 64 n) k x := fun h2 => (hs x).2 ⟨h1, h2⟩
      exact Or.inr (by simp [mappedHeap, h2])
    · exact Or.inl (by simp [mappedHeap, h1])
  have hunion :
      (mappedHeap base n).union (mappedHeap (base + BitVec.ofNat 64 n) k) =
        mappedHeap base (n + k) := by
    refine Heap.ext_phys (fun _ => rfl) rfl rfl ?_
    funext x
    dsimp [Heap.union, mappedHeap]
    by_cases h1 : InRegion base n x
    · simp [h1, (hs x).1.mpr (Or.inl h1)]
    · by_cases h2 : InRegion (base + BitVec.ofNat 64 n) k x <;> simp [h1, h2, (hs x).1]
  ext h
  simp only [holds_memMapped_iff, SepProp.holds_sepConj_iff]
  constructor
  · rintro rfl
    exact ⟨mappedHeap base n, mappedHeap (base + BitVec.ofNat 64 n) k,
      hdisj, hunion.symm, rfl, rfl⟩
  · rintro ⟨_, _, _, rfl, rfl, rfl⟩
    exact hunion

theorem memMapped_split_le (base : BitVec 64) {k n : Nat} (hkn : k ≤ n) (hn : n ≤ 2 ^ 64) :
    memMapped base n =
      (memMapped base k ∗ memMapped (base + BitVec.ofNat 64 k) (n - k)) := by
  have heq : n = k + (n - k) := (Nat.add_sub_of_le hkn).symm
  conv => lhs; rw [heq]
  exact memMapped_split base k (n - k) (by omega)

theorem memMapped_disjoint_inRegion {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat} :
    memMapped b₁ n₁ ∗ memMapped b₂ n₂ ⊢
      ⌜∀ a, ¬ (InRegion b₁ n₁ a ∧ InRegion b₂ n₂ a)⌝ ∗ memMapped b₁ n₁ ∗ memMapped b₂ n₂ := by
  refine SepProp.entails_iff.mpr fun h hh => ?_
  obtain ⟨h₁, h₂, hd, rfl, e1, e2⟩ := SepProp.holds_sepConj_iff.mp hh
  rw [holds_memMapped_iff] at e1 e2; subst e1 e2
  rw [pure_sepConj]
  refine ⟨fun a ⟨ha1, ha2⟩ => ?_, SepProp.holds_sepConj_iff.mpr
    ⟨mappedHeap b₁ n₁, mappedHeap b₂ n₂, hd, rfl, holds_memMapped_iff.mpr rfl, holds_memMapped_iff.mpr rfl⟩⟩
  rcases hd.2.2.2.2 a with h1 | h2
  · simp [mappedHeap, ha1] at h1
  · simp [mappedHeap, ha2] at h2

theorem memMapped_disjointRegions {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁ := by first | decide | omega)
    (hn₂ : 0 < n₂ := by first | decide | omega) :
    memMapped b₁ n₁ ∗ memMapped b₂ n₂ ⊢
      ⌜DisjointRegions b₁ n₁ b₂ n₂⌝ ∗ memMapped b₁ n₁ ∗ memMapped b₂ n₂ := by
  refine SepProp.entails_iff.mpr fun h hh => ?_
  obtain ⟨h₁, h₂, hd, rfl, e1, e2⟩ := SepProp.holds_sepConj_iff.mp hh
  rw [holds_memMapped_iff] at e1 e2; subst e1 e2
  have hdisj : ∀ a, ¬ (InRegion b₁ n₁ a ∧ InRegion b₂ n₂ a) := by
    intro a ⟨ha1, ha2⟩
    rcases hd.2.2.2.2 a with h1 | h2
    · simp [mappedHeap, ha1] at h1
    · simp [mappedHeap, ha2] at h2
  rw [pure_sepConj]
  refine ⟨⟨?_, ?_⟩, SepProp.holds_sepConj_iff.mpr
    ⟨mappedHeap b₁ n₁, mappedHeap b₂ n₂, hd, rfl, holds_memMapped_iff.mpr rfl, holds_memMapped_iff.mpr rfl⟩⟩
  · apply Classical.byContradiction
    intro hlt
    have hin1 : InRegion b₁ n₁ b₂ := by simp only [InRegion]; omega
    have hin2 : InRegion b₂ n₂ b₂ := by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
    exact hdisj b₂ ⟨hin1, hin2⟩
  · apply Classical.byContradiction
    intro hlt
    have hin2 : InRegion b₂ n₂ b₁ := by simp only [InRegion]; omega
    have hin1 : InRegion b₁ n₁ b₁ := by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
    exact hdisj b₁ ⟨hin1, hin2⟩

theorem Satisfies.disjointRegions_of_memMapped {m : Memory} {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    {R : SepProp} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (h : m ⊨ memMapped b₁ n₁ ∗ (memMapped b₂ n₂ ∗ R)) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  rw [← sepConj_assoc] at h
  have h' := Satisfies.of_sep_left h
  have h'' := Satisfies.mono (memMapped_disjointRegions hn₁ hn₂) h'
  exact ((satisfies_pure_sepConj _ _ m).mp (by simpa [sepConj_assoc] using h'')).1

theorem Satisfies.perm_mapped_of_memMapped {m : Memory} {base : BitVec 64} {len : Nat}
    {R : SepProp} (h : m ⊨ memMapped base len ∗ R)
    {a : BitVec 64} (ha : InRegion base len a) :
    (m.perm a).mapped = true := by
  obtain ⟨_, ⟨_, _, _, rfl, e, _⟩, hm⟩ := satSep_iff.mp h
  rw [holds_memMapped_iff] at e; subst e
  exact ((Heap.Matches.of_union_left hm).2.2 a (by simp [mappedHeap, ha])).1

theorem Satisfies.isAnon_of_memMapped {m : Memory} {base : BitVec 64} {len : Nat}
    {R : SepProp} (h : m ⊨ memMapped base len ∗ R)
    {a : BitVec 64} (ha : InRegion base len a) :
    m.isAnon a = true := by
  obtain ⟨_, ⟨_, _, _, rfl, e, _⟩, hm⟩ := satSep_iff.mp h
  rw [holds_memMapped_iff] at e; subst e
  exact ((Heap.Matches.of_union_left hm).2.2 a (by simp [mappedHeap, ha])).2

theorem Satisfies.allAnon_of_memMapped {m : Memory} {base : BitVec 64} {len : Nat}
    {R : SepProp} (h : m ⊨ memMapped base len ∗ R) :
    m.allAnon base len = true := by
  rw [Memory.allAnon_iff]
  intro i hi
  have hin : InRegion base len (base + BitVec.ofNat 64 i) := by
    simp only [InRegion]
    have hsub : base + BitVec.ofNat 64 i - base = BitVec.ofNat 64 i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]
    rw [hsub, BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi
  exact Satisfies.isAnon_of_memMapped h hin

theorem Satisfies.allAnon_of_memMapped_sub {m : Memory} {base : BitVec 64} {len : Nat}
    {R : SepProp} (h : m ⊨ memMapped base len ∗ R)
    {a : BitVec 64} {k : Nat} (hk : (a - base).toNat + k ≤ len) (hlen : len ≤ 2 ^ 64) :
    m.allAnon a k = true := by
  rw [Memory.allAnon_iff]
  intro i hi
  exact Satisfies.isAnon_of_memMapped h (IsBlock.inRegion_sub_range hk hlen hi)

/-- Replacing an owned `memRegion base len` by zero-filled `PROT_NONE` pages (the memory effect of
    a `MAP_FIXED` `PROT_NONE` `mmap`: `Memory.unmapNonFrozen`, then `Memory.mapZero`, then
    `Memory.setPermNonFrozen base len Perm.protNone`) preserves any separately owned assertion `P`.
    The region itself is given up: its bytes are no longer readable or writable. -/
theorem Satisfies.mmapFixedProtNone {P : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegion base len ∗ P) :
    ((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len Perm.protNone ⊨ P := by
  obtain ⟨_, ⟨h₁, hp, hdisj, rfl, h1, hP⟩, hm⟩ := satSep_iff.mp h
  have hcov := (IsBlock.memRegion base len).covers h1
  have hm_hp := Heap.Matches.of_union_right hdisj hm
  refine SepProp.satisfies_iff.mpr ⟨hp, hP, ⟨fun a c hpa => ?_, hm_hp.2.1, fun a hma => ?_⟩⟩
  rotate_left
  · obtain ⟨hmapped, hanon⟩ := hm_hp.2.2 a hma
    by_cases hin : (a - base).toNat < len
    · by_cases hfr : (m.perm a).frozen = true
      · have hunm_p : (m.unmapNonFrozen base len).perm a = m.perm a := by
          rw [Memory.perm_unmapNonFrozen]; simp [hfr]
        have hunm_a : (m.unmapNonFrozen base len).isAnon a = m.isAnon a := by
          rw [Memory.isAnon_unmapNonFrozen]; simp [hfr]
        have hmz_p : ((m.unmapNonFrozen base len).mapZero base len).perm a = m.perm a := by
          rw [Memory.perm_mapZero, hunm_p]; simp [hmapped]
        have hmz_a : ((m.unmapNonFrozen base len).mapZero base len).isAnon a = m.isAnon a := by
          rw [Memory.isAnon_mapZero, hunm_p, hunm_a]; simp [hmapped]
        have hsp_p : (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len
            Perm.protNone).perm a = m.perm a := by
          rw [Memory.perm_setPermNonFrozen, hmz_p]; simp [hfr]
        rw [hsp_p, Memory.isAnon_setPermNonFrozen_apply, hmz_a]
        exact ⟨hmapped, hanon⟩
      · simp only [Bool.not_eq_true] at hfr
        have hunm : (m.unmapNonFrozen base len).perm a = none := by
          rw [Memory.perm_unmapNonFrozen]; simp only [decide_eq_true hin, hfr]; rfl
        have hmz_p : ((m.unmapNonFrozen base len).mapZero base len).perm a = some Perm.rw := by
          rw [Memory.perm_mapZero, hunm]; simp only [decide_eq_true hin]; rfl
        have hmz_a : ((m.unmapNonFrozen base len).mapZero base len).isAnon a = true := by
          rw [Memory.isAnon_mapZero, hunm]; simp only [decide_eq_true hin]; rfl
        have hsp_p : (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len
            Perm.protNone).perm a = some Perm.protNone := by
          rw [Memory.perm_setPermNonFrozen, hmz_p]; simp only [decide_eq_true hin]; rfl
        rw [hsp_p, Memory.isAnon_setPermNonFrozen_apply]
        exact ⟨rfl, hmz_a⟩
    · have hsp_p : (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len
          Perm.protNone).perm a = m.perm a := by
        rw [Memory.perm_setPermNonFrozen, Memory.perm_mapZero, Memory.perm_unmapNonFrozen]
        simp only [decide_eq_false hin, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have hsp_a : (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len
          Perm.protNone).isAnon a = m.isAnon a := by
        rw [Memory.isAnon_setPermNonFrozen_apply, Memory.isAnon_mapZero, Memory.isAnon_unmapNonFrozen]
        simp only [decide_eq_false hin, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [hsp_p, hsp_a]
      exact ⟨hmapped, hanon⟩
  have hnot_in : ¬ (a - base).toNat < len := by
    intro hin
    obtain ⟨b, hb1⟩ := hcov a hin
    rcases hdisj.1 a with h1 | h2 | ⟨_, h1, _⟩
    · rw [hb1] at h1; contradiction
    · rw [hpa] at h2; contradiction
    · rw [hb1] at h1; cases h1
  have hr : (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len
      Perm.protNone).read8 a = m.read8 a := by
    rw [Memory.read8_setPermNonFrozen, Memory.read8_mapZero, Memory.read8_unmapNonFrozen]
    simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hpm : (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len
      Perm.protNone).perm a = m.perm a := by
    rw [Memory.perm_setPermNonFrozen, Memory.perm_mapZero, Memory.perm_unmapNonFrozen]
    simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hlf : (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len
      Perm.protNone).isLazyFree a = m.isLazyFree a := by
    rw [Memory.isLazyFree_setPermNonFrozen, Memory.isLazyFree_mapZero, Memory.isLazyFree_unmapNonFrozen]
    simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hc := hm_hp.1 a c hpa
  cases c <;> simp only [hr, hpm, hlf] <;> exact hc

theorem AgreesOutside.zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    AgreesOutside m (m.zeroNonFrozen base len) base len := by
  refine ⟨fun a hout => ?_, Memory.perm_zeroNonFrozen m base len, fun a hout => ?_,
    fun a hlf => ?_, fun a han => by simpa using han⟩
  · have hnot_in : ¬ (a - base).toNat < len := (outsideRegion_iff_not_inRegion base len a).mp hout
    rw [Memory.read8_zeroNonFrozen]
    simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · have hnot_in : ¬ (a - base).toNat < len := (outsideRegion_iff_not_inRegion base len a).mp hout
    rw [Memory.isLazyFree_zeroNonFrozen]
    simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · rw [Memory.isLazyFree_zeroNonFrozen]
    split
    · rfl
    · exact hlf

/-- Zero-filling an owned `memRegion base len` via `Memory.zeroNonFrozen` (`madvise` with
    `MADV_DONTNEED`) preserves `memRegion base len ∗ P`. -/
theorem Satisfies.zeroNonFrozen {P : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegion base len ∗ P) :
    m.zeroNonFrozen base len ⊨ memRegion base len ∗ P :=
  (IsBlock.memRegion base len).update (IsBlock.memRegion base len) (Nat.le_refl _) h
    (AgreesOutside.zeroNonFrozen m base len) trivial

/-! ## `PROT_NONE` Block Atoms (`IsBlockProtNone`) and Permission-Transition Bridges

Per Linux `mm/mprotect.c` (`mprotect_fixup` / `change_protection`), `PROT_NONE` pages are
exclusive, non-frozen mapped regions whose underlying physical byte values are preserved across
`mprotect` transitions between `Perm.protNone` and `Perm.rw`, remaining inaccessible to loads,
stores, and instruction fetches when `Perm.protNone`. -/

/-- `P` owns `[base, base + len)` exclusively as `PROT_NONE`, with preserved byte contents
    described by `Φ` (`P h ↔ ∃ m, Φ m ∧ h = regionHeapProtNone base len m`). -/
structure IsBlockProtNone (P : SepProp) (base : BitVec 64) (len : Nat) (Φ : Memory → Prop) : Prop where
  iff : ∀ h : Heap, P h ↔ ∃ m, Φ m ∧ h = regionHeapProtNone base len m
  congr : ∀ m m' : Memory, (∀ a, InRegion base len a → m'.read8 a = m.read8 a) → Φ m → Φ m'

namespace IsBlockProtNone

variable {P Q : SepProp} {b b' : BitVec 64} {n : Nat} {Φ Ψ : Memory → Prop}

theorem regionHeapProtNone_matches (b : BitVec 64) (n : Nat) (m : Memory)
    (hperm : ∀ a, InRegion b n a → m.perm a = some Perm.protNone ∧ m.isLazyFree a = false) :
    (regionHeapProtNone b n m).Matches m := by
  refine Heap.Matches.of_phys rfl rfl fun a c hc => ?_
  by_cases ha : InRegion b n a
  · simp [regionHeapProtNone, ha] at hc
    subst hc
    obtain ⟨hp, hlf⟩ := hperm a ha
    exact ⟨rfl, hp, hlf⟩
  · simp [regionHeapProtNone, ha] at hc

theorem covers (hb : IsBlockProtNone P b n Φ) {h : Heap} (hp : P h) :
    ∀ a, InRegion b n a → ∃ v, h a = some (.protNone v) := by
  obtain ⟨m, -, rfl⟩ := (hb.iff h).mp hp
  exact fun a ha => ⟨m.read8 a, by simp [regionHeapProtNone, ha]⟩

theorem read (hb : IsBlockProtNone P b n Φ) {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R) : Φ m := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨m₀, hΦ, rfl⟩ := (hb.iff _).mp hp
  have hm₁ := Heap.Matches.of_union_left hm
  exact hb.congr m₀ m
    (fun a ha => (hm₁.1 a (.protNone (m₀.read8 a)) (by simp [regionHeapProtNone, ha])).1) hΦ

theorem perm_protNone (hb : IsBlockProtNone P b n Φ) {m : Memory} {R : SepProp}
    (h : m ⊨ P ∗ R) {a : BitVec 64} (ha : InRegion b n a) :
    m.perm a = some Perm.protNone := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨v, hv⟩ := hb.covers hp a ha
  exact ((Heap.Matches.of_union_left hm).1 a (.protNone v) hv).2.1

theorem isLazyFree_false (hb : IsBlockProtNone P b n Φ) {m : Memory} {R : SepProp}
    (h : m ⊨ P ∗ R) {a : BitVec 64} (ha : InRegion b n a) :
    m.isLazyFree a = false := by
  obtain ⟨_, ⟨h₁, _, _, rfl, hp, _⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨v, hv⟩ := hb.covers hp a ha
  exact ((Heap.Matches.of_union_left hm).1 a (.protNone v) hv).2.2

theorem cast (hb : IsBlockProtNone P b n Φ) (hbase : b = b') (hΦ : ∀ m, Φ m ↔ Ψ m) :
    IsBlockProtNone P b' n Ψ := by
  subst hbase
  exact ⟨fun h => (hb.iff h).trans (exists_congr fun m => and_congr_left fun _ => hΦ m),
    fun m m' hag h => (hΦ m').mp (hb.congr m m' hag ((hΦ m).mpr h))⟩

theorem sepConj {a a' : BitVec 64} {k : Nat} {Φ₁ Φ₂ : Memory → Prop}
    (hP : IsBlockProtNone P a n Φ₁) (hQ : IsBlockProtNone Q a' k Φ₂)
    (ha : a' = a + BitVec.ofNat 64 n) (hnk : n + k ≤ 2 ^ 64) :
    IsBlockProtNone (P ∗ Q) a (n + k) (fun m => Φ₁ m ∧ Φ₂ m) := by
  have hs := fun x => IsBlock.inRegion_append (x := x) ha hnk
  refine ⟨fun h => ⟨?_, ?_⟩, fun m m' hag ⟨h₁, h₂⟩ =>
    ⟨hP.congr m m' (fun x hx => hag x ((hs x).1.mpr (Or.inl hx))) h₁,
     hQ.congr m m' (fun x hx => hag x ((hs x).1.mpr (Or.inr hx))) h₂⟩⟩
  · intro hh
    obtain ⟨h₁, h₂, _, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
    obtain ⟨m₁, hΦ₁, rfl⟩ := (hP.iff _).mp hp
    obtain ⟨m₂, hΦ₂, rfl⟩ := (hQ.iff _).mp hq
    let m : Memory := Memory.ofFn fun x => if InRegion a n x then m₁.read8 x else m₂.read8 x
    have hm : ∀ x, m.read8 x = if InRegion a n x then m₁.read8 x else m₂.read8 x :=
      fun _ => Memory.read8_ofFn _ _ _
    refine ⟨m, ⟨hP.congr m₁ m (fun x hx => by simp [hm, hx]) hΦ₁,
      hQ.congr m₂ m (fun x hx => by
        have : ¬InRegion a n x := fun h => (hs x).2 ⟨h, hx⟩
        simp [hm, this]) hΦ₂⟩, ?_⟩
    refine Heap.ext_phys fun x => ?_
    by_cases h₁ : InRegion a n x
    · simp [Heap.union, regionHeapProtNone, hm, h₁, (hs x).1.mpr (Or.inl h₁)]
    · by_cases h₂ : InRegion a' k x <;> simp [Heap.union, regionHeapProtNone, hm, h₁, h₂, (hs x).1]
  · rintro ⟨m, ⟨hΦ₁, hΦ₂⟩, rfl⟩
    refine SepProp.holds_sepConj_iff.mpr ⟨regionHeapProtNone a n m, regionHeapProtNone a' k m,
      Heap.Disjoint.of_phys_left rfl rfl fun x => ?_, ?_,
      (hP.iff _).mpr ⟨m, hΦ₁, rfl⟩, (hQ.iff _).mpr ⟨m, hΦ₂, rfl⟩⟩
    · by_cases h₁ : InRegion a n x
      · have : ¬InRegion a' k x := fun h₂ => (hs x).2 ⟨h₁, h₂⟩
        exact Or.inr (Or.inl (by simp [regionHeapProtNone, this]))
      · exact Or.inl (by simp [regionHeapProtNone, h₁])
    · refine Heap.ext_phys fun x => ?_
      by_cases h₁ : InRegion a n x
      · simp [Heap.union, regionHeapProtNone, h₁, (hs x).1.mpr (Or.inl h₁)]
      · by_cases h₂ : InRegion a' k x <;> simp [Heap.union, regionHeapProtNone, h₁, h₂, (hs x).1]

theorem sepExists {α : Sort u} {P : α → SepProp} {Φ : α → Memory → Prop}
    {b : BitVec 64} {n : Nat}
    (h : ∀ x, IsBlockProtNone (P x) b n (Φ x)) :
    IsBlockProtNone (∃∗ x, P x) b n (fun m => ∃ x, Φ x m) :=
  ⟨fun hp => SepProp.holds_sepExists_iff.trans
     ⟨fun ⟨x, hx⟩ => let ⟨m, hm, e⟩ := ((h x).iff hp).mp hx; ⟨m, ⟨x, hm⟩, e⟩,
      fun ⟨m, ⟨x, hm⟩, e⟩ => ⟨x, ((h x).iff hp).mpr ⟨m, hm, e⟩⟩⟩,
   fun m m' hag ⟨x, hx⟩ => ⟨x, (h x).congr m m' hag hx⟩⟩

theorem eq (hP : IsBlockProtNone P b n Φ) (hQ : IsBlockProtNone Q b n Ψ)
    (h : ∀ m, Φ m ↔ Ψ m) : P = Q := by
  ext hp
  rw [hP.iff, hQ.iff]
  exact exists_congr fun m => and_congr_left fun _ => h m

theorem entails (hP : IsBlockProtNone P b n Φ) (hQ : IsBlockProtNone Q b n Ψ)
    (h : ∀ m, Φ m → Ψ m) : P ⊢ Q := by
  refine SepProp.entails_iff.mpr fun hp h1 => ?_
  obtain ⟨m, hΦ, e⟩ := (hP.iff hp).mp h1
  exact (hQ.iff hp).mpr ⟨m, h m hΦ, e⟩

theorem pointsTo8ProtNone (a : BitVec 64) (v : BitVec 8) :
    IsBlockProtNone (a ↦₈ₙ v) a 1 (fun m => m.read8 a = v) := by
  have hreg : ∀ x, InRegion a 1 x ↔ x = a := fun x => by
    simp only [InRegion]; constructor <;> intro h <;> bv_arith
  refine ⟨fun h => ⟨fun hp => ⟨(default : Memory).write8 a v, Memory.read8_write8_same _ _ _, ?_⟩, ?_⟩,
    fun m m' hag hm => (hag a ((hreg a).mpr rfl)).trans hm⟩
  · have hp : h = Heap.singletonProtNone a v := holds_pointsTo8ProtNone_iff.mp hp
    subst hp
    refine Heap.ext_phys fun x => ?_
    by_cases hx : x = a <;> simp [Heap.singletonProtNone, regionHeapProtNone, hreg, hx]
  · rintro ⟨m, rfl, rfl⟩
    rw [holds_pointsTo8ProtNone_iff]
    refine Heap.ext_phys fun x => ?_
    by_cases hx : x = a <;> simp [Heap.singletonProtNone, regionHeapProtNone, hreg, hx]

theorem regionBlockProtNone (b : BitVec 64) (n : Nat) (m₀ : Memory) :
    IsBlockProtNone (regionBlockProtNone b n m₀) b n
      (fun m => ∀ x, InRegion b n x → m.read8 x = m₀.read8 x) := by
  refine ⟨fun h => ⟨fun hp => ⟨m₀, fun _ _ => rfl, holds_regionBlockProtNone_iff.mp hp⟩, ?_⟩,
    fun m m' hag hm x hx => (hag x hx).trans (hm x hx)⟩
  rintro ⟨m, hm, rfl⟩
  rw [holds_regionBlockProtNone_iff]
  refine Heap.ext_phys fun x => ?_
  simp only [regionHeapProtNone]
  split <;> simp_all

theorem memRegionProtNone (b : BitVec 64) (n : Nat) :
    IsBlockProtNone (memRegionProtNone b n) b n (fun _ => True) :=
  ⟨fun _ => holds_memRegionProtNone_iff.trans ⟨fun ⟨m, e⟩ => ⟨m, trivial, e⟩, fun ⟨m, _, e⟩ => ⟨m, e⟩⟩,
    fun _ _ _ _ => trivial⟩

theorem pointsToBytesProtNone (a : BitVec 64) (bs : List (BitVec 8)) :
    IsBlockProtNone (a ↦ₙ bs) a bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes a bs.length = bs) := by
  induction bs generalizing a with
  | nil =>
    rw [pointsToBytesProtNone_nil]
    have hr : ∀ m, regionHeapProtNone a 0 m = Heap.empty := fun m => by
      refine Heap.ext_phys fun x => ?_
      simp [regionHeapProtNone, InRegion, Heap.empty]
    refine ⟨fun h => ⟨fun hp => ⟨default, ⟨by simp, by simp⟩, ?_⟩, ?_⟩,
      fun _ _ _ h => h⟩
    · rw [SepProp.holds_emp_iff] at hp; simp [hp, hr]
    · rintro ⟨m, -, rfl⟩; rw [SepProp.holds_emp_iff]; simp [hr]
  | cons x bs ih =>
    rw [pointsToBytesProtNone_cons]
    by_cases hlen : bs.length + 1 ≤ 2 ^ 64
    · have hb := (pointsTo8ProtNone a x).sepConj (ih (a + 1#64)) (by bv_arith) (by omega)
      have e : 1 + bs.length = (x :: bs).length := by simp; omega
      rw [e] at hb
      refine hb.cast rfl fun m => ?_
      simp only [List.length_cons, Memory.readBytes, List.cons.injEq]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨hlen, h1, h3⟩
      · rintro ⟨-, h1, h3⟩; exact ⟨h1, by omega, h3⟩
    · refine ⟨fun h => ⟨fun hp => ?_, fun ⟨_, ⟨hl, _⟩, _⟩ => by simp at hl; omega⟩,
        fun _ _ _ ⟨hl, _⟩ => by simp at hl; omega⟩
      exfalso
      obtain ⟨h₁, h₂, hd, -, hp₁, hp₂⟩ := SepProp.holds_sepConj_iff.mp hp
      obtain ⟨v1, hv1⟩ := (pointsTo8ProtNone a x).covers hp₁ a (by simp [InRegion])
      obtain ⟨v2, hv2⟩ := (ih (a + 1#64)).covers hp₂ a (by simp only [InRegion]; bv_arith)
      rcases hd.1 a with h | h | ⟨_, h, _⟩
      · rw [hv1] at h; contradiction
      · rw [hv2] at h; contradiction
      · rw [hv1] at h; cases h

theorem pointsToBytesProtNone_len {a : BitVec 64} {bs : List (BitVec 8)} (h : bs.length = n) :
    IsBlockProtNone (a ↦ₙ bs) a n
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes a bs.length = bs) := by
  subst h; exact pointsToBytesProtNone a bs

end IsBlockProtNone

theorem pointsToBytesProtNone_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ₙ (xs ++ ys)) = (a ↦ₙ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ₙ ys) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytesProtNone_cons, pointsToBytesProtNone_cons, ih, sepConj_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (x :: xs).length := by
      simp only [List.length_cons]; bv_arith
    rw [e]

@[simp]
theorem pointsToBytesProtNone_singleton (a : BitVec 64) (b : BitVec 8) :
    (a ↦ₙ [b]) = (a ↦₈ₙ b) := by
  rw [pointsToBytesProtNone_cons, pointsToBytesProtNone_nil, sepConj_emp]

@[simp, arm64_norm]
theorem memRegionProtNone_zero (base : BitVec 64) : memRegionProtNone base 0 = emp := by
  ext h
  rw [(IsBlockProtNone.memRegionProtNone base 0).iff]
  have hr : ∀ m, regionHeapProtNone base 0 m = Heap.empty := fun m => by
    refine Heap.ext_phys fun x => ?_
    simp [regionHeapProtNone, InRegion, Heap.empty]
  simp only [SepProp.holds_emp_iff, hr, true_and]
  exact ⟨fun ⟨_, hm⟩ => hm, fun hm => ⟨default, hm⟩⟩

theorem memRegionProtNone_split (base : BitVec 64) (n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegionProtNone base (n + k) =
      memRegionProtNone base n ∗ memRegionProtNone (base + BitVec.ofNat 64 n) k :=
  IsBlockProtNone.eq (IsBlockProtNone.memRegionProtNone base (n + k))
    ((IsBlockProtNone.memRegionProtNone base n).sepConj
      (IsBlockProtNone.memRegionProtNone _ k) rfl h)
    (fun _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩)

theorem memRegionProtNone_split_le (base : BitVec 64) {k n : Nat} (hkn : k ≤ n) (hn : n ≤ 2 ^ 64) :
    memRegionProtNone base n =
      memRegionProtNone base k ∗ memRegionProtNone (base + BitVec.ofNat 64 k) (n - k) := by
  have heq : n = k + (n - k) := (Nat.add_sub_of_le hkn).symm
  conv => lhs; rw [heq]
  exact memRegionProtNone_split base k (n - k) (by omega)

theorem pointsToBytesProtNone_entails_memRegionProtNone (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₙ bs) ⊢ memRegionProtNone a bs.length :=
  IsBlockProtNone.entails (IsBlockProtNone.pointsToBytesProtNone a bs)
    (IsBlockProtNone.memRegionProtNone a _) fun _ _ => trivial

/-- Transition a read-write block `P` (`IsBlock P base len Φ`) to its `PROT_NONE` counterpart
    `P_pn` (`IsBlockProtNone P_pn base len Φ`) across
    `Memory.setPermNonFrozen base len Perm.protNone` (`mprotect(..., PROT_NONE)` per Linux
    `mm/mprotect.c` `mprotect_fixup` / `change_protection`), preserving byte values and any
    frame `R` (including `memMapped base len`). -/
theorem IsBlock.setPermProtNone {P P_pn : SepProp} {base : BitVec 64} {len : Nat}
    {Φ : Memory → Prop} (hb : IsBlock P base len Φ) (hpn : IsBlockProtNone P_pn base len Φ)
    {m : Memory} {R : SepProp} (h : m ⊨ P ∗ R) :
    m.setPermNonFrozen base len Perm.protNone ⊨ P_pn ∗ R := by
  let m' := m.setPermNonFrozen base len Perm.protNone
  have hΦ' : Φ m' :=
    hpn.congr m m' (fun a _ => Memory.read8_setPermNonFrozen m base len Perm.protNone a) (hb.read h)
  obtain ⟨_, ⟨h₁, hR, hd, rfl, hp, hr⟩, hm⟩ := satSep_iff.mp h
  have hcov := hb.covers hp
  have hm₁ := Heap.Matches.of_union_left hm
  have hmR := Heap.Matches.of_union_right hd hm
  have hperm_pn : ∀ a, InRegion base len a → m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false := by
    intro a ha
    obtain ⟨v, hv⟩ := hcov a ha
    obtain ⟨-, hpm, hlf⟩ := hm₁.1 a (.rw v) hv
    have hin : (a - base).toNat < len := ha
    dsimp [m']
    refine ⟨?_, ?_⟩
    · rw [Memory.perm_setPermNonFrozen, hpm]; simp only [decide_eq_true hin]; rfl
    · rw [Memory.isLazyFree_setPermNonFrozen, hlf]
  have hdisj : (regionHeapProtNone base len m').Disjoint hR := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
    by_cases ha : InRegion base len a
    · obtain ⟨v, hv⟩ := hcov a ha
      rcases hd.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hv] at h1; contradiction
      · exact Or.inr (Or.inl h2)
      · rw [hv] at h1; cases h1
    · exact Or.inl (by simp [regionHeapProtNone, ha])
  have hmR' : hR.Matches m' := by
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => ?_⟩
    · have hnot_in : ¬ (a - base).toNat < len := by
        intro hin
        obtain ⟨v, hv⟩ := hcov a hin
        rcases hd.1 a with h1 | h2 | ⟨_, h1, _⟩
        · rw [hv] at h1; contradiction
        · rw [hc] at h2; contradiction
        · rw [hv] at h1; cases h1
      have hpm : m'.perm a = m.perm a := by
        dsimp [m']; rw [Memory.perm_setPermNonFrozen]
        simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have hlf : m'.isLazyFree a = m.isLazyFree a := by
        dsimp [m']; rw [Memory.isLazyFree_setPermNonFrozen]
      have hcell := hmR.1 a c hc
      cases c <;> simp only [m', Memory.read8_setPermNonFrozen, hpm, hlf] <;> exact hcell
    · obtain ⟨hmapped, hanon⟩ := hmR.2.2 a hmap
      dsimp [m']
      rw [Memory.perm_setPermNonFrozen, Memory.isAnon_setPermNonFrozen_apply]
      split
      · exact ⟨rfl, hanon⟩
      · exact ⟨hmapped, hanon⟩
  exact satSep_iff.mpr ⟨(regionHeapProtNone base len m').union hR,
    ⟨regionHeapProtNone base len m', hR, hdisj, rfl, (hpn.iff _).mpr ⟨m', hΦ', rfl⟩, hr⟩,
    Heap.Matches.union (IsBlockProtNone.regionHeapProtNone_matches base len m' hperm_pn) hmR'⟩

/-- Transition a `PROT_NONE` block `P_pn` (`IsBlockProtNone P_pn base len Φ`) to its read-write
    counterpart `P` (`IsBlock P base len Φ`) across `Memory.setPermNonFrozen base len Perm.rw`
    (`mprotect(..., PROT_READ | PROT_WRITE)` per Linux `mm/mprotect.c` `mprotect_fixup` /
    `change_protection`), exposing the preserved byte values and preserving any frame `R`. -/
theorem IsBlockProtNone.setPermRw {P_pn P : SepProp} {base : BitVec 64} {len : Nat}
    {Φ : Memory → Prop} (hpn : IsBlockProtNone P_pn base len Φ) (hb : IsBlock P base len Φ)
    {m : Memory} {R : SepProp} (h : m ⊨ P_pn ∗ R) :
    m.setPermNonFrozen base len Perm.rw ⊨ P ∗ R := by
  let m' := m.setPermNonFrozen base len Perm.rw
  have hΦ' : Φ m' :=
    hb.congr m m' (fun a _ => Memory.read8_setPermNonFrozen m base len Perm.rw a) (hpn.read h)
  obtain ⟨_, ⟨h₁, hR, hd, rfl, hp, hr⟩, hm⟩ := satSep_iff.mp h
  have hcov := hpn.covers hp
  have hm₁ := Heap.Matches.of_union_left hm
  have hmR := Heap.Matches.of_union_right hd hm
  have hperm_rw : m'.RW base len := by
    intro a ha
    obtain ⟨v, hv⟩ := hcov a ha
    obtain ⟨-, hpm, hlf⟩ := hm₁.1 a (.protNone v) hv
    have hin : (a - base).toNat < len := ha
    dsimp [m']
    refine Memory.permNoLazy_eq_some_rw_iff.mpr ⟨?_, ?_⟩
    · rw [Memory.perm_setPermNonFrozen, hpm]; simp only [decide_eq_true hin]; rfl
    · rw [Memory.isLazyFree_setPermNonFrozen, hlf]
  have hdisj : (regionHeap base len m').Disjoint hR := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
    by_cases ha : InRegion base len a
    · obtain ⟨v, hv⟩ := hcov a ha
      rcases hd.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hv] at h1; contradiction
      · exact Or.inr (Or.inl h2)
      · rw [hv] at h1; cases h1
    · exact Or.inl (by simp [regionHeap, ha])
  have hmR' : hR.Matches m' := by
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => ?_⟩
    · have hnot_in : ¬ (a - base).toNat < len := by
        intro hin
        obtain ⟨v, hv⟩ := hcov a hin
        rcases hd.1 a with h1 | h2 | ⟨_, h1, _⟩
        · rw [hv] at h1; contradiction
        · rw [hc] at h2; contradiction
        · rw [hv] at h1; cases h1
      have hpm : m'.perm a = m.perm a := by
        dsimp [m']; rw [Memory.perm_setPermNonFrozen]
        simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have hlf : m'.isLazyFree a = m.isLazyFree a := by
        dsimp [m']; rw [Memory.isLazyFree_setPermNonFrozen]
      have hcell := hmR.1 a c hc
      cases c <;> simp only [m', Memory.read8_setPermNonFrozen, hpm, hlf] <;> exact hcell
    · obtain ⟨hmapped, hanon⟩ := hmR.2.2 a hmap
      dsimp [m']
      rw [Memory.perm_setPermNonFrozen, Memory.isAnon_setPermNonFrozen_apply]
      split
      · exact ⟨rfl, hanon⟩
      · exact ⟨hmapped, hanon⟩
  exact satSep_iff.mpr ⟨(regionHeap base len m').union hR,
    ⟨regionHeap base len m', hR, hdisj, rfl, (hb.iff _).mpr ⟨m', hΦ', rfl⟩, hr⟩,
    Heap.Matches.union (IsBlock.regionHeap_matches base len m' hperm_rw) hmR'⟩

/-- Promoting a `PROT_NONE` byte slice `base ↦ₙ bs` to read-write via
    `Memory.setPermNonFrozen base bs.length Perm.rw` (`mprotect(..., PROT_READ | PROT_WRITE)` per
    Linux `mm/mprotect.c` `mprotect_fixup` / `change_protection`) exposes the preserved bytes
    `base ↦ₛ bs` alongside any frame `P`. -/
theorem Satisfies.setPermRw_of_pointsToBytesProtNone {P : SepProp} {m : Memory}
    {base : BitVec 64} {bs : List (BitVec 8)} (h : m ⊨ (base ↦ₙ bs) ∗ P) :
    m.setPermNonFrozen base bs.length Perm.rw ⊨ (base ↦ₛ bs) ∗ P :=
  (IsBlockProtNone.pointsToBytesProtNone base bs).setPermRw (IsBlock.pointsToBytes base bs) h

/-- Demoting a read-write byte slice `base ↦ₛ bs` to `PROT_NONE` via
    `Memory.setPermNonFrozen base bs.length Perm.protNone` (`mprotect(..., PROT_NONE)` per Linux
    `mm/mprotect.c` `mprotect_fixup` / `change_protection`) preserves its underlying bytes as
    `base ↦ₙ bs` alongside any frame `P`. -/
theorem Satisfies.setPermProtNone_of_pointsToBytes {P : SepProp} {m : Memory}
    {base : BitVec 64} {bs : List (BitVec 8)} (h : m ⊨ (base ↦ₛ bs) ∗ P) :
    m.setPermNonFrozen base bs.length Perm.protNone ⊨ (base ↦ₙ bs) ∗ P :=
  (IsBlock.pointsToBytes base bs).setPermProtNone (IsBlockProtNone.pointsToBytesProtNone base bs) h

/-- Promoting an untyped `memRegionProtNone base len` to read-write via
    `Memory.setPermNonFrozen base len Perm.rw` yields `memRegion base len` alongside any
    frame `P`. -/
theorem Satisfies.setPermRw_of_memRegionProtNone {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegionProtNone base len ∗ P) :
    m.setPermNonFrozen base len Perm.rw ⊨ memRegion base len ∗ P :=
  (IsBlockProtNone.memRegionProtNone base len).setPermRw (IsBlock.memRegion base len) h

/-- Demoting an untyped `memRegion base len` to `PROT_NONE` via
    `Memory.setPermNonFrozen base len Perm.protNone` yields `memRegionProtNone base len`
    alongside `P`. -/
theorem Satisfies.setPermProtNone_of_memRegion {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegion base len ∗ P) :
    m.setPermNonFrozen base len Perm.protNone ⊨ memRegionProtNone base len ∗ P :=
  (IsBlock.memRegion base len).setPermProtNone (IsBlockProtNone.memRegionProtNone base len) h

private theorem inRegion_add_ofNat_lt {base : BitVec 64} {len i : Nat} (hi : i < len) :
    InRegion base len (base + BitVec.ofNat 64 i) := by
  simp only [InRegion]
  have hsub : base + BitVec.ofNat 64 i - base = BitVec.ofNat 64 i := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [hsub, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi

/-- Every owned `memRegionProtNone base len` is non-frozen (`m.allPerm (!·.frozen) base len = true`),
    discharging the frozen-memory guard of `execMprotect` / `execMadvise`. -/
theorem Satisfies.allPerm_not_frozen_of_memRegionProtNone {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegionProtNone base len ∗ P) :
    m.allPerm (fun p => !p.frozen) base len = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  rw [(IsBlockProtNone.memRegionProtNone base len).perm_protNone h (inRegion_add_ofNat_lt hi)]
  rfl

/-- Every owned `memRegionProtNone base len` is mapped (`m.allPerm (·.mapped) base len = true`),
    discharging the mapped-range guard of `execMprotect` / `execMadvise`. -/
theorem Satisfies.allPerm_mapped_of_memRegionProtNone {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegionProtNone base len ∗ P) :
    m.allPerm (·.mapped) base len = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  rw [(IsBlockProtNone.memRegionProtNone base len).perm_protNone h (inRegion_add_ofNat_lt hi)]
  rfl

/-- Every owned `base ↦ₙ bs` slice is non-frozen (`m.allPerm (!·.frozen) base bs.length = true`). -/
theorem Satisfies.allPerm_not_frozen_of_pointsToBytesProtNone {P : SepProp} {m : Memory}
    {base : BitVec 64} {bs : List (BitVec 8)} (h : m ⊨ (base ↦ₙ bs) ∗ P) :
    m.allPerm (fun p => !p.frozen) base bs.length = true :=
  Satisfies.allPerm_not_frozen_of_memRegionProtNone
    (Satisfies.mono (sepConj_mono_left (pointsToBytesProtNone_entails_memRegionProtNone base bs)) h)

/-- Every owned `base ↦ₙ bs` slice is mapped (`m.allPerm (·.mapped) base bs.length = true`). -/
theorem Satisfies.allPerm_mapped_of_pointsToBytesProtNone {P : SepProp} {m : Memory}
    {base : BitVec 64} {bs : List (BitVec 8)} (h : m ⊨ (base ↦ₙ bs) ∗ P) :
    m.allPerm (·.mapped) base bs.length = true :=
  Satisfies.allPerm_mapped_of_memRegionProtNone
    (Satisfies.mono (sepConj_mono_left (pointsToBytesProtNone_entails_memRegionProtNone base bs)) h)

/-- Every owned `memRegion base len` is non-frozen (`m.allPerm (!·.frozen) base len = true`). -/
theorem Satisfies.allPerm_not_frozen_of_memRegion {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegion base len ∗ P) :
    m.allPerm (fun p => !p.frozen) base len = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  rw [(IsBlock.memRegion base len).perm_rw h (inRegion_add_ofNat_lt hi)]
  rfl

/-- Every owned `memRegion base len` is mapped (`m.allPerm (·.mapped) base len = true`). -/
theorem Satisfies.allPerm_mapped_of_memRegion {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegion base len ∗ P) :
    m.allPerm (·.mapped) base len = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  rw [(IsBlock.memRegion base len).perm_rw h (inRegion_add_ofNat_lt hi)]
  rfl

/-- Every owned `base ↦ₛ bs` slice is non-frozen (`m.allPerm (!·.frozen) base bs.length = true`). -/
theorem Satisfies.allPerm_not_frozen_of_pointsToBytes {P : SepProp} {m : Memory}
    {base : BitVec 64} {bs : List (BitVec 8)} (h : m ⊨ (base ↦ₛ bs) ∗ P) :
    m.allPerm (fun p => !p.frozen) base bs.length = true :=
  Satisfies.allPerm_not_frozen_of_memRegion
    (Satisfies.mono (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsToBytes base bs) (IsBlock.memRegion base _) fun _ _ => trivial)) h)

/-- Every owned `base ↦ₛ bs` slice is mapped (`m.allPerm (·.mapped) base bs.length = true`). -/
theorem Satisfies.allPerm_mapped_of_pointsToBytes {P : SepProp} {m : Memory}
    {base : BitVec 64} {bs : List (BitVec 8)} (h : m ⊨ (base ↦ₛ bs) ∗ P) :
    m.allPerm (·.mapped) base bs.length = true :=
  Satisfies.allPerm_mapped_of_memRegion
    (Satisfies.mono (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsToBytes base bs) (IsBlock.memRegion base _) fun _ _ => trivial)) h)

private theorem readBytes_replicate_zero_of_inRegion {m : Memory} {base : BitVec 64} {len : Nat}
    (hz : ∀ a, InRegion base len a → m.read8 a = 0#8) (hlen : len ≤ 2 ^ 64) :
    ∀ (k off : Nat), off + k ≤ len →
      m.readBytes (base + BitVec.ofNat 64 off) k = List.replicate k 0#8
  | 0, _, _ => rfl
  | k + 1, off, hle => by
    have ha : InRegion base len (base + BitVec.ofNat 64 off) :=
      inRegion_add_ofNat_lt (by omega)
    have hr8 := hz _ ha
    have hstep : base + BitVec.ofNat 64 off + 1#64 = base + BitVec.ofNat 64 (off + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    simp only [Memory.readBytes, List.replicate_succ, hr8, hstep,
      readBytes_replicate_zero_of_inRegion hz hlen k (off + 1) (by omega)]

/-- Mapping an unmapped region `[base, base + len)` as `PROT_NONE` (`mmap(..., PROT_NONE, ...)`:
    `Memory.mapZero` followed by `Memory.setPermNonFrozen base len Perm.protNone`) produces a
    zero-filled `PROT_NONE` byte slice `base ↦ₙ List.replicate len 0#8` together with
    `memMapped base len` alongside any existing assertion `P`. -/
theorem Satisfies.mapZeroProtNone_mapped {P : SepProp} {m : Memory} (h : m ⊨ P)
    {base : BitVec 64} {len : Nat} (hmap : m.canMap base len = true) (hlen : len ≤ 2 ^ 64) :
    (m.mapZero base len).setPermNonFrozen base len Perm.protNone ⊨
      (base ↦ₙ List.replicate len 0#8) ∗ memMapped base len ∗ P := by
  have hm := Satisfies.mapZero_mapped h hmap
  have hblk := IsBlock.pointsToBytes_len (a := base) (bs := List.replicate len 0#8)
    List.length_replicate
  have hbytes : m.mapZero base len ⊨
      (base ↦ₛ List.replicate len 0#8) ∗ (memMapped base len ∗ P) :=
    (IsBlock.memRegion base len).update hblk (Nat.le_refl _) hm
      (AgreesOutside.rfl' _ base len)
      ⟨by simp [hlen], by
        simpa using readBytes_replicate_zero_of_inRegion
          (fun a ha => m.read8_mapZero_of_canMap hmap ha) hlen len 0 (by omega)⟩
  simpa [List.length_replicate] using Satisfies.setPermProtNone_of_pointsToBytes hbytes

/-- Mapping an unmapped region `[base, base + len)` as `PROT_NONE` produces
    `base ↦ₙ List.replicate len 0#8` alongside any existing assertion `P`. -/
theorem Satisfies.mapZeroProtNone {P : SepProp} {m : Memory} (h : m ⊨ P)
    {base : BitVec 64} {len : Nat} (hmap : m.canMap base len = true) (hlen : len ≤ 2 ^ 64) :
    (m.mapZero base len).setPermNonFrozen base len Perm.protNone ⊨
      (base ↦ₙ List.replicate len 0#8) ∗ P :=
  Satisfies.drop_mid (Satisfies.mapZeroProtNone_mapped h hmap hlen)

/-- Unmapping an owned `memRegionProtNone base len` together with its mapping reservation token
    `memMapped base len` via `Memory.unmapNonFrozen` (`munmap`) preserves any separately owned
    assertion `P`. -/
theorem Satisfies.unmapNonFrozen_protNone {P : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegionProtNone base len ∗ memMapped base len ∗ P) :
    m.unmapNonFrozen base len ⊨ P := by
  obtain ⟨_, ⟨h₁, _, hdisj1, rfl, h1, hrest⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨h₂, hp, hdisj2, rfl, h2, hP⟩ := SepProp.holds_sepConj_iff.mp hrest
  have hcov := (IsBlockProtNone.memRegionProtNone base len).covers h1
  have h2_eq : h₂ = mappedHeap base len := holds_memMapped_iff.mp h2
  subst h2_eq
  have ⟨_, hd1p⟩ := (Heap.disjoint_union_right hdisj2).mp hdisj1
  have hm_hp := Heap.Matches.of_union_right hdisj2 (Heap.Matches.of_union_right hdisj1 hm)
  refine SepProp.satisfies_iff.mpr ⟨hp, hP, ⟨fun a c hpa => ?_, hm_hp.2.1, fun a hma => ?_⟩⟩
  · have hnot_in : ¬ (a - base).toNat < len := by
      intro hin
      obtain ⟨b, hb1⟩ := hcov a hin
      rcases hd1p.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hb1] at h1; contradiction
      · rw [hpa] at h2; contradiction
      · rw [hb1] at h1; cases h1
    have hr : (m.unmapNonFrozen base len).read8 a = m.read8 a := by
      rw [Memory.read8_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hpm : (m.unmapNonFrozen base len).perm a = m.perm a := by
      rw [Memory.perm_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hlf : (m.unmapNonFrozen base len).isLazyFree a = m.isLazyFree a := by
      rw [Memory.isLazyFree_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hcell := hm_hp.1 a c hpa
    cases c <;> simp only [hr, hpm, hlf] <;> exact hcell
  · have hnot_in : ¬ (a - base).toNat < len := by
      intro hin
      have hin' : InRegion base len a := hin
      rcases hdisj2.2.2.2.2 a with hmap1 | hmap2
      · simp [mappedHeap, hin'] at hmap1
      · rw [hma] at hmap2; contradiction
    have hpm : (m.unmapNonFrozen base len).perm a = m.perm a := by
      rw [Memory.perm_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have han : (m.unmapNonFrozen base len).isAnon a = m.isAnon a := by
      rw [Memory.isAnon_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [hpm, han]
    exact hm_hp.2.2 a hma

/-- Replacing an owned `memRegion base len` in place with zero-filled `PROT_NONE` pages via a
    `MAP_FIXED` `PROT_NONE` `mmap` (`Memory.unmapNonFrozen`, then `Memory.mapZero`, then
    `Memory.setPermNonFrozen base len Perm.protNone`) retains ownership of the region as
    `base ↦ₙ List.replicate len 0#8` alongside any frame `P` (including `memMapped base len`). -/
theorem Satisfies.mmapFixedProtNone_owned {P : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegion base len ∗ P) (hlen : len ≤ 2 ^ 64) :
    ((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len Perm.protNone ⊨
      (base ↦ₙ List.replicate len 0#8) ∗ P := by
  let m₀ := (m.unmapNonFrozen base len).mapZero base len
  have hunm_in : ∀ a, InRegion base len a → (m.unmapNonFrozen base len).perm a = none := by
    intro a ha
    have hrw := (IsBlock.memRegion base len).perm_rw h ha
    have hin : (a - base).toNat < len := ha
    rw [Memory.perm_unmapNonFrozen, hrw]
    simp only [decide_eq_true hin]; rfl
  have hag : AgreesOutside m m₀ base len := by
    refine ⟨fun a hout => ?_, ?_, fun a hout => ?_, fun a hlf => ?_, fun a han => ?_⟩
    · have hnot_in : ¬ (a - base).toNat < len := (outsideRegion_iff_not_inRegion base len a).mp hout
      dsimp [m₀]
      rw [Memory.read8_mapZero, Memory.read8_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · funext a
      by_cases hin : (a - base).toNat < len
      · have hrw := (IsBlock.memRegion base len).perm_rw h hin
        dsimp [m₀]
        rw [Memory.perm_mapZero, hunm_in a hin, hrw]
        simp only [decide_eq_true hin]; rfl
      · dsimp [m₀]
        rw [Memory.perm_mapZero, Memory.perm_unmapNonFrozen]
        simp only [decide_eq_false hin, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · have hnot_in : ¬ (a - base).toNat < len := (outsideRegion_iff_not_inRegion base len a).mp hout
      dsimp [m₀]
      rw [Memory.isLazyFree_mapZero, Memory.isLazyFree_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · dsimp [m₀]
      rw [Memory.isLazyFree_mapZero, Memory.isLazyFree_unmapNonFrozen]
      split
      · rfl
      · exact hlf
    · by_cases hin : (a - base).toNat < len
      · dsimp [m₀]
        rw [Memory.isAnon_mapZero, hunm_in a hin]
        simp only [decide_eq_true hin]; rfl
      · dsimp [m₀]
        rw [Memory.isAnon_mapZero, Memory.isAnon_unmapNonFrozen]
        simp only [decide_eq_false hin, Bool.false_and, Bool.false_eq_true, ↓reduceIte, han]
  have hz : ∀ a, InRegion base len a → m₀.read8 a = 0#8 := by
    intro a ha
    have hin : (a - base).toNat < len := ha
    dsimp [m₀]
    rw [Memory.read8_mapZero, hunm_in a ha]
    simp only [decide_eq_true hin]; rfl
  have hblk := IsBlock.pointsToBytes_len (a := base) (bs := List.replicate len 0#8)
    List.length_replicate
  have hbytes : m₀ ⊨ (base ↦ₛ List.replicate len 0#8) ∗ P :=
    (IsBlock.memRegion base len).update hblk (Nat.le_refl _) h hag
      ⟨by simp [hlen], by
        simpa using readBytes_replicate_zero_of_inRegion hz hlen len 0 (by omega)⟩
  simpa [List.length_replicate] using Satisfies.setPermProtNone_of_pointsToBytes hbytes

/-! ## Lazy-Free Read-Write Regions (`memRegionLazy`, `↦₈ₗ`..`↦₁₂₈ₗ`) and `MADV_FREE` Bridges -/

theorem regionHeapLazy_matches (base : BitVec 64) (len : Nat) (m : Memory)
    (hrw : ∀ a, InRegion base len a → m.perm a = some Perm.rw) :
    (regionHeapLazy base len).Matches m := by
  refine Heap.Matches.of_phys rfl rfl fun a c hc => ?_
  by_cases ha : InRegion base len a
  · simp [regionHeapLazy, ha] at hc; subst hc; exact hrw a ha
  · simp [regionHeapLazy, ha] at hc

@[simp, arm64_norm]
theorem memRegionLazy_zero (base : BitVec 64) : memRegionLazy base 0 = emp := by
  ext h
  simp only [holds_memRegionLazy_iff, SepProp.holds_emp_iff]
  have heq : regionHeapLazy base 0 = Heap.empty := by
    refine Heap.ext_phys fun x => ?_
    simp [regionHeapLazy, InRegion, Heap.empty]
  rw [heq]

theorem memRegionLazy_split (base : BitVec 64) (n k : Nat) (hnk : n + k ≤ 2 ^ 64) :
    memRegionLazy base (n + k) =
      (memRegionLazy base n ∗ memRegionLazy (base + BitVec.ofNat 64 n) k) := by
  have hs := fun x => IsBlock.inRegion_append (a := base) (n := n) (k := k) (x := x) rfl hnk
  have hdisj : (regionHeapLazy base n).Disjoint (regionHeapLazy (base + BitVec.ofNat 64 n) k) := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun x => ?_
    by_cases h1 : InRegion base n x
    · have h2 : ¬ InRegion (base + BitVec.ofNat 64 n) k x := fun h2 => (hs x).2 ⟨h1, h2⟩
      exact Or.inr (Or.inl (by simp [regionHeapLazy, h2]))
    · exact Or.inl (by simp [regionHeapLazy, h1])
  have hunion :
      (regionHeapLazy base n).union (regionHeapLazy (base + BitVec.ofNat 64 n) k) =
        regionHeapLazy base (n + k) := by
    refine Heap.ext_phys fun x => ?_
    by_cases h1 : InRegion base n x
    · simp [Heap.union, regionHeapLazy, h1, (hs x).1.mpr (Or.inl h1)]
    · by_cases h2 : InRegion (base + BitVec.ofNat 64 n) k x <;>
        simp [Heap.union, regionHeapLazy, h1, h2, (hs x).1]
  ext h
  simp only [holds_memRegionLazy_iff, SepProp.holds_sepConj_iff]
  constructor
  · rintro rfl
    exact ⟨regionHeapLazy base n, regionHeapLazy (base + BitVec.ofNat 64 n) k,
      hdisj, hunion.symm, rfl, rfl⟩
  · rintro ⟨_, _, _, rfl, rfl, rfl⟩
    exact hunion

theorem memRegionLazy_split_le (base : BitVec 64) {k n : Nat} (hkn : k ≤ n) (hn : n ≤ 2 ^ 64) :
    memRegionLazy base n =
      (memRegionLazy base k ∗ memRegionLazy (base + BitVec.ofNat 64 k) (n - k)) := by
  have heq : n = k + (n - k) := (Nat.add_sub_of_le hkn).symm
  conv => lhs; rw [heq]
  exact memRegionLazy_split base k (n - k) (by omega)

theorem pointsTo8Lazy_eq_memRegionLazy (a : BitVec 64) : (a ↦₈ₗ) = memRegionLazy a 1 := by
  have hreg : ∀ x, InRegion a 1 x ↔ x = a := fun x => by
    simp only [InRegion]; constructor <;> intro h <;> bv_arith
  ext h
  simp only [holds_pointsTo8Lazy_iff, holds_memRegionLazy_iff]
  have heq : Heap.singletonLazy a = regionHeapLazy a 1 := by
    refine Heap.ext_phys fun x => ?_
    by_cases hx : x = a <;> simp [Heap.singletonLazy, regionHeapLazy, hreg, hx]
  rw [heq]

theorem pointsTo16Lazy_eq_memRegionLazy (a : BitVec 64) : (a ↦₁₆ₗ) = memRegionLazy a 2 := by
  simp only [pointsTo16Lazy, pointsTo8Lazy_eq_memRegionLazy]
  rw [show a + 0#64 = a from by bv_arith]
  exact (memRegionLazy_split a 1 1 (by decide)).symm

theorem pointsTo32Lazy_eq_memRegionLazy (a : BitVec 64) : (a ↦₃₂ₗ) = memRegionLazy a 4 := by
  have hsplit : (a ↦₃₂ₗ) = pointsTo16Lazy a ∗ pointsTo16Lazy (a + 2#64) := by
    simp only [pointsTo32Lazy, pointsTo16Lazy, sepConj_assoc,
      show a + 2#64 + 0#64 = a + 2#64 from by bv_arith,
      show a + 2#64 + 1#64 = a + 3#64 from by bv_arith]
  rw [hsplit, pointsTo16Lazy_eq_memRegionLazy, pointsTo16Lazy_eq_memRegionLazy]
  exact (memRegionLazy_split a 2 2 (by decide)).symm

theorem pointsTo64Lazy_eq_memRegionLazy (a : BitVec 64) : (a ↦₆₄ₗ) = memRegionLazy a 8 := by
  have h03 : pointsTo32Lazy a = memRegionLazy a 4 := pointsTo32Lazy_eq_memRegionLazy a
  have h47 : pointsTo32Lazy (a + 4#64) = memRegionLazy (a + 4#64) 4 :=
    pointsTo32Lazy_eq_memRegionLazy (a + 4#64)
  have hsplit : (a ↦₆₄ₗ) = pointsTo32Lazy a ∗ pointsTo32Lazy (a + 4#64) := by
    simp only [pointsTo64Lazy, pointsTo32Lazy, sepConj_assoc,
      show a + 4#64 + 0#64 = a + 4#64 from by bv_arith,
      show a + 4#64 + 1#64 = a + 5#64 from by bv_arith,
      show a + 4#64 + 2#64 = a + 6#64 from by bv_arith,
      show a + 4#64 + 3#64 = a + 7#64 from by bv_arith]
  rw [hsplit, h03, h47]
  exact (memRegionLazy_split a 4 4 (by decide)).symm

theorem pointsTo128Lazy_eq_memRegionLazy (a : BitVec 64) : (a ↦₁₂₈ₗ) = memRegionLazy a 16 := by
  simp only [pointsTo128Lazy, pointsTo64Lazy_eq_memRegionLazy]
  exact (memRegionLazy_split a 8 8 (by decide)).symm

/-- Frame-preserving update weakening any `IsBlock P base len Φ` to `memRegionLazy base len`. -/
theorem IsBlock.bupd_memRegionLazy {P : SepProp} {base : BitVec 64} {len : Nat} {Φ : Memory → Prop}
    (hb : IsBlock P base len Φ) : P ⊢ |==> memRegionLazy base len := by
  refine SepProp.entails_iff.mpr fun h hp => SepProp.holds_bupd_iff.mpr fun m hf hd hm => ?_
  have hcov := hb.covers hp
  have hm₁ := Heap.Matches.of_union_left hm
  have hm_f := Heap.Matches.of_union_right hd hm
  have hrw : ∀ a, InRegion base len a → m.perm a = some Perm.rw := by
    intro a ha
    obtain ⟨v, hv⟩ := hcov a ha
    exact (hm₁.1 a (.rw v) hv).2.1
  have hd' : (regionHeapLazy base len).Disjoint hf := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
    by_cases ha : InRegion base len a
    · obtain ⟨v, hv⟩ := hcov a ha
      rcases hd.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hv] at h1; contradiction
      · exact Or.inr (Or.inl h2)
      · rw [hv] at h1; cases h1
    · exact Or.inl (by simp [regionHeapLazy, ha])
  exact ⟨regionHeapLazy base len, holds_memRegionLazy_iff.mpr rfl, hd',
    Heap.Matches.union (regionHeapLazy_matches base len m hrw) hm_f⟩

theorem memRegion_bupd_memRegionLazy (base : BitVec 64) (len : Nat) :
    memRegion base len ⊢ |==> memRegionLazy base len :=
  (IsBlock.memRegion base len).bupd_memRegionLazy

theorem pointsTo8_bupd_lazy (a : BitVec 64) (v : BitVec 8) : (a ↦₈ v) ⊢ |==> (a ↦₈ₗ) := by
  rw [pointsTo8Lazy_eq_memRegionLazy]
  exact (IsBlock.pointsTo8 a v).bupd_memRegionLazy

theorem pointsTo64_bupd_lazy (a : BitVec 64) (v : BitVec 64) : (a ↦₆₄ v) ⊢ |==> (a ↦₆₄ₗ) := by
  rw [pointsTo64Lazy_eq_memRegionLazy]
  exact (IsBlock.pointsTo64 a v).bupd_memRegionLazy

theorem Satisfies.to_memRegionLazy {P R : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    {Φ : Memory → Prop} (hb : IsBlock P base len Φ) (h : m ⊨ P ∗ R) :
    m ⊨ memRegionLazy base len ∗ R :=
  (satisfies_bupd _ m).mp
    (Satisfies.mono (Entails.trans (sepConj_mono_left hb.bupd_memRegionLazy) (bupd_frame_r _ R)) h)

theorem Satisfies.memRegion_to_lazy {R : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegion base len ∗ R) : m ⊨ memRegionLazy base len ∗ R :=
  Satisfies.to_memRegionLazy (IsBlock.memRegion base len) h

theorem Satisfies.pointsTo8_to_lazy {R : SepProp} {m : Memory} {a : BitVec 64} {v : BitVec 8}
    (h : m ⊨ (a ↦₈ v) ∗ R) : m ⊨ (a ↦₈ₗ) ∗ R := by
  rw [pointsTo8Lazy_eq_memRegionLazy]
  exact Satisfies.to_memRegionLazy (IsBlock.pointsTo8 a v) h

theorem Satisfies.pointsTo64_to_lazy {R : SepProp} {m : Memory} {a : BitVec 64} {v : BitVec 64}
    (h : m ⊨ (a ↦₆₄ v) ∗ R) : m ⊨ (a ↦₆₄ₗ) ∗ R := by
  rw [pointsTo64Lazy_eq_memRegionLazy]
  exact Satisfies.to_memRegionLazy (IsBlock.pointsTo64 a v) h

theorem Satisfies.perm_rw_of_memRegionLazy {R : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegionLazy base len ∗ R) {a : BitVec 64} (ha : InRegion base len a) :
    m.perm a = some Perm.rw := by
  obtain ⟨_, ⟨_, _, _, rfl, e, _⟩, hm⟩ := satSep_iff.mp h
  rw [holds_memRegionLazy_iff] at e; subst e
  exact (Heap.Matches.of_union_left hm).1 a .lazy (by simp [regionHeapLazy, ha])

theorem Satisfies.allPerm_not_frozen_of_memRegionLazy {R : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegionLazy base len ∗ R) :
    m.allPerm (fun p => !p.frozen) base len = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  rw [Satisfies.perm_rw_of_memRegionLazy h (inRegion_add_ofNat_lt hi)]
  rfl

theorem Satisfies.allPerm_mapped_of_memRegionLazy {R : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegionLazy base len ∗ R) :
    m.allPerm (·.mapped) base len = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  rw [Satisfies.perm_rw_of_memRegionLazy h (inRegion_add_ofNat_lt hi)]
  rfl

theorem Satisfies.canWrite_of_memRegionLazy {R : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (hn : len ≤ 2 ^ 64) (h : m ⊨ memRegionLazy base len ∗ R) :
    m.canWrite base len = true := by
  unfold Memory.canWrite
  rw [Memory.allPerm_iff]
  intro i hi
  rw [Satisfies.perm_rw_of_memRegionLazy h (inRegion_base_add base len i hi hn)]
  rfl

theorem Satisfies.canWrite_sub_of_memRegionLazy {R : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegionLazy base len ∗ R)
    {a : BitVec 64} {k : Nat} (hk : (a - base).toNat + k ≤ len) (hn : len ≤ 2 ^ 64) :
    m.canWrite a k = true := by
  unfold Memory.canWrite
  rw [Memory.allPerm_iff]
  intro i hi
  rw [Satisfies.perm_rw_of_memRegionLazy h (IsBlock.inRegion_sub_range hk hn hi)]
  rfl

/-- Upgrade `memRegionLazy base len` to any `IsBlock P' base len Φ'` after an `AgreesOutside`
    transition that clears `isLazyFree` on `[base, base + len)` and establishes `Φ' m'`. -/
theorem Satisfies.update_of_memRegionLazy {P' R : SepProp} {m m' : Memory}
    {base : BitVec 64} {len : Nat} {Φ' : Memory → Prop}
    (hb' : IsBlock P' base len Φ')
    (h : m ⊨ memRegionLazy base len ∗ R)
    (hag : AgreesOutside m m' base len)
    (hlf_in : ∀ a, InRegion base len a → m'.isLazyFree a = false)
    (hΦ' : Φ' m') : m' ⊨ P' ∗ R := by
  obtain ⟨_, ⟨h₁, hR, hd, rfl, e, hr⟩, hm⟩ := satSep_iff.mp h
  rw [holds_memRegionLazy_iff] at e; subst e
  have hm₁ := Heap.Matches.of_union_left hm
  have hmR := Heap.Matches.of_union_right hd hm
  have hmR' : hR.Matches m' := by
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => ?_⟩
    · have hout : OutsideRegion base len a := by
        rw [outsideRegion_iff_not_inRegion]
        intro hin
        have hlz : (regionHeapLazy base len).phys a = some .lazy := by simp [regionHeapLazy, hin]
        rcases hd.1 a with h1 | h2 | ⟨_, h1, _⟩
        · rw [hlz] at h1; contradiction
        · rw [hc] at h2; contradiction
        · rw [hlz] at h1; cases h1
      have hcell := hmR.1 a c hc
      cases c <;>
        simp only [hag.read8_eq hout, hag.perm_eq, hag.isLazyFree_eq hout] <;> exact hcell
    · obtain ⟨hmapped, hanon⟩ := hmR.2.2 a hmap
      rw [hag.perm_eq]
      exact ⟨hmapped, hag.isAnon_true hanon⟩
  have hrw' : m'.RW base len := by
    intro a ha
    have hpm : m.perm a = some Perm.rw := hm₁.1 a .lazy (by simp [regionHeapLazy, ha])
    exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨(congrFun hag.perm_eq a).trans hpm, hlf_in a ha⟩
  have hdisj' : (regionHeap base len m').Disjoint hR := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun x => ?_
    by_cases hx : InRegion base len x
    · have hlz : (regionHeapLazy base len).phys x = some .lazy := by simp [regionHeapLazy, hx]
      rcases hd.1 x with h1 | h2 | ⟨_, h1, _⟩
      · rw [hlz] at h1; contradiction
      · exact Or.inr (Or.inl h2)
      · rw [hlz] at h1; cases h1
    · exact Or.inl (by simp [regionHeap, hx])
  exact satSep_iff.mpr ⟨(regionHeap base len m').union hR,
    ⟨regionHeap base len m', hR, hdisj', rfl, (hb'.iff _).mpr ⟨m', hΦ', rfl⟩, hr⟩,
    Heap.Matches.union (IsBlock.regionHeap_matches base len m' hrw') hmR'⟩

theorem Satisfies.write8_pointsTo8Lazy {R : SepProp} {m : Memory} {a : BitVec 64} (v : BitVec 8)
    (h : m ⊨ (a ↦₈ₗ) ∗ R) : m.write8 a v ⊨ (a ↦₈ v) ∗ R := by
  rw [pointsTo8Lazy_eq_memRegionLazy] at h
  refine Satisfies.update_of_memRegionLazy (IsBlock.pointsTo8 a v) h
    ((AgreesOutside.rfl' m a 1).write8 (by simp [InRegion]))
    (fun x hx => ?_) (Memory.read8_write8_same m a v)
  have hxa : x = a := by simp only [InRegion] at hx; bv_arith
  subst hxa; simp

theorem Satisfies.write16_pointsTo16Lazy {R : SepProp} {m : Memory} {a : BitVec 64} (v : BitVec 16)
    (h : m ⊨ (a ↦₁₆ₗ) ∗ R) : m.write16 a v ⊨ (a ↦₁₆ v) ∗ R := by
  rw [pointsTo16Lazy_eq_memRegionLazy] at h
  refine Satisfies.update_of_memRegionLazy (IsBlock.pointsTo16 a v) h
    ((AgreesOutside.rfl' m a 2).write16 (by simp) (by decide))
    (fun x hx => ?_) (Memory.read16_write16_same m a v)
  have hor : x = a + 0#64 ∨ x = a + 1#64 := by simp only [InRegion] at hx; bv_omega
  simp only [Memory.write16]
  rcases hor with rfl | rfl <;> simp

theorem Satisfies.write32_pointsTo32Lazy {R : SepProp} {m : Memory} {a : BitVec 64} (v : BitVec 32)
    (h : m ⊨ (a ↦₃₂ₗ) ∗ R) : m.write32 a v ⊨ (a ↦₃₂ v) ∗ R := by
  rw [pointsTo32Lazy_eq_memRegionLazy] at h
  refine Satisfies.update_of_memRegionLazy (IsBlock.pointsTo32 a v) h
    ((AgreesOutside.rfl' m a 4).write32 (by simp) (by decide))
    (fun x hx => ?_) (Memory.read32_write32_same m a v)
  have hor : x = a + 0#64 ∨ x = a + 1#64 ∨ x = a + 2#64 ∨ x = a + 3#64 := by
    simp only [InRegion] at hx; bv_omega
  simp only [Memory.write32]
  rcases hor with rfl | rfl | rfl | rfl <;> simp

theorem Satisfies.write64_pointsTo64Lazy {R : SepProp} {m : Memory} {a : BitVec 64} (v : BitVec 64)
    (h : m ⊨ (a ↦₆₄ₗ) ∗ R) : m.write64 a v ⊨ (a ↦₆₄ v) ∗ R := by
  rw [pointsTo64Lazy_eq_memRegionLazy] at h
  refine Satisfies.update_of_memRegionLazy (IsBlock.pointsTo64 a v) h
    ((AgreesOutside.rfl' m a 8).write64 (by simp) (by decide))
    (fun x hx => ?_) (Memory.read64_write64_same m a v)
  have hor : x = a + 0#64 ∨ x = a + 1#64 ∨ x = a + 2#64 ∨ x = a + 3#64 ∨
      x = a + 4#64 ∨ x = a + 5#64 ∨ x = a + 6#64 ∨ x = a + 7#64 := by
    simp only [InRegion] at hx; bv_omega
  simp only [Memory.write64]
  rcases hor with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem Satisfies.write128_pointsTo128Lazy {R : SepProp} {m : Memory} {a : BitVec 64} (v : BitVec 128)
    (h : m ⊨ (a ↦₁₂₈ₗ) ∗ R) : m.write128 a v ⊨ (a ↦₁₂₈ v) ∗ R := by
  rw [pointsTo128Lazy_eq_memRegionLazy, memRegionLazy_split a 8 8 (by decide),
    ← pointsTo64Lazy_eq_memRegionLazy a, ← pointsTo64Lazy_eq_memRegionLazy (a + 8#64)] at h
  simp only [Memory.write128, pointsTo128]
  have h1 : m.write64 a (v.extractLsb' 0 64) ⊨
      (a ↦₆₄ v.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ₗ) ∗ R :=
    Satisfies.write64_pointsTo64Lazy (v.extractLsb' 0 64) (by simpa [sepConj_assoc] using h)
  have h2 : (m.write64 a (v.extractLsb' 0 64)).write64 (a + 8#64) (v.extractLsb' 64 64) ⊨
      ((a + 8#64) ↦₆₄ v.extractLsb' 64 64) ∗ (a ↦₆₄ v.extractLsb' 0 64) ∗ R :=
    Satisfies.write64_pointsTo64Lazy (v.extractLsb' 64 64)
      (by simpa [sepConj_left_comm, sepConj_assoc] using h1)
  simpa [sepConj_left_comm, sepConj_assoc] using h2

/-- Zero-filling an owned `memRegionLazy base len` via `Memory.zeroNonFrozen` (`madvise` with
    `MADV_DONTNEED`) clears `isLazyFree` and upgrades back to `memRegion base len ∗ P`. -/
theorem Satisfies.zeroNonFrozen_of_memRegionLazy {P : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegionLazy base len ∗ P) :
    m.zeroNonFrozen base len ⊨ memRegion base len ∗ P := by
  refine Satisfies.update_of_memRegionLazy (IsBlock.memRegion base len) h
    (AgreesOutside.zeroNonFrozen m base len) (fun a ha => ?_) trivial
  have hrw := Satisfies.perm_rw_of_memRegionLazy h ha
  have hin : (a - base).toNat < len := ha
  rw [Memory.isLazyFree_zeroNonFrozen, hrw]
  simp only [decide_eq_true hin]; rfl

/-- Zero-filling an owned `memRegionLazy base len` (`len ≤ 2 ^ 64`) via `Memory.zeroNonFrozen`
    (`madvise` with `MADV_DONTNEED`) clears `isLazyFree` and produces the zero-filled byte slice
    `(base ↦ₛ List.replicate len 0#8) ∗ P`. -/
theorem Satisfies.zeroNonFrozen_pointsToBytes_of_memRegionLazy {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (hlen : len ≤ 2 ^ 64)
    (h : m ⊨ memRegionLazy base len ∗ P) :
    m.zeroNonFrozen base len ⊨ (base ↦ₛ List.replicate len 0#8) ∗ P := by
  have hm := Satisfies.zeroNonFrozen_of_memRegionLazy h
  have hblk := IsBlock.pointsToBytes_len (a := base) (bs := List.replicate len 0#8)
    List.length_replicate
  exact (IsBlock.memRegion base len).update hblk (Nat.le_refl _) hm
    (AgreesOutside.rfl' _ base len)
    ⟨by simp [hlen], by
      simpa using readBytes_replicate_zero_of_inRegion
        (fun a ha => by
          have hrw := Satisfies.perm_rw_of_memRegionLazy h ha
          have hin : (a - base).toNat < len := ha
          rw [Memory.read8_zeroNonFrozen, hrw]
          simp only [decide_eq_true hin]; rfl) hlen len 0 (by omega)⟩

/-- Zero-filling an owned `memRegion base len` (`len ≤ 2 ^ 64`) via `Memory.zeroNonFrozen`
    (`madvise` with `MADV_DONTNEED`) produces the zero-filled byte slice
    `(base ↦ₛ List.replicate len 0#8) ∗ P`. -/
theorem Satisfies.zeroNonFrozen_pointsToBytes {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (hlen : len ≤ 2 ^ 64)
    (h : m ⊨ memRegion base len ∗ P) :
    m.zeroNonFrozen base len ⊨ (base ↦ₛ List.replicate len 0#8) ∗ P :=
  Satisfies.zeroNonFrozen_pointsToBytes_of_memRegionLazy hlen (Satisfies.memRegion_to_lazy h)

/-- Marking an owned `memRegionLazy base len` as `lazyFree` via `Memory.madvFreeNonFrozen`
    (`madvise` with `MADV_FREE`) preserves `memRegionLazy base len ∗ P`. -/
theorem Satisfies.madvFreeNonFrozen_of_memRegionLazy {P : SepProp} {m : Memory}
    {base : BitVec 64} {len : Nat} (h : m ⊨ memRegionLazy base len ∗ P) :
    m.madvFreeNonFrozen base len ⊨ memRegionLazy base len ∗ P := by
  obtain ⟨_, ⟨_, hR, hd, rfl, e, hr⟩, hm⟩ := satSep_iff.mp h
  rw [holds_memRegionLazy_iff] at e; subst e
  have hm₁ := Heap.Matches.of_union_left hm
  have hmR := Heap.Matches.of_union_right hd hm
  let m' := m.madvFreeNonFrozen base len
  have hm₁' : (regionHeapLazy base len).Matches m' :=
    regionHeapLazy_matches base len m' fun a ha => by
      simp [m', hm₁.1 a .lazy (by simp [regionHeapLazy, ha])]
  have hmR' : hR.Matches m' := by
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => ?_⟩
    · have hnot_in : ¬ (a - base).toNat < len := by
        intro hin
        have hin' : InRegion base len a := hin
        have hlz : (regionHeapLazy base len).phys a = some .lazy := by simp [regionHeapLazy, hin']
        rcases hd.1 a with h1 | h2 | ⟨_, h1, _⟩
        · rw [hlz] at h1; contradiction
        · rw [hc] at h2; contradiction
        · rw [hlz] at h1; cases h1
      have hlf : m'.isLazyFree a = m.isLazyFree a := by
        dsimp [m']
        rw [Memory.isLazyFree_madvFreeNonFrozen]
        simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have hcell := hmR.1 a c hc
      cases c <;> simp only [m', Memory.read8_madvFreeNonFrozen, Memory.perm_madvFreeNonFrozen, hlf] <;>
        exact hcell
    · simp only [m', Memory.perm_madvFreeNonFrozen, Memory.isAnon_madvFreeNonFrozen_apply]
      exact hmR.2.2 a hmap
  exact satSep_iff.mpr ⟨(regionHeapLazy base len).union hR,
    ⟨regionHeapLazy base len, hR, hd, rfl, holds_memRegionLazy_iff.mpr rfl, hr⟩,
    Heap.Matches.union hm₁' hmR'⟩

/-- Marking an owned `memRegion base len` as `lazyFree` via `Memory.madvFreeNonFrozen`
    (`madvise` with `MADV_FREE`) yields `memRegionLazy base len ∗ P`. -/
theorem Satisfies.madvFreeNonFrozen {P : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegion base len ∗ P) :
    m.madvFreeNonFrozen base len ⊨ memRegionLazy base len ∗ P :=
  Satisfies.madvFreeNonFrozen_of_memRegionLazy (Satisfies.memRegion_to_lazy h)

/-- Unmapping an owned `memRegionLazy base len` together with `memMapped base len` via
    `Memory.unmapNonFrozen` (`munmap`) preserves any separately owned assertion `P`. -/
theorem Satisfies.unmapNonFrozen_lazy {P : SepProp} {m : Memory} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegionLazy base len ∗ memMapped base len ∗ P) :
    m.unmapNonFrozen base len ⊨ P := by
  obtain ⟨_, ⟨h₁, _, hdisj1, rfl, e1, hrest⟩, hm⟩ := satSep_iff.mp h
  obtain ⟨h₂, hp, hdisj2, rfl, e2, hP⟩ := SepProp.holds_sepConj_iff.mp hrest
  rw [holds_memRegionLazy_iff] at e1; rw [holds_memMapped_iff] at e2; subst e1 e2
  have ⟨_, hd1p⟩ := (Heap.disjoint_union_right hdisj2).mp hdisj1
  have hm_hp := Heap.Matches.of_union_right hdisj2 (Heap.Matches.of_union_right hdisj1 hm)
  refine SepProp.satisfies_iff.mpr ⟨hp, hP, ⟨fun a c hpa => ?_, hm_hp.2.1, fun a hma => ?_⟩⟩
  · have hnot_in : ¬ (a - base).toNat < len := by
      intro hin
      have hin' : InRegion base len a := hin
      have hlz : (regionHeapLazy base len).phys a = some .lazy := by simp [regionHeapLazy, hin']
      rcases hd1p.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hlz] at h1; contradiction
      · rw [hpa] at h2; contradiction
      · rw [hlz] at h1; cases h1
    have hr : (m.unmapNonFrozen base len).read8 a = m.read8 a := by
      rw [Memory.read8_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hpm : (m.unmapNonFrozen base len).perm a = m.perm a := by
      rw [Memory.perm_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hlf : (m.unmapNonFrozen base len).isLazyFree a = m.isLazyFree a := by
      rw [Memory.isLazyFree_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hcell := hm_hp.1 a c hpa
    cases c <;> simp only [hr, hpm, hlf] <;> exact hcell
  · have hnot_in : ¬ (a - base).toNat < len := by
      intro hin
      have hin' : InRegion base len a := hin
      rcases hdisj2.2.2.2.2 a with hmap1 | hmap2
      · simp [mappedHeap, hin'] at hmap1
      · rw [hma] at hmap2; contradiction
    have hpm : (m.unmapNonFrozen base len).perm a = m.perm a := by
      rw [Memory.perm_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have han : (m.unmapNonFrozen base len).isAnon a = m.isAnon a := by
      rw [Memory.isAnon_unmapNonFrozen]
      simp only [decide_eq_false hnot_in, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [hpm, han]
    exact hm_hp.2.2 a hma

/-! ## Reflective AC Normalization of Separating Conjunctions (`SepTree`)

`SepTree.eq_of_isPerm` proves `A = B` for any two separating-conjunction trees `A`, `B` (over a
shared atom table) whose atom multisets agree, ignoring `emp` and parenthesization. The side
condition is a `List Nat` permutation check discharged by `rfl` (kernel evaluation), so the proof
term is linear in the number of atoms. -/

/-- A separating-conjunction tree over an atom table (`atom i` denotes the `i`-th atom). -/
inductive SepTree where
  | atom (i : Nat)
  | nil
  | sep (l r : SepTree)

/-- Right-nested separating conjunction of the atoms indexed by `is` (ending in `emp`). -/
def sepList (atoms : List SepProp) : List Nat → SepProp
  | [] => emp
  | i :: is => atoms.getD i emp ∗ sepList atoms is

namespace SepTree

/-- Interpretation of a `SepTree` over an atom table. -/
def denote (atoms : List SepProp) : SepTree → SepProp
  | atom i => atoms.getD i emp
  | nil => emp
  | sep l r => denote atoms l ∗ denote atoms r

/-- Atom indices of a `SepTree`, left to right. -/
def flatten : SepTree → List Nat
  | atom i => [i]
  | nil => []
  | sep l r => flatten l ++ flatten r

theorem sepList_append (atoms : List SepProp) (l₁ l₂ : List Nat) :
    sepList atoms (l₁ ++ l₂) = sepList atoms l₁ ∗ sepList atoms l₂ := by
  induction l₁ with
  | nil => exact (emp_sepConj _).symm
  | cons i is ih => simp only [List.cons_append, sepList, ih, sepConj_assoc]

theorem denote_eq (atoms : List SepProp) : ∀ t : SepTree, t.denote atoms = sepList atoms t.flatten
  | atom i => (sepConj_emp _).symm
  | nil => rfl
  | sep l r => by rw [denote, flatten, sepList_append, denote_eq atoms l, denote_eq atoms r]

theorem sepList_perm (atoms : List SepProp) {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    sepList atoms l₁ = sepList atoms l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [sepList, ih]
  | swap x y l => exact sepConj_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- AC(+`emp`) equality of two trees whose atom multisets agree. -/
theorem eq_of_isPerm (atoms : List SepProp) (t₁ t₂ : SepTree)
    (h : t₁.flatten.isPerm t₂.flatten = true) : t₁.denote atoms = t₂.denote atoms := by
  rw [denote_eq, denote_eq]
  exact sepList_perm atoms (List.isPerm_iff.mp h)

end SepTree

/-! ### Sort-Based Certificates

`SepTree.eq_of_sortIdx` is the `O(N log N)` variant of `eq_of_isPerm`: atoms are looked up in a
balanced `SepAtomTree` (`O(log N)` per leaf instead of `List.getD`'s `O(N)`), and the multiset
check compares merge-sorted index lists instead of running `List.isPerm`. -/

/-- A balanced (Braun) binary tree of atoms used as the atom table of `SepTree.denoteT`: index `0`
    is the root, odd `n` lives in the left subtree at index `n / 2`, and even `n > 0` in the right
    subtree at index `n / 2 - 1`, so lookup takes `O(log N)` kernel steps. -/
inductive SepAtomTree where
  | leaf
  | node (x : SepProp) (l r : SepAtomTree)

/-- Lookup in a `SepAtomTree` (`emp` when out of range). Defined by the recursor, without
    `brecOn`, for cheap kernel evaluation. -/
noncomputable def SepAtomTree.get : SepAtomTree → Nat → SepProp :=
  @SepAtomTree.rec (fun _ => Nat → SepProp) (fun _ => emp)
    (fun x _ _ ihl ihr n =>
      cond (n.beq 0) x (cond ((n % 2).beq 1) (ihl (n / 2)) (ihr (n / 2 - 1))))

namespace SepTree

/-! Kernel-evaluated sorting of atom indices. Every function below is defined by its recursor
(no `brecOn` / `match` compilation), since the certificates are checked by kernel reduction. -/

/-- Insert `x` into a sorted list, continuing with `rec` (the merge of the rest of the left list)
    once `x` is placed. -/
noncomputable def mergeIns (x : Nat) (rec : List Nat → List Nat) : List Nat → List Nat :=
  @List.rec Nat (fun _ => List Nat) (x :: rec [])
    (fun y ys ih => cond (Nat.ble x y) (x :: rec (y :: ys)) (y :: ih))

/-- Merge of two sorted lists. -/
noncomputable def merge : List Nat → List Nat → List Nat :=
  @List.rec Nat (fun _ => List Nat → List Nat) (fun ys => ys) (fun x _ ih => mergeIns x ih)

/-- One bottom-up merge round: merges adjacent lists pairwise (`o` holds an unpaired list). -/
noncomputable def mergePairs : List (List Nat) → Option (List Nat) → List (List Nat) :=
  @List.rec (List Nat) (fun _ => Option (List Nat) → List (List Nat))
    (fun o => @Option.rec (List Nat) (fun _ => List (List Nat)) [] (fun a => [a]) o)
    (fun b _ ih o => @Option.rec (List Nat) (fun _ => List (List Nat)) (ih (some b))
      (fun a => merge a b :: ih none) o)

/-- `n` merge rounds. -/
noncomputable def mergeRounds : Nat → List (List Nat) → List (List Nat) :=
  @Nat.rec (fun _ => List (List Nat) → List (List Nat)) (fun ls => ls)
    (fun _ ih ls => ih (mergePairs ls none))

/-- List append. -/
noncomputable def idxAppend : List Nat → List Nat → List Nat :=
  @List.rec Nat (fun _ => List Nat → List Nat) (fun ys => ys) (fun x _ ih ys => x :: ih ys)

/-- List flatten. -/
noncomputable def idxFlatten : List (List Nat) → List Nat :=
  @List.rec (List Nat) (fun _ => List Nat) [] (fun l _ ih => idxAppend l ih)

/-- The singleton runs `[i]` of the atoms of a tree, left to right, prepended to `acc`. -/
noncomputable def runs : SepTree → List (List Nat) → List (List Nat) :=
  @SepTree.rec (fun _ => List (List Nat) → List (List Nat)) (fun i acc => [i] :: acc)
    (fun acc => acc) (fun _ _ ihl ihr acc => ihl (ihr acc))

/-- The atom indices of a tree, sorted by bottom-up merge sort (64 rounds sort any tree of
    fewer than `2^64` atoms; the permutation property holds regardless). -/
noncomputable def sortIdx (t : SepTree) : List Nat := idxFlatten (mergeRounds 64 (runs t []))

/-- Boolean equality of index lists. -/
noncomputable def idxBEq : List Nat → List Nat → Bool :=
  @List.rec Nat (fun _ => List Nat → Bool)
    (fun ys => @List.rec Nat (fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun x _ ih ys => @List.rec Nat (fun _ => Bool) false (fun y ys' _ => x.beq y && ih ys') ys)

/-- Interpretation of a `SepTree` through an atom lookup function `f`. -/
noncomputable def denoteF (f : Nat → SepProp) : SepTree → SepProp :=
  @SepTree.rec (fun _ => SepProp) f emp (fun _ _ ihl ihr => ihl ∗ ihr)

/-- Interpretation of a `SepTree` over a `SepAtomTree` atom table. -/
noncomputable abbrev denoteT (tbl : SepAtomTree) (t : SepTree) : SepProp := denoteF tbl.get t

theorem mergeIns_perm (x : Nat) (xs : List Nat) (rec : List Nat → List Nat)
    (hrec : ∀ zs, (rec zs).Perm (xs ++ zs)) : ∀ ys, (mergeIns x rec ys).Perm (x :: (xs ++ ys))
  | [] => (hrec []).cons x
  | y :: ys => by
    show (cond (Nat.ble x y) (x :: rec (y :: ys)) (y :: mergeIns x rec ys)).Perm _
    cases Nat.ble x y
    · exact ((mergeIns_perm x xs rec hrec ys).cons y).trans
        ((List.Perm.swap x y _).trans (List.perm_middle.symm.cons x))
    · exact (hrec _).cons x

theorem merge_perm : ∀ xs ys : List Nat, (merge xs ys).Perm (xs ++ ys)
  | [], ys => List.Perm.refl ys
  | x :: xs, ys => mergeIns_perm x xs (merge xs) (merge_perm xs) ys

theorem mergePairs_perm : ∀ (ls : List (List Nat)) (o : Option (List Nat)),
    (mergePairs ls o).flatten.Perm (o.getD [] ++ ls.flatten)
  | [], none => by simp [mergePairs]
  | [], some a => by simp [mergePairs]
  | b :: ls, none => by
    show (mergePairs ls (some b)).flatten.Perm _
    simpa using mergePairs_perm ls (some b)
  | b :: ls, some a => by
    show (merge a b :: mergePairs ls none).flatten.Perm _
    simp only [List.flatten_cons, Option.getD_some, ← List.append_assoc]
    exact (merge_perm a b).append (by simpa using mergePairs_perm ls none)

theorem mergeRounds_perm : ∀ (n : Nat) (ls : List (List Nat)),
    (mergeRounds n ls).flatten.Perm ls.flatten
  | 0, _ => List.Perm.refl _
  | n + 1, ls => (mergeRounds_perm n (mergePairs ls none)).trans (by
      simpa using mergePairs_perm ls none)

theorem idxAppend_eq : ∀ xs ys : List Nat, idxAppend xs ys = xs ++ ys
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (idxAppend_eq xs ys)

theorem idxFlatten_eq : ∀ ls : List (List Nat), idxFlatten ls = ls.flatten
  | [] => rfl
  | l :: ls => by
    show idxAppend l (idxFlatten ls) = _
    rw [idxAppend_eq, idxFlatten_eq ls, List.flatten_cons]

theorem runs_flatten : ∀ (t : SepTree) (acc : List (List Nat)),
    (runs t acc).flatten = t.flatten ++ acc.flatten
  | .atom i, acc => by simp [runs, flatten]
  | .nil, acc => by simp [runs, flatten]
  | .sep l r, acc => by
    show (runs l (runs r acc)).flatten = _
    simp [flatten, runs_flatten l, runs_flatten r]

theorem sortIdx_perm (t : SepTree) : (sortIdx t).Perm t.flatten := by
  have h := mergeRounds_perm 64 (runs t [])
  rw [runs_flatten] at h
  simpa [sortIdx, idxFlatten_eq] using h

theorem idxBEq_eq : ∀ {l₁ l₂ : List Nat}, idxBEq l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    have h' : (x.beq y && idxBEq xs ys) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    rw [h'.1, idxBEq_eq h'.2]

/-- Right-nested separating conjunction of `f i` over `is` (ending in `emp`). -/
def sepListF (f : Nat → SepProp) : List Nat → SepProp
  | [] => emp
  | i :: is => f i ∗ sepListF f is

theorem sepListF_append (f : Nat → SepProp) (l₁ l₂ : List Nat) :
    sepListF f (l₁ ++ l₂) = sepListF f l₁ ∗ sepListF f l₂ := by
  induction l₁ with
  | nil => exact (emp_sepConj _).symm
  | cons i is ih => simp only [List.cons_append, sepListF, ih, sepConj_assoc]

theorem denoteF_eq (f : Nat → SepProp) : ∀ t : SepTree, t.denoteF f = sepListF f t.flatten
  | .atom i => (sepConj_emp _).symm
  | .nil => rfl
  | .sep l r => by
    show l.denoteF f ∗ r.denoteF f = _
    rw [flatten, sepListF_append, denoteF_eq f l, denoteF_eq f r]

theorem sepListF_perm (f : Nat → SepProp) {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    sepListF f l₁ = sepListF f l₂ := by
  induction h with
  | nil => rfl
  | cons i is ih => simp only [sepListF, ih]
  | swap x y l => exact sepConj_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- AC(+`emp`) equality of two trees whose sorted atom indices agree. The side condition is
    discharged by `rfl` in `O(N log N)` kernel steps. -/
theorem eq_of_sortIdx (f : Nat → SepProp) (t₁ t₂ : SepTree)
    (h : idxBEq (sortIdx t₁) (sortIdx t₂) = true) : t₁.denoteF f = t₂.denoteF f := by
  rw [denoteF_eq, denoteF_eq]
  exact sepListF_perm f ((sortIdx_perm t₁).symm.trans ((idxBEq_eq h) ▸ sortIdx_perm t₂))

end SepTree

/-! ## Authoritative Ghost Map Assertions (`ghostMapAuth`, `ghostMapElem`) -/

/-- Partial heap owning the full authoritative ghost map `L` at ghost name `γ`. -/
def ghostMapAuthHeap (γ : GhostName) (L : BitVec 64 → Option Nat) : Heap :=
  { phys := fun _ => none
    auth := fun γ' k => if γ' = γ then some (L k) else none
    frag := fun _ _ => none }

/-- Partial heap owning the single fragment entry `p ↪[γ] v` at ghost name `γ`. -/
def ghostMapElemHeap (γ : GhostName) (p : BitVec 64) (v : Nat) : Heap :=
  { phys := fun _ => none
    auth := fun _ _ => none
    frag := fun γ' k => if γ' = γ ∧ k = p then some v else none }

/-- Authoritative ownership of the ghost map `L : BitVec 64 → Option Nat` at ghost name `γ`. -/
def ghostMapAuth (γ : GhostName) (L : BitVec 64 → Option Nat) : SepProp :=
  ⟨fun h => h = ghostMapAuthHeap γ L⟩

/-- Fragment ownership of key `p` mapped to `v` at ghost name `γ`. -/
def ghostMapElem (γ : GhostName) (p : BitVec 64) (v : Nat) : SepProp :=
  ⟨fun h => h = ghostMapElemHeap γ p v⟩

theorem ghostMapAuthHeap_matches (γ : GhostName) (L : BitVec 64 → Option Nat) (m : Memory) :
    (ghostMapAuthHeap γ L).Matches m := by
  refine ⟨fun _ _ h => by contradiction, ⟨γ + 1, fun γ' hγ' k => ?_⟩, fun _ h => by contradiction⟩
  have hne : γ' ≠ γ := Nat.ne_of_gt hγ'
  exact ⟨by simp [ghostMapAuthHeap, hne], rfl⟩

theorem ghostMapElemHeap_matches (γ : GhostName) (p : BitVec 64) (v : Nat) (m : Memory) :
    (ghostMapElemHeap γ p v).Matches m := by
  refine ⟨fun _ _ h => by contradiction, ⟨γ + 1, fun γ' hγ' k => ?_⟩, fun _ h => by contradiction⟩
  have hne : γ' ≠ γ := Nat.ne_of_gt hγ'
  exact ⟨rfl, by simp [ghostMapElemHeap, hne]⟩

/-- Allocate a fresh ghost map initialized to `L` at some fresh ghost name `γ`. -/
theorem ghostMap_init (L : BitVec 64 → Option Nat) :
    emp ⊢ |==> ∃∗ γ : GhostName, ghostMapAuth γ L := by
  refine SepProp.entails_iff.mpr fun h he => SepProp.holds_bupd_iff.mpr fun m hf _ hm => ?_
  rw [SepProp.holds_emp_iff] at he; subst he
  rw [Heap.union_empty_left] at hm
  rcases hm.2.1 with ⟨γ, hγ⟩
  have hd : (ghostMapAuthHeap γ L).Disjoint hf := by
    refine ⟨fun _ => Or.inl rfl, fun γ' k => ?_, fun _ _ => Or.inl rfl,
      fun γ' k oa v h => ?_, fun _ => Or.inl rfl⟩
    · by_cases hγ' : γ' = γ
      · subst γ'
        exact Or.inr (hγ γ (Nat.le_refl γ) k).1
      · exact Or.inl (by simp [ghostMapAuthHeap, hγ'])
    · rcases h with ⟨ha, hfv⟩ | ⟨_, hfv⟩
      · dsimp [ghostMapAuthHeap] at ha
        by_cases hγ' : γ' = γ
        · subst γ'
          have hfn := (hγ γ (Nat.le_refl γ) k).2
          rw [hfn] at hfv; contradiction
        · simp [hγ'] at ha
      · dsimp [ghostMapAuthHeap] at hfv; contradiction
  exact ⟨ghostMapAuthHeap γ L, SepProp.holds_sepExists_iff.mpr ⟨γ, rfl⟩, hd,
    Heap.Matches.union (ghostMapAuthHeap_matches γ L m) hm⟩

/-- Combining `ghostMapAuth γ L` with `ghostMapElem γ p v` witnesses `L p = some v`. -/
theorem ghostMap_lookup (γ : GhostName) (L : BitVec 64 → Option Nat) (p : BitVec 64) (v : Nat) :
    ghostMapAuth γ L ∗ ghostMapElem γ p v ⊢
      ⌜L p = some v⌝ ∗ ghostMapAuth γ L ∗ ghostMapElem γ p v := by
  refine SepProp.entails_iff.mpr fun h hh => ?_
  obtain ⟨h₁, h₂, hd, rfl, e1, e2⟩ := SepProp.holds_sepConj_iff.mp hh
  change h₁ = _ at e1; change h₂ = _ at e2; subst e1 e2
  have hlp : L p = some v := by
    apply hd.2.2.2.1 γ p (L p) v
    exact Or.inl ⟨by simp [ghostMapAuthHeap], by simp [ghostMapElemHeap]⟩
  rw [pure_sepConj]
  exact ⟨hlp, SepProp.holds_sepConj_iff.mpr ⟨_, _, hd, rfl, rfl, rfl⟩⟩

/-- Insert a fresh key `p` (`L p = none`) with value `v` into `ghostMapAuth γ L`, producing
    `ghostMapElem γ p v`. -/
theorem ghostMap_alloc (γ : GhostName) (L : BitVec 64 → Option Nat) (p : BitVec 64) (v : Nat)
    (hnone : L p = none) :
    ghostMapAuth γ L ⊢
      |==> (ghostMapAuth γ (fun k => if k = p then some v else L k) ∗ ghostMapElem γ p v) := by
  refine SepProp.entails_iff.mpr fun h he => SepProp.holds_bupd_iff.mpr fun m hf hd hm => ?_
  change h = _ at he; subst he
  let L' : BitVec 64 → Option Nat := fun k => if k = p then some v else L k
  let h₁' := ghostMapAuthHeap γ L'
  let h₂' := ghostMapElemHeap γ p v
  have hm_f : hf.Matches m := Heap.Matches.of_union_right hd hm
  have hfp_none : hf.frag γ p = none := by
    cases hfp : hf.frag γ p with
    | none => rfl
    | some w =>
      have hbad := hd.2.2.2.1 γ p (L p) w (Or.inl ⟨by simp [ghostMapAuthHeap], hfp⟩)
      rw [hnone] at hbad; contradiction
  have hd12 : h₁'.Disjoint h₂' := by
    refine ⟨fun _ => Or.inl rfl, fun _ _ => Or.inr rfl, fun _ _ => Or.inl rfl,
      fun γ' k oa w h => ?_, fun _ => Or.inl rfl⟩
    rcases h with ⟨ha, hf_w⟩ | ⟨ha, _⟩
    · dsimp [h₁', ghostMapAuthHeap] at ha
      dsimp [h₂', ghostMapElemHeap] at hf_w
      by_cases hγ' : γ' = γ
      · subst γ'
        by_cases hkp : k = p
        · subst k
          simp [L'] at ha hf_w
          rw [← ha, ← hf_w]
        · simp [hkp] at hf_w
      · simp [hγ'] at hf_w
    · dsimp [h₂', ghostMapElemHeap] at ha; contradiction
  have hd1f : h₁'.Disjoint hf := by
    refine ⟨fun _ => Or.inl rfl, fun γ' k => ?_, fun _ _ => Or.inl rfl,
      fun γ' k oa w h => ?_, fun _ => Or.inl rfl⟩
    · rcases hd.2.1 γ' k with h1 | h2
      · dsimp [ghostMapAuthHeap] at h1
        exact Or.inl (by dsimp [h₁', ghostMapAuthHeap]; split at h1 <;> simp_all)
      · exact Or.inr h2
    · rcases h with ⟨ha, hf_w⟩ | ⟨_, hf_w⟩
      · dsimp [h₁', ghostMapAuthHeap] at ha
        by_cases hγ' : γ' = γ
        · subst γ'
          simp only [ite_true, Option.some.injEq] at ha
          subst oa
          by_cases hkp : k = p
          · subst k; rw [hfp_none] at hf_w; contradiction
          · simp only [L', hkp, ite_false]
            exact hd.2.2.2.1 γ k (L k) w (Or.inl ⟨by simp [ghostMapAuthHeap], hf_w⟩)
        · simp [hγ'] at ha
      · dsimp [h₁', ghostMapAuthHeap] at hf_w; contradiction
  have hd2f : h₂'.Disjoint hf := by
    refine ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun γ' k => ?_,
      fun γ' k oa w h => ?_, fun _ => Or.inl rfl⟩
    · dsimp [h₂', ghostMapElemHeap]
      by_cases hγp : γ' = γ ∧ k = p
      · rcases hγp with ⟨rfl, rfl⟩
        exact Or.inr hfp_none
      · simp [hγp]
    · rcases h with ⟨ha, _⟩ | ⟨ha, hf_w⟩
      · dsimp [h₂', ghostMapElemHeap] at ha; contradiction
      · dsimp [h₂', ghostMapElemHeap] at hf_w
        by_cases hγp : γ' = γ ∧ k = p
        · rcases hγp with ⟨rfl, rfl⟩
          rcases hd.2.1 γ' k with h1 | h2
          · simp [ghostMapAuthHeap] at h1
          · rw [h2] at ha; contradiction
        · simp [hγp] at hf_w
  have hd_u : (h₁'.union h₂').Disjoint hf :=
    (Heap.disjoint_union_left hd12).mpr ⟨hd1f, hd2f⟩
  refine ⟨h₁'.union h₂', SepProp.holds_sepConj_iff.mpr ⟨h₁', h₂', hd12, rfl, rfl, rfl⟩, hd_u, ?_⟩
  exact Heap.Matches.union
    (Heap.Matches.union (ghostMapAuthHeap_matches γ L' m) (ghostMapElemHeap_matches γ p v m))
    hm_f

/-- Delete key `p` from `ghostMapAuth γ L` by consuming `ghostMapElem γ p v`. -/
theorem ghostMap_delete (γ : GhostName) (L : BitVec 64 → Option Nat) (p : BitVec 64) (v : Nat) :
    ghostMapAuth γ L ∗ ghostMapElem γ p v ⊢
      |==> ghostMapAuth γ (fun k => if k = p then none else L k) := by
  refine SepProp.entails_iff.mpr fun h hh => SepProp.holds_bupd_iff.mpr fun m hf hd hm => ?_
  obtain ⟨h₁, h₂, hd12, rfl, e1, e2⟩ := SepProp.holds_sepConj_iff.mp hh
  change h₁ = _ at e1; change h₂ = _ at e2; subst e1 e2
  let L' : BitVec 64 → Option Nat := fun k => if k = p then none else L k
  let h' := ghostMapAuthHeap γ L'
  have ⟨hd1f, hd2f⟩ := (Heap.disjoint_union_left hd12).mp hd
  have hm_f : hf.Matches m := Heap.Matches.of_union_right hd hm
  have hfp_none : hf.frag γ p = none := by
    rcases hd2f.2.2.1 γ p with h1 | h2
    · simp [ghostMapElemHeap] at h1
    · exact h2
  have hd' : h'.Disjoint hf := by
    refine ⟨fun _ => Or.inl rfl, fun γ' k => ?_, fun _ _ => Or.inl rfl,
      fun γ' k oa w h => ?_, fun _ => Or.inl rfl⟩
    · rcases hd1f.2.1 γ' k with h1 | h2
      · dsimp [ghostMapAuthHeap] at h1
        exact Or.inl (by dsimp [h', ghostMapAuthHeap]; split at h1 <;> simp_all)
      · exact Or.inr h2
    · rcases h with ⟨ha, hf_w⟩ | ⟨_, hf_w⟩
      · dsimp [h', ghostMapAuthHeap] at ha
        by_cases hγ' : γ' = γ
        · subst γ'
          simp only [ite_true, Option.some.injEq] at ha
          subst oa
          by_cases hkp : k = p
          · subst k; rw [hfp_none] at hf_w; contradiction
          · simp only [L', hkp, ite_false]
            exact hd1f.2.2.2.1 γ k (L k) w (Or.inl ⟨by simp [ghostMapAuthHeap], hf_w⟩)
        · simp [hγ'] at ha
      · dsimp [h', ghostMapAuthHeap] at hf_w; contradiction
  exact ⟨h', rfl, hd', Heap.Matches.union (ghostMapAuthHeap_matches γ L' m) hm_f⟩

/-- Two fragments at the same key `(γ, p)` are mutually exclusive. -/
theorem ghostMapElem_exclusive (γ : GhostName) (p : BitVec 64) (v₁ v₂ : Nat) :
    ghostMapElem γ p v₁ ∗ ghostMapElem γ p v₂ ⊢ ⌜False⌝ := by
  refine SepProp.entails_iff.mpr fun h hh => ?_
  obtain ⟨h₁, h₂, hd, rfl, e1, e2⟩ := SepProp.holds_sepConj_iff.mp hh
  change h₁ = _ at e1; change h₂ = _ at e2; subst e1 e2
  exfalso
  rcases hd.2.2.1 γ p with h1 | h2
  · simp [ghostMapElemHeap] at h1
  · simp [ghostMapElemHeap] at h2

/-- A fragment token `ghostMapElem γ p v` cannot be forged from `emp`. -/
theorem ghostMapElem_not_forgeable (γ : GhostName) (p : BitVec 64) (v : Nat) :
    ¬ (emp ⊢ ghostMapElem γ p v) := by
  intro h
  have h1 : Heap.empty = ghostMapElemHeap γ p v :=
    SepProp.entails_iff.mp h Heap.empty (SepProp.holds_emp_iff.mpr rfl)
  have h2 := congrFun (congrFun (congrArg Heap.frag h1) γ) p
  simp [Heap.empty, ghostMapElemHeap] at h2

/-- A single fragment token `ghostMapElem γ p v` is satisfiable on any physical memory `m`. -/
theorem ghostMapElem_satisfiable (γ : GhostName) (p : BitVec 64) (v : Nat) (m : Memory) :
    m ⊨ ghostMapElem γ p v :=
  SepProp.satisfies_iff.mpr ⟨ghostMapElemHeap γ p v, rfl, ghostMapElemHeap_matches γ p v m⟩

/-! ## Seal Separation Logic Abstraction Boundary -/

set_option allowUnsafeReducibility true in
attribute [irreducible]
  Heap.empty Heap.singleton Heap.singletonRO Heap.singletonProtNone Heap.singletonLazy
  Heap.Disjoint Heap.union Heap.Matches Heap.CoversRegion Heap.complement
  SepProp.Satisfies SepProp.Entails SepProp.bupd SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepImp SepProp.sepExists
  SepProp.complementSep
  ghostMapAuth ghostMapElem
  pointsTo8 pointsToBytes pointsTo16 pointsTo32 pointsTo64 pointsTo128 pointsToWords64
  pointsTo8RO pointsToBytesRO pointsTo16RO pointsTo32RO pointsTo64RO pointsTo128RO pointsToWords64RO
  pointsTo8ProtNone pointsToBytesProtNone
  pointsTo8Lazy pointsTo16Lazy pointsTo32Lazy pointsTo64Lazy pointsTo128Lazy
  regionHeap regionHeapRO regionHeapProtNone regionHeapLazy mappedHeap
  regionBlock regionBlockRO regionBlockProtNone memRegion memRegionProtNone memRegionLazy memMapped
  stackFrame16At stackFrame32At

-- Define separation-logic typeclass instances after `attribute [irreducible]` so Lean's
-- discrimination tree indexes `SepProp.sepConj`, `SepProp.emp`, and all spatial predicates
-- as irreducible constants instead of unfolding them to `fun h => ...`.
/-- Per-atom-kind lookup of the `IsBlock` description of a spatial atom `P` (base address, byte
    length, and content predicate `Φ`). Instances are keyed on the atom's head constant only; there
    is no instance search through `∗` (reassociation is done reflectively by `SepTree`). -/
class SepBlock (P : SepProp) (base : outParam (BitVec 64)) (len : outParam Nat)
    (Φ : outParam (Memory → Prop)) : Prop where
  isBlock : IsBlock P base len Φ

instance (a : BitVec 64) (v : BitVec 8) : SepBlock (a ↦₈ v) a 1 (fun m => m.read8 a = v) :=
  ⟨IsBlock.pointsTo8 a v⟩
instance (a : BitVec 64) (bs : List (BitVec 8)) :
  SepBlock (a ↦ₛ bs) a bs.length
      (fun m => bs.length ≤ 2 ^ 64 ∧ m.readBytes a bs.length = bs) :=
  ⟨IsBlock.pointsToBytes a bs⟩
instance (a : BitVec 64) (v : BitVec 16) : SepBlock (a ↦₁₆ v) a 2 (fun m => m.read16 a = v) :=
  ⟨IsBlock.pointsTo16 a v⟩
instance (a : BitVec 64) (v : BitVec 32) : SepBlock (a ↦₃₂ v) a 4 (fun m => m.read32 a = v) :=
  ⟨IsBlock.pointsTo32 a v⟩
instance (a : BitVec 64) (v : BitVec 64) : SepBlock (a ↦₆₄ v) a 8 (fun m => m.read64 a = v) :=
  ⟨IsBlock.pointsTo64 a v⟩
instance (a : BitVec 64) (v : BitVec 128) : SepBlock (a ↦₁₂₈ v) a 16 (fun m => m.read128 a = v) :=
  ⟨IsBlock.pointsTo128 a v⟩
instance (b : BitVec 64) (n : Nat) (m₀ : Memory) :
    SepBlock (regionBlock b n m₀) b n (fun m => ∀ x, InRegion b n x → m.read8 x = m₀.read8 x) :=
  ⟨IsBlock.regionBlock b n m₀⟩
instance (b : BitVec 64) (n : Nat) : SepBlock (memRegion b n) b n (fun _ => True) :=
  ⟨IsBlock.memRegion b n⟩
instance (sp : BitVec 64) : SepBlock (stackFrame16At sp) (sp - 16#64) 16 (fun _ => True) :=
  ⟨IsBlock.stackFrame16At sp⟩
instance (sp : BitVec 64) : SepBlock (stackFrame32At sp) (sp - 32#64) 32 (fun _ => True) :=
  ⟨IsBlock.stackFrame32At sp⟩

end

end ProofLib
