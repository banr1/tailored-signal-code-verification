/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.SepLogic
public import Arm64.Trusted.Spec.SepLogicModel
public import Arm64.Trusted.Spec.Hoare
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.Abi.Aapcs
public import ProofLib.Hoare.Safety
import ProofLib.SepLogic.Model

/-!
# Separation-Logic and Hoare-Judgment Metatheory

Collects 72 algebraic, semantic, and operational laws for the TCB specification primitives in
[`Arm64/Trusted/Spec/SepLogic.lean`](../../Trusted/Spec/SepLogic.lean) and
[`Arm64/Trusted/Spec/Hoare.lean`](../../Trusted/Spec/Hoare.lean), proving each by direct reference
to its theorem in `ProofLib`. Companion module [`SpecAdequacyTour.lean`](SpecAdequacyTour.lean)
demonstrates end-to-end operational adequacy of concrete `c_spec` and `c_type_spec` contracts over
`Arm64.Steps`, `State.readReg64`, and `Memory.read8` / `read64` / `readBytes`.
-/

@[expose] public section

namespace Arm64.Testing.Tours.SepLogicLawsTour

universe u

open Arm64

/-! ## Partial Commutative Monoid Laws for `Heap`

[`Arm64/Trusted/Spec/SepLogic.lean`](../../Trusted/Spec/SepLogic.lean) models a partial heap
(`Heap`) with physical byte cells (`Heap.phys : BitVec 64 → Option HeapCell`, where `HeapCell` is
`.rw b` for exclusive read-write ownership, `.ro b` for duplicable read-only ownership, or
`.protNone b` for exclusive inaccessible `PROT_NONE` ownership with preserved byte `b`), virtual
mapping tokens (`Heap.mapped`), and ghost authoritative/fragment map slots (`Heap.auth`,
`Heap.frag`).

The separating conjunction `P ∗ Q` is defined over `Heap.Disjoint` and `Heap.union`, and memory
satisfaction `m ⊨ P` is mediated by `Heap.Matches m`. Below we witness that
`(Heap, Heap.empty, Heap.Disjoint, Heap.union)` forms a partial commutative monoid compatible with
`Heap.Matches`: symmetry and unit laws (`Disjoint.symm`, `disjoint_empty_*`, `*_union`),
associativity, commutativity, and distribution across disjoint unions, singleton non-aliasing for
`.rw` and `.protNone` cells, and projection of `Heap.Matches` across disjoint unions.
-/

namespace Heap

/-- Heap disjointness (`Heap.Disjoint`) is symmetric. -/
theorem Disjoint.symm {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) : h₂.Disjoint h₁ :=
  ProofLib.Heap.Disjoint.symm hd

/-- The empty heap is left-disjoint from every heap. -/
theorem disjoint_empty_left (h : Heap) : Heap.empty.Disjoint h :=
  ProofLib.Heap.disjoint_empty_left h

/-- The empty heap is right-disjoint from every heap. -/
theorem disjoint_empty_right (h : Heap) : h.Disjoint Heap.empty :=
  ProofLib.Heap.disjoint_empty_right h

/-- Left identity of `Heap.union`. -/
theorem empty_union (h : Heap) : Heap.empty.union h = h :=
  ProofLib.Heap.union_empty_left h

/-- Right identity of `Heap.union`. -/
theorem union_empty (h : Heap) : h.union Heap.empty = h :=
  ProofLib.Heap.union_empty_right h

/-- Commutativity of `Heap.union` on disjoint heaps. -/
theorem union_comm {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) :
    h₁.union h₂ = h₂.union h₁ :=
  ProofLib.Heap.union_comm_of_disjoint hd

/-- Associativity of `Heap.union`. -/
theorem union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) :=
  ProofLib.Heap.union_assoc h₁ h₂ h₃

/-- Disjointness distributes over left `Heap.union` when the unioned heaps are disjoint. -/
theorem disjoint_union_left {h₁ h₂ h₃ : Heap} (hd12 : h₁.Disjoint h₂) :
    (h₁.union h₂).Disjoint h₃ ↔ h₁.Disjoint h₃ ∧ h₂.Disjoint h₃ :=
  ProofLib.Heap.disjoint_union_left hd12

/-- Disjointness distributes over right `Heap.union` when the unioned heaps are disjoint. -/
theorem disjoint_union_right {h₁ h₂ h₃ : Heap} (hd23 : h₂.Disjoint h₃) :
    h₁.Disjoint (h₂.union h₃) ↔ h₁.Disjoint h₂ ∧ h₁.Disjoint h₃ :=
  ProofLib.Heap.disjoint_union_right hd23

/-- Two read-write singleton heaps are disjoint if and only if their addresses are distinct. -/
theorem disjoint_singleton_iff (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) :
    (Heap.singleton a₁ v₁).Disjoint (Heap.singleton a₂ v₂) ↔ a₁ ≠ a₂ :=
  ProofLib.Heap.disjoint_singleton_iff a₁ a₂ v₁ v₂

/-- Two `PROT_NONE` singleton heaps are disjoint if and only if their addresses are distinct. -/
theorem disjoint_singletonProtNone_iff (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) :
    (Heap.singletonProtNone a₁ v₁).Disjoint (Heap.singletonProtNone a₂ v₂) ↔ a₁ ≠ a₂ :=
  ProofLib.Heap.disjoint_singletonProtNone_iff a₁ a₂ v₁ v₂

/-- The empty heap matches every memory. -/
theorem Matches.empty (m : Memory) : Heap.empty.Matches m :=
  ProofLib.Heap.Matches.empty m

/-- If a union of two heaps matches `m`, its left component matches `m`. -/
theorem Matches.of_union_left {h₁ h₂ : Heap} {m : Memory}
    (hm : (h₁.union h₂).Matches m) : h₁.Matches m :=
  ProofLib.Heap.Matches.of_union_left hm

/-- If a disjoint union of two heaps matches `m`, its right component matches `m`. -/
theorem Matches.of_union_right {h₁ h₂ : Heap} {m : Memory}
    (hd : h₁.Disjoint h₂) (hm : (h₁.union h₂).Matches m) : h₂.Matches m :=
  ProofLib.Heap.Matches.of_union_right hd hm

end Heap

/-! ## Separation Logic Laws for `SepProp`

Built on the `Heap` PCM, `SepProp` in [`Arm64/Trusted/Spec/SepLogic.lean`](../../Trusted/Spec/SepLogic.lean)
satisfies the laws of bunched implications (BI) and the basic update modality (`|==>`): the
entailment preorder `P ⊢ Q` and its soundness over `m ⊨ P`; the commutative monoid `(SepProp, ∗, emp)`
and monotonicity of `∗`; the magic wand adjunction `(P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)` and modus ponens;
pure assertion lifting (`⌜p⌝`), extraction, and existential (`∃∗`) distribution over `∗`; and
introduction, monotonicity, idempotence, and frame preservation for `|==>`.
-/

/-- Reflexivity of entailment (`⊢`). -/
theorem entails_refl (P : SepProp) : P ⊢ P :=
  ProofLib.Entails.refl P

/-- Transitivity of entailment (`⊢`). -/
theorem entails_trans {P Q R : SepProp} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  ProofLib.Entails.trans h₁ h₂

/-- Soundness of entailment (`⊢`) with respect to memory satisfaction (`⊨`). -/
theorem satisfies_mono {P Q : SepProp} {m : Memory} (h : P ⊢ Q) (hm : m ⊨ P) : m ⊨ Q :=
  ProofLib.Satisfies.mono h hm

/-- Commutativity of separating conjunction (`∗`). -/
theorem sepConj_comm (P Q : SepProp) : (P ∗ Q) = (Q ∗ P) :=
  ProofLib.sepConj_comm P Q

/-- Associativity of separating conjunction (`∗`). -/
theorem sepConj_assoc (P Q R : SepProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) :=
  ProofLib.sepConj_assoc P Q R

/-- Left identity of `emp` for separating conjunction (`∗`). -/
theorem emp_sepConj (P : SepProp) : (emp ∗ P) = P :=
  ProofLib.emp_sepConj P

/-- Right identity of `emp` for separating conjunction (`∗`). -/
theorem sepConj_emp (P : SepProp) : (P ∗ emp) = P :=
  ProofLib.sepConj_emp P

/-- Monotonicity of separating conjunction (`∗`) with respect to entailment (`⊢`). -/
theorem sepConj_mono {P₁ P₂ Q₁ Q₂ : SepProp} (hp : P₁ ⊢ P₂) (hq : Q₁ ⊢ Q₂) :
    (P₁ ∗ Q₁) ⊢ (P₂ ∗ Q₂) :=
  ProofLib.sepConj_mono hp hq

/-- Left monotonicity of separating conjunction (`∗`). -/
theorem sepConj_mono_left {P₁ P₂ Q : SepProp} (hp : P₁ ⊢ P₂) :
    (P₁ ∗ Q) ⊢ (P₂ ∗ Q) :=
  ProofLib.sepConj_mono_left hp

/-- Right monotonicity of separating conjunction (`∗`). -/
theorem sepConj_mono_right {P Q₁ Q₂ : SepProp} (hq : Q₁ ⊢ Q₂) :
    (P ∗ Q₁) ⊢ (P ∗ Q₂) :=
  ProofLib.sepConj_mono_right hq

/-- Magic wand (`-∗`) adjunction: `(P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)`. -/
theorem sepImp_adj (P Q R : SepProp) : ((P ∗ Q) ⊢ R) ↔ (P ⊢ (Q -∗ R)) :=
  ProofLib.sepImp_adj P Q R

/-- Magic wand (`-∗`) elimination (modus ponens): `P ∗ (P -∗ Q) ⊢ Q`. -/
theorem sepImp_elim (P Q : SepProp) : (P ∗ (P -∗ Q)) ⊢ Q :=
  ProofLib.Entails.wand_elim P Q

/-- Pure `True` is equal to `emp`. -/
theorem pure_true : (⌜True⌝ : SepProp) = emp :=
  ProofLib.pure_true

/-- Separating conjunction with a pure assertion `⌜p⌝` reduces to pointwise conjunction. -/
theorem pure_sepConj (p : Prop) (P : SepProp) : (⌜p⌝ ∗ P) = ⟨fun h => p ∧ P h⟩ :=
  ProofLib.pure_sepConj p P

/-- `⌜False⌝ ∗ R` is unsatisfiable in every memory `m`. -/
theorem pure_false_unsat (m : Memory) (R : SepProp) : ¬ (m ⊨ (⌜False⌝ ∗ R)) :=
  ProofLib.not_satisfies_false_sepConj

/-- Pure extraction adjunction for `⌜p⌝ ∗ P ⊢ Q`. -/
theorem pure_extract_iff (p : Prop) (P Q : SepProp) :
    ((⌜p⌝ ∗ P) ⊢ Q) ↔ (p → (P ⊢ Q)) :=
  ProofLib.pure_extract_iff p P Q

/-- Existential quantification (`∃∗`) distributes over left separating conjunction (`∗`). -/
theorem sepExists_sepConj_left {α : Sort u} (P : α → SepProp) (Q : SepProp) :
    ((∃∗ x, P x) ∗ Q) = (∃∗ x, P x ∗ Q) :=
  ProofLib.sepExists_sepConj_left P Q

/-- Existential quantification (`∃∗`) distributes over right separating conjunction (`∗`). -/
theorem sepExists_sepConj_right {α : Sort u} (P : SepProp) (Q : α → SepProp) :
    (P ∗ (∃∗ x, Q x)) = (∃∗ x, P ∗ Q x) :=
  ProofLib.sepExists_sepConj_right P Q

/-- Introduction rule for the basic update modality (`P ⊢ |==> P`). -/
theorem bupd_intro {P : SepProp} : P ⊢ |==> P :=
  ProofLib.bupd_intro P

/-- Monotonicity of the basic update modality (`(P ⊢ Q) → (|==> P ⊢ |==> Q)`). -/
theorem bupd_mono {P Q : SepProp} (hPQ : P ⊢ Q) : (|==> P) ⊢ |==> Q :=
  ProofLib.bupd_mono hPQ

/-- Idempotence / transitivity of the basic update modality (`|==> |==> P ⊢ |==> P`). -/
theorem bupd_trans {P : SepProp} : (|==> |==> P) ⊢ |==> P :=
  ProofLib.bupd_trans P

/-- Right frame rule for the basic update modality (`(|==> P) ∗ R ⊢ |==> (P ∗ R)`). -/
theorem bupd_frame_r {P R : SepProp} : (|==> P) ∗ R ⊢ |==> (P ∗ R) :=
  ProofLib.bupd_frame_r P R

/-! ## Points-To and Memory Satisfaction Laws

The points-to primitives in [`Arm64/Trusted/Spec/SepLogic.lean`](../../Trusted/Spec/SepLogic.lean)
connect `SepProp` assertions (`↦₈`, `↦₁₆`, `↦₃₂`, `↦₆₄`, `↦ₛ`, `↦₈ₙ`, `↦ₙ`, `memRegionProtNone`,
`memMapped`) to concrete `Memory` reads and permissions: mutual exclusion of `↦₈` and `↦₈ₙ` at the
same address, frame projection under `m ⊨ P ∗ Q`, concrete byte and little-endian multi-byte read
and permission extraction, contiguous range splitting, and allocation/permission transitions across
`mmap`, `mprotect`, and `munmap` (preserving underlying byte contents across permission changes per
Linux `mm/mprotect.c`).
-/

/-- Exclusivity / non-aliasing of `pointsTo8`: two `↦₈` assertions at the same address are
    mutually inconsistent. -/
theorem pointsTo8_conflict (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    (a ↦₈ v₁ ∗ a ↦₈ v₂) ⊢ ⌜False⌝ :=
  ProofLib.pointsTo8_conflict a v₁ v₂

/-- Exclusivity / non-aliasing of `pointsTo8ProtNone`: two `↦₈ₙ` assertions at the same address
    are mutually inconsistent. -/
theorem pointsTo8ProtNone_conflict (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    (a ↦₈ₙ v₁ ∗ a ↦₈ₙ v₂) ⊢ ⌜False⌝ :=
  ProofLib.pointsTo8ProtNone_conflict a v₁ v₂

/-- Mutual exclusion between `pointsTo8ProtNone` (`↦₈ₙ`) and `pointsTo8` (`↦₈`) at the same address. -/
theorem pointsTo8ProtNone_pointsTo8_conflict (a : BitVec 64) (v₁ v₂ : BitVec 8) :
    (a ↦₈ₙ v₁ ∗ a ↦₈ v₂) ⊢ ⌜False⌝ :=
  ProofLib.pointsTo8ProtNone_pointsTo8_conflict a v₁ v₂

/-- Dropping a right frame under memory satisfaction (`m ⊨ P ∗ Q → m ⊨ P`). -/
theorem satisfies_sepConj_left {P Q : SepProp} {m : Memory} (hm : m ⊨ P ∗ Q) : m ⊨ P :=
  ProofLib.Satisfies.of_sep_left hm

/-- Dropping a left frame under memory satisfaction (`m ⊨ P ∗ Q → m ⊨ Q`). -/
theorem satisfies_sepConj_right {P Q : SepProp} {m : Memory} (hm : m ⊨ P ∗ Q) : m ⊨ Q :=
  ProofLib.Satisfies.of_sep_right hm

/-- Memory satisfaction of a single byte `a ↦₈ v` gives `m.read8 a = v` and `m.perm a = some Perm.rw`. -/
theorem satisfies_pointsTo8 {m : Memory} {a : BitVec 64} {v : BitVec 8}
    (hm : m ⊨ (a ↦₈ v)) : m.read8 a = v ∧ m.perm a = some Perm.rw :=
  ProofLib.satisfies_pointsTo8 hm

/-- Framed byte read and permission extraction from `m ⊨ (a ↦₈ v) ∗ R`. -/
theorem satisfies_pointsTo8_frame {m : Memory} {a : BitVec 64} {v : BitVec 8} {R : SepProp}
    (hm : m ⊨ (a ↦₈ v) ∗ R) : m.read8 a = v ∧ m.perm a = some Perm.rw :=
  ProofLib.satisfies_pointsTo8_frame hm

/-- Framed preserved-byte and permission extraction from `m ⊨ (a ↦₈ₙ v) ∗ R`. -/
theorem satisfies_pointsTo8ProtNone_frame {m : Memory} {a : BitVec 64} {v : BitVec 8} {R : SepProp}
    (hm : m ⊨ (a ↦₈ₙ v) ∗ R) : m.read8 a = v ∧ m.perm a = some Perm.protNone :=
  ProofLib.satisfies_pointsTo8ProtNone_frame hm

/-- Framed 16-bit little-endian read extraction from `m ⊨ (a ↦₁₆ v) ∗ R`. -/
theorem satisfies_pointsTo16_frame {m : Memory} {a : BitVec 64} {v : BitVec 16} {R : SepProp}
    (hm : m ⊨ (a ↦₁₆ v) ∗ R) : m.read16 a = v :=
  (ProofLib.IsBlock.pointsTo16 a v).read hm

/-- Framed 32-bit little-endian read extraction from `m ⊨ (a ↦₃₂ v) ∗ R`. -/
theorem satisfies_pointsTo32_frame {m : Memory} {a : BitVec 64} {v : BitVec 32} {R : SepProp}
    (hm : m ⊨ (a ↦₃₂ v) ∗ R) : m.read32 a = v :=
  (ProofLib.IsBlock.pointsTo32 a v).read hm

/-- Framed 64-bit little-endian read extraction from `m ⊨ (a ↦₆₄ v) ∗ R`. -/
theorem satisfies_pointsTo64_frame {m : Memory} {a : BitVec 64} {v : BitVec 64} {R : SepProp}
    (hm : m ⊨ (a ↦₆₄ v) ∗ R) : m.read64 a = v :=
  (ProofLib.IsBlock.pointsTo64 a v).read hm

/-- Contiguous byte-slice splitting (`↦ₛ`) over list concatenation (`bs₁ ++ bs₂`). -/
theorem pointsToBytes_append (a : BitVec 64) (bs₁ bs₂ : List (BitVec 8)) :
    (a ↦ₛ (bs₁ ++ bs₂)) = (a ↦ₛ bs₁ ∗ (a + BitVec.ofNat 64 bs₁.length) ↦ₛ bs₂) :=
  ProofLib.pointsToBytes_append a bs₁ bs₂

/-- Contiguous `PROT_NONE` byte-slice splitting (`↦ₙ`) over list concatenation (`bs₁ ++ bs₂`). -/
theorem pointsToBytesProtNone_append (a : BitVec 64) (bs₁ bs₂ : List (BitVec 8)) :
    (a ↦ₙ (bs₁ ++ bs₂)) = (a ↦ₙ bs₁ ∗ (a + BitVec.ofNat 64 bs₁.length) ↦ₙ bs₂) :=
  ProofLib.pointsToBytesProtNone_append a bs₁ bs₂

/-- Contiguous `PROT_NONE` region splitting (`memRegionProtNone a (n₁ + n₂)`). -/
theorem memRegionProtNone_split (a : BitVec 64) (n₁ n₂ : Nat) (h : n₁ + n₂ ≤ 2 ^ 64) :
    memRegionProtNone a (n₁ + n₂) =
      (memRegionProtNone a n₁ ∗ memRegionProtNone (a + BitVec.ofNat 64 n₁) n₂) :=
  ProofLib.memRegionProtNone_split a n₁ n₂ h

/-- Zero-length virtual-address mapping reservation (`memMapped a 0 = emp`). -/
theorem memMapped_zero (a : BitVec 64) : memMapped a 0 = emp :=
  ProofLib.memMapped_zero a

/-- Contiguous virtual-address mapping reservation splitting (`memMapped a (n₁ + n₂)`). -/
theorem memMapped_split (a : BitVec 64) (n₁ n₂ : Nat) (h : n₁ + n₂ ≤ 2 ^ 64) :
    memMapped a (n₁ + n₂) = (memMapped a n₁ ∗ memMapped (a + BitVec.ofNat 64 n₁) n₂) :=
  ProofLib.memMapped_split a n₁ n₂ h

/-- Mutual exclusion (`DisjointRegions`) of two separated `memMapped` tokens. -/
theorem memMapped_disjointRegions {a₁ a₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (memMapped a₁ n₁ ∗ memMapped a₂ n₂) ⊢
      ⌜DisjointRegions a₁ n₁ a₂ n₂⌝ ∗ memMapped a₁ n₁ ∗ memMapped a₂ n₂ :=
  ProofLib.memMapped_disjointRegions hn₁ hn₂

/-- Allocating a fresh region (`m.mapZero a n`) produces both `memRegion a n` and `memMapped a n`. -/
theorem satisfies_mapZero_mapped {m : Memory} {P : SepProp} {a : BitVec 64} {n : Nat}
    (hP : m ⊨ P) (hmap : m.canMap a n = true) :
    m.mapZero a n ⊨ memRegion a n ∗ memMapped a n ∗ P :=
  ProofLib.Satisfies.mapZero_mapped hP hmap

/-- Allocating a fresh `PROT_NONE` region produces zero-filled `a ↦ₙ List.replicate n 0#8` and
    `memMapped a n` alongside `P`. -/
theorem satisfies_mapZeroProtNone_mapped {m : Memory} {P : SepProp} {a : BitVec 64} {n : Nat}
    (hP : m ⊨ P) (hmap : m.canMap a n = true) (hn : n ≤ 2 ^ 64) :
    (m.mapZero a n).setPermNonFrozen a n Perm.protNone ⊨
      (a ↦ₙ List.replicate n 0#8) ∗ memMapped a n ∗ P :=
  ProofLib.Satisfies.mapZeroProtNone_mapped hP hmap hn

/-- Promoting `a ↦ₙ bs` to read-write via `setPermNonFrozen ... Perm.rw` exposes `a ↦ₛ bs`. -/
theorem satisfies_setPermRw_of_pointsToBytesProtNone {m : Memory} {P : SepProp}
    {a : BitVec 64} {bs : List (BitVec 8)} (h : m ⊨ (a ↦ₙ bs) ∗ P) :
    m.setPermNonFrozen a bs.length Perm.rw ⊨ (a ↦ₛ bs) ∗ P :=
  ProofLib.Satisfies.setPermRw_of_pointsToBytesProtNone h

/-- Demoting `a ↦ₛ bs` to `PROT_NONE` via `setPermNonFrozen ... Perm.protNone` preserves `a ↦ₙ bs`. -/
theorem satisfies_setPermProtNone_of_pointsToBytes {m : Memory} {P : SepProp}
    {a : BitVec 64} {bs : List (BitVec 8)} (h : m ⊨ (a ↦ₛ bs) ∗ P) :
    m.setPermNonFrozen a bs.length Perm.protNone ⊨ (a ↦ₙ bs) ∗ P :=
  ProofLib.Satisfies.setPermProtNone_of_pointsToBytes h

/-- Replacing `memRegion a n` in place via `MAP_FIXED` `PROT_NONE` `mmap` yields
    `a ↦ₙ List.replicate n 0#8` alongside `P`. -/
theorem satisfies_mmapFixedProtNone_owned {m : Memory} {P : SepProp} {a : BitVec 64} {n : Nat}
    (h : m ⊨ memRegion a n ∗ P) (hn : n ≤ 2 ^ 64) :
    ((m.unmapNonFrozen a n).mapZero a n).setPermNonFrozen a n Perm.protNone ⊨
      (a ↦ₙ List.replicate n 0#8) ∗ P :=
  ProofLib.Satisfies.mmapFixedProtNone_owned h hn

/-- Unmapping a non-frozen region (`m.unmapNonFrozen a n`) consumes both `memRegion a n` and
    `memMapped a n`, preserving any disjoint frame `P`. -/
theorem satisfies_unmapNonFrozen {m : Memory} {P : SepProp} {a : BitVec 64} {n : Nat}
    (h : m ⊨ memRegion a n ∗ memMapped a n ∗ P) :
    m.unmapNonFrozen a n ⊨ P :=
  ProofLib.Satisfies.unmapNonFrozen h

/-- Unmapping a `PROT_NONE` region (`m.unmapNonFrozen a n`) consumes both `memRegionProtNone a n`
    and `memMapped a n`, preserving any disjoint frame `P`. -/
theorem satisfies_unmapNonFrozen_protNone {m : Memory} {P : SepProp} {a : BitVec 64} {n : Nat}
    (h : m ⊨ memRegionProtNone a n ∗ memMapped a n ∗ P) :
    m.unmapNonFrozen a n ⊨ P :=
  ProofLib.Satisfies.unmapNonFrozen_protNone h

/-! ## Hoare and Operational Judgment Laws

[`Arm64/Trusted/Spec/Hoare.lean`](../../Trusted/Spec/Hoare.lean) defines subroutine contracts
(`Spec`, `subroutine_ok`, `raw_subroutine_ok`) and trace judgments (`reaches_stop`, `safe_until`)
over the small-step operational relation `Step` / `Steps` / `StepsUntil` in
[`Arm64/Trusted/ISA/Semantics.lean`](../../Trusted/ISA/Semantics.lean). Below we witness the frame
and consequence rules for `subroutine_ok`, operational determinism and prefix comparability of
`Step`, `Steps`, and `StepsUntil`, and adequacy from total correctness (`reaches_stop`) to
no-fault-before-outcome and partial correctness (`safe_until`).
-/

/-- Frame extension of a subroutine specification `spec` by an additional caller frame `F`. -/
def Spec.frame {α : Type} (spec : Spec α) (F : SepProp) : Spec α :=
  spec.withPreserves (fun _ => F)

/-- Built-in Frame Rule for `subroutine_ok`: because `subroutine_ok` quantifies over all frames
    `R : SepProp`, framing `spec` by any `F : SepProp` is preserved via `sepConj_assoc`. -/
theorem subroutine_ok_frame {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (F : SepProp)
    (hok : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (Spec.frame spec F) :=
  Spec.withPreserves.frame hok (fun _ => F)

/-- Rule of Consequence (precondition strengthening / postcondition weakening) for `subroutine_ok`. -/
theorem subroutine_ok_conseq {α : Type} {prog : Program} {entry : BitVec 64}
    {spec₁ spec₂ : Spec α}
    (hok : subroutine_ok prog entry spec₁)
    (h_pre : ∀ x s0, spec₂.pre x s0 ⊢ spec₁.pre x s0)
    (h_post : ∀ x s0 sf, spec₁.post x s0 sf ⊢ spec₂.post x s0 sf)
    (h_panic : ∀ x s0 sf, spec₁.onPanic x s0 sf ⊢ spec₂.onPanic x s0 sf)
    (h_exit : ∀ x code s0 sf, spec₁.onExit x code s0 sf ⊢ spec₂.onExit x code s0 sf)
    (h_oom : ∀ x s0 sf, spec₁.onOom x s0 sf ⊢ spec₂.onOom x s0 sf :=
      by intro x s0 sf; exact entails_refl _) :
    subroutine_ok prog entry spec₂ :=
  hok.conseq h_pre h_post h_panic h_exit h_oom

/-- Only `.Running` states can take a `Step`. -/
theorem Step.status_running {prog : Program} {s s' : State} (h : Step prog s s') :
    s.status = .Running :=
  Arm64.Step.status_running h

/-- Single-step operational semantics (`Step`) is deterministic. -/
theorem Step.deterministic {prog : Program} {s s₁ s₂ : State}
    (h₁ : Step prog s s₁) (h₂ : Step prog s s₂) : s₁ = s₂ :=
  Arm64.Step.deterministic h₁ h₂

/-- Comparing two `Steps` runs from the same start state `s0`: by determinism of `Step`,
    one run is a prefix of the other (`Steps prog s₁ s₂ ∨ Steps prog s₂ s₁`). -/
theorem Steps.compare {prog : Program} {s0 s₁ s₂ : State}
    (h₁ : Steps prog s0 s₁) (h₂ : Steps prog s0 s₂) :
    Steps prog s₁ s₂ ∨ Steps prog s₂ s₁ :=
  ProofLib.Steps.compare h₁ h₂

/-- Along any execution `Steps prog s0 sf`, every state `t` reachable from `s0` is either
    strictly before `sf` on the deterministic trace (and therefore `.Running` by
    `Step.status_running`) or reachable from `sf` (`Steps prog sf t`). -/
theorem Steps.running_or_steps_of {prog : Program} {s0 sf t : State}
    (hsf : Steps prog s0 sf) (ht : Steps prog s0 t) :
    t.status = .Running ∨ Steps prog sf t :=
  ProofLib.Steps.running_or_steps_of hsf ht

/-- From `subroutine_ok prog entry spec` and the AAPCS64 entry conditions, execution reaches an
    outcome state `sf` (`SubroutineOutcome spec x R s0 sf`) and every state `t` reachable from
    `s0` is either `.Running` (prior to `sf`) or reachable from `sf` (`Steps prog sf t`). -/
theorem subroutine_ok.no_fault_before_outcome {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hok : subroutine_ok prog entry spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hL : prog.CodeLoaded s0.mem) :
    ∃ sf, Steps prog s0 sf ∧ SubroutineOutcome spec x R s0 sf ∧
      ∀ t, Steps prog s0 t → t.status = .Running ∨ Steps prog sf t :=
  Arm64.subroutine_ok.no_fault_before_outcome hok x R s0 hpc hrun hpre hsp hL

/-- From `raw_subroutine_ok prog entry spec` and the entry conditions, execution reaches an
    outcome state `sf` (`SubroutineOutcome spec x R s0 sf`) and every state `t` reachable from
    `s0` is either `.Running` (prior to `sf`) or reachable from `sf` (`Steps prog sf t`). -/
theorem raw_subroutine_ok.no_fault_before_outcome {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hok : raw_subroutine_ok prog entry spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hL : prog.CodeLoaded s0.mem) :
    ∃ sf, Steps prog s0 sf ∧ SubroutineOutcome spec x R s0 sf ∧
      ∀ t, Steps prog s0 t → t.status = .Running ∨ Steps prog sf t :=
  Arm64.raw_subroutine_ok.no_fault_before_outcome hok x R s0 hpc hrun hpre hL

/-- Corollary of `subroutine_ok.no_fault_before_outcome` for the `Returned` disjunct (when the
    specification forbids panic, exit, and OOM, which are the `Spec` defaults). -/
theorem subroutine_ok.no_fault_before_return {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hok : subroutine_ok prog entry spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hL : prog.CodeLoaded s0.mem)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∃ sf, Steps prog s0 sf ∧
      Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
      ∀ t, Steps prog s0 t → t.status = .Running ∨ Steps prog sf t :=
  Arm64.subroutine_ok.no_fault_before_return hok x R s0 hpc hrun hpre hsp hL h_noPanic h_noExit h_noOom

/-- Corollary of `raw_subroutine_ok.no_fault_before_outcome` for the `Returned` disjunct (when the
    specification forbids panic, exit, and OOM). -/
theorem raw_subroutine_ok.no_fault_before_return {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hok : raw_subroutine_ok prog entry spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∃ sf, Steps prog s0 sf ∧
      Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
      ∀ t, Steps prog s0 t → t.status = .Running ∨ Steps prog sf t :=
  Arm64.raw_subroutine_ok.no_fault_before_return hok x R s0 hpc hrun hpre hL h_noPanic h_noExit h_noOom

/-- Comparing two `StepsUntil` traces from the same start state `s0`: either `s₂` is reachable from
    `s₁`, or `s₂` is a strict prefix state (hence `¬ stop s₂` and `s₂.status = .Running`). -/
theorem StepsUntil.compare {prog : Program} {stop : State → Prop} {s0 s₁ s₂ : State}
    (h₁ : StepsUntil prog stop s0 s₁) (h₂ : StepsUntil prog stop s0 s₂) :
    StepsUntil prog stop s₁ s₂ ∨ (¬ stop s₂ ∧ s₂.status = .Running) :=
  ProofLib.StepsUntil.compare h₁ h₂

/-- Total-to-partial adequacy for `reaches_stop`: total correctness (`reaches_stop`) implies
    safety-style partial correctness (`safe_until`) with the same postcondition `Q`. -/
theorem reaches_stop_imp_safe_until {prog : Program} {stop : State → Prop} {s0 : State}
    {Q : State → Prop} {oom : State → Prop} (h : reaches_stop prog stop s0 Q) :
    safe_until prog stop s0 Q oom :=
  h.to_safe

end Arm64.Testing.Tours.SepLogicLawsTour
