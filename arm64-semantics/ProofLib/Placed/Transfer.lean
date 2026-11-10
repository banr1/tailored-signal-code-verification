/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Check
public import ProofLib.Process
public import ProofLib.ObjectLoad
public import ProofLib.SepLogic
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Placed Library Transfer into a Loaded ELF

Transfers code-loading, initial data ownership (`dataInit`), decidable disjointness checks
(`Interned.checkDisjoint`), extern hook resolution, and subroutine contracts from a placed library
(`lib.InElf img pl`) into the initial process state of an ELF executable (`img.loadState`) and down
to `Steps Program.pureMem`.
-/

@[expose] public section

namespace Arm64.Obj

open Arm64.Process ProofLib

/-! ## Segment bytes in the initial memory -/

/-- Every byte mapped by `img`'s segments (as `Snapshot.cellAt` resolves it) is in the initial
    memory with the same permission. The stack region comes after the segments and `mapZero` only
    maps unmapped bytes, so no disjointness side condition is needed. -/
theorem _root_.Arm64.Process.ElfImage.loadState_cell {img : ElfImage} {inputs : ProcessInputs}
    {s : State} (hload : img.loadState inputs = .ok s) {a : BitVec 64} {p : Perm} {b : BitVec 8}
    (h : Snapshot.cellAt img.segments a = some (some p, b)) :
    s.mem.read8 a = b ∧ s.mem.perm a = some p.rwx := by
  obtain ⟨_, stackRegion, _, hmem, _⟩ := ElfImage.loadState_eq_ok hload
  have hc : Snapshot.cellAt (img.segments ++ [stackRegion]) a = some (some p, b) := by
    unfold Snapshot.cellAt at h ⊢
    rw [List.findSome?_append, h]
    rfl
  let baseMem : Memory := ⟨Snapshot.loadCellAt (img.segments ++ [stackRegion])⟩
  have hbp : baseMem.perm a = some p.rwx := by
    rw [Snapshot.perm_loadCellAt]
    simp [Memory.perm, hc]
  have hbr : baseMem.read8 a = b := by
    rw [Snapshot.read8_loadCellAt]
    simp [Memory.read8, hc]
  have hbm : (baseMem.perm a).mapped = true := by
    rw [hbp]; rfl
  have hcell : s.mem.cells a = baseMem.cells a := by
    rw [hmem]
    dsimp only [Memory.mapZero, baseMem] at hbm ⊢
    simp only [hbm, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by unfold Memory.read8; rw [hcell]; exact hbr,
    by unfold Memory.perm; rw [hcell]; exact hbp⟩

/-- Bytes the image maps (`ElfMaps`) with a fixed permission `p` are held in the initial memory. -/
theorem ElfMaps.holdsBytes {img : ElfImage} {inputs : ProcessInputs} {s : State}
    (hload : img.loadState inputs = .ok s) {addr : BitVec 64} {bs : List (BitVec 8)}
    {ok : Perm → Bool} {p : Perm} (hok : ∀ q, ok q = true → q = p) (h : ElfMaps img addr bs ok)
    (hrwx : p.rwx = p := by rfl) :
    HoldsBytes s.mem addr bs (fun _ => p) := by
  intro i hi
  obtain ⟨q, hq, hqok⟩ := h i hi
  have hc := ElfImage.loadState_cell hload hq
  rw [hok q hqok, hrwx] at hc
  exact ⟨hc.1, hc.2, ElfImage.loadState_isLazyFree hload _⟩

/-! ## Code -/

/-- The placed program's code is loaded in the initial memory of an executable containing the
    library, for any externs and overrides. -/
theorem PlacedLib.codeLoaded_of_inElf {lib : PlacedLib} {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable pl) (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s)
    {X O : String → Option (State → State)} {svc : State → State} :
    (lib.program pl X O svc).CodeLoaded s.mem := by
  have ht := hpl.text
  have hlen : (lib.text.patched pl).length = lib.text.code.length :=
    CodeBlock.length_patched_of_aligned pl ht.len_aligned
  have hhold := ElfMaps.holdsBytes hload (p := Perm.rx) (fun q hq => by simpa using hq) hin.text
  refine Program.CodeLoaded.intro ?_ ?_ fun i hi => ?_
  · have h1 : 4 ∣ lib.text.align := Nat.dvd_of_mod_eq_zero ht.align_pos.2
    have h2 : lib.text.align ∣ pl.base.toNat := Nat.dvd_of_mod_eq_zero ht.base_aligned
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h1 h2)
  · simp only [program_base, program_code, hlen]; exact ht.no_wrap
  · exact hhold i hi

/-! ## Data -/

/-- A data object's initial bytes are in the initial memory, with a permission accepted by
    `PlacedLib.InElf`. -/
theorem PlacedLib.holdsData_of_inElf {lib : PlacedLib} {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s) {d : SymDataInfo} (hd : d ∈ lib.data) :
    ∀ (i : Nat) (hi : i < (lib.patchedData pl d).length),
      s.mem.read8 (pl.ρ d.sym + BitVec.ofNat 64 i) = (lib.patchedData pl d)[i] ∧
      ∃ p, s.mem.perm (pl.ρ d.sym + BitVec.ofNat 64 i) = some p ∧
        (if d.readOnly then p.r else p == Perm.rw) = true := by
  intro i hi
  obtain ⟨p, hp, hok⟩ := hin.data d hd i hi
  have hc := ElfImage.loadState_cell hload hp
  refine ⟨hc.1, p.rwx, hc.2, ?_⟩
  cases hr : d.readOnly <;> simp only [hr, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hok ⊢
  · rw [hok]; rfl
  · exact hok

/-- Patching one in-bounds data relocation preserves the byte count. -/
theorem PlacedLib.length_patchDataReloc {lib : PlacedLib} {pl : Placement} {addr : BitVec 64}
    {bytes : List (BitVec 8)} {r : RelocEntry} (h : r.off + dataRelocWidth r.kind ≤ bytes.length) :
    (lib.patchDataReloc pl addr bytes r).length = bytes.length := by
  unfold PlacedLib.patchDataReloc
  cases hk : r.kind <;> simp only [hk, dataRelocWidth] at h ⊢ <;>
    simp only [List.length_append, List.length_take, List.length_drop,
      ProofLib.ObjectLoad.RoDataFactsAux.bytesLE_length] <;> omega

/-- A data object's patched bytes are its template bytes plus its zero tail. -/
theorem PlacedLib.length_patchedData {lib : PlacedLib} {pl : Placement} {d : SymDataInfo}
    (h : ∀ r ∈ d.relocs, r.off + dataRelocWidth r.kind ≤ d.bytes.length) :
    (lib.patchedData pl d).length = d.bytes.length + d.zeroTail := by
  unfold PlacedLib.patchedData
  suffices ∀ (rs : List RelocEntry) (bs : List (BitVec 8)),
      (∀ r ∈ rs, r.off + dataRelocWidth r.kind ≤ bs.length) →
      (rs.foldl (lib.patchDataReloc pl (pl.ρ d.sym)) bs).length = bs.length by
    rw [List.length_append, this d.relocs d.bytes h, List.length_replicate]
  intro rs
  induction rs with
  | nil => intro _ _; rfl
  | cons r rs ih =>
    intro bs hrs
    have hl := PlacedLib.length_patchDataReloc (lib := lib) (pl := pl) (addr := pl.ρ d.sym)
      (hrs r (by simp))
    simp only [List.foldl_cons]
    rw [ih _ (fun r' hr' => hl ▸ hrs r' (by simp [hr'])), hl]

/-- A data object's initial bytes fit in the address space after its address. -/
theorem PlacedLib.Placeable.patchedData_no_wrap {lib : PlacedLib} {pl : Placement}
    (hpl : lib.Placeable pl) {d : SymDataInfo} (hd : d ∈ lib.data) :
    (pl.ρ d.sym).toNat + (lib.patchedData pl d).length ≤ 2 ^ 64 := by
  rw [PlacedLib.length_patchedData fun r hr => (hpl.data_relocs_ok d hd r hr).2.1]
  have := (hpl.data_ok d hd).2.2.2
  omega

/-- An address in a region is the base plus its in-bounds offset. -/
theorem inRegion_offset {base a : BitVec 64} {len : Nat} (h : InRegion base len a) :
    (a - base).toNat < len ∧ base + BitVec.ofNat 64 (a - base).toNat = a := by
  refine ⟨h, ?_⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

/-- The sub-heap owning data object `d`'s initial bytes in `m`: read-only cells if `d.readOnly`,
    read-write cells otherwise. -/
def PlacedLib.dataHeap (lib : PlacedLib) (pl : Placement) (m : Memory) (d : SymDataInfo) : Heap :=
  if d.readOnly then regionHeapRO (pl.ρ d.sym) (lib.patchedData pl d).length m
  else regionHeap (pl.ρ d.sym) (lib.patchedData pl d).length m

/-- The assertion `PlacedLib.dataInit` uses for data object `d`. -/
def PlacedLib.dataProp (lib : PlacedLib) (pl : Placement) (d : SymDataInfo) : SepProp :=
  if d.readOnly then pointsToBytesRO (pl.ρ d.sym) (lib.patchedData pl d)
  else pointsToBytes (pl.ρ d.sym) (lib.patchedData pl d)

/-- `dataHeap` satisfies `dataProp` and matches the initial memory. -/
theorem PlacedLib.dataHeap_spec {lib : PlacedLib} {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable pl) (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s) {d : SymDataInfo} (hd : d ∈ lib.data) :
    (lib.dataProp pl d).holds (lib.dataHeap pl s.mem d) ∧
      (lib.dataHeap pl s.mem d).Matches s.mem := by
  have hlen := hpl.patchedData_no_wrap hd
  have hhold := PlacedLib.holdsData_of_inElf hin hload hd
  have hread : s.mem.readBytes (pl.ρ d.sym) (lib.patchedData pl d).length = lib.patchedData pl d :=
    Memory.readBytes_of_read8 fun i hi => (hhold i hi).1
  have hperm : ∀ a, InRegion (pl.ρ d.sym) (lib.patchedData pl d).length a → ∃ p,
      s.mem.perm a = some p ∧ (if d.readOnly then p.r else p == Perm.rw) = true := by
    intro a ha
    obtain ⟨hi, he⟩ := inRegion_offset ha
    have := (hhold _ hi).2
    rwa [he] at this
  unfold PlacedLib.dataProp PlacedLib.dataHeap
  cases hro : d.readOnly
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨((ProofLib.IsBlock.pointsToBytes _ _).iff _).2 ⟨s.mem, ⟨by omega, hread⟩, rfl⟩,
      ProofLib.IsBlock.regionHeap_matches _ _ _ fun a ha => ?_⟩
    obtain ⟨p, hp, hok⟩ := hperm a ha
    simp only [hro, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hok
    exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨by rw [hp, hok], ElfImage.loadState_isLazyFree hload a⟩
  · simp only [↓reduceIte]
    refine ⟨((ProofLib.IsBlockRO.pointsToBytesRO _ _ (by omega)).iff _).2 ⟨s.mem, hread, rfl⟩,
      ProofLib.IsBlockRO.regionHeapRO_matches _ _ _ fun a ha => ?_⟩
    obtain ⟨p, hp, hok⟩ := hperm a ha
    simp only [hro, ↓reduceIte] at hok
    exact ⟨by rw [hp]; exact hok, ElfImage.loadState_isLazyFree hload a⟩

/-- A read-only data object gives `pl.ρ d.sym ↦ᵣ lib.patchedData pl d` in the initial memory (any
    readable permission suffices for `↦ᵣ`). -/
theorem PlacedLib.satisfies_dataRO_of_inElf {lib : PlacedLib} {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable pl) (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s) {d : SymDataInfo} (hd : d ∈ lib.data)
    (hro : d.readOnly = true) :
    s.mem ⊨ pointsToBytesRO (pl.ρ d.sym) (lib.patchedData pl d) := by
  have ⟨hp, hm⟩ := PlacedLib.dataHeap_spec hpl hin hload hd
  simp only [PlacedLib.dataProp, hro, ↓reduceIte] at hp
  exact SepProp.satisfies_iff.mpr ⟨_, hp, hm⟩

/-- Writable data objects of `lib` under `pl` share no byte with any other data object. -/
def PlacedLib.DataDisjoint (lib : PlacedLib) (pl : Placement) : Prop :=
  lib.data.Pairwise fun d₁ d₂ =>
    (d₁.readOnly = true ∧ d₂.readOnly = true) ∨
      ∀ a, InRegion (pl.ρ d₁.sym) (lib.patchedData pl d₁).length a →
        ¬ InRegion (pl.ρ d₂.sym) (lib.patchedData pl d₂).length a

/-- `dataHeap` has no ghost or mapping state. -/
theorem PlacedLib.dataHeap_auth (lib : PlacedLib) (pl : Placement) (m : Memory) (d : SymDataInfo) :
    (lib.dataHeap pl m d).auth = fun _ _ => none := by
  unfold PlacedLib.dataHeap; split <;> with_unfolding_all rfl

theorem PlacedLib.dataHeap_frag (lib : PlacedLib) (pl : Placement) (m : Memory) (d : SymDataInfo) :
    (lib.dataHeap pl m d).frag = fun _ _ => none := by
  unfold PlacedLib.dataHeap; split <;> with_unfolding_all rfl

theorem PlacedLib.dataHeap_mapped (lib : PlacedLib) (pl : Placement) (m : Memory)
    (d : SymDataInfo) : (lib.dataHeap pl m d).mapped = fun _ => false := by
  unfold PlacedLib.dataHeap; split <;> with_unfolding_all rfl

/-- A `dataHeap` cell lies in the object's region, and is read-only for a read-only object. -/
theorem PlacedLib.dataHeap_phys {lib : PlacedLib} {pl : Placement} {m : Memory} {d : SymDataInfo}
    {a : BitVec 64} {c : HeapCell} (h : (lib.dataHeap pl m d).phys a = some c) :
    InRegion (pl.ρ d.sym) (lib.patchedData pl d).length a ∧
      (d.readOnly = true → c = .ro (m.read8 a)) := by
  unfold PlacedLib.dataHeap at h
  cases hro : d.readOnly <;> simp only [hro, Bool.false_eq_true, ↓reduceIte, regionHeap,
    regionHeapRO] at h <;> split at h <;> first | contradiction | skip
  · exact ⟨by assumption, fun h => nomatch h⟩
  · rename_i hin; injection h with h; exact ⟨hin, fun _ => h.symm⟩

/-- Pairwise-disjoint data objects give a heap for `sepAll (ds.map dataProp)` matching the initial
    memory (induction invariant for `satisfies_dataInit_of_inElf`). -/
theorem PlacedLib.sepAll_dataHeap {lib : PlacedLib} {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable pl) (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s) :
    ∀ (ds : List SymDataInfo), (∀ d ∈ ds, d ∈ lib.data) →
      ds.Pairwise (fun d₁ d₂ => (d₁.readOnly = true ∧ d₂.readOnly = true) ∨
        ∀ a, InRegion (pl.ρ d₁.sym) (lib.patchedData pl d₁).length a →
          ¬ InRegion (pl.ρ d₂.sym) (lib.patchedData pl d₂).length a) →
      ∃ h : Heap, (sepAll (ds.map (lib.dataProp pl))).holds h ∧ h.Matches s.mem ∧
        h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false) ∧
        ∀ a c, h.phys a = some c → ∃ d ∈ ds, (lib.dataHeap pl s.mem d).phys a = some c
  | [], _, _ =>
    by with_unfolding_all exact ⟨Heap.empty, SepProp.holds_emp_iff.mpr rfl,
      Heap.Matches.of_phys rfl rfl (fun _ _ h => by simp [Heap.empty] at h) rfl, rfl, rfl, rfl,
      fun _ _ h => by simp [Heap.empty] at h⟩
  | [d], hmem, _ => by
    have ⟨hp, hm⟩ := PlacedLib.dataHeap_spec hpl hin hload (hmem d (by simp))
    exact ⟨_, hp, hm, PlacedLib.dataHeap_auth .., PlacedLib.dataHeap_frag ..,
      PlacedLib.dataHeap_mapped .., fun a c h => ⟨d, by simp, h⟩⟩
  | d :: d' :: ds, hmem, hpw => by
    obtain ⟨hrest, hrp, hrm, hra, hrf, hrmap, hrphys⟩ :=
      PlacedLib.sepAll_dataHeap hpl hin hload (d' :: ds)
        (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) hpw.of_cons
    have ⟨hp, hm⟩ := PlacedLib.dataHeap_spec hpl hin hload (hmem d (by simp))
    have hdisj : (lib.dataHeap pl s.mem d).Disjoint hrest := by
      refine Heap.Disjoint.of_phys_left (PlacedLib.dataHeap_auth ..) (PlacedLib.dataHeap_frag ..)
        (fun a => ?_) (PlacedLib.dataHeap_mapped ..)
      cases h1 : (lib.dataHeap pl s.mem d).phys a with
      | none => exact Or.inl rfl
      | some c1 =>
        cases h2 : hrest.phys a with
        | none => exact Or.inr (Or.inl rfl)
        | some c2 =>
          obtain ⟨x, hx, hxa⟩ := hrphys a c2 h2
          have ⟨hin1, hro1⟩ := PlacedLib.dataHeap_phys h1
          have ⟨hin2, hro2⟩ := PlacedLib.dataHeap_phys hxa
          rcases List.rel_of_pairwise_cons hpw hx with ⟨hr1, hr2⟩ | hdis
          · exact Or.inr (Or.inr ⟨_, by rw [hro1 hr1], by rw [hro2 hr2]⟩)
          · exact absurd hin2 (hdis a hin1)
    refine ⟨(lib.dataHeap pl s.mem d).union hrest, ?_, Heap.Matches.union hm hrm, ?_, ?_, ?_, ?_⟩
    · show (lib.dataProp pl d ∗ sepAll ((d' :: ds).map (lib.dataProp pl))).holds _
      exact SepProp.holds_sepConj_iff.mpr ⟨_, _, hdisj, rfl, hp, hrp⟩
    · funext γ k; simp only [Heap.union, PlacedLib.dataHeap_auth, hra]
    · funext γ k; simp only [Heap.union, PlacedLib.dataHeap_frag, hrf]
    · funext a; simp only [Heap.union, PlacedLib.dataHeap_mapped, hrmap, Bool.or_false]
    · intro a c h
      simp only [Heap.union] at h
      cases h1 : (lib.dataHeap pl s.mem d).phys a with
      | none =>
        rw [h1] at h
        obtain ⟨x, hx, hxa⟩ := hrphys a c h
        exact ⟨x, List.mem_cons_of_mem _ hx, hxa⟩
      | some c1 =>
        rw [h1] at h
        exact ⟨d, by simp, h1.trans h⟩

/-- The library's initial data (`lib.dataInit pl`) holds in the initial memory. -/
theorem PlacedLib.satisfies_dataInit_of_inElf {lib : PlacedLib} {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable pl) (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s) (hdisj : lib.DataDisjoint pl) :
    s.mem ⊨ lib.dataInit pl := by
  obtain ⟨h, hp, hm, _⟩ := PlacedLib.sepAll_dataHeap hpl hin hload lib.data (fun _ hd => hd) hdisj
  exact SepProp.satisfies_iff.mpr ⟨h, hp, hm⟩

/-! ### A decidable `DataDisjoint` check -/

/-- Address ranges `(start, length)` in increasing order, each ending (without wrapping) at or
    before the next one starts. -/
def rangesSorted : List (BitVec 64 × Nat) → Bool
  | [] => true
  | [(a, n)] => Nat.ble (a.toNat + n) 18446744073709551616
  | (a, n) :: (b, k) :: rs => Nat.ble (a.toNat + n) b.toNat && rangesSorted ((b, k) :: rs)

theorem rangesSorted_pairwise : ∀ {rs : List (BitVec 64 × Nat)}, rangesSorted rs = true →
    rs.Pairwise (fun x y => x.1.toNat + x.2 ≤ y.1.toNat) ∧ ∀ x ∈ rs, x.1.toNat + x.2 ≤ 2 ^ 64
  | [], _ => ⟨List.Pairwise.nil, fun _ h => nomatch h⟩
  | [(a, n)], h => by
    simp only [rangesSorted, Nat.ble_eq] at h
    exact ⟨List.pairwise_singleton _ _, fun x hx => by simp at hx; subst hx; exact h⟩
  | (a, n) :: (b, k) :: rs, h => by
    simp only [rangesSorted, Bool.and_eq_true, Nat.ble_eq] at h
    have ⟨hpw, hb⟩ := rangesSorted_pairwise h.2
    refine ⟨List.Pairwise.cons (fun y hy => ?_) hpw, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact h.1
      · have := List.rel_of_pairwise_cons hpw hy
        have := hb (b, k) (by simp)
        simp only at *; omega
    · rcases List.mem_cons.1 hx with rfl | hx
      · have := hb (b, k) (by simp); simp only at *; omega
      · exact hb x hx

/-- Regions `[a, a + n)` and `[b, b + k)` with `a + n ≤ b` and no wrap share no address. -/
theorem not_inRegion_of_le {a b x : BitVec 64} {n k : Nat} (hab : a.toNat + n ≤ b.toNat)
    (hb : b.toNat + k ≤ 2 ^ 64) (h1 : InRegion a n x) : ¬ InRegion b k x := by
  unfold InRegion at *
  intro h2
  have e1 : (x - a).toNat = (x.toNat + (2 ^ 64 - a.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  have e2 : (x - b).toNat = (x.toNat + (2 ^ 64 - b.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  have := x.isLt; have := a.isLt; have := b.isLt
  by_cases hxa : a.toNat ≤ x.toNat
  · rw [show x.toNat + (2 ^ 64 - a.toNat) = (x.toNat - a.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at e1
    by_cases hxb : b.toNat ≤ x.toNat
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)] at e2; omega
  · rw [Nat.mod_eq_of_lt (by omega)] at e1; omega

/-- `DataDisjoint` from address-sorted, non-overlapping data objects (checkable by `decide` at
    a concrete placement). -/
theorem PlacedLib.dataDisjoint_of_sorted {lib : PlacedLib} {pl : Placement}
    (h : rangesSorted (lib.data.map fun d => (pl.ρ d.sym, (lib.patchedData pl d).length)) = true) :
    lib.DataDisjoint pl := by
  have ⟨hpw, hb⟩ := rangesSorted_pairwise h
  rw [List.pairwise_map] at hpw
  refine hpw.imp_of_mem fun {d₁ d₂} _ hd₂ hle => Or.inr fun a h1 => ?_
  exact not_inRegion_of_le hle (hb _ (List.mem_map_of_mem hd₂)) h1

/-- Interned form of the `dataDisjoint_of_sorted` check: reads addresses from `ly.addrs` and
    lengths from the template (`bytes.length + zeroTail`), so `decide` never patches data. -/
def Interned.dataSorted (L : Interned.Lib) (ly : Interned.Layout) : Bool :=
  rangesSorted (L.data.map fun d => (ly.addrs.getD d.sym 0#64, d.bytes.length + d.zeroTail))

theorem Interned.dataDisjoint_of_dataSorted {L : Interned.Lib} {ly : Interned.Layout}
    {lib : PlacedLib} {pl : Placement} (hlib : lib = L.toLib) (hpl0 : pl = ly.toPlacement L.names)
    (hnd : L.names.Nodup) (hok : L.IdsOk) (hpl : lib.Placeable pl)
    (h : Interned.dataSorted L ly = true) : lib.DataDisjoint pl := by
  subst hlib hpl0
  apply PlacedLib.dataDisjoint_of_sorted
  have heq : (L.toLib.data.map fun d =>
      ((ly.toPlacement L.names).ρ d.sym, (L.toLib.patchedData (ly.toPlacement L.names) d).length)) =
      L.data.map fun d => (ly.addrs.getD d.sym 0#64, d.bytes.length + d.zeroTail) := by
    simp only [Interned.Lib.toLib, List.map_map]
    refine List.map_congr_left fun d hd => ?_
    have hdi : d.toInfo L.names ∈ L.toLib.data := List.mem_map_of_mem hd
    simp only [Function.comp_apply, Prod.mk.injEq]
    refine ⟨Interned.toPlacement_ρ hnd (hok.data d hd).1, ?_⟩
    rw [PlacedLib.length_patchedData fun r hr => (hpl.data_relocs_ok _ hdi r hr).2.1]
    rfl
  rw [heq]; exact h

/-! ## Combined link check: placement, ELF containment, and data disjointness -/

/-- `Interned.check` plus `Interned.dataSorted`: one `decide +kernel` gives `Placeable`, `InElf`,
    and `DataDisjoint` (`Interned.checkDisjoint_spec`). -/
def Interned.checkDisjoint (L : Interned.Lib) (ly : Interned.Layout)
    (nameChars : List (List Char)) (img : ElfImage) (enc : EncSymTable (BitVec 64)) : Bool :=
  Interned.check L ly nameChars img enc && Interned.dataSorted L ly

theorem Interned.checkDisjoint_spec {L : Interned.Lib} {ly : Interned.Layout}
    {nameChars : List (List Char)} {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    (hnames : L.names = nameChars.map String.ofList)
    (hsyms : img.symbols = ProofLib.ProgramReflection.toStringAssoc symChars)
    (h : Interned.checkDisjoint L ly nameChars img
      (ProofLib.ObjectLoad.prepareCharAssocVal symChars) = true) :
    L.toLib.Placeable (ly.toPlacement L.names) ∧ L.toLib.InElf img (ly.toPlacement L.names) ∧
      L.toLib.DataDisjoint (ly.toPlacement L.names) := by
  simp only [Interned.checkDisjoint, Bool.and_eq_true] at h
  obtain ⟨hc, hs⟩ := h
  have ⟨hpl, hin⟩ := Interned.check_spec hnames hsyms hc
  have hnn : Interned.namesNodup nameChars = true := by
    simp only [Interned.check, Bool.and_eq_true] at hc; exact hc.1.1.1.1.1.1
  have hids : L.idsOk = true := by
    simp only [Interned.check, Bool.and_eq_true] at hc; exact hc.1.1.1.1.1.2
  exact ⟨hpl, hin, Interned.dataDisjoint_of_dataSorted rfl rfl
    (Interned.nodup_of_namesNodup hnames hnn) (Interned.Lib.idsOk_spec hids) hpl hs⟩

/-- Distinct extern stub offsets, as `externAt?_program` needs (decidable at a concrete
    placement). -/
theorem Interned.externsNodup_of_check {L : Interned.Lib} {ly : Interned.Layout}
    {lib : PlacedLib} {pl : Placement} (hlib : lib = L.toLib) (hpl0 : pl = ly.toPlacement L.names)
    (hnd : L.names.Nodup) (hok : L.IdsOk)
    (h : (L.externs.map fun e => (ly.addrs.getD e 0#64 - ly.base).toNat).Nodup) :
    (lib.text.externs.map fun e' => (pl.ρ e' - pl.base).toNat).Nodup := by
  subst hlib hpl0
  simp only [Interned.Lib.toLib_text, Interned.Lib.block, List.map_map]
  rwa [List.map_congr_left (g := fun e => (ly.addrs.getD e 0#64 - ly.base).toNat) fun e he => by
    simp only [Function.comp_apply, Interned.toPlacement_ρ hnd (hok.externs e he),
      Interned.toPlacement_base]]

/-! ## Externs and calls -/

theorem findSome?_stubs_none {X : String → Option (State → State)} {g : String → Nat} {k : Nat} :
    ∀ (L : List String), (∀ x ∈ L, g x ≠ k) →
      (L.map fun e' => (e', g e')).findSome?
        (fun (p : String × Nat) => if p.2 == k then X p.1 else none) = none
  | [], _ => rfl
  | x :: L, h => by
    have hx : (g x == k) = false := by simpa using h x (by simp)
    simp only [List.map_cons, List.findSome?_cons, hx, Bool.false_eq_true, ↓reduceIte]
    exact findSome?_stubs_none L fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- With distinct offsets, the stub lookup at `e`'s offset finds `X e`. -/
theorem findSome?_stubs {X : String → Option (State → State)} {g : String → Nat} {e : String} :
    ∀ (L : List String), (L.map g).Nodup → e ∈ L →
      (L.map fun e' => (e', g e')).findSome?
        (fun (p : String × Nat) => if p.2 == g e then X p.1 else none) = X e
  | [], _, he => nomatch he
  | x :: L, hnd, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.findSome?_cons]
    by_cases hxe : x = e
    · subst hxe
      have hrest := findSome?_stubs_none (X := X) (k := g x) L fun y hy hgy =>
        hnd.1 (List.mem_map.2 ⟨y, hy, hgy⟩)
      simp only [beq_self_eq_true, ↓reduceIte]
      cases X x with
      | none => exact hrest
      | some _ => rfl
    · have heL : e ∈ L := by
        rcases List.mem_cons.1 he with h | h
        · exact absurd h.symm hxe
        · exact h
      have hne : (g x == g e) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro hg; exact hnd.1 (hg ▸ List.mem_map_of_mem heL)
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact findSome?_stubs L hnd.2 heL

/-- The placed program's hook at extern `e`'s address `pl.ρ e` is `X e`, falling back to an
    override hook at the same offset when `X e = none`. Requires the externs' offsets from
    `pl.base` to be pairwise distinct (decidable at a concrete placement). -/
theorem PlacedLib.externAt?_program {lib : PlacedLib} {pl : Placement}
    {X O : String → Option (State → State)} {svc : State → State} {e : String}
    (hnd : (lib.text.externs.map fun e' => (pl.ρ e' - pl.base).toNat).Nodup)
    (he : e ∈ lib.text.externs) :
    (lib.program pl X O svc).externAt? (pl.ρ e) = (X e).or
      ((lib.program pl X O svc).symbols.findSome? fun (n, o) =>
        if o == (pl.ρ e - pl.base).toNat then O n else none) := by
  dsimp only [Program.externAt?, Program.hookAtOff?, PlacedLib.program]
  rw [findSome?_stubs (g := fun e' => (pl.ρ e' - pl.base).toNat) _ hnd he]

/-- Converse: every hook of the placed program with no overrides is some extern's `X e`, entered
    at `pl.ρ e`'s offset from `pl.base`. -/
theorem PlacedLib.externAt?_program_inv {lib : PlacedLib} {pl : Placement}
    {X : String → Option (State → State)} {svc : State → State} {pc : BitVec 64}
    {f : State → State}
    (h : (lib.program pl X (fun _ => none) svc).externAt? pc = some f) :
    ∃ e ∈ lib.text.externs, (pl.ρ e - pl.base).toNat = (pc - pl.base).toNat ∧ X e = some f := by
  dsimp only [Program.externAt?, Program.hookAtOff?, PlacedLib.program] at h
  have hO : ∀ L : List (String × Nat), L.findSome? (fun _ => (none : Option (State → State))) =
      none := by
    intro L; induction L <;> simp [*]
  simp only [ite_self] at h
  rw [hO, Option.or_none] at h
  obtain ⟨⟨n, o⟩, hmem, hf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨e, he, heq⟩ := List.mem_map.1 hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  by_cases ho : ((pl.ρ e - pl.base).toNat == (pc - pl.base).toNat) = true
  · simp only [ho, ↓reduceIte] at hf
    exact ⟨e, he, by simpa using ho, hf⟩
  · simp only [ho, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hf

/-- Lower `lib.subroutineOk fnName spec X O` at a concrete placement `pl` under which the library
    is contained in `img`, to a `Steps Program.pureMem` execution from any state `s0` whose memory
    is a frozen-preserving evolution of the initial memory `s.mem`. `h_hooks` discharges each
    hook of the placed program (for an extern built with `pureMemStubHook (pl.ρ e)`, by the
    executable's own code at `pl.ρ e`). -/
theorem PlacedLib.subroutineOk_toPureMem {S α : Type} [ToBaseSpec S α] {lib : PlacedLib}
    {fnName : String} {spec : Placement → S} {X O : String → Option (State → State)}
    (hok : lib.subroutineOk fnName spec X O) {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable pl) (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s)
    (h_noPanic : ∀ x s0 sf, (ToBaseSpec.toSpec (spec pl) pl.base).onPanic x s0 sf = ⌜False⌝)
    (h_noExit : ∀ x c s0 sf, (ToBaseSpec.toSpec (spec pl) pl.base).onExit x c s0 sf = ⌜False⌝)
    (h_noOom : ∀ x s0 sf, (ToBaseSpec.toSpec (spec pl) pl.base).onOom x s0 sf = ⌜False⌝)
    {x : α} {R : SepProp} {s0 : State} (hfrozen : s.mem.KeepsFrozen s0.mem)
    (hpc : s0.pc = lib.fnAddr pl fnName) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (ToBaseSpec.toSpec (spec pl) pl.base).pre x s0 ∗ R)
    (hsp : s0.spAligned = true)
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      (lib.program pl X O).externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem → Steps Program.pureMem st (f st)) :
    ∃ sf : State,
      Steps Program.pureMem s0 sf ∧ Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ (ToBaseSpec.toSpec (spec pl) pl.base).post x s0 sf ∗ R) :=
  subroutine_ok_toPureMem (hok.2 pl hpl) h_noPanic h_noExit h_noOom hpc hrun hpre hsp
    ((PlacedLib.codeLoaded_of_inElf hpl hin hload).of_keepsFrozen hfrozen) h_hooks

/-! ## Lowering with panicking hooks -/

/-- `Steps.toPureMem_of_running` for traces that may stop at a panicking hook: every hook call is
    either realized by `Program.pureMem`, or the hook panics (`(f st).status = .Panicked`) and
    `Program.pureMem` runs from the hook's entry state to a state satisfying `Q`. The trace must
    end `.Running` or in a `SubroutineOutcome` status. -/
theorem Steps.toPureMem_or_hookPanic {prog : Program} {Q : State → Prop} {s0 s sf : State}
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      prog.externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem →
      Steps Program.pureMem st (f st) ∨
        ((f st).status = .Panicked ∧ ∃ sq, Steps Program.pureMem st sq ∧ Q sq))
    (h_kf : s0.mem.KeepsFrozen s.mem) (h_steps : Steps prog s sf)
    (h_end : sf.status = .Running ∨ sf.status = .Panicked ∨ (∃ c, sf.status = .Exited c) ∨
      sf.status = .OutOfMemory)
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    Steps Program.pureMem s sf ∨ ∃ sq, Steps Program.pureMem s sq ∧ Q sq := by
  induction h_steps with
  | refl s => exact Or.inl (Steps.refl s)
  | @step s1 s2 s3 h1 h2 ih =>
    have h_kf2 : s0.mem.KeepsFrozen s2.mem := h_kf.trans h1.keepsFrozen
    cases h1 with
    | @exec inst hr hf =>
      have hf' : Program.pureMem.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem at hf ⊢
        split at hf
        · contradiction
        · exact hf
      have hev : prog.evalInst inst s1 = Program.pureMem.evalInst inst s1 := by
        simp only [Program.evalInst, Program.pureMem, Program.pureWithSvc, Program.ofSvc, h_svc]
      rcases ih h_kf2 h_end with h | ⟨sq, hq, hQ⟩
      · rw [hev] at h; exact Or.inl (Steps.step (Step.exec hr hf') h)
      · rw [hev] at hq; exact Or.inr ⟨sq, Steps.step (Step.exec hr hf') hq, hQ⟩
    | halt_unmapped _ _ _ =>
      have heq := Steps.from_not_running h2 (by simp)
      subst heq
      simp at h_end
    | extern hr he _ _ =>
      rcases h_hooks s1.pc _ s1 he rfl hr h_kf with hh | ⟨_, hq⟩
      · rcases ih h_kf2 h_end with h | ⟨sq, hq, hQ⟩
        · exact Or.inl (hh.trans h)
        · exact Or.inr ⟨sq, hh.trans hq, hQ⟩
      · exact Or.inr hq
    | extern_fault _ _ _ =>
      have heq := Steps.from_not_running h2 (by simp)
      subst heq
      simp at h_end

/-- Panic-tolerant `subroutine_ok_toPureMem`: no `onPanic`/`onExit`/`onOom` restriction. Either
    `Program.pureMem` reaches a `SubroutineOutcome` (ruling out unwanted outcomes is left to the
    caller), or some hook panicked and `Program.pureMem` reaches `Q` (see
    `Steps.toPureMem_or_hookPanic`). -/
theorem subroutine_ok_toPureMem_or_hookPanic {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {Q : State → Prop} (h_sub : subroutine_ok prog entry spec)
    {x : α} {R : SepProp} {s0 : State} (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hcode : prog.CodeLoaded s0.mem)
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      prog.externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem →
      Steps Program.pureMem st (f st) ∨
        ((f st).status = .Panicked ∧ ∃ sq, Steps Program.pureMem st sq ∧ Q sq))
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    (∃ sf, Steps Program.pureMem s0 sf ∧ SubroutineOutcome spec x R s0 sf) ∨
      ∃ sq, Steps Program.pureMem s0 sq ∧ Q sq := by
  obtain ⟨sf, h_steps, hout⟩ := reaches_outcome_iff.1 (subroutine_ok_iff.1 h_sub x R s0 hpc hrun hpre hsp) hcode
  have h_end : sf.status = .Running ∨ sf.status = .Panicked ∨ (∃ c, sf.status = .Exited c) ∨
      sf.status = .OutOfMemory := by
    rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, hc, _⟩ | ⟨ho, _⟩
    · exact Or.inl hret.2.2
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc⟩))
    · exact Or.inr (Or.inr (Or.inr ho))
  rcases Steps.toPureMem_or_hookPanic h_hooks (Memory.KeepsFrozen.refl _) h_steps h_end h_svc
    with h | h
  · exact Or.inl ⟨sf, h, hout⟩
  · exact Or.inr h

/-- Panic-tolerant `PlacedLib.subroutineOk_toPureMem` (see
    `subroutine_ok_toPureMem_or_hookPanic`): for externs such as `Rust.withPanics X'`, a panic
    hook at `pl.ρ e` is discharged by the executable's real panic path reaching `Q`. -/
theorem PlacedLib.subroutineOk_toPureMem_or_hookPanic {S α : Type} [ToBaseSpec S α]
    {lib : PlacedLib} {fnName : String} {spec : Placement → S}
    {X O : String → Option (State → State)} {Q : State → Prop}
    (hok : lib.subroutineOk fnName spec X O) {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable pl) (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s)
    {x : α} {R : SepProp} {s0 : State} (hfrozen : s.mem.KeepsFrozen s0.mem)
    (hpc : s0.pc = lib.fnAddr pl fnName) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (ToBaseSpec.toSpec (spec pl) pl.base).pre x s0 ∗ R)
    (hsp : s0.spAligned = true)
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      (lib.program pl X O).externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem →
      Steps Program.pureMem st (f st) ∨
        ((f st).status = .Panicked ∧ ∃ sq, Steps Program.pureMem st sq ∧ Q sq)) :
    (∃ sf, Steps Program.pureMem s0 sf ∧
        SubroutineOutcome (ToBaseSpec.toSpec (spec pl) pl.base) x R s0 sf) ∨
      ∃ sq, Steps Program.pureMem s0 sq ∧ Q sq :=
  subroutine_ok_toPureMem_or_hookPanic (hok.2 pl hpl) hpc hrun hpre hsp
    ((PlacedLib.codeLoaded_of_inElf hpl hin hload).of_keepsFrozen hfrozen) h_hooks

/-- Outcome-preserving `subroutine_ok_toPureMem`: lowers `subroutine_ok prog entry spec` directly
    to a `Steps Program.pureMem` execution satisfying `SubroutineOutcome spec x R s0 sf` across
    all four outcomes (`.Running` return, `.Panicked`, `.Exited`, and `.OutOfMemory`) without
    requiring `onPanic`/`onExit`/`onOom` to be `⌜False⌝`. -/
theorem subroutine_ok_toPureMem_outcome {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h_sub : subroutine_ok prog entry spec)
    {x : α} {R : SepProp} {s0 : State} (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hcode : prog.CodeLoaded s0.mem)
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      prog.externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem → Steps Program.pureMem st (f st))
    (h_svc : prog.svc = Syscall.standard := by rfl) :
    ∃ sf, Steps Program.pureMem s0 sf ∧ SubroutineOutcome spec x R s0 sf := by
  rcases subroutine_ok_toPureMem_or_hookPanic (Q := fun _ => False) h_sub hpc hrun hpre hsp hcode
      (fun pc f st he hpc' hrun' hkf => Or.inl (h_hooks pc f st he hpc' hrun' hkf)) h_svc with
    h | ⟨_, _, hf⟩
  · exact h
  · exact False.elim hf

/-- Outcome-preserving `PlacedLib.subroutineOk_toPureMem`: lowers `lib.subroutineOk fnName spec X O`
    at placement `pl` in `img` to `Steps Program.pureMem` preserving `onPanic`, `onExit`, and `onOom`. -/
theorem PlacedLib.subroutineOk_toPureMem_outcome {S α : Type} [ToBaseSpec S α]
    {lib : PlacedLib} {fnName : String} {spec : Placement → S}
    {X O : String → Option (State → State)}
    (hok : lib.subroutineOk fnName spec X O) {pl : Placement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable pl) (hin : lib.InElf img pl)
    (hload : img.loadState inputs = .ok s)
    {x : α} {R : SepProp} {s0 : State} (hfrozen : s.mem.KeepsFrozen s0.mem)
    (hpc : s0.pc = lib.fnAddr pl fnName) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (ToBaseSpec.toSpec (spec pl) pl.base).pre x s0 ∗ R)
    (hsp : s0.spAligned = true)
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      (lib.program pl X O).externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem → Steps Program.pureMem st (f st)) :
    ∃ sf, Steps Program.pureMem s0 sf ∧
      SubroutineOutcome (ToBaseSpec.toSpec (spec pl) pl.base) x R s0 sf :=
  subroutine_ok_toPureMem_outcome (hok.2 pl hpl) hpc hrun hpre hsp
    ((PlacedLib.codeLoaded_of_inElf hpl hin hload).of_keepsFrozen hfrozen) h_hooks

/-! ## Lifting `Program.pureMem` traces to hooked programs with unfetched hooks -/

/-- Every extern hook entry point of `P` is non-fetchable in `Program.pureMem` across all
    frozen-preserving evolutions of `m`. Holds vacuously when `P` has no hooks
    (`Program.hooksUnfetched_of_noExterns`), and also holds when `P`'s extern hooks sit on frozen
    bytes where `Program.pureMem.fetchMem` returns `none`
    (`Program.hooksUnfetched_of_frozenNonDecode` / `Program.hooksUnfetched_of_frozenZeroWord`). -/
def _root_.Arm64.Program.HooksUnfetched (P : Program) (m : Memory) : Prop :=
  ∀ m' pc, m.KeepsFrozen m' → P.externAt? pc ≠ none →
    Program.pureMem.fetchMem m' pc = none

/-- Any hook-free program (`∀ pc, P.externAt? pc = none`) satisfies `P.HooksUnfetched m`. -/
theorem _root_.Arm64.Program.hooksUnfetched_of_noExterns {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (m : Memory) :
    P.HooksUnfetched m := by
  intro _ pc _ hne
  exact False.elim (hne (hext pc))

/-- Monotonicity of `Program.HooksUnfetched` along `Memory.KeepsFrozen`. -/
theorem _root_.Arm64.Program.HooksUnfetched.of_keepsFrozen {P : Program} {m0 m : Memory}
    (h : P.HooksUnfetched m0) (hkf : m0.KeepsFrozen m) :
    P.HooksUnfetched m :=
  fun m' pc hkf' hne => h m' pc (hkf.trans hkf') hne

/-- If every hooked address of `P` sits on four frozen bytes in `m0` where `Program.pureMem`
    cannot fetch an instruction (either non-executable or non-decoding 32-bit word), then
    `P.HooksUnfetched m` holds for any frozen-preserving evolution `m` of `m0`. -/
theorem _root_.Arm64.Program.hooksUnfetched_of_frozenNonDecode {P : Program} {m0 m : Memory}
    (hkf : m0.KeepsFrozen m)
    (hnd : ∀ pc, P.externAt? pc ≠ none →
      m0.Frozen (pc + 0#64) ∧ m0.Frozen (pc + 1#64) ∧
      m0.Frozen (pc + 2#64) ∧ m0.Frozen (pc + 3#64) ∧
      Program.pureMem.fetchMem m0 pc = none) :
    P.HooksUnfetched m := by
  intro m' pc hkf' hne
  have hkf0 : m0.KeepsFrozen m' := hkf.trans hkf'
  obtain ⟨hf0, hf1, hf2, hf3, hfetch0⟩ := hnd pc hne
  have hr32 : m'.read32 pc = m0.read32 pc := by
    simp only [Memory.read32, (hkf0 _ hf0).1, (hkf0 _ hf1).1, (hkf0 _ hf2).1, (hkf0 _ hf3).1]
  have hce : m'.canExec pc 4 = m0.canExec pc 4 := by
    have hp0 : m'.perm pc = m0.perm pc := by simpa [BitVec.add_zero] using (hkf0 _ hf0).2.1
    have hp1 : m'.perm (pc + 1#64) = m0.perm (pc + 1#64) := (hkf0 _ hf1).2.1
    have hp2 : m'.perm (pc + 2#64) = m0.perm (pc + 2#64) := (hkf0 _ hf2).2.1
    have hp3 : m'.perm (pc + 3#64) = m0.perm (pc + 3#64) := (hkf0 _ hf3).2.1
    have h12 : (1#64 : BitVec 64) + 1#64 = 2#64 := rfl
    have h21 : (2#64 : BitVec 64) + 1#64 = 3#64 := rfl
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, h12, h21, hp0, hp1, hp2, hp3]
  simpa only [Program.fetchMem, hr32, hce] using hfetch0

/-- Specialization of `Program.hooksUnfetched_of_frozenNonDecode` to frozen zero-word (`0#32`,
    `UDF #0`) stubs. -/
theorem _root_.Arm64.Program.hooksUnfetched_of_frozenZeroWord {P : Program} {m0 m : Memory}
    (hkf : m0.KeepsFrozen m)
    (hstub : ∀ pc, P.externAt? pc ≠ none →
      m0.Frozen (pc + 0#64) ∧ m0.Frozen (pc + 1#64) ∧
      m0.Frozen (pc + 2#64) ∧ m0.Frozen (pc + 3#64) ∧
      m0.read32 pc = 0#32) :
    P.HooksUnfetched m := by
  refine Program.hooksUnfetched_of_frozenNonDecode hkf fun pc hne => ?_
  obtain ⟨hf0, hf1, hf2, hf3, hz⟩ := hstub pc hne
  refine ⟨hf0, hf1, hf2, hf3, ?_⟩
  have hdec : decode (0#32) = none := rfl
  simp only [Program.fetchMem, hz, hdec, ite_self]

private theorem pureMem_externAt_none (pc : BitVec 64) :
    Program.pureMem.externAt? pc = none := rfl

/-- Lift a `Steps Program.pureMem` trace ending in a `SubroutineOutcome` status (`.Running`,
    `.Panicked`, `.Exited`, or `.OutOfMemory`, hence never `.Halted`) to `Steps P` whenever
    `P.svc = Syscall.standard` and `P.HooksUnfetched s0.mem`. -/
theorem _root_.Arm64.Steps.of_pureMem_outcome {P : Program} {s0 s sf : State}
    (hsvc : P.svc = Syscall.standard)
    (hhooks : P.HooksUnfetched s0.mem)
    (h_kf : s0.mem.KeepsFrozen s.mem)
    (h_steps : Steps Program.pureMem s sf)
    (h_end : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory) :
    Steps P s sf := by
  induction h_steps with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    have h_kf2 : s0.mem.KeepsFrozen s2.mem := h_kf.trans h1.keepsFrozen
    cases h1 with
    | @exec inst hr hf =>
      have hext : P.externAt? s1.pc = none := by
        cases hx : P.externAt? s1.pc with
        | none => rfl
        | some f =>
          have hnone := hhooks s1.mem s1.pc h_kf (by simp [hx])
          rw [hnone] at hf
          cases hf
      have hfP : P.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem at hf ⊢
        rw [pureMem_externAt_none s1.pc] at hf
        rwa [hext]
      have hev : Program.pureMem.evalInst inst s1 = P.evalInst inst s1 := by
        simp only [Program.evalInst, Program.pureMem, Program.pureWithSvc, Program.ofSvc, hsvc]
      have hrest := ih h_kf2 h_end
      rw [hev] at hrest
      exact Steps.step (Step.exec hr hfP) hrest
    | halt_unmapped _ _ _ =>
      have heq := Steps.from_not_running h2 (by simp)
      subst heq
      simp at h_end
    | extern _ he _ _ =>
      rw [pureMem_externAt_none] at he
      cases he
    | extern_fault _ he _ =>
      rw [pureMem_externAt_none] at he
      cases he

/-- Lift a `subroutine_ok Program.pureMem` contract across all four `SubroutineOutcome`s to any
    program `P` with `P.svc = Syscall.standard` whose extern hooks are unfetched when `P` is loaded. -/
theorem _root_.Arm64.Program.subroutine_ok_of_pureMem {α : Type} {P : Program}
    {entry : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok Program.pureMem entry spec)
    (hhooks : ∀ m, P.CodeLoaded m → P.HooksUnfetched m)
    (hsvc : P.svc = Syscall.standard := by rfl) :
    subroutine_ok P entry spec := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp hcode
  have hpureL : Program.pureMem.CodeLoaded s0.mem := by
    rw [Program.codeLoaded_iff]
    exact ⟨rfl, by decide, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1 (subroutine_ok_iff.1 hok x R s0 hpc hrun hpre hsp) hpureL
  have hend : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory := by
    rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, hc, _⟩ | ⟨ho, _⟩
    · exact Or.inl hret.2.2
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc⟩))
    · exact Or.inr (Or.inr (Or.inr ho))
  exact ⟨sf, Steps.of_pureMem_outcome hsvc (hhooks s0.mem hcode) (Memory.KeepsFrozen.refl _)
    hsteps hend, hout⟩

end Arm64.Obj
