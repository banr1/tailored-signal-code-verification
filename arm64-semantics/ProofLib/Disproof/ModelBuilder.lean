/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.SubroutineHook
public import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.Model

/-!
# Sparse Memory and Counterexample State Builder

Constructs concrete initial `State` witnesses (`mkDisproofState`) and sparse overlaid `Memory`
models (`buildDisproofMem`) for machine-code counterexamples. `DisproofRegion` pairs declarative
byte and word region descriptions with their separation-logic assertions (`toSepProp`,
`listToSepProp`), and `DisproofRegionsValidB` discharges `CodeLoaded`, separation-logic
satisfaction, and unmapped-address (`Perm.none`) obligations by `decide`.
-/

@[expose] public section

namespace ProofLib.Disproof

open Arm64
open ProofLib

/-! ## Low-Level Region Specifications and Memory Overlay -/

/-- Specification of a contiguous memory region `[base, base + len)` mapped with permission `perm`
    and initialized with `bytes` (zero-padded if `bytes.length < len`). -/
structure MemRegionSpec where
  base  : BitVec 64
  len   : Nat
  perm  : Perm := Perm.rw
  bytes : List (BitVec 8) := []
  deriving DecidableEq, Repr

namespace MemRegionSpec

/-- Read-write byte slice `[base, base + bytes.length)` initialized to `bytes`. -/
def rwBytes (base : BitVec 64) (bytes : List (BitVec 8)) : MemRegionSpec :=
  { base, len := bytes.length, perm := Perm.rw, bytes }

/-- Read-write region `[base, base + len)`, zero-filled past `bytes`. -/
def rwRegion (base : BitVec 64) (len : Nat) (bytes : List (BitVec 8) := []) : MemRegionSpec :=
  { base, len, perm := Perm.rw, bytes }

/-- Read-only byte slice `[base, base + bytes.length)` initialized to `bytes`. -/
def roBytes (base : BitVec 64) (bytes : List (BitVec 8)) : MemRegionSpec :=
  { base, len := bytes.length, perm := Perm.ro, bytes }

/-- Computable disjointness check (`DisjointRegions`) between two region specifications. -/
def disjointB (r₁ r₂ : MemRegionSpec) : Bool :=
  decide (r₁.len ≤ (r₂.base - r₁.base).toNat ∧ r₂.len ≤ (r₁.base - r₂.base).toNat)

theorem disjointB_iff (r₁ r₂ : MemRegionSpec) :
    r₁.disjointB r₂ = true ↔ DisjointRegions r₁.base r₁.len r₂.base r₂.len := by
  simp [disjointB, DisjointRegions]

end MemRegionSpec

/-- Overlay region `r` onto memory `m`: addresses in `InRegion r.base r.len` receive permission
    `r.perm` and byte `(r.bytes[(a - r.base).toNat]?).getD 0#8`; other addresses retain
    `m.cells a`. -/
def overlayRegion (r : MemRegionSpec) (m : Memory) : Memory :=
  ⟨fun a =>
    if InRegion r.base r.len a then
      some (some r.perm, (r.bytes[(a - r.base).toNat]?).getD 0#8)
    else
      m.cells a⟩

theorem overlayRegion_read8_in {r : MemRegionSpec} {m : Memory} {a : BitVec 64}
    (h : InRegion r.base r.len a) :
    (overlayRegion r m).read8 a = (r.bytes[(a - r.base).toNat]?).getD 0#8 := by
  simp [Memory.read8, overlayRegion, h]

theorem overlayRegion_read8_out {r : MemRegionSpec} {m : Memory} {a : BitVec 64}
    (h : ¬ InRegion r.base r.len a) :
    (overlayRegion r m).read8 a = m.read8 a := by
  simp [Memory.read8, overlayRegion, h]

theorem overlayRegion_perm_in {r : MemRegionSpec} {m : Memory} {a : BitVec 64}
    (h : InRegion r.base r.len a) (hrwx : r.perm.rwx = r.perm := by rfl) :
    (overlayRegion r m).perm a = some r.perm := by
  simp [Memory.perm, overlayRegion, h, hrwx]

theorem overlayRegion_perm_out {r : MemRegionSpec} {m : Memory} {a : BitVec 64}
    (h : ¬ InRegion r.base r.len a) :
    (overlayRegion r m).perm a = m.perm a := by
  simp [Memory.perm, overlayRegion, h]

theorem overlayRegion_isLazyFree_in {r : MemRegionSpec} {m : Memory} {a : BitVec 64}
    (h : InRegion r.base r.len a) :
    (overlayRegion r m).isLazyFree a = r.perm.lazyFree := by
  simp [Memory.isLazyFree, overlayRegion, h]

theorem overlayRegion_isLazyFree_out {r : MemRegionSpec} {m : Memory} {a : BitVec 64}
    (h : ¬ InRegion r.base r.len a) :
    (overlayRegion r m).isLazyFree a = m.isLazyFree a := by
  simp [Memory.isLazyFree, overlayRegion, h]

theorem overlayRegion_isAnon_in {r : MemRegionSpec} {m : Memory} {a : BitVec 64}
    (h : InRegion r.base r.len a) :
    (overlayRegion r m).isAnon a = r.perm.anon := by
  simp [Memory.isAnon, overlayRegion, h]

theorem overlayRegion_isAnon_out {r : MemRegionSpec} {m : Memory} {a : BitVec 64}
    (h : ¬ InRegion r.base r.len a) :
    (overlayRegion r m).isAnon a = m.isAnon a := by
  simp [Memory.isAnon, overlayRegion, h]

/-- Build a sparse memory by overlaying each region in `rs` onto `Memory.empty`. -/
def buildRegionsMem : List MemRegionSpec → Memory
  | [] => Memory.empty
  | r :: rs => overlayRegion r (buildRegionsMem rs)

@[simp]
theorem buildRegionsMem_nil : buildRegionsMem [] = Memory.empty := rfl

@[simp]
theorem buildRegionsMem_cons (r : MemRegionSpec) (rs : List MemRegionSpec) :
    buildRegionsMem (r :: rs) = overlayRegion r (buildRegionsMem rs) := rfl

/-- Build a disproof counterexample memory by overlaying `prog`'s code image onto `buildRegionsMem rs`. -/
def buildDisproofMem (prog : Program) (rs : List MemRegionSpec) : Memory :=
  loadCodeMem prog (buildRegionsMem rs)

/-! ## Unmapped Addresses and `CodeLoaded` -/

theorem buildRegionsMem_perm_none (rs : List MemRegionSpec) (a : BitVec 64)
    (hout : ∀ r ∈ rs, ¬ InRegion r.base r.len a) :
    (buildRegionsMem rs).perm a = none := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    have hr : ¬ InRegion r.base r.len a := hout r (List.Mem.head _)
    rw [buildRegionsMem_cons, overlayRegion_perm_out hr]
    exact ih fun r' hr' => hout r' (List.Mem.tail _ hr')

theorem buildDisproofMem_perm_none (prog : Program) (rs : List MemRegionSpec) (a : BitVec 64)
    {codeBase : BitVec 64} {codeLen : Nat}
    (hbase : prog.base = codeBase := by rfl)
    (hlen : prog.code.length = codeLen := by rfl)
    (hcode : ¬ InRegion codeBase codeLen a := by decide)
    (hrs : ∀ r ∈ rs, ¬ InRegion r.base r.len a := by decide) :
    (buildDisproofMem prog rs).perm a = none := by
  unfold buildDisproofMem
  rw [loadCodeMem_perm_out (by rwa [hbase, hlen])]
  exact buildRegionsMem_perm_none rs a hrs

theorem buildDisproofMem_codeLoaded (prog : Program) (rs : List MemRegionSpec)
    {codeBase : BitVec 64} {codeLen : Nat}
    (hbase : prog.base = codeBase := by rfl)
    (hlen : prog.code.length = codeLen := by rfl)
    (h_al : codeBase.toNat % 4 = 0 := by decide)
    (h_len : codeBase.toNat + codeLen ≤ 2 ^ 64 := by decide) :
    prog.CodeLoaded (buildDisproofMem prog rs) :=
  codeLoaded_loadCodeMem (buildRegionsMem rs) (by rwa [hbase]) (by rwa [hbase, hlen])

/-! ## Separation-Logic Satisfaction for Overlaid Regions -/

theorem overlayRegion_readBytes {r : MemRegionSpec} (m : Memory)
    (hlen_eq : r.len = r.bytes.length) (hlen : r.bytes.length ≤ 2 ^ 64) :
    (overlayRegion r m).readBytes r.base r.bytes.length = r.bytes := by
   refine Memory.readBytes_of_read8 fun i hi => ?_
   have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi hlen
   have hsub_bv : r.base + BitVec.ofNat 64 i - r.base = BitVec.ofNat 64 i := by bv_omega
   have hsub : (r.base + BitVec.ofNat 64 i - r.base).toNat = i := by
     rw [hsub_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
   have hin : InRegion r.base r.len (r.base + BitVec.ofNat 64 i) := by
     simpa [InRegion, hsub, hlen_eq] using hi
   rw [overlayRegion_read8_in hin]
   simp [hsub, hi]

section UnsealSepLogic

set_option allowUnsafeReducibility true
attribute [local semireducible]
  Heap.empty Heap.singleton Heap.singletonRO Heap.singletonProtNone Heap.singletonLazy
  Heap.Disjoint Heap.union Heap.Matches
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepExists
  pointsTo8 pointsToBytes pointsTo16 pointsTo32 pointsTo64 pointsTo128 pointsToWords64
  pointsTo8ProtNone pointsToBytesProtNone pointsTo8Lazy
  regionHeap regionHeapRO regionHeapProtNone regionHeapLazy
  regionBlock regionBlockProtNone memRegion memRegionProtNone memRegionLazy

theorem Heap.eq_none_of_matches_perm_none {m : Memory} {h : Heap}
    (hm : h.Matches m) {a : BitVec 64} (hp : m.perm a = none) :
    h a = none := by
  cases ha : h a with
  | none => rfl
  | some c =>
    cases c with
    | rw b =>
      have ⟨_, hperm, _⟩ := hm.1 a (.rw b) ha
      rw [hp] at hperm; cases hperm
    | ro b =>
      have ⟨_, hperm, _⟩ := hm.1 a (.ro b) ha
      rw [hp] at hperm; cases hperm
    | protNone b =>
      have ⟨_, hperm, _⟩ := hm.1 a (.protNone b) ha
      rw [hp] at hperm; cases hperm
    | lazy =>
      have hperm := hm.1 a .lazy ha
      rw [hp] at hperm; cases hperm
    | protNoneLazy =>
      have hperm := hm.1 a .protNoneLazy ha
      rw [hp] at hperm; cases hperm

theorem Heap.mapped_eq_false_of_matches_perm_none {m : Memory} {h : Heap}
    (hm : h.Matches m) {a : BitVec 64} (hp : m.perm a = none) :
    h.mapped a = false := by
  cases hma : h.mapped a with
  | false => rfl
  | true =>
    have hperm := (hm.2.2 a hma).1
    rw [hp] at hperm; contradiction

theorem Heap.Matches.overlayRegion_of_perm_none {r : MemRegionSpec} {m : Memory} {h : Heap}
    (hm : h.Matches m)
    (hfresh : ∀ a, InRegion r.base r.len a → m.perm a = none) :
    h.Matches (overlayRegion r m) := by
  refine ⟨fun a c hac => ?_, hm.2.1, fun a hma => ?_⟩
  · have hout : ¬ InRegion r.base r.len a := fun hin => by
      rw [Heap.eq_none_of_matches_perm_none hm (hfresh a hin)] at hac
      contradiction
    have hc := hm.1 a c hac
    cases c <;>
      simp only [overlayRegion_read8_out hout, overlayRegion_perm_out hout,
        overlayRegion_isLazyFree_out hout] <;>
      exact hc
  · have hout : ¬ InRegion r.base r.len a := fun hin => by
      rw [Heap.mapped_eq_false_of_matches_perm_none hm (hfresh a hin)] at hma
      contradiction
    rw [overlayRegion_perm_out hout, overlayRegion_isAnon_out hout]
    exact hm.2.2 a hma

theorem satisfies_overlayRegion_preserve {r : MemRegionSpec} {m : Memory} {Q : SepProp}
    (hfresh : ∀ a, InRegion r.base r.len a → m.perm a = none)
    (hQ : m ⊨ Q) :
    overlayRegion r m ⊨ Q := by
  obtain ⟨h, hQ_h, hm⟩ := SepProp.satisfies_iff.mp hQ
  exact SepProp.satisfies_iff.mpr
    ⟨h, hQ_h, Heap.Matches.overlayRegion_of_perm_none hm hfresh⟩

theorem satisfies_loadCodeMem_of_perm_none {prog : Program} {m : Memory} {Q : SepProp}
    (hfresh : ∀ a, InRegion prog.base prog.code.length a → m.perm a = none)
    (hQ : m ⊨ Q) :
    loadCodeMem prog m ⊨ Q := by
  obtain ⟨h, hQ_h, hm⟩ := SepProp.satisfies_iff.mp hQ
  exact SepProp.satisfies_iff.mpr ⟨h, hQ_h, Heap.Matches.loadCodeMem_of_eq_none hm fun a hin =>
    Heap.eq_none_of_matches_perm_none hm (hfresh a hin)⟩

theorem IsBlock.satisfies_overlayRegion {P Q : SepProp} {r : MemRegionSpec} {Φ : Memory → Prop}
    {m : Memory}
    (hblk : IsBlock P r.base r.len Φ)
    (hperm : r.perm = Perm.rw)
    (hΦ : Φ (overlayRegion r m))
    (hfresh : ∀ a, InRegion r.base r.len a → m.perm a = none)
    (hQ : m ⊨ Q) :
    overlayRegion r m ⊨ P ∗ Q := by
  obtain ⟨hq, hQ_hq, hmq⟩ := SepProp.satisfies_iff.mp hQ
  let m' := overlayRegion r m
  have hrw : m'.RW r.base r.len := by
    intro a ha
    refine Memory.permNoLazy_eq_some_rw_iff.mpr ⟨?_, ?_⟩
    · rw [overlayRegion_perm_in ha (by rw [hperm]; rfl), hperm]
    · rw [overlayRegion_isLazyFree_in ha, hperm]; rfl
  have hm_blk : (regionHeap r.base r.len m').Matches m' :=
    IsBlock.regionHeap_matches r.base r.len m' hrw
  have hm_q : hq.Matches m' := Heap.Matches.overlayRegion_of_perm_none hmq hfresh
  have hdisj : (regionHeap r.base r.len m').Disjoint hq := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
    by_cases ha : InRegion r.base r.len a
    · exact Or.inr (Or.inl (Heap.eq_none_of_matches_perm_none hmq (hfresh a ha)))
    · exact Or.inl (by simp [regionHeap, ha])
  exact SepProp.satisfies_iff.mpr ⟨(regionHeap r.base r.len m').union hq,
    SepProp.holds_sepConj_iff.mpr
      ⟨regionHeap r.base r.len m', hq, hdisj, rfl, (hblk.iff _).mpr ⟨m', hΦ, rfl⟩, hQ_hq⟩,
    Heap.Matches.union hm_blk hm_q⟩

theorem IsBlockRO.satisfies_overlayRegion {P_ro Q : SepProp} {r : MemRegionSpec} {Φ : Memory → Prop}
    {m : Memory}
    (hblk : IsBlockRO P_ro r.base r.len Φ)
    (hperm : r.perm = Perm.ro)
    (hΦ : Φ (overlayRegion r m))
    (hfresh : ∀ a, InRegion r.base r.len a → m.perm a = none)
    (hQ : m ⊨ Q) :
    overlayRegion r m ⊨ P_ro ∗ Q := by
  have hro : (overlayRegion r m).RO r.base r.len := by
    intro a ha
    refine ⟨?_, ?_⟩
    · rw [overlayRegion_perm_in ha (by rw [hperm]; rfl), hperm]
    · rw [overlayRegion_isLazyFree_in ha, hperm]; rfl
  exact hblk.intro_of_ro hro hΦ (satisfies_overlayRegion_preserve hfresh hQ)

end UnsealSepLogic

theorem overlayRegion_rwBytes_satisfies {base : BitVec 64} {bs : List (BitVec 8)}
    {m : Memory} {Q : SepProp}
    (hlen : bs.length ≤ 2 ^ 64)
    (hfresh : ∀ a, InRegion base bs.length a → m.perm a = none)
    (hQ : m ⊨ Q) :
    overlayRegion (MemRegionSpec.rwBytes base bs) m ⊨ (base ↦ₛ bs) ∗ Q :=
  IsBlock.satisfies_overlayRegion (IsBlock.pointsToBytes base bs) rfl
    ⟨hlen, overlayRegion_readBytes m rfl hlen⟩ hfresh hQ

theorem overlayRegion_rwRegion_satisfies {base : BitVec 64} {len : Nat} {bytes : List (BitVec 8)}
    {m : Memory} {Q : SepProp}
    (hfresh : ∀ a, InRegion base len a → m.perm a = none)
    (hQ : m ⊨ Q) :
    overlayRegion (MemRegionSpec.rwRegion base len bytes) m ⊨ memRegion base len ∗ Q :=
  IsBlock.satisfies_overlayRegion (IsBlock.memRegion base len) rfl trivial hfresh hQ

theorem overlayRegion_roBytes_satisfies {base : BitVec 64} {bs : List (BitVec 8)}
    {m : Memory} {Q : SepProp}
    (hlen : bs.length ≤ 2 ^ 64)
    (hfresh : ∀ a, InRegion base bs.length a → m.perm a = none)
    (hQ : m ⊨ Q) :
    overlayRegion (MemRegionSpec.roBytes base bs) m ⊨ (base ↦ᵣ bs) ∗ Q :=
  IsBlockRO.satisfies_overlayRegion (IsBlockRO.pointsToBytesRO base bs hlen) rfl
    (overlayRegion_readBytes m rfl hlen) hfresh hQ

/-! ## Declarative `DisproofRegion` Builder -/

/-- Declarative specification of a memory region in a counterexample model, pairing its physical
    layout (`toSpec`) with its separation-logic assertion (`toSepProp`). -/
inductive DisproofRegion where
  | rw8      (base : BitVec 64) (val : BitVec 8)
  | rw16     (base : BitVec 64) (val : BitVec 16)
  | rw32     (base : BitVec 64) (val : BitVec 32)
  | rw64     (base : BitVec 64) (val : BitVec 64)
  | rwBytes  (base : BitVec 64) (bytes : List (BitVec 8))
  | rwRegion (base : BitVec 64) (len : Nat) (initBytes : List (BitVec 8) := [])
  | ro8      (base : BitVec 64) (val : BitVec 8)
  | ro16     (base : BitVec 64) (val : BitVec 16)
  | ro32     (base : BitVec 64) (val : BitVec 32)
  | ro64     (base : BitVec 64) (val : BitVec 64)
  | roBytes  (base : BitVec 64) (bytes : List (BitVec 8))
  deriving DecidableEq, Repr

namespace DisproofRegion

def toSpec : DisproofRegion → MemRegionSpec
  | .rw8 base val           => MemRegionSpec.rwBytes base [val]
  | .rw16 base val          => MemRegionSpec.rwBytes base (unpack16 val)
  | .rw32 base val          => MemRegionSpec.rwBytes base (unpack32 val)
  | .rw64 base val          => MemRegionSpec.rwBytes base (unpack64 val)
  | .rwBytes base bytes     => MemRegionSpec.rwBytes base bytes
  | .rwRegion base len init => MemRegionSpec.rwRegion base len init
  | .ro8 base val           => MemRegionSpec.roBytes base [val]
  | .ro16 base val          => MemRegionSpec.roBytes base (unpack16 val)
  | .ro32 base val          => MemRegionSpec.roBytes base (unpack32 val)
  | .ro64 base val          => MemRegionSpec.roBytes base (unpack64 val)
  | .roBytes base bytes     => MemRegionSpec.roBytes base bytes

/-- The separation-logic assertion established by a single `DisproofRegion`. -/
def toSepProp : DisproofRegion → SepProp
  | .rw8 base val       => base ↦₈ val
  | .rw16 base val      => base ↦₁₆ val
  | .rw32 base val      => base ↦₃₂ val
  | .rw64 base val      => base ↦₆₄ val
  | .rwBytes base bytes => base ↦ₛ bytes
  | .rwRegion base len _ => memRegion base len
  | .ro8 base val       => base ↦₈ᵣ val
  | .ro16 base val      => base ↦₁₆ᵣ val
  | .ro32 base val      => base ↦₃₂ᵣ val
  | .ro64 base val      => base ↦₆₄ᵣ val
  | .roBytes base bytes => base ↦ᵣ bytes

/-- The separating conjunction of assertions established by a list of `DisproofRegion`s. -/
@[simp]
def listToSepProp : List DisproofRegion → SepProp
  | []      => SepProp.emp
  | [r]     => r.toSepProp
  | r :: rs => r.toSepProp ∗ listToSepProp rs

theorem satisfies_overlay (r : DisproofRegion) {m : Memory} {Q : SepProp}
    (hlen : r.toSpec.len ≤ 2 ^ 64)
    (hfresh : ∀ a, InRegion r.toSpec.base r.toSpec.len a → m.perm a = none)
    (hQ : m ⊨ Q) :
    overlayRegion r.toSpec m ⊨ r.toSepProp ∗ Q := by
  cases r with
  | rw8 base val =>
    rw [toSepProp, ← pointsToBytes_singleton]
    exact overlayRegion_rwBytes_satisfies hlen hfresh hQ
  | rw16 base val =>
    rw [toSepProp, pointsTo16_eq_pointsToBytes]
    exact overlayRegion_rwBytes_satisfies hlen hfresh hQ
  | rw32 base val =>
    rw [toSepProp, pointsTo32_eq_pointsToBytes]
    exact overlayRegion_rwBytes_satisfies hlen hfresh hQ
  | rw64 base val =>
    rw [toSepProp, pointsTo64_eq_pointsToBytes]
    exact overlayRegion_rwBytes_satisfies hlen hfresh hQ
  | rwBytes base bytes =>
    exact overlayRegion_rwBytes_satisfies hlen hfresh hQ
  | rwRegion base len init =>
    exact overlayRegion_rwRegion_satisfies hfresh hQ
  | ro8 base val =>
    rw [toSepProp, ← pointsToBytesRO_singleton]
    exact overlayRegion_roBytes_satisfies hlen hfresh hQ
  | ro16 base val =>
    rw [toSepProp, pointsTo16RO_eq_pointsToBytesRO]
    exact overlayRegion_roBytes_satisfies hlen hfresh hQ
  | ro32 base val =>
    rw [toSepProp, pointsTo32RO_eq_pointsToBytesRO]
    exact overlayRegion_roBytes_satisfies hlen hfresh hQ
  | ro64 base val =>
    rw [toSepProp, pointsTo64RO_eq_pointsToBytesRO]
    exact overlayRegion_roBytes_satisfies hlen hfresh hQ
  | roBytes base bytes =>
    exact overlayRegion_roBytes_satisfies hlen hfresh hQ

end DisproofRegion

/-- Computable check that all regions in `rs` have `len ≤ 2 ^ 64` and are pairwise disjoint. -/
def RegionsPairwiseDisjointB : List MemRegionSpec → Bool
  | [] => true
  | r :: rs =>
    decide (r.len ≤ 2 ^ 64) &&
    rs.all (fun r' => r.disjointB r') &&
    RegionsPairwiseDisjointB rs

/-- Computable check that a code image `[codeBase, codeBase + codeLen)` is valid (`4`-byte aligned,
    no-wrap) and disjoint from every region in `rs`, and that `rs` is pairwise disjoint. -/
def DisproofRegionsValidB (codeBase : BitVec 64) (codeLen : Nat) (rs : List DisproofRegion) : Bool :=
  let specs := rs.map DisproofRegion.toSpec
  let codeSpec : MemRegionSpec := { base := codeBase, len := codeLen, perm := Perm.rx }
  decide (codeBase.toNat % 4 = 0) &&
  decide (codeBase.toNat + codeLen ≤ 2 ^ 64) &&
  specs.all (fun r => codeSpec.disjointB r) &&
  RegionsPairwiseDisjointB specs

theorem DisjointRegions.not_inRegion_right {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) (hlen₁ : n₁ ≤ 2 ^ 64)
    {a : BitVec 64} (ha : InRegion b₁ n₁ a) : ¬ InRegion b₂ n₂ a :=
  (outsideRegion_iff_not_inRegion b₂ n₂ a).mp (h.symm.outside ha hlen₁)

theorem buildRegionsMem_satisfies (rs : List DisproofRegion)
    (hdisj : RegionsPairwiseDisjointB (rs.map DisproofRegion.toSpec) = true) :
    buildRegionsMem (rs.map DisproofRegion.toSpec) ⊨ DisproofRegion.listToSepProp rs := by
  induction rs with
  | nil =>
    exact satisfies_emp _
  | cons r rest ih =>
    simp only [List.map_cons, RegionsPairwiseDisjointB, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hdisj
    rcases hdisj with ⟨⟨hlen, hall⟩, hrest⟩
    have hfresh : ∀ a, InRegion r.toSpec.base r.toSpec.len a →
        (buildRegionsMem (rest.map DisproofRegion.toSpec)).perm a = none := by
      intro a ha
      refine buildRegionsMem_perm_none _ a fun r' hr' => ?_
      have hd : DisjointRegions r.toSpec.base r.toSpec.len r'.base r'.len :=
        (MemRegionSpec.disjointB_iff _ _).mp (hall r' hr')
      exact DisjointRegions.not_inRegion_right hd hlen ha
    have hsat := r.satisfies_overlay hlen hfresh (ih hrest)
    cases rest with
    | nil =>
      simpa [DisproofRegion.listToSepProp, sepConj_emp] using hsat
    | cons r' rest' =>
      exact hsat

/-- If `DisproofRegionsValidB codeBase codeLen rs = true` (discharged by `decide` on concrete
    regions), then `buildDisproofMem prog (rs.map DisproofRegion.toSpec)` satisfies
    `DisproofRegion.listToSepProp rs`. -/
theorem buildDisproofMem_satisfies (prog : Program) (rs : List DisproofRegion)
    {codeBase : BitVec 64} {codeLen : Nat}
    (hbase : prog.base = codeBase := by rfl)
    (hlen : prog.code.length = codeLen := by rfl)
    (hvalid : DisproofRegionsValidB codeBase codeLen rs = true := by decide) :
    buildDisproofMem prog (rs.map DisproofRegion.toSpec) ⊨ DisproofRegion.listToSepProp rs := by
  simp only [DisproofRegionsValidB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hvalid
  rcases hvalid with ⟨⟨⟨_, hcode_len⟩, hcode_disj⟩, hrs_disj⟩
  have hcode_le : prog.code.length ≤ 2 ^ 64 := by
    rw [hlen]; exact Nat.le_trans (Nat.le_add_left _ _) hcode_len
  refine satisfies_loadCodeMem_of_perm_none (fun a ha => ?_) (buildRegionsMem_satisfies rs hrs_disj)
  refine buildRegionsMem_perm_none _ a fun r' hr' => ?_
  have hd : DisjointRegions prog.base prog.code.length r'.base r'.len := by
    rw [hbase, hlen]; exact (MemRegionSpec.disjointB_iff _ _).mp (hcode_disj r' hr')
  exact DisjointRegions.not_inRegion_right hd hcode_le ha

theorem buildDisproofMem_codeLoaded_of_valid (prog : Program) (rs : List DisproofRegion)
    {codeBase : BitVec 64} {codeLen : Nat}
    (hbase : prog.base = codeBase := by rfl)
    (hlen : prog.code.length = codeLen := by rfl)
    (hvalid : DisproofRegionsValidB codeBase codeLen rs = true := by decide) :
    prog.CodeLoaded (buildDisproofMem prog (rs.map DisproofRegion.toSpec)) := by
  simp only [DisproofRegionsValidB, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  rcases hvalid with ⟨⟨⟨h_al, h_len⟩, _⟩, _⟩
  exact buildDisproofMem_codeLoaded prog (rs.map DisproofRegion.toSpec) hbase hlen h_al h_len

/-! ## Initial Counterexample State -/

/-- Apply `(Reg, BitVec 64)` GPR overrides onto `rf`, ignoring writes to register index 31. -/
def applyRegOverrides (regs : List (Reg × BitVec 64)) (rf : RegFile) : RegFile :=
  regs.foldl (fun acc (r, v) =>
    match r with
    | .gpr idx => if idx == 31#5 then acc else acc.write idx v
    | _ => acc) rf

/-- Construct a concrete initial `State` for a machine-code counterexample at `entry_pc` with
    stack pointer `sp0`, unaligned sentinel return address `lr0` in `x30`, register overrides `regs`,
    declarative memory regions `rs`, and external symbol table `symtab`. -/
def mkDisproofState (prog : Program) (entry_pc : BitVec 64)
    (sp0 : BitVec 64 := 0x0000_7fff_ffff_0000#64)
    (lr0 : BitVec 64 := 0xdead_beef_0000_0001#64)
    (regs : List (Reg × BitVec 64) := [])
    (rs : List DisproofRegion := [])
    (symtab : String → String → Option (BitVec 64) := fun _ _ => none) : State :=
  { regs   := applyRegOverrides regs { regs := fun idx => if idx = 30#5 then lr0 else 0#64 }
    sp     := sp0
    pc     := entry_pc
    mem    := buildDisproofMem prog (rs.map DisproofRegion.toSpec)
    symtab := symtab }

@[simp]
theorem mkDisproofState_pc (prog : Program) (entry_pc sp0 lr0 : BitVec 64)
    (regs : List (Reg × BitVec 64)) (rs : List DisproofRegion)
    (symtab : String → String → Option (BitVec 64)) :
    (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab).pc = entry_pc := rfl

@[simp]
theorem mkDisproofState_sp (prog : Program) (entry_pc sp0 lr0 : BitVec 64)
    (regs : List (Reg × BitVec 64)) (rs : List DisproofRegion)
    (symtab : String → String → Option (BitVec 64)) :
    (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab).sp = sp0 := rfl

@[simp]
theorem mkDisproofState_status (prog : Program) (entry_pc sp0 lr0 : BitVec 64)
    (regs : List (Reg × BitVec 64)) (rs : List DisproofRegion)
    (symtab : String → String → Option (BitVec 64)) :
    (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab).status = .Running := rfl

@[simp]
theorem mkDisproofState_mem (prog : Program) (entry_pc sp0 lr0 : BitVec 64)
    (regs : List (Reg × BitVec 64)) (rs : List DisproofRegion)
    (symtab : String → String → Option (BitVec 64)) :
    (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab).mem =
      buildDisproofMem prog (rs.map DisproofRegion.toSpec) := rfl

@[simp]
theorem mkDisproofState_symtab (prog : Program) (entry_pc sp0 lr0 : BitVec 64)
    (regs : List (Reg × BitVec 64)) (rs : List DisproofRegion)
    (symtab : String → String → Option (BitVec 64)) :
    (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab).symtab = symtab := rfl

theorem mkDisproofState_aapcsEntry (prog : Program) (entry_pc : BitVec 64)
    (sp0 : BitVec 64 := 0x0000_7fff_ffff_0000#64)
    (lr0 : BitVec 64 := 0xdead_beef_0000_0001#64)
    (regs : List (Reg × BitVec 64) := [])
    (rs : List DisproofRegion := [])
    (symtab : String → String → Option (BitVec 64) := fun _ _ => none)
    (hsp : (sp0 &&& 15#64 == 0#64) = true := by decide) :
    AapcsEntry (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab) entry_pc := by
  refine ⟨rfl, rfl, ?_⟩
  simpa [State.spAligned, mkDisproofState] using hsp

theorem mkDisproofState_codeLoaded (prog : Program) (entry_pc : BitVec 64)
    (sp0 : BitVec 64 := 0x0000_7fff_ffff_0000#64)
    (lr0 : BitVec 64 := 0xdead_beef_0000_0001#64)
    (regs : List (Reg × BitVec 64) := [])
    (rs : List DisproofRegion := [])
    (symtab : String → String → Option (BitVec 64) := fun _ _ => none)
    {codeBase : BitVec 64} {codeLen : Nat}
    (hbase : prog.base = codeBase := by rfl)
    (hlen : prog.code.length = codeLen := by rfl)
    (hvalid : DisproofRegionsValidB codeBase codeLen rs = true := by decide) :
    prog.CodeLoaded (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab).mem :=
  buildDisproofMem_codeLoaded_of_valid prog rs hbase hlen hvalid

theorem mkDisproofState_satisfies (prog : Program) (entry_pc : BitVec 64)
    (sp0 : BitVec 64 := 0x0000_7fff_ffff_0000#64)
    (lr0 : BitVec 64 := 0xdead_beef_0000_0001#64)
    (regs : List (Reg × BitVec 64) := [])
    (rs : List DisproofRegion := [])
    (symtab : String → String → Option (BitVec 64) := fun _ _ => none)
    {codeBase : BitVec 64} {codeLen : Nat}
    (hbase : prog.base = codeBase := by rfl)
    (hlen : prog.code.length = codeLen := by rfl)
    (hvalid : DisproofRegionsValidB codeBase codeLen rs = true := by decide) :
    (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab).mem ⊨ DisproofRegion.listToSepProp rs :=
  buildDisproofMem_satisfies prog rs hbase hlen hvalid

theorem mkDisproofState_perm_none (prog : Program) (entry_pc a : BitVec 64)
    (sp0 : BitVec 64 := 0x0000_7fff_ffff_0000#64)
    (lr0 : BitVec 64 := 0xdead_beef_0000_0001#64)
    (regs : List (Reg × BitVec 64) := [])
    (rs : List DisproofRegion := [])
    (symtab : String → String → Option (BitVec 64) := fun _ _ => none)
    {codeBase : BitVec 64} {codeLen : Nat}
    (hbase : prog.base = codeBase := by rfl)
    (hlen : prog.code.length = codeLen := by rfl)
    (hcode : ¬ InRegion codeBase codeLen a := by decide)
    (hrs : ∀ r ∈ rs.map DisproofRegion.toSpec, ¬ InRegion r.base r.len a := by decide) :
    (mkDisproofState prog entry_pc sp0 lr0 regs rs symtab).mem.perm a = none :=
  buildDisproofMem_perm_none prog (rs.map DisproofRegion.toSpec) a hbase hlen hcode hrs

end ProofLib.Disproof
