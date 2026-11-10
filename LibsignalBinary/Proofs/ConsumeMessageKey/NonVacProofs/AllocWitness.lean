/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Aesop.BuiltinRules
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import Mathlib.Tactic.ToDual
public import ProofLib.Hoare.LibcHooks
public import LibsignalBinary.Proofs.SpecLemmas.RustHeapAllocProofDefs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.VCGen
import VCVio.Prelude.Core

@[expose] public section

namespace CryptoVerification.LibsignalSession.NonVacuityWitness

open Arm64 ProofLib CryptoVerification.RustHeap

/-- Witness `RustAlloc` instance with `emp` pool and live tokens. -/
def A₀ : RustAlloc := ⟨emp, fun _ _ _ => emp⟩

/-- Existence of a non-null, `align`-aligned unmapped region of `size` bytes in `m`. -/
def HasRoom (m : Memory) (size align : Nat) : Prop :=
  ∃ p : BitVec 64, p ≠ 0 ∧ p.toNat % align = 0 ∧ Unmapped m p size

theorem heapMatches_mapFresh {h : Heap} {m : Memory} (hm : h.Matches m)
    (base : BitVec 64) (len : Nat) (p : Perm) :
    h.Matches (m.mapFresh base len p) := by
  unfold Heap.Matches at hm ⊢
  refine ⟨fun a c hac => ?_, hm.2.1, fun a hmap => ?_⟩
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

/-- `Memory.mapFresh` on an unmapped region produces a `memRegion` separated from existing assertions. -/
theorem satisfies_mapFresh_unmapped {P : SepProp} {m : Memory} {p : BitVec 64} {size : Nat}
    (hP : m ⊨ P) (hu : Unmapped m p size) :
    m.mapFresh p size Perm.rw ⊨ memRegion p size ∗ P := by
  have hmap : m.canMap p size = true := by
    rw [Memory.canMap, Memory.allPerm_iff]
    intro i hi
    have hin : InRegion p size (p + BitVec.ofNat 64 i) := by
      simp only [InRegion]
      have hsub : p + BitVec.ofNat 64 i - p = BitVec.ofNat 64 i := by
        rw [BitVec.add_comm, BitVec.add_sub_cancel]
      rw [hsub, BitVec.toNat_ofNat]
      exact Nat.lt_of_le_of_lt (Nat.mod_le i (2 ^ 64)) hi
    rw [Bool.not_eq_true']
    exact hu (p + BitVec.ofNat 64 i) hin
  refine (IsBlock.memRegion p size).update (IsBlock.memRegion p size) (Nat.le_refl _)
    (Satisfies.mapZero hP hmap) ⟨?_, ?_, ?_, ?_, ?_⟩ trivial
  · intro a hout
    rw [outsideRegion_iff_not_inRegion] at hout
    have hlt : ¬ ((a - p).toNat < size) := hout
    simp only [Memory.read8_mapFresh, Memory.read8_mapZero, hlt, decide_false, Bool.false_and]
    rfl
  · ext a
    simp [Memory.perm_mapFresh, Memory.perm_mapZero, Perm.rw, Perm.rwx]
  · intro a hout
    rw [outsideRegion_iff_not_inRegion] at hout
    have hlt : ¬ ((a - p).toNat < size) := hout
    simp only [Memory.isLazyFree_mapFresh, Memory.isLazyFree_mapZero, hlt, decide_false,
      Bool.false_and]
    rfl
  · intro a hlf
    rw [Memory.isLazyFree_mapZero] at hlf
    simp [Memory.isLazyFree_mapFresh, Perm.rw, hlf]
  · intro a han
    simpa [Memory.isAnon_mapFresh, Memory.isAnon_mapZero, Perm.rw] using han

noncomputable def allocBody (s : State) : State :=
  let size := (s.readReg64 .x0).toNat
  let align := (s.readReg64 .x1).toNat
  letI := Classical.propDecidable (HasRoom s.mem size align)
  if h : HasRoom s.mem size align then
    let p := Classical.choose h
    (s.setMem (s.mem.mapFresh p size Perm.rw)).writeReg64 .x0 p
  else
    (s.appendTrace [allocFailedEvent]).writeReg64 .x0 0#64

noncomputable def witnessAllocHook : State → State :=
  retHook allocBody

noncomputable def reallocBody (s : State) : State :=
  let p := s.readReg64 .x0
  let old := (s.readReg64 .x1).toNat
  let align := (s.readReg64 .x2).toNat
  let new := (s.readReg64 .x3).toNat
  letI := Classical.propDecidable (HasRoom s.mem new align)
  if h : HasRoom s.mem new align then
    let q := Classical.choose h
    let m1 := s.mem.mapFresh q new Perm.rw
    let m2 := m1.writeBytes q (s.mem.readBytes p (min old new))
    (s.setMem m2).writeReg64 .x0 q
  else
    (s.appendTrace [allocFailedEvent]).writeReg64 .x0 0#64

noncomputable def witnessReallocHook : State → State :=
  retHook reallocBody

def witnessDeallocHook : State → State :=
  hookNoop

noncomputable def witnessHooks : String → Option (State → State) := fun sym =>
  if sym = "__rustc::__rust_alloc" then some witnessAllocHook
  else if sym = "__rustc::__rust_dealloc" then some witnessDeallocHook
  else if sym = "__rustc::__rust_realloc" then some witnessReallocHook
  else none

theorem readBytes_add (m : Memory) (p : BitVec 64) (j k : Nat) :
    m.readBytes p (j + k) = m.readBytes p j ++ m.readBytes (p + BitVec.ofNat 64 j) k := by
  induction j generalizing p with
  | zero =>
    simp [Memory.readBytes]
  | succ j ih =>
    rw [Nat.succ_add, Memory.readBytes_succ, Memory.readBytes_succ, List.cons_append, ih (p + 1#64)]
    have hadd : p + 1#64 + BitVec.ofNat 64 j = p + BitVec.ofNat 64 (j + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 j]
    rw [hadd]

theorem readReg64_setPC_writeReg64_x0 (s : State) (v pc : BitVec 64) :
    ((s.writeReg64 .x0 v).setPC pc).readReg64 .x0 = v := rfl

theorem witnessAllocHook_ok : HookOk witnessAllocHook (rustAllocSpec A₀) := by
  refine retHook_ok fun ⟨size, align⟩ R s0 hrun hpre _hsp => ?_
  simp only [rustAllocSpec, A₀, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, _hlayout⟩, hmem⟩
  unfold retHook allocBody
  dsimp only
  rw [hx0, hx1]
  split
  · rename_i hroom
    have hspec := Classical.choose_spec hroom
    rcases hspec with ⟨hp_ne, hp_al, hp_unmap⟩
    set p := Classical.choose hroom
    refine ⟨Memory.keepsFrozen_mapFresh s0.mem p size Perm.rw, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [rustAllocSpec]
    simp only [A₀, emp_sepConj, readReg64_setPC_writeReg64_x0,
      hp_ne, ↓reduceIte, sepConj_assoc]
    have hmap := satisfies_mapFresh_unmapped hmem hp_unmap
    change s0.mem.mapFresh p size Perm.rw ⊨
      stackAt s0.sp allocHookStack ∗ (⌜p.toNat % align = 0 ∧ s0.trace = s0.trace⌝ ∗
        (memRegion p size ∗ R))
    have heq :
        (stackAt s0.sp allocHookStack ∗ (⌜p.toNat % align = 0 ∧ s0.trace = s0.trace⌝ ∗
          (memRegion p size ∗ R))) =
        (⌜p.toNat % align = 0 ∧ s0.trace = s0.trace⌝ ∗
          (memRegion p size ∗ (stackAt s0.sp allocHookStack ∗ R))) := by
      ac_rfl
    rw [heq, satisfies_pure_sepConj]
    exact ⟨⟨hp_al, rfl⟩, hmap⟩
  · rename_i hnroom
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    have hzero : (0#64 : BitVec 64) = 0 := rfl
    dsimp only [rustAllocSpec]
    simp only [A₀, emp_sepConj, readReg64_setPC_writeReg64_x0,
      hzero, ↓reduceIte, sepConj_assoc]
    change s0.mem ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜s0.trace ++ [allocFailedEvent] = s0.trace ++ [allocFailedEvent]⌝ ∗ R)
    rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
    exact ⟨rfl, hmem⟩

theorem witnessDeallocHook_ok : HookOk witnessDeallocHook (rustDeallocSpec A₀) := by
  refine hookNoop_ok fun ⟨p, size, align⟩ R s0 hpre => ?_
  simp only [rustDeallocSpec, A₀, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨rfl, ?_⟩
  exact Satisfies.of_sep_right hpre.2

theorem witnessReallocHook_ok : HookOk witnessReallocHook (rustReallocSpec A₀) := by
  refine retHook_ok fun ⟨p, old, align, new, bs⟩ R s0 hrun hpre _hsp => ?_
  simp only [rustReallocSpec, A₀, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlayout, hbs_old, hbs_new⟩, hmem⟩
  have hnew_le : new ≤ 2 ^ 64 := by
    rcases hlayout with ⟨_, _, hle⟩
    omega
  unfold retHook reallocBody
  dsimp only
  rw [hx0, hx1, hx2, hx3]
  split
  · rename_i hroom
    have hspec := Classical.choose_spec hroom
    rcases hspec with ⟨hq_ne, hq_al, hq_unmap⟩
    set q := Classical.choose hroom
    let c := min old new
    have hc_le_new : c ≤ new := Nat.min_le_right old new
    have hbs_le_c : bs.length ≤ c := Nat.le_min.mpr ⟨hbs_old, hbs_new⟩
    obtain ⟨_, hread_bs⟩ := (IsBlock.pointsToBytes p bs).read hmem
    have hcopy_eq : s0.mem.readBytes p c =
        bs ++ s0.mem.readBytes (p + BitVec.ofNat 64 bs.length) (c - bs.length) := by
      have hc_split : c = bs.length + (c - bs.length) := by omega
      conv => lhs; rw [hc_split]
      rw [readBytes_add, hread_bs]
    let extra := s0.mem.readBytes (p + BitVec.ofNat 64 bs.length) (c - bs.length)
    have hextra_len : extra.length = c - bs.length := Memory.readBytes_length ..
    let copied := s0.mem.readBytes p c
    have hcopied_len : copied.length = c := Memory.readBytes_length ..
    let m1 := s0.mem.mapFresh q new Perm.rw
    have hm1 : m1 ⊨ memRegion q new ∗
        ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          (stackAt s0.sp allocHookStack ∗ R))) :=
      satisfies_mapFresh_unmapped hmem hq_unmap
    have hnew_split : new = copied.length + (new - c) := by omega
    rw [hnew_split, memRegion_split q copied.length (new - c) (by omega), sepConj_assoc] at hm1
    have hkf1 : s0.mem.KeepsFrozen m1 := Memory.keepsFrozen_mapFresh s0.mem q new Perm.rw
    have hkf2 : m1.KeepsFrozen (m1.writeBytes q copied) :=
      keepsFrozen_writeBytes_of_memRegion copied (by omega) hm1
    have hm2 := satisfies_writeBytes copied (by omega) hm1
    rw [hcopied_len] at hm2
    refine ⟨hkf1.trans hkf2, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [rustReallocSpec]
    simp only [A₀, emp_sepConj, readReg64_setPC_writeReg64_x0,
      hq_ne, ↓reduceIte, sepConj_assoc]
    change m1.writeBytes q copied ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜q.toNat % align = 0 ∧ s0.trace = s0.trace⌝ ∗
          ((q ↦ₛ bs) ∗
            (memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)))
    rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hq_al, rfl⟩, ?_⟩
    rw [show copied = bs ++ extra from hcopy_eq, pointsToBytes_append, sepConj_assoc] at hm2
    have hm2_ent : m1.writeBytes q (bs ++ extra) ⊨
        (q ↦ₛ bs) ∗
          (memRegion (q + BitVec.ofNat 64 bs.length) extra.length ∗
            (memRegion (q + BitVec.ofNat 64 c) (new - c) ∗
              ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
                (stackAt s0.sp allocHookStack ∗ R))))) := by
      refine Satisfies.mono (sepConj_mono_right (sepConj_mono_left ?_)) hm2
      exact pointsToBytes_entails_memRegion (q + BitVec.ofNat 64 bs.length) extra
    rw [hextra_len, ← sepConj_assoc (memRegion (q + BitVec.ofNat 64 bs.length) (c - bs.length))] at hm2_ent
    have haddr_c : q + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (c - bs.length) =
        q + BitVec.ofNat 64 c := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hbs_le_c]
    have hmerge :
        (memRegion (q + BitVec.ofNat 64 bs.length) (c - bs.length) ∗
          memRegion (q + BitVec.ofNat 64 c) (new - c)) =
        memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) := by
      have hlen_eq : c - bs.length + (new - c) = new - bs.length := by omega
      rw [← haddr_c, ← memRegion_split (q + BitVec.ofNat 64 bs.length) (c - bs.length) (new - c) (by omega), hlen_eq]
    rw [hmerge] at hm2_ent
    have hrearr1 :
        ((q ↦ₛ bs) ∗
          (memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
            ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
              (stackAt s0.sp allocHookStack ∗ R))))) =
        (((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)) ∗
          (stackAt s0.sp allocHookStack ∗
            ((q ↦ₛ bs) ∗ (memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)))) := by
      ac_rfl
    rw [hrearr1] at hm2_ent
    rw [← show copied = bs ++ extra from hcopy_eq] at hm2_ent
    exact Satisfies.of_sep_right hm2_ent
  · rename_i hnroom
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    have hzero : (0#64 : BitVec 64) = 0 := rfl
    dsimp only [rustReallocSpec]
    simp only [A₀, emp_sepConj, readReg64_setPC_writeReg64_x0,
      hzero, ↓reduceIte, sepConj_assoc]
    change s0.mem ⊨
      stackAt s0.sp allocHookStack ∗
        (⌜s0.trace ++ [allocFailedEvent] = s0.trace ++ [allocFailedEvent]⌝ ∗
          ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R)))
    rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    have hrearr :
        (stackAt s0.sp allocHookStack ∗
          ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R))) =
        ((p ↦ₛ bs) ∗ (memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          (stackAt s0.sp allocHookStack ∗ R))) := by
      ac_rfl
    rw [hrearr]
    exact hmem

theorem witnessHooks_allocHooks : AllocHooks A₀ witnessHooks := by
  refine ⟨⟨witnessAllocHook, rfl, witnessAllocHook_ok⟩,
    ⟨witnessDeallocHook, rfl, witnessDeallocHook_ok⟩,
    ⟨witnessReallocHook, rfl, witnessReallocHook_ok⟩⟩

theorem witnessHooks_succeedsWithRoom : AllocSucceedsWithRoom A₀ witnessHooks := by
  refine ⟨?_, ?_⟩
  · intro f hf size align R s _hrun _hsp hpre hroom
    simp only [witnessHooks, ↓reduceIte, Option.some.injEq] at hf
    subst hf
    simp only [rustAllocSpec, A₀, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, _⟩, _⟩
    have hroom' : HasRoom s.mem (s.readReg64 .x0).toNat (s.readReg64 .x1).toNat := by
      rw [hx0, hx1]; exact hroom
    simp only [witnessAllocHook, retHook, allocBody, hroom', ↓reduceDIte,
      readReg64_setPC_writeReg64_x0]
    exact (Classical.choose_spec hroom').1
  · intro f hf p old align new bs R s _hrun _hsp hpre hroom
    simp only [witnessHooks] at hf
    have hf' : witnessReallocHook = f := by
      simpa using hf
    subst hf'
    simp only [rustReallocSpec, A₀, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, _, hx2, hx3, _⟩, _⟩
    have hroom' : HasRoom s.mem (s.readReg64 .x3).toNat (s.readReg64 .x2).toNat := by
      rw [hx2, hx3]; exact hroom
    simp only [witnessReallocHook, retHook, reallocBody, hroom', ↓reduceDIte,
      readReg64_setPC_writeReg64_x0]
    exact (Classical.choose_spec hroom').1

end CryptoVerification.LibsignalSession.NonVacuityWitness
