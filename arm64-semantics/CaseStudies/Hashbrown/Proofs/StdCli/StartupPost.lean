/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StartupLayout
public import CaseStudies.Hashbrown.Proofs.StdCli.StartupPre
public import CaseStudies.Hashbrown.Proofs.StdCli.StdoutFlush
public import CaseStudies.Hashbrown.Proofs.StdCli.Shims
public import ProofLib.StdStartup.CleanupAndExit
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WP.StepsProcessSyscalls
import CaseStudies.Hashbrown.Proofs.StdCli.StdoutInit
import ProofLib.BV

/-!
# Placement-Generic Post-`userMain` Teardown and `exit_group`

Verifies the placement-generic post-`userMain` teardown path parameterized by
`HbCliLayout` and `HbStartupLayout`, covering `<futex::Once>::call`, `cleanupClosure`,
`LineWriter` flush and deallocation, `drop_handler` alternate signal stack unmapping,
and `musl` `exit` to `exit_group`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

/-! ## Auxiliary-vector `AT_MINSIGSTKSZ` lookup and altstack size -/

/-- First-match `AT_*` tag lookup over an `auxv` entry list (`0#64` if absent, matching `musl`
    `__getauxval`). -/
def hbAuxvLookup (entries : List (BitVec 64 × BitVec 64)) (tag : BitVec 64) : BitVec 64 :=
  match entries.find? (·.1 == tag) with
  | some (_, v) => v
  | none => 0#64

/-- Exact signal-altstack RW payload byte size computed by both `make_handler` and `drop_handler`:
    `max(0x3000, getauxval(AT_MINSIGSTKSZ = 51))`. -/
def hbAltstackRawSz (entries : List (BitVec 64 × BitVec 64)) : Nat :=
  max 12288 (hbAuxvLookup entries 51#64).toNat

theorem hbAltstackRawSz_eq_csel (entries : List (BitVec 64 × BitVec 64)) :
    (if BitVec.ult 0x3000#64 (hbAuxvLookup entries 51#64)
     then hbAuxvLookup entries 51#64
     else 0x3000#64).toNat = hbAltstackRawSz entries := by
  unfold hbAltstackRawSz
  split
  · next h =>
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at h
    omega
  · next h =>
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at h
    change 12288 = max 12288 (hbAuxvLookup entries 51#64).toNat
    omega

theorem hbAltstackRawSz_eq_reqSz (entries : List (BitVec 64 × BitVec 64)) :
    hbAltstackRawSz entries = hbAltstackReqSz entries := by
  unfold hbAltstackRawSz hbAltstackReqSz hbAuxvLookup
  cases entries.find? (·.1 == 51#64) with
  | none => decide
  | some kv => simp only [Option.map_some, Option.getD_some]; omega

theorem hbPageAlignUp_add_4096 (n : Nat) :
    Arm64.pageAlignUp (n + 4096) = 4096 + Arm64.pageAlignUp n := by
  unfold Arm64.pageAlignUp Arm64.PAGE_SIZE
  omega

/-! ## Frame preservation across altstack `Memory.unmapNonFrozen` -/

/-- An RW separation-logic assertion `P` (free of `memMapped` tokens and ghost state) survives
    unmapping `[uBase, uBase + 4096 + uRwSz)` whenever separated in `m` from
    `memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz`. -/
def RwSurvivesUnmap (uBase : BitVec 64) (uRwSz : Nat) (P : SepProp) : Prop :=
  ∀ {m : Memory} {R : SepProp},
    uBase.toNat + 4096 + uRwSz ≤ 2 ^ 64 →
    (m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ P ∗ R) →
    SupportedOn 0#64 (fun k => OwnsRW P (BitVec.ofNat 64 k))
      (m.unmapNonFrozen uBase (4096 + uRwSz)) P

theorem rwSurvivesUnmap_congr {uBase : BitVec 64} {uRwSz : Nat} {P Q : SepProp}
    (heq : P = Q) (hP : RwSurvivesUnmap uBase uRwSz P) : RwSurvivesUnmap uBase uRwSz Q :=
  heq ▸ hP

private theorem not_inUnmap_of_disj {uBase a : BitVec 64} {uRwSz : Nat} {m : Memory} {Q : SepProp}
    (hbnd : uBase.toNat + 4096 + uRwSz ≤ 2 ^ 64)
    (hm : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ Q)
    (hpn : m.perm a ≠ some .protNone) (hQ : OwnsRW Q a ∨ OwnsRO Q a) :
    ¬ ((a - uBase).toNat < 4096 + uRwSz) := by
  intro hin
  by_cases h4 : (a - uBase).toNat < 4096
  · exact hpn ((IsBlockProtNone.memRegionProtNone uBase 4096).perm_protNone hm h4)
  · have hin_rw : InRegion (uBase + 4096#64) uRwSz a := by
      unfold InRegion
      have hle : 4096#64 ≤ a - uBase := by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega
      rw [show a - (uBase + 4096#64) = (a - uBase) - 4096#64 by bv_omega,
          BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat]; omega
    have hm_rw : m ⊨ memRegion (uBase + 4096#64) uRwSz ∗ (Q ∗ memRegionProtNone uBase 4096) :=
      Satisfies.mono (by sep_entail) hm
    rw [memRegion_eq_exists_bytes (uBase + 4096#64) uRwSz (by omega),
        sepExists_sepConj_left, satisfies_sepExists] at hm_rw
    obtain ⟨bs, hm_bs⟩ := hm_rw
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_bs
    have hm_q : m ⊨ (Q ∗ memRegionProtNone uBase 4096) ∗ ((uBase + 4096#64) ↦ₛ bs) :=
      Satisfies.mono (by sep_entail) hm_bs.2
    have hown_bs := ownsRW_pointsToBytes_at (by omega) (hm_bs.1 ▸ hin_rw)
    exact hQ.elim (fun hw => not_satisfies_ownsRW_ownsRW (ownsRW_sepConj_left hw) hown_bs hm_q)
      (fun hr => not_satisfies_ownsRO_ownsRW (ownsRO_sepConj_left hr) hown_bs hm_q)

theorem rwSurvivesUnmap_emp (uBase : BitVec 64) (uRwSz : Nat) :
    RwSurvivesUnmap uBase uRwSz emp := fun {m _} _ _ => by
  have hsat : m.unmapNonFrozen uBase (4096 + uRwSz) ⊨ (0#64 ↦ₛ []) := by rw [pointsToBytes_nil]; exact satisfies_emp _
  simpa only [pointsToBytes_nil] using SupportedOn.of_pointsToBytes (b := 0#64)
    (S := fun k => OwnsRW emp (BitVec.ofNat 64 k)) hsat fun _ hx => nomatch hx

theorem rwSurvivesUnmap_pointsTo8 (uBase a : BitVec 64) (uRwSz : Nat) (v : BitVec 8) :
    RwSurvivesUnmap uBase uRwSz (a ↦₈ v) := by
  intro m R hbnd hm
  have hm_a : m ⊨ (a ↦₈ v) ∗ (memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ R) :=
    Satisfies.mono (by sep_entail) hm
  have hrd : m.read8 a = v := (IsBlock.pointsTo8 a v).read hm_a
  have hperm_rw : m.perm a = some .rw ∧ m.isLazyFree a = false :=
    Memory.permNoLazy_eq_some_rw_iff.mp ((IsBlock.pointsTo8 a v).permNoLazy_rw hm_a (by simp [InRegion]))
  have hout := not_inUnmap_of_disj hbnd hm (by rw [hperm_rw.1]; decide)
    (.inl (ownsRW_sepConj_left (ownsRW_pointsTo8 a v)))
  have hhb : Obj.HoldsBytes (m.unmapNonFrozen uBase (4096 + uRwSz)) a [v] (fun _ => .rw) := fun i hi => by
    obtain rfl : i = 0 := by simpa using hi
    simp only [BitVec.add_zero, List.getElem_cons_zero, Memory.read8_unmapNonFrozen,
      Memory.perm_unmapNonFrozen, Memory.isLazyFree_unmapNonFrozen, decide_eq_false hout,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hrd, hperm_rw.1, hperm_rw.2⟩
  have hsat1 := Satisfies.pointsToBytes_of_holdsBytes_rw (by have := a.isLt; simp; omega) hhb
  simpa only [pointsToBytes_singleton] using SupportedOn.of_pointsToBytes (b := 0#64)
    (S := fun k => OwnsRW (a ↦₈ v) (BitVec.ofNat 64 k)) hsat1 fun x hx => by
      obtain rfl : x = a := by
        unfold InRegion at hx; simp at hx
        have hz : x - a = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx); bv_omega
      rw [BitVec.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact ownsRW_pointsTo8 x v

theorem rwSurvivesUnmap_sepConj {uBase : BitVec 64} {uRwSz : Nat} {P Q : SepProp}
    (hP : RwSurvivesUnmap uBase uRwSz P) (hQ : RwSurvivesUnmap uBase uRwSz Q) :
    RwSurvivesUnmap uBase uRwSz (P ∗ Q) := fun {m R} hbnd hm => by
  have hmP : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ P ∗ (Q ∗ R) := Satisfies.mono (by sep_entail) hm
  have hmQ : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ Q ∗ (P ∗ R) := Satisfies.mono (by sep_entail) hm
  have hmPQ : m ⊨ P ∗ (Q ∗ (memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ R)) := Satisfies.mono (by sep_entail) hm
  exact (SupportedOn.sepConj (hP hbnd hmP) (hQ hbnd hmQ) fun _ hkP hkQ =>
    not_satisfies_ownsRW_ownsRW hkP (ownsRW_sepConj_left hkQ) hmPQ).widen
    fun _ hk => hk.elim ownsRW_sepConj_left ownsRW_sepConj_right

theorem rwSurvivesUnmap_pointsToBytes (uBase : BitVec 64) (uRwSz : Nat) :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64), RwSurvivesUnmap uBase uRwSz (a ↦ₛ bs)
  | [], a => rwSurvivesUnmap_congr (pointsToBytes_nil a).symm (rwSurvivesUnmap_emp uBase uRwSz)
  | v :: rest, a => rwSurvivesUnmap_congr (pointsToBytes_cons a v rest).symm
      (rwSurvivesUnmap_sepConj (rwSurvivesUnmap_pointsTo8 uBase a uRwSz v)
        (rwSurvivesUnmap_pointsToBytes uBase uRwSz rest (a + 1#64)))

theorem rwSurvivesUnmap_pointsTo32 (uBase a : BitVec 64) (uRwSz : Nat) (v : BitVec 32) :
    RwSurvivesUnmap uBase uRwSz (a ↦₃₂ v) :=
  rwSurvivesUnmap_congr (pointsTo32_eq_pointsToBytes a v).symm (rwSurvivesUnmap_pointsToBytes uBase uRwSz _ a)

theorem rwSurvivesUnmap_pointsTo64 (uBase a : BitVec 64) (uRwSz : Nat) (v : BitVec 64) :
    RwSurvivesUnmap uBase uRwSz (a ↦₆₄ v) :=
  rwSurvivesUnmap_congr (pointsTo64_eq_pointsToBytes a v).symm (rwSurvivesUnmap_pointsToBytes uBase uRwSz _ a)

theorem rwSurvivesUnmap_memRegion (uBase a : BitVec 64) (uRwSz n : Nat)
    (hn : n ≤ 2 ^ 64 := by decide) : RwSurvivesUnmap uBase uRwSz (memRegion a n) := by
  intro m R hbnd hm
  have hm_mr : m ⊨ memRegion a n ∗ (memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ R) :=
    Satisfies.mono (by sep_entail) hm
  rw [memRegion_eq_exists_bytes a n hn, sepExists_sepConj_left, satisfies_sepExists] at hm_mr
  obtain ⟨bs, hm_bs⟩ := hm_mr; rw [sepConj_assoc, satisfies_pure_sepConj] at hm_bs; obtain ⟨hlen, hm_bs⟩ := hm_bs
  have hm_bs' : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ (a ↦ₛ bs) ∗ R := Satisfies.mono (by sep_entail) hm_bs
  have hsat_bs := (rwSurvivesUnmap_pointsToBytes uBase uRwSz bs a hbnd hm_bs').satisfies
  exact SupportedOn.mono (hlen ▸ pointsToBytes_entails_memRegion a bs)
    (SupportedOn.of_pointsToBytes (b := 0#64) (S := fun k => OwnsRW (memRegion a n) (BitVec.ofNat 64 k)) hsat_bs
      fun x hx => by rw [BitVec.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact ownsRW_memRegion a n x (hlen ▸ hx))

theorem rwSurvivesUnmap_stackAt (uBase sp : BitVec 64) (uRwSz sz : Nat)
    (hsz : sz ≤ 2 ^ 64 := by decide) :
    RwSurvivesUnmap uBase uRwSz (stackAt sp sz) :=
  rwSurvivesUnmap_memRegion uBase (sp - BitVec.ofNat 64 sz) uRwSz sz hsz

theorem rwSurvivesUnmap_exists64 (uBase a : BitVec 64) (uRwSz : Nat) :
    RwSurvivesUnmap uBase uRwSz (∃∗ v : BitVec 64, a ↦₆₄ v) := by
  intro m R hbnd hm
  have hm_ex : m ⊨ (∃∗ v : BitVec 64, a ↦₆₄ v) ∗
      (memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ R) :=
    Satisfies.mono (by sep_entail) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  obtain ⟨v, hm_v⟩ := hm_ex
  have hm_v' : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ (a ↦₆₄ v) ∗ R :=
    Satisfies.mono (by sep_entail) hm_v
  have hsat_bs : m.unmapNonFrozen uBase (4096 + uRwSz) ⊨ (a ↦ₛ unpack64 v) := by
    rw [← pointsTo64_eq_pointsToBytes]
    exact (rwSurvivesUnmap_pointsTo64 uBase a uRwSz v hbnd hm_v').satisfies
  have hs2 := SupportedOn.of_pointsToBytes (b := 0#64)
    (S := fun k => OwnsRW (∃∗ w : BitVec 64, a ↦₆₄ w) (BitVec.ofNat 64 k)) hsat_bs fun x hx => by
      rw [BitVec.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      refine OwnsRW.sepExists fun w => ?_
      rw [pointsTo64_eq_pointsToBytes]
      exact ownsRW_pointsToBytes_at (by simp) (by simpa using hx)
  rw [← pointsTo64_eq_pointsToBytes] at hs2
  exact SupportedOn.mono (Entails.sepExists_right v (Entails.refl _)) hs2

private theorem ro8_outside_unmap {uBase a : BitVec 64} {uRwSz : Nat} {v : BitVec 8}
    {m : Memory} {R : SepProp} (hbnd : uBase.toNat + 4096 + uRwSz ≤ 2 ^ 64)
    (hm : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ (a ↦₈ᵣ v) ∗ R) :
    ¬ ((a - uBase).toNat < 4096 + uRwSz) ∧ (m.unmapNonFrozen uBase (4096 + uRwSz)).read8 a = v ∧
      ((m.unmapNonFrozen uBase (4096 + uRwSz)).perm a).r = true ∧
      (m.unmapNonFrozen uBase (4096 + uRwSz)).isLazyFree a = false := by
  have hm_ro : m ⊨ (a ↦₈ᵣ v) ∗ (memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ R) :=
    Satisfies.mono (by sep_entail) hm
  have hrd : m.read8 a = v := (IsBlockRO.pointsTo8RO a v).read hm_ro
  have hpr : (m.perm a).r = true := (IsBlockRO.pointsTo8RO a v).perm_r hm_ro (by simp [InRegion])
  have hlf : m.isLazyFree a = false := (IsBlockRO.pointsTo8RO a v).isLazyFree_false hm_ro (by simp [InRegion])
  have hout := not_inUnmap_of_disj hbnd hm (fun hp => by rw [hp] at hpr; cases hpr)
    (.inr (ownsRO_sepConj_left (ownsRO_pointsTo8RO a v)))
  refine ⟨hout, ?_, ?_, ?_⟩
  · rw [Memory.read8_unmapNonFrozen]; simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hrd]
  · rw [Memory.perm_unmapNonFrozen]; simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hpr]
  · rw [Memory.isLazyFree_unmapNonFrozen]; simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlf]

def RoPostFacts (C : HbCliLayout) (haveLse : BitVec 8) (m : Memory) : Prop :=
  m.read8 C.std.haveLseAtomicsAddr = haveLse ∧ m.canRead C.std.haveLseAtomicsAddr 1 = true ∧
  m.read64 C.globalPanicCountAddr = 0#64 ∧ m.canRead C.globalPanicCountAddr 8 = true

def RoSafe (C : HbCliLayout) (Keep : SepProp) : Prop :=
  ∀ x, OwnsRW Keep x → x ≠ C.std.haveLseAtomicsAddr ∧ ¬ InRegion C.globalPanicCountAddr 8 x

private theorem ownsRO_pointsToBytesRO_at
    (bs : List (BitVec 8)) (a x : BitVec 64) (hx : InRegion a bs.length x) : OwnsRO (a ↦ᵣ bs) x := by
  induction bs generalizing a with
  | nil => simp [InRegion] at hx
  | cons b bs ih =>
    rw [pointsToBytesRO_cons]
    by_cases hxa : x = a
    · subst hxa; exact ownsRO_sepConj_left (ownsRO_pointsTo8RO x b)
    · refine ownsRO_sepConj_right (ih (a + 1#64) ?_)
      unfold InRegion at hx ⊢
      have hne : (x - a).toNat ≠ 0 := fun h0 => hxa (by
        have hz : x - a = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0); bv_omega)
      have hle : 1#64 ≤ x - a := by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega
      rw [show x - (a + 1#64) = (x - a) - 1#64 by bv_omega, BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat]
      simp only [List.length_cons] at hx; omega

private theorem ownsRO_pointsTo64RO_at (a v x : BitVec 64) (hx : InRegion a 8 x) : OwnsRO (a ↦₆₄ᵣ v) x := by
  rw [pointsTo64RO_eq_pointsToBytesRO]; exact ownsRO_pointsToBytesRO_at (unpack64 v) a x (by rwa [unpack64_length])

theorem roSafe_of_pre {C : HbCliLayout} {haveLse : BitVec 8} {Keep R : SepProp} {m : Memory}
    (hm : m ⊨ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ Keep ∗ R) :
    RoSafe C Keep := fun x hown => by
  have hm1 : m ⊨ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (Keep ∗ ((C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ R)) := Satisfies.mono (by sep_entail) hm
  have hm2 : m ⊨ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ (Keep ∗ ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ R)) := Satisfies.mono (by sep_entail) hm
  exact ⟨fun hxeq => by subst hxeq; exact not_satisfies_ownsRO_ownsRW (ownsRO_pointsTo8RO _ haveLse) (ownsRW_sepConj_left hown) hm1,
         fun hin => not_satisfies_ownsRO_ownsRW (ownsRO_pointsTo64RO_at _ _ x hin) (ownsRW_sepConj_left hown) hm2⟩

theorem roPostFacts_of_unmap {C : HbCliLayout} {uBase : BitVec 64} {uRwSz : Nat}
    {haveLse : BitVec 8} {m : Memory} {R : SepProp}
    (hbnd : uBase.toNat + 4096 + uRwSz ≤ 2 ^ 64)
    (hm : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ R) :
    RoPostFacts C haveLse (m.unmapNonFrozen uBase (4096 + uRwSz)) := by
  let m' := m.unmapNonFrozen uBase (4096 + uRwSz)
  have hm_lse : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ ((C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ R) := Satisfies.mono (by sep_entail) hm
  obtain ⟨_, hlse_rd, hlse_pr, hlse_lf⟩ := ro8_outside_unmap hbnd hm_lse
  have hm_pc : m ⊨ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ (memRegionProtNone uBase 4096 ∗
      memRegion (uBase + 4096#64) uRwSz ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ R) :=
    Satisfies.mono (by sep_entail) hm
  have hpc_rd0 := (IsBlockRO.pointsTo64RO C.globalPanicCountAddr 0#64).read hm_pc
  have hm_pc' : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗
      (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ R) :=
    Satisfies.mono (by sep_entail) hm
  have hbyte : ∀ i < 8, let ai := C.globalPanicCountAddr + BitVec.ofNat 64 i
      m'.read8 ai = m.read8 ai ∧ (m'.perm ai).r = true ∧ m'.isLazyFree ai = false := fun i hi => by
    intro ai
    have hin : InRegion C.globalPanicCountAddr 8 ai := by
      unfold InRegion
      rw [show ai - C.globalPanicCountAddr = BitVec.ofNat 64 i by dsimp [ai]; bv_omega,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
    have hpr := (IsBlockRO.pointsTo64RO _ _).perm_r hm_pc hin
    have hlf := (IsBlockRO.pointsTo64RO _ _).isLazyFree_false hm_pc hin
    have hout := not_inUnmap_of_disj hbnd hm_pc' (fun hp => by rw [hp] at hpr; cases hpr)
      (.inr (ownsRO_sepConj_left (ownsRO_pointsTo64RO_at _ _ ai hin)))
    refine ⟨?_, ?_, ?_⟩ <;> dsimp [m']
    · rw [Memory.read8_unmapNonFrozen]; simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · rw [Memory.perm_unmapNonFrozen]; simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hpr]
    · rw [Memory.isLazyFree_unmapNonFrozen]; simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlf]
  have h0 := hbyte 0 (by omega); have h1 := hbyte 1 (by omega); have h2 := hbyte 2 (by omega); have h3 := hbyte 3 (by omega)
  have h4 := hbyte 4 (by omega); have h5 := hbyte 5 (by omega); have h6 := hbyte 6 (by omega); have h7 := hbyte 7 (by omega)
  dsimp only at h0 h1 h2 h3 h4 h5 h6 h7
  have h0z : (m'.perm C.globalPanicCountAddr).r = true ∧ m'.isLazyFree C.globalPanicCountAddr = false := by simpa using h0.2
  refine ⟨hlse_rd, ?_, ?_, ?_⟩
  · dsimp only [m', Memory.canRead, Memory.allPerm, Memory.allNoLazyFree]; rw [hlse_pr, hlse_lf]; rfl
  · rw [← hpc_rd0]; dsimp only [Memory.read64]; rw [h0.1, h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1]
  · dsimp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [h0z.1, h0z.2, h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2, h5.2.1, h5.2.2, h6.2.1, h6.2.2, h7.2.1, h7.2.2]; rfl

private theorem write8_cells_ne (m : Memory) (ea x : BitVec 64) (v : BitVec 8) (hne : x ≠ ea) :
    (m.write8 ea v).read8 x = m.read8 x ∧ (m.write8 ea v).perm x = m.perm x ∧ (m.write8 ea v).isLazyFree x = m.isLazyFree x := by
  simp [Memory.write8, Memory.read8, Memory.perm, Memory.rawPerm, Memory.isLazyFree, hne]

private theorem roPostFacts_write8 {C : HbCliLayout} {haveLse v : BitVec 8} {ea : BitVec 64} {m : Memory}
    (hdisj : ea ≠ C.std.haveLseAtomicsAddr ∧ ¬ InRegion C.globalPanicCountAddr 8 ea)
    (hro : RoPostFacts C haveLse m) : RoPostFacts C haveLse (m.write8 ea v) := by
  obtain ⟨hr1, hc1, hr8, hc8⟩ := hro
  have hlse := write8_cells_ne m ea C.std.haveLseAtomicsAddr v hdisj.1.symm
  have hne_i : ∀ i < 8, C.globalPanicCountAddr + BitVec.ofNat 64 i ≠ ea := fun i hi heq =>
    hdisj.2 (by unfold InRegion; rw [← heq, show C.globalPanicCountAddr + BitVec.ofNat 64 i - C.globalPanicCountAddr =
      BitVec.ofNat 64 i by bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)
  have b0 := write8_cells_ne m ea _ v (hne_i 0 (by omega)); have b1 := write8_cells_ne m ea _ v (hne_i 1 (by omega))
  have b2 := write8_cells_ne m ea _ v (hne_i 2 (by omega)); have b3 := write8_cells_ne m ea _ v (hne_i 3 (by omega))
  have b4 := write8_cells_ne m ea _ v (hne_i 4 (by omega)); have b5 := write8_cells_ne m ea _ v (hne_i 5 (by omega))
  have b6 := write8_cells_ne m ea _ v (hne_i 6 (by omega)); have b7 := write8_cells_ne m ea _ v (hne_i 7 (by omega))
  have b0z : (m.write8 ea v).perm C.globalPanicCountAddr = m.perm C.globalPanicCountAddr ∧
      (m.write8 ea v).isLazyFree C.globalPanicCountAddr = m.isLazyFree C.globalPanicCountAddr := by simpa using b0.2
  refine ⟨hlse.1.trans hr1, ?_, ?_, ?_⟩
  · dsimp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree] at hc1 ⊢; rwa [hlse.2.1, hlse.2.2]
  · rw [← hr8]; dsimp only [Memory.read64]; rw [b0.1, b1.1, b2.1, b3.1, b4.1, b5.1, b6.1, b7.1]
  · dsimp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree] at hc8 ⊢; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hc8 ⊢
    rwa [b0z.1, b0z.2, b1.2.1, b1.2.2, b2.2.1, b2.2.2, b3.2.1, b3.2.2, b4.2.1, b4.2.2, b5.2.1, b5.2.2, b6.2.1, b6.2.2, b7.2.1, b7.2.2]

private theorem inRegion_off (a : BitVec 64) {n i : Nat} (hi : i < n) (hn : n ≤ 8) :
    InRegion a n (a + BitVec.ofNat 64 i) := by
  unfold InRegion
  rw [show a + BitVec.ofNat 64 i - a = BitVec.ofNat 64 i by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi

private theorem roPostFacts_write32 {C : HbCliLayout} {haveLse : BitVec 8} {v : BitVec 32}
    {ea : BitVec 64} {m : Memory}
    (hd : ∀ x, InRegion ea 4 x → x ≠ C.std.haveLseAtomicsAddr ∧ ¬ InRegion C.globalPanicCountAddr 8 x)
    (hro : RoPostFacts C haveLse m) :
    RoPostFacts C haveLse (m.write32 ea v) :=
  roPostFacts_write8 (hd _ (inRegion_off ea (i := 3) (by omega) (by omega)))
    (roPostFacts_write8 (hd _ (inRegion_off ea (i := 2) (by omega) (by omega)))
      (roPostFacts_write8 (hd _ (inRegion_off ea (i := 1) (by omega) (by omega)))
        (roPostFacts_write8 (hd _ (inRegion_off ea (i := 0) (by omega) (by omega))) hro)))

theorem roPostFacts_write64 {C : HbCliLayout} {haveLse : BitVec 8} {v : BitVec 64}
    {ea : BitVec 64} {m : Memory}
    (hd : ∀ x, InRegion ea 8 x → x ≠ C.std.haveLseAtomicsAddr ∧ ¬ InRegion C.globalPanicCountAddr 8 x)
    (hro : RoPostFacts C haveLse m) :
    RoPostFacts C haveLse (m.write64 ea v) :=
  roPostFacts_write8 (hd _ (inRegion_off ea (i := 7) (by omega) (by omega)))
    (roPostFacts_write8 (hd _ (inRegion_off ea (i := 6) (by omega) (by omega)))
      (roPostFacts_write8 (hd _ (inRegion_off ea (i := 5) (by omega) (by omega)))
        (roPostFacts_write8 (hd _ (inRegion_off ea (i := 4) (by omega) (by omega)))
          (roPostFacts_write8 (hd _ (inRegion_off ea (i := 3) (by omega) (by omega)))
            (roPostFacts_write8 (hd _ (inRegion_off ea (i := 2) (by omega) (by omega)))
              (roPostFacts_write8 (hd _ (inRegion_off ea (i := 1) (by omega) (by omega)))
                (roPostFacts_write8 (hd _ (inRegion_off ea (i := 0) (by omega) (by omega))) hro)))))))

/-! ## Symbolic teardown code bundle and `WordTree` validator -/

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd (($t) - ($pc)))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .X64 $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdr32Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W32 .W32 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr32Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .W32 $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdr8Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W32 .B8 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr8Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .B8 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term =>
  `(Instr.bl (($t) - ($pc)))
local macro "iB " pc:term:arg t:term:arg : term =>
  `(Instr.b (($t) - ($pc)))

/-- 11 executed words of `stdoutCleanupClosure` (`L.stdoutCleanupClosureAddr + 0x00 .. + 0x28`),
    omitting the unexecuted cold `unwrap_failed` prologue word at `+ 0x2c`. -/
def hbStdoutCleanupClosureWords : List (BitVec 32) :=
  [ 0xf940000a#32, 0xa9402149#32, 0xf900015f#32, 0xb4000109#32,
    0x6f00e400#32, 0x5280002a#32, 0x3900012a#32, 0xa9027d0a#32,
    0x3900c11f#32, 0xad000100#32, 0xd65f03c0#32 ]

def hbLangStartPostChunks (C : HbCliLayout) : List CodeChunk :=
  let L := C.std; let ls := C.langStartInternalAddr
  [ .words L.beginShortBacktraceAddr beginShortBacktraceWords,
    .words (C.langStartClosureAddr + 0x10#64) [0x12001c00#32, 0xa8c17bfd#32, 0xd65f03c0#32],
    .words (ls + 0x394#64) [0x93407c13#32, 0xd503201f#32],
    .instrs ls 0x39c [iAdr .x8 (ls + 0x39c#64) L.cleanupOnceAddr],
    .words (ls + 0x3a0#64) [0x88dffd08#32, 0x35000c68#32],
    .instrs ls 0x3a8 [iBl (ls + 0x3a8#64) L.errnoLocationAddr],
    .words (ls + 0x3ac#64) [0xaa0003f4#32],
    .instrs ls 0x3b0 [iAdrp .x2 (ls + 0x3b0#64) L.exitingThreadIdAddr, iAddLo12 .x2 .x2 L.exitingThreadIdAddr],
    .words (ls + 0x3b8#64) [0xaa1f03e0#32, 0xaa1403e1#32],
    .instrs ls 0x3c0 [iBl (ls + 0x3c0#64) L.cas8AcqAddr],
    .words (ls + 0x3c4#64) [0xf100001f#32, 0x54000141#32, 0xaa1303e0#32, 0xa94f4ff4#32, 0xa94e57f6#32,
      0xa94d5ff8#32, 0xa94c67fa#32, 0xa94b6ffc#32, 0xa94a7bfd#32, 0x910403ff#32, 0xd65f03c0#32],
    .words (ls + 0x530#64) [0x52800028#32, 0xd10013a9#32, 0x381fc3a8#32, 0xf90003e9#32, 0xd503201f#32],
    .instrs ls 0x544 [iAdr .x0 (ls + 0x544#64) L.cleanupOnceAddr],
    .words (ls + 0x548#64) [0xd503201f#32],
    .instrs ls 0x54c [iAdr .x3 (ls + 0x54c#64) L.cleanupVtableAddr],
    .words (ls + 0x550#64) [0xd503201f#32],
    .words (ls + 0x558#64) [0x910003e2#32, 0x2a1f03e1#32],
    .instrs ls 0x560 [iBl (ls + 0x560#64) L.onceCallAddr, iB (ls + 0x564#64) (ls + 0x3a8#64)],
    .words (L.cMainAddr + 0x34#64) [0xa9417bfd#32, 0x910083ff#32, 0xd65f03c0#32] ]

def hbStdoutOnceLockPostChunks (C : HbCliLayout) : List CodeChunk :=
  let L := C.std; let oi := L.stdoutOnceLockInitAddr; let g := L.stdoutGlobalAddr
  [ .instrs0 oi [iAdrp .x8 oi (g + 0x38#64), iAddLo12 .x8 .x8 (g + 0x38#64)],
    .words (oi + 0x08#64) [0x88dffd08#32, 0x35000048#32, 0xd65f03c0#32, 0xd10103ff#32, 0xa9037bfd#32, 0x9100c3fd#32, 0xd503201f#32],
    .instrs oi 0x24 [iAdr .x8 (oi + 0x24#64) g],
    .words (oi + 0x28#64) [0xd10007a9#32, 0xa900a3e0#32, 0xd503201f#32],
    .instrs oi 0x34 [iAdr .x3 (oi + 0x34#64) L.stdoutVtableAddr],
    .words (oi + 0x38#64) [0xf9000fe9#32, 0x910023e9#32],
    .instrs oi 0x40 [iBl (oi + 0x40#64) C.outlinedFn72Addr],
    .words (oi + 0x44#64) [0x9100e100#32, 0xd10043a2#32, 0x52800021#32, 0xf81f03a9#32],
    .instrs oi 0x54 [iBl (oi + 0x54#64) L.onceCallAddr],
    .words (oi + 0x58#64) [0xa9437bfd#32, 0x910103ff#32, 0xd65f03c0#32],
    .words L.stdoutCleanupClosureAddr hbStdoutCleanupClosureWords ] ++
  hbOutlinedFn72Chunks C

def hbCleanupClosurePostChunks (C : HbCliLayout) : List CodeChunk :=
  let L := C.std; let cc := L.cleanupClosureAddr; let g := L.stdoutGlobalAddr
  [ .words cc [0xd10183ff#32, 0xa9027bfd#32, 0xf9001bf7#32, 0xa90457f6#32, 0xa9054ff4#32, 0x910083fd#32,
      0xf9400008#32, 0x39400109#32, 0x3900011f#32, 0x7100053f#32, 0x54000c21#32, 0x390073bf#32],
    .instrs cc 0x30 [iAdrp .x8 (cc + 0x30#64) (g + 0x38#64), iAddLo12 .x8 .x8 (g + 0x38#64)],
    .words (cc + 0x38#64) [0x88dffd08#32, 0x35000be8#32, 0x394073a8#32, 0x37000a08#32, 0xd2a00000#32,
      0xf2800b00#32, 0xd503201f#32, 0xd503201f#32, 0xd53bd057#32, 0xf8606af6#32, 0xb4000176#32],
    .instrs cc 0x64 [iAdrp .x19 (cc + 0x64#64) g, iLdr64Lo12 .x8 .x19 g],
    .words (cc + 0x6c#64) [0xeb0802df#32, 0x54000361#32],
    .instrs cc 0x8c [iAdrp .x8 (cc + 0x8c#64) L.threadIdCounterAddr],
    .words (cc + 0x90#64) [0xaa0003f3#32],
    .instrs cc 0x94 [iAdrp .x20 (cc + 0x94#64) L.threadIdCounterAddr, iAddLo12 .x20 .x20 L.threadIdCounterAddr,
      iLdr64Lo12 .x21 .x8 L.threadIdCounterAddr],
    .words (cc + 0xa0#64) [0xb10006bf#32, 0x54000820#32, 0x910006a1#32, 0xaa1503e0#32, 0xaa1403e2#32, 0x910006b6#32],
    .instrs cc 0xb8 [iBl (cc + 0xb8#64) L.cas8RelaxAddr],
    .words (cc + 0xbc#64) [0xeb15001f#32, 0xaa0003f5#32, 0x54fffee1#32, 0xf8336af6#32],
    .instrs cc 0xcc [iAdrp .x19 (cc + 0xcc#64) g, iLdr64Lo12 .x8 .x19 g],
    .words (cc + 0xd4#64) [0xeb0802df#32, 0x54fffce0#32],
    .instrs cc 0xdc [iAdrp .x2 (cc + 0xdc#64) (g + 0x08#64), iAddLo12 .x2 .x2 (g + 0x08#64)],
    .words (cc + 0xe4#64) [0x2a1f03e0#32, 0x52800021#32],
    .instrs cc 0xec [iBl (cc + 0xec#64) L.cas4AcqAddr],
    .words (cc + 0xf0#64) [0x7100001f#32, 0x54000481#32],
    .instrs cc 0xf8 [iStr64Lo12 .x22 .x19 g],
    .words (cc + 0xfc#64) [0x52800028#32],
    .instrs cc 0x100 [iAdrp .x19 (cc + 0x100#64) (g + 0x0c#64), iAddLo12 .x19 .x19 (g + 0x0c#64)],
    .words (cc + 0x108#64) [0xf9000bff#32, 0xb9000268#32, 0x52800028#32, 0xa90023ff#32, 0xf8404268#32, 0x390063ff#32, 0xb5000568#32],
    .instrs cc 0x124 [iAdrp .x20 (cc + 0x124#64) (g + 0x10#64), iAddLo12 .x20 .x20 (g + 0x10#64)],
    .words (cc + 0x12c#64) [0x92800008#32, 0xaa1403e0#32, 0xf8008408#32],
    .instrs cc 0x138 [iBl (cc + 0x138#64) C.lineWriterDropAddr],
    .words (cc + 0x13c#64) [0xad4007e0#32, 0xf8404268#32, 0xb9400269#32, 0x91000508#32, 0x71000529#32,
      0x3c80c260#32, 0x3c81c261#32, 0xf8004268#32, 0xb9000269#32, 0x54000121#32, 0xd503201f#32],
    .instrs cc 0x168 [iAdr .x8 (cc + 0x168#64) g],
    .words (cc + 0x16c#64) [0x2a1f03e0#32, 0x91002101#32, 0xf900011f#32],
    .instrs cc 0x178 [iBl (cc + 0x178#64) L.swp4RelAddr],
    .words (cc + 0x17c#64) [0x7100081f#32, 0x540002e0#32],
    .instrs cc 0x184 [iAdrp .x8 (cc + 0x184#64) C.mainAltstackAddr, iLdr64Lo12 .x0 .x8 C.mainAltstackAddr,
      iBl (cc + 0x18c#64) C.dropStackHandlerAddr],
    .words (cc + 0x190#64) [0xa9454ff4#32, 0xf9401bf7#32, 0xa94457f6#32, 0xa9427bfd#32, 0x910183ff#32, 0xd65f03c0#32],
    .words (cc + 0x1b8#64) [0x910073a0#32],
    .instrs cc 0x1bc [iBl (cc + 0x1bc#64) L.stdoutOnceLockInitAddr],
    .words (cc + 0x1c0#64) [0x394073a8#32, 0x3607f428#32, 0x17ffffef#32] ]

def hbLineWriterDropChunks (C : HbCliLayout) : List CodeChunk :=
  let lw := C.lineWriterDropAddr
  [ .words lw [0xd100c3ff#32, 0xa9017bfd#32, 0xa9024ff4#32, 0x910043fd#32,
      0x39406008#32, 0xaa0003f3#32, 0x37000208#32, 0xaa1303e0#32],
    .instrs lw 0x20 [iBl (lw + 0x20#64) C.bufWriterFlushBufAddr],
    .words (lw + 0x24#64) [0xb40001a0#32],
    .words (lw + 0x58#64) [0xf9400261#32, 0xb4000081#32, 0xf9400660#32, 0x52800022#32],
    .instrs lw 0x68 [iBl (lw + 0x68#64) C.rustDeallocAddr],
    .words (lw + 0x6c#64) [0xa9424ff4#32, 0xa9417bfd#32, 0x9100c3ff#32, 0xd65f03c0#32] ]

def hbDropHandlerChunks (C : HbCliLayout) (S : HbStartupLayout) : List CodeChunk :=
  let L := C.std; let dh := C.dropStackHandlerAddr
  [ .words dh [0xd103c3ff#32, 0xa90a7bfd#32, 0xa90b67fa#32, 0xa90c5ff8#32, 0xa90d57f6#32,
      0xa90e4ff4#32, 0x910283fd#32, 0xb4000260#32, 0xaa0003f3#32, 0x52800660#32],
    .instrs dh 0x28 [iBl (dh + 0x28#64) L.getauxvalAddr],
    .words (dh + 0x2c#64) [0x52860008#32],
    .instrs dh 0x30 [iAdrp .x9 (dh + 0x30#64) L.pageSizeGlobalAddr],
    .words (dh + 0x34#64) [0xf1400c1f#32],
    .instrs dh 0x38 [iLdr64Lo12 .x20 .x9 L.pageSizeGlobalAddr],
    .words (dh + 0x3c#64) [0x52800049#32, 0x9a888015#32, 0xd10123a0#32, 0xaa1f03e1#32,
      0xf81b83bf#32, 0xb81c03a9#32, 0xf81c83b5#32],
    .instrs dh 0x58 [iBl (dh + 0x58#64) S.sigaltstackAddr],
    .words (dh + 0x5c#64) [0xcb140260#32, 0x8b1402a1#32],
    .instrs dh 0x64 [iBl (dh + 0x64#64) S.munmapWrapperAddr, iBl (dh + 0x68#64) L.errnoLocationAddr,
      iAdrp .x20 (dh + 0x6c#64) S.threadInfoLockAddr, iAddLo12 .x20 .x20 S.threadInfoLockAddr],
    .words (dh + 0x74#64) [0xaa0003f3#32, 0x2a1f03e0#32, 0x52800021#32, 0xaa1403e2#32],
    .instrs dh 0x84 [iBl (dh + 0x84#64) L.cas4AcqAddr],
    .words (dh + 0x88#64) [0x7100001f#32, 0x54001461#32, 0xd503201f#32],
    .instrs dh 0x94 [iAdr .x21 (dh + 0x94#64) C.globalPanicCountAddr],
    .words (dh + 0x98#64) [0xf94002a8#32, 0xf240f91f#32, 0x540014c1#32, 0x2a1f03f6#32, 0x39401298#32,
      0x91002282#32, 0xaa1f03e0#32, 0xaa1303e1#32, 0x390063f6#32, 0x7100031f#32, 0x1a9f07e8#32, 0xa900d3e8#32],
    .instrs dh 0xc8 [iBl (dh + 0xc8#64) L.cas8AcqAddr],
    .words (dh + 0xcc#64) [0xf100001f#32, 0x54000180#32],
    .instrs dh 0x100 [iAdrp .x25 (dh + 0x100#64) S.threadInfoRootAddr,
      iAdrp .x23 (dh + 0x104#64) (S.threadInfoLockAddr + 8#64),
      iAddLo12 .x23 .x23 (S.threadInfoLockAddr + 8#64), iLdr64Lo12 .x8 .x25 S.threadInfoRootAddr],
    .words (dh + 0x110#64) [0xb4000d28#32],
    .words (dh + 0x2b4#64) [0xc89ffeff#32, 0x37000096#32, 0xf94002a8#32, 0xf240f91f#32, 0x540004e1#32],
    .instrs dh 0x2c8 [iAdrp .x1 (dh + 0x2c8#64) S.threadInfoLockAddr, iAddLo12 .x1 .x1 S.threadInfoLockAddr],
    .words (dh + 0x2d0#64) [0x2a1f03e0#32],
    .instrs dh 0x2d4 [iBl (dh + 0x2d4#64) L.swp4RelAddr],
    .words (dh + 0x2d8#64) [0x7100081f#32, 0x54000340#32, 0xa94e4ff4#32, 0xa94d57f6#32,
      0xa94c5ff8#32, 0xa94b67fa#32, 0xa94a7bfd#32, 0x9103c3ff#32, 0xd65f03c0#32] ]

def hbTeardownSysChunks (C : HbCliLayout) (S : HbStartupLayout) : List CodeChunk :=
  let L := C.std
  [ .words L.errnoLocationAddr errnoLocationWords,
    .words L.syscallRetAddr syscallRetNonnegWords,
    .instrs L.syscallRetAddr 0x24 [iBl (L.syscallRetAddr + 0x24#64) L.errnoLocationAddr],
    .words (L.syscallRetAddr + 0x28#64) [0xaa0003e1#32, 0x4b1303f3#32, 0x92800000#32, 0xb9000033#32, 0x17fffff8#32],
    .words S.sigaltstackAddr [0xa9bf7bfd#32, 0x910003fd#32, 0xb4000100#32, 0xb9400802#32, 0x370800a2#32,
      0xf9400804#32, 0xd282ffe3#32, 0xeb03009f#32, 0x540000e9#32, 0x37000182#32, 0xd2801088#32, 0xd4000001#32],
    .instrs S.sigaltstackAddr 0x30 [iBl (S.sigaltstackAddr + 0x30#64) L.syscallRetAddr],
    .words (S.sigaltstackAddr + 0x34#64) [0xa8c17bfd#32, 0xd65f03c0#32],
    .words S.munmapWrapperAddr [0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32, 0xaa0003f4#32, 0xaa0103f3#32],
    .instrs S.munmapWrapperAddr 0x14 [iBl (S.munmapWrapperAddr + 0x14#64) S.vmWaitAddr],
    .words (S.munmapWrapperAddr + 0x18#64) [0xaa1403e0#32, 0xaa1303e1#32, 0xd2801ae8#32, 0xd4000001#32],
    .instrs S.munmapWrapperAddr 0x28 [iBl (S.munmapWrapperAddr + 0x28#64) L.syscallRetAddr],
    .words (S.munmapWrapperAddr + 0x2c#64) [0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32],
    .words S.vmWaitAddr [0xd65f03c0#32] ]

def hbMuslExitChunks (C : HbCliLayout) (S : HbStartupLayout) : List CodeChunk :=
  let L := C.std
  [ .instrs L.libcStartMainStage2Addr 0x38 [iBl (L.libcStartMainStage2Addr + 0x38#64) L.exitAddr],
    .words L.exitAddr [0xa9be7bfd#32, 0x910003fd#32, 0xf9000bf3#32, 0x2a0003f3#32],
    .instrs L.exitAddr 0x10 [iBl (L.exitAddr + 0x10#64) L.dummyExitAddr,
      iBl (L.exitAddr + 0x14#64) L.libcExitFiniAddr, iBl (L.exitAddr + 0x18#64) L.stdioExitNeededAddr],
    .words (L.exitAddr + 0x1c#64) [0x2a1303e0#32],
    .instrs L.exitAddr 0x20 [iBl (L.exitAddr + 0x20#64) L.sysExitAddr],
    .words L.dummyExitAddr [0xd65f03c0#32],
    .words L.libcExitFiniAddr [0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32],
    .instrs L.libcExitFiniAddr 0x0c [iAdrp .x19 (L.libcExitFiniAddr + 0x0c#64) S.gotFiniArrayEndAddr,
      iAdrp .x20 (L.libcExitFiniAddr + 0x10#64) S.gotFiniArrayStartAddr,
      iLdr64Lo12 .x19 .x19 S.gotFiniArrayEndAddr, iLdr64Lo12 .x20 .x20 S.gotFiniArrayStartAddr],
    .words (L.libcExitFiniAddr + 0x1c#64) [0xeb14027f#32, 0x54000089#32, 0xf85f8e60#32,
      0xd63f0000#32, 0x17fffffc#32, 0xa94153f3#32, 0xa8c27bfd#32],
    .instrs L.libcExitFiniAddr 0x38 [iB (L.libcExitFiniAddr + 0x38#64) L.finiFnAddr],
    .instrs0 L.doFiniAddr [iAdrp .x1 L.doFiniAddr L.finalizedAddr, iLdr8Lo12 .x0 .x1 L.finalizedAddr],
    .words (L.doFiniAddr + 0x08#64) [0x35000340#32],
    .instrs L.doFiniAddr 0x0c [iAdrp .x0 (L.doFiniAddr + 0x0c#64) (L.gotAddr + 0x20#64)],
    .words (L.doFiniAddr + 0x10#64) [0x52800022#32],
    .instrs L.doFiniAddr 0x14 [iStr8Lo12 .x2 .x1 L.finalizedAddr, iLdr64Lo12 .x0 .x0 (L.gotAddr + 0x20#64)],
    .words (L.doFiniAddr + 0x1c#64) [0xb40001a0#32],
    .instrs L.doFiniAddr 0x50 [iAdrp .x0 (L.doFiniAddr + 0x50#64) (L.gotAddr + 0x28#64), iLdr64Lo12 .x0 .x0 (L.gotAddr + 0x28#64)],
    .words (L.doFiniAddr + 0x58#64) [0xb40000c0#32],
    .words (L.doFiniAddr + 0x70#64) [0xd65f03c0#32],
    .words L.finiFnAddr [0xa9bf7bfd#32, 0x910003fd#32, 0xa8c17bfd#32, 0xd65f03c0#32],
    .words L.oflLockFnAddr [0xa9bf7bfd#32, 0xd503201f#32],
    .instrs L.oflLockFnAddr 0x08 [iAdr .x0 (L.oflLockFnAddr + 0x08#64) L.oflLockAddr],
    .words (L.oflLockFnAddr + 0x0c#64) [0x910003fd#32],
    .instrs L.oflLockFnAddr 0x10 [iBl (L.oflLockFnAddr + 0x10#64) L.lockFnAddr],
    .words (L.oflLockFnAddr + 0x14#64) [0xa8c17bfd#32, 0xd503201f#32],
    .instrs L.oflLockFnAddr 0x1c [iAdr .x0 (L.oflLockFnAddr + 0x1c#64) L.oflHeadAddr],
    .words (L.oflLockFnAddr + 0x20#64) [0xd65f03c0#32],
    .instrs0 L.lockFnAddr [iAdrp .x3 L.lockFnAddr L.libcAddr, iAddLo12 .x2 .x3 L.libcAddr],
    .words (L.lockFnAddr + 0x08#64) [0xaa0003e4#32, 0x320107e1#32, 0x39400c42#32, 0x13001c42#32, 0x34000402#32],
    .words (L.lockFnAddr + 0x98#64) [0xd65f03c0#32],
    .words L.stdioExitNeededAddr [0xa9be7bfd#32, 0x910003fd#32, 0xf9000bf3#32],
    .instrs L.stdioExitNeededAddr 0x0c [iBl (L.stdioExitNeededAddr + 0x0c#64) L.oflLockFnAddr],
    .words (L.stdioExitNeededAddr + 0x10#64) [0xf9400013#32, 0xaa1303e0#32, 0xb4000093#32],
    .instrs L.stdioExitNeededAddr 0x28 [iAdrp .x0 (L.stdioExitNeededAddr + 0x28#64) L.stdinUsedAddr,
      iLdr64Lo12 .x0 .x0 L.stdinUsedAddr, iBl (L.stdioExitNeededAddr + 0x30#64) L.closeFileAddr,
      iAdrp .x0 (L.stdioExitNeededAddr + 0x34#64) L.stdoutUsedAddr, iLdr64Lo12 .x0 .x0 L.stdoutUsedAddr,
      iBl (L.stdioExitNeededAddr + 0x3c#64) L.closeFileAddr, iAdrp .x0 (L.stdioExitNeededAddr + 0x40#64) L.stderrUsedAddr],
    .words (L.stdioExitNeededAddr + 0x44#64) [0xf9400bf3#32, 0xa8c27bfd#32],
    .instrs L.stdioExitNeededAddr 0x4c [iLdr64Lo12 .x0 .x0 L.stderrUsedAddr, iB (L.stdioExitNeededAddr + 0x50#64) L.closeFileAddr],
    .words L.closeFileAddr [0xb4000400#32, 0xa9be7bfd#32, 0x910003fd#32, 0xf9000bf3#32, 0xaa0003f3#32,
      0xb9408c01#32, 0x36f802a1#32, 0xf9401661#32, 0xf9401e60#32, 0xeb00003f#32, 0x540000c0#32],
    .words (L.closeFileAddr + 0x40#64) [0xa9408261#32, 0xeb00003f#32, 0x54000160#32],
    .words (L.closeFileAddr + 0x74#64) [0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32, 0xd65f03c0#32],
    .words L.sysExitAddr sysExitWords ]

/-- Check that an optional decoded instruction is `adr x4, <imm>`. -/
def isAdrX4 : Option Instr → Bool
  | some (.adr false r _) => decide (r = .gpr 4#5)
  | _ => false

private theorem isAdrX4_eq_true_iff {oi : Option Instr} :
    isAdrX4 oi = true ↔ ∃ imm, oi = some (.adr false (.gpr 4#5) imm) := by
  constructor
  · cases oi with
    | none => simp [isAdrX4]
    | some i =>
      cases i <;> simp [isAdrX4]
      rename_i isPage rd imm
      cases isPage <;> simp [decide_eq_true_eq]
  · rintro ⟨imm, rfl⟩; rfl

/-- Check that `addr` decodes in `t` to `adr x4, <imm>` (used at `lang_start_internal + 0x554`,
    where `x4` holds the unexecuted poisoned-`CLEANUP` panic location). -/
def checkAdrX4At (base : BitVec 64) (t : WordTree) (addr : BitVec 64) : Bool :=
  let off := (addr - base).toNat
  (base + BitVec.ofNat 64 off == addr) && decide (off < 2 ^ 64) &&
  isAdrX4 (t.fetchDecodeAt off)

/-- Decidable code-presence bundle for post-`userMain` teardown and `musl` `exit_group` on `P`. -/
structure HbPostMainCode (P : Program) (C : HbCliLayout) (S : HbStartupLayout) : Prop where
  no_hooks       : P.NoHooks
  svc_eq         : P.svc = Syscall.standard
  lsAdrX4        : ∃ imm : BitVec 64,
    P.fetch (C.langStartInternalAddr + 0x554#64) = some (.adr false (.gpr 4#5) imm)
  langStartPost  : CodeChunks P (hbLangStartPostChunks C)
  onceCallPost   : CodeChunks P (hbOnceCallPostChunks C)
  stdoutOncePost : CodeChunks P (hbStdoutOnceLockPostChunks C)
  cleanupPost    : CodeChunks P (hbCleanupClosurePostChunks C)
  lineWriterDrop : CodeChunks P (hbLineWriterDropChunks C)
  dropHandler    : CodeChunks P (hbDropHandlerChunks C S)
  teardownSys    : CodeChunks P (hbTeardownSysChunks C S)
  muslExit       : CodeChunks P (hbMuslExitChunks C S)
  getauxval      : hasInstrs P C.std.getauxvalAddr (getauxvalInstrs C.std)
  cas8Relax      : hasInstrs P C.std.cas8RelaxAddr (cas8RelaxInstrs C.std)
  cas4Acq        : hasInstrs P C.std.cas4AcqAddr (cas4AcqInstrs C.std)
  cas8Acq        : hasInstrs P C.std.cas8AcqAddr (cas8AcqInstrs C.std)
  swp4Rel        : hasInstrs P C.std.swp4RelAddr (swp4RelInstrs C.std)
  stdout         : HbStdoutCode P C
  shims          : HbShimsCode P C

theorem HbPostMainCode.atomics {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    (hc : HbPostMainCode P C S) :
    StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr :=
  stdOutlineAtomics_of_hasInstrs P C.std hc.cas8Relax hc.cas4Acq hc.cas8Acq hc.swp4Rel

/-- $O(k \log N)$ boolean `WordTree` validator for `HbPostMainCode`. -/
def checkHbPostMainCode (C : HbCliLayout) (S : HbStartupLayout)
    (base : BitVec 64) (t : WordTree) : Bool :=
  let L := C.std
  checkAdrX4At base t (C.langStartInternalAddr + 0x554#64) &&
  (hbLangStartPostChunks C).all (checkCodeChunk base t) &&
  (hbOnceCallPostChunks C).all (checkCodeChunk base t) &&
  (hbStdoutOnceLockPostChunks C).all (checkCodeChunk base t) &&
  (hbCleanupClosurePostChunks C).all (checkCodeChunk base t) &&
  (hbLineWriterDropChunks C).all (checkCodeChunk base t) &&
  (hbDropHandlerChunks C S).all (checkCodeChunk base t) &&
  (hbTeardownSysChunks C S).all (checkCodeChunk base t) &&
  (hbMuslExitChunks C S).all (checkCodeChunk base t) &&
  checkCodeChunk base t (.instrs0 L.getauxvalAddr (getauxvalInstrs L)) &&
  checkCodeChunk base t (.instrs0 L.cas8RelaxAddr (cas8RelaxInstrs L)) &&
  checkCodeChunk base t (.instrs0 L.cas4AcqAddr (cas4AcqInstrs L)) &&
  checkCodeChunk base t (.instrs0 L.cas8AcqAddr (cas8AcqInstrs L)) &&
  checkCodeChunk base t (.instrs0 L.swp4RelAddr (swp4RelInstrs L)) &&
  checkHbStdoutCode C base t &&
  checkHbShimsCode C base t

private theorem hbPostCodeChunks_of_all {P : Program} {b : BitVec 64} {t : WordTree}
    (hc : ∀ {c : CodeChunk}, checkCodeChunk b t c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all (checkCodeChunk b t) = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hc (by simpa using h)
  | _ :: _ :: _, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hc h.1, hbPostCodeChunks_of_all hc h.2⟩

/-- Construct `HbPostMainCode P C S` from `checkHbPostMainCode C S P.base t = true` on a `WordTree`. -/
theorem hbPostMainCode_of_wordTree {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {t : WordTree} (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbPostMainCode C S P.base t = true) : HbPostMainCode P C S := by
  have hno_hooks : P.NoHooks := Program.NoHooks.of_eq_none
    (funext fun s => Option.isNone_iff_eq_none.mp (hext s))
    (funext fun s => Option.isNone_iff_eq_none.mp (hovr s))
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf (beq_iff_eq.mp h.1.1) h.1.2 hext hovr h.2
  simp only [checkHbPostMainCode, Bool.and_eq_true] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hadr, hls⟩, hoc⟩, hso⟩, hcc⟩, hlw⟩, hdh⟩, hts⟩, hme⟩, hgav⟩, hc1⟩, hc2⟩, hc3⟩, hc4⟩, hstd⟩, hsh⟩
  unfold checkAdrX4At at hadr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, isAdrX4_eq_true_iff] at hadr
  rcases hadr with ⟨⟨hbase, hbnd⟩, imm, hfetch⟩
  have hadr' : ∃ imm : BitVec 64, P.fetch (C.langStartInternalAddr + 0x554#64) = some (.adr false (.gpr 4#5) imm) :=
    ⟨imm, hbase ▸ fetch_of_wordTree n hcode hwf hfetch hbnd (hookAtOff?_eq_none_of_isNone hext hovr _)⟩
  exact ⟨hno_hooks, hsvc, hadr', hbPostCodeChunks_of_all hc hls, hbPostCodeChunks_of_all hc hoc,
    hbPostCodeChunks_of_all hc hso, hbPostCodeChunks_of_all hc hcc, hbPostCodeChunks_of_all hc hlw,
    hbPostCodeChunks_of_all hc hdh, hbPostCodeChunks_of_all hc hts, hbPostCodeChunks_of_all hc hme,
    hc hgav, hc hc1, hc hc2, hc hc3, hc hc4,
    hbStdoutCode_of_wordTree n hcode hwf hstubs hsyms hext hovr hstd,
    hbShimsCode_of_wordTree n hcode hwf hext hovr hsh⟩

/-! ## Post-`userMain` teardown and `exit_group` execution -/

theorem hbPageAlignUp_ge (n : Nat) : n ≤ Arm64.pageAlignUp n := by
  unfold Arm64.pageAlignUp PAGE_SIZE; omega

theorem roPostFacts_of_pre {C : HbCliLayout} {haveLse : BitVec 8} {R : SepProp} {m : Memory}
    (hm : m ⊨ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ R) :
    RoPostFacts C haveLse m := by
  have hm1 : m ⊨ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ ((C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ R) := Satisfies.mono (by sep_entail) hm
  have hm2 : m ⊨ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ R) := Satisfies.mono (by sep_entail) hm
  have hin1 : InRegion C.std.haveLseAtomicsAddr 1 C.std.haveLseAtomicsAddr := by
    simpa using inRegion_off C.std.haveLseAtomicsAddr (i := 0) (by omega) (by omega)
  have hc1 : m.canRead C.std.haveLseAtomicsAddr 1 = true := by
    have hp := (IsBlockRO.pointsTo8RO _ _).perm_r hm1 hin1
    have hlf := (IsBlockRO.pointsTo8RO _ _).isLazyFree_false hm1 hin1
    dsimp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree]; rw [hp, hlf]; rfl
  have hc8 : m.canRead C.globalPanicCountAddr 8 = true := by
    have hb : ∀ i < 8, (m.perm (C.globalPanicCountAddr + BitVec.ofNat 64 i)).r = true ∧
        m.isLazyFree (C.globalPanicCountAddr + BitVec.ofNat 64 i) = false := fun i hi =>
      ⟨(IsBlockRO.pointsTo64RO _ _).perm_r hm2 (inRegion_off _ hi (by omega)),
       (IsBlockRO.pointsTo64RO _ _).isLazyFree_false hm2 (inRegion_off _ hi (by omega))⟩
    have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega); have b3 := hb 3 (by omega)
    have b4 := hb 4 (by omega); have b5 := hb 5 (by omega); have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
    have b0z : (m.perm C.globalPanicCountAddr).r = true ∧ m.isLazyFree C.globalPanicCountAddr = false := by simpa using b0
    dsimp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [b0z.1, b0z.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2]; rfl
  exact ⟨(IsBlockRO.pointsTo8RO _ _).read hm1, hc1, (IsBlockRO.pointsTo64RO _ _).read hm2, hc8⟩

def HbPostExitFields (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions

theorem HbPostExitFields.rfl (s : State) : HbPostExitFields s s :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩

theorem HbPostExitFields.trans {s0 s1 s2 : State}
    (h01 : HbPostExitFields s0 s1) (h12 : HbPostExitFields s1 s2) :
    HbPostExitFields s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1, h12.2.2.2.trans h01.2.2.2⟩

theorem HbPostExitFields.ofStd {s0 sf : State} (h : StdFieldsPreserved s0 sf) :
    HbPostExitFields s0 sf := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem HbPostExitFields.ofState {s0 sf : State} (h : StdStatePreserved s0 sf) :
    HbPostExitFields s0 sf := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem HbPostExitFields.ofMallocng {s0 sf : State} (h : MallocngStatePreserved s0 sf) :
    HbPostExitFields s0 sf := ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1⟩

theorem hbStdState_toProcess {s0 sf : State} (h : StdStatePreserved s0 sf) :
    ProcessFieldsPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem hbProc_of_nsp_exit {s0 s1 : State}
    (hn : ProofLib.NonSyscallPreserved s0 s1) (he : HbPostExitFields s0 s1) :
    ProcessFieldsPreserved s0 s1 :=
  ⟨he.1, he.2.1, he.2.2.1, he.2.2.2, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, congrFun hn.2.1⟩

@[local simp] theorem hbExitF_w64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    HbPostExitFields s0 (s.writeReg64 r v) ↔ HbPostExitFields s0 s := by
  cases r <;> simp [State.writeReg64, HbPostExitFields]
@[local simp] theorem hbExitF_w32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    HbPostExitFields s0 (s.writeReg32 r v) ↔ HbPostExitFields s0 s := by simp [State.writeReg32]
@[local simp] theorem hbExitF_wReg (s0 s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    HbPostExitFields s0 (s.writeReg w r v) ↔ HbPostExitFields s0 s := by cases w <;> simp [State.writeReg]
@[local simp] theorem hbExitF_wV128 (s0 s : State) (i : BitVec 5) (v : BitVec 128) :
    HbPostExitFields s0 (s.writeVReg128 i v) ↔ HbPostExitFields s0 s := Iff.rfl
@[local simp] theorem hbExitF_pstate (s0 s : State) (p : PState) :
    HbPostExitFields s0 (s.setPState p) ↔ HbPostExitFields s0 s := Iff.rfl
@[local simp] theorem hbExitF_advPC (s0 s : State) :
    HbPostExitFields s0 s.advancePC ↔ HbPostExitFields s0 s := Iff.rfl
@[local simp] theorem hbExitF_setPC (s0 s : State) (pc : BitVec 64) :
    HbPostExitFields s0 (s.setPC pc) ↔ HbPostExitFields s0 s := Iff.rfl
@[local simp] theorem hbExitF_setMem (s0 s : State) (m : Memory) :
    HbPostExitFields s0 (s.setMem m) ↔ HbPostExitFields s0 s := Iff.rfl

theorem hbSetMem_setMem (s : State) (m1 m2 : Memory) : (s.setMem m1).setMem m2 = s.setMem m2 := by cases s; rfl
theorem hbSetMem_w64 (s : State) (m : Memory) (r : Reg) (v : BitVec 64) :
    (s.setMem m).writeReg64 r v = (s.writeReg64 r v).setMem m := by cases s; cases r <;> rfl
theorem hbSetMem_w32 (s : State) (m : Memory) (r : Reg) (v : BitVec 32) :
    (s.setMem m).writeReg32 r v = (s.writeReg32 r v).setMem m := by cases s; cases r <;> rfl
theorem hbSetMem_wReg (s : State) (m : Memory) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.setMem m).writeReg w r v = (s.writeReg w r v).setMem m := by cases s; cases w <;> cases r <;> rfl
theorem hbSetMem_wV128 (s : State) (m : Memory) (i : BitVec 5) (v : BitVec 128) :
    (s.setMem m).writeVReg128 i v = (s.writeVReg128 i v).setMem m := by cases s; rfl
theorem hbSetMem_pstate (s : State) (m : Memory) (p : PState) :
    (s.setMem m).setPState p = (s.setPState p).setMem m := by cases s; rfl
theorem hbSetMem_advPC (s : State) (m : Memory) : (s.setMem m).advancePC = s.advancePC.setMem m := by cases s; rfl
theorem hbSetMem_setPC (s : State) (m : Memory) (pc : BitVec 64) :
    (s.setMem m).setPC pc = (s.setPC pc).setMem m := by cases s; rfl

theorem hbHeap_of_proc {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s1 s2 : State}
    (hp : ProcessFieldsPreserved s1 s2) : M.Heap γ lc blk s1 ⊢ M.Heap γ lc blk s2 :=
  M.heap_transport hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2

theorem hbBv64_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_lin
scoped macro "hb_wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, hbBv64_add_sub_cancel, *]; try rfl; try bv_lin)
scoped macro "hb_exit_rfl" : term => `(by simp [HbPostExitFields.rfl])
scoped macro "hb_norm_jmp" : tactic => `(tactic| (try (conv in State.setPC _ _ => arg 2; rw [hbBv64_add_sub_cancel])))

theorem hb_wp_step_proc {P : Program} {target_pc : BitVec 64} (mid : BitVec 64) {s0 s_base : State}
    {Pre Post : SepProp} {post : State → SepProp → Prop} (hno : P.NoHooks) (hsvc : P.svc = Syscall.standard)
    (hblk : SepWP (P.withSvc noSyscalls) mid s0 Pre
      (fun s1 Q => HbPostExitFields s0 s1 ∧ s1 = s_base.setMem s1.mem ∧ (Q ⊢ Post)))
    (hcont : ∀ m1 : Memory, ProcessFieldsPreserved s0 (s_base.setMem m1) → SepWP P target_pc (s_base.setMem m1) Post post) :
    SepWP P target_pc s0 Pre post :=
  SepWP.cut (SepWP.mono (SepWP.lift_noSyscalls hno hblk hsvc)
    (fun s1 _ _ _ ⟨hnsp, hex, hs1, hQ⟩ => by
      have hp : ProcessFieldsPreserved s0 (s_base.setMem s1.mem) := hs1 ▸ hbProc_of_nsp_exit hnsp hex
      rw [hs1]; exact SepWP.weaken_pre hQ (hcont s1.mem hp)) (fun _ _ _ ho => ho))

theorem hb_done_proc {P : Program} {mid : BitVec 64} {s0 s s_base : State} {Q : SepProp}
    (hpush : ∀ m, s.setMem m = s_base.setMem m := by
      intro _; (try conv => lhs; simp only [hbSetMem_setMem, hbSetMem_w64, hbSetMem_w32, hbSetMem_wReg,
        hbSetMem_wV128, hbSetMem_pstate, hbSetMem_advPC, hbSetMem_setPC]); try rfl)
    (hpc : s.pc = mid := by exact hb_wp_a) (hrun : s.status = .Running := by simp [wp_norm, arm64_norm, *])
    (hex : HbPostExitFields s0 s := by exact hb_exit_rfl) :
    SepWP P mid s Q (fun s1 Q1 => HbPostExitFields s0 s1 ∧ s1 = s_base.setMem s1.mem ∧ (Q1 ⊢ Q)) :=
  SepWP.done hpc hrun ⟨hex, (by cases s; rfl : s = s.setMem s.mem).trans (hpush s.mem), by sep_entail⟩

theorem hbFetchAtAcc_noSvc {P : Program} {base : BitVec 64} {acc : Prop} (hacc : acc) :
    ∀ (off : Nat) (is : List Instr),
      (∀ i (hi : i < is.length), P.fetch (base + BitVec.ofNat 64 (off + 4 * i)) = some (is[i]'hi)) →
      hbFetchAtAcc (P.withSvc noSyscalls) base off is acc
  | _, [], _ => hacc
  | off, _ :: xs, h =>
    ⟨by simpa [fetch_withSvc] using h 0 (Nat.zero_lt_succ _),
     hbFetchAtAcc_noSvc hacc (off + 4) xs fun i hi => by
       simpa [show off + 4 + 4 * i = off + 4 * (i + 1) by omega] using h (i + 1) (Nat.succ_lt_succ hi)⟩

theorem hbChunk_toStepAcc_noSvc {P : Program} {acc : Prop} (hacc : acc) :
    ∀ {c : CodeChunk}, c.holds P → hbChunkStepAcc (P.withSvc noSyscalls) acc c
  | .words _ _, h => ⟨h, hacc⟩
  | .instrs0 _ _, h => hbFetchAtAcc_noSvc hacc 0 _ fun i hi => by simpa using h i hi
  | .instrs _ o _, h => hbFetchAtAcc_noSvc hacc o _ fun i hi => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]; exact h i hi

theorem hbCodeChunks_toStepFacts_noSvc {P : Program} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → HbCodeStepFacts (P.withSvc noSyscalls) cs
  | [], _ => trivial
  | [_], h => hbChunk_toStepAcc_noSvc trivial h
  | _ :: _ :: _, ⟨h1, h2⟩ => hbChunk_toStepAcc_noSvc (hbCodeChunks_toStepFacts_noSvc h2) h1

scoped macro "hb_unpack_code " chunks:ident h:term : tactic => `(tactic| (have _hc := hbCodeChunks_toStepFacts $h; simp only [$chunks:ident, hbOutlinedFn72Chunks, List.cons_append, List.nil_append, HbCodeStepFacts, hbChunkStepAcc, hbFetchAtAcc, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc; (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

scoped macro "hb_unpack_code_nosvc " chunks:ident h:term : tactic => `(tactic| (have _hc := hbCodeChunks_toStepFacts_noSvc $h; simp only [$chunks:ident, hbOutlinedFn72Chunks, List.cons_append, List.nil_append, HbCodeStepFacts, hbChunkStepAcc, hbFetchAtAcc, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc; (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

theorem hbPointsTo8_combine32_sub (sp o0 o1 o2 o3 : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl) (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₈ b0) ∗ ((sp - o1) ↦₈ b1) ∗ ((sp - o2) ↦₈ b2) ∗ ((sp - o3) ↦₈ b3) ∗ R =
      ((sp - o0) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ R := by
  subst h1 h2 h3
  simpa only [sepConj_assoc, show sp - o0 + 1#64 = sp - (o0 - 1#64) by bv_lin,
    show sp - o0 + 2#64 = sp - (o0 - 2#64) by bv_lin,
    show sp - o0 + 3#64 = sp - (o0 - 3#64) by bv_lin] using congrArg (· ∗ R) (pointsTo8_quad (sp - o0) b0 b1 b2 b3)

theorem hbPointsTo32_split8_sub (sp o0 o1 o2 o3 : BitVec 64) (v : BitVec 32) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl) (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₃₂ v) ∗ R =
      ((sp - o0) ↦₈ v.extractLsb' 0 8) ∗ ((sp - o1) ↦₈ v.extractLsb' 8 8) ∗
      ((sp - o2) ↦₈ v.extractLsb' 16 8) ∗ ((sp - o3) ↦₈ v.extractLsb' 24 8) ∗ R := by
  rw [hbPointsTo8_combine32_sub sp o0 o1 o2 o3 _ _ _ _ R h1 h2 h3,
    show v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v by bv_bits]

theorem hbStackAt_split (sp : BitVec 64) (a b : Nat) {n : Nat}
    (hab : n = a + b := by rfl) (h : a + b ≤ 2 ^ 64 := by decide) :
    stackAt sp n = stackAt (sp - BitVec.ofNat 64 a) b ∗ stackAt sp a := by
  subst hab; rw [stackAt_split_bottom sp a b h]; unfold stackAt; rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem hbCombine_cell_byte4_sat (sp o8 o4 o3 o2 o1 : BitVec 64) {lo : BitVec 32} {b0 b1 b2 b3 : BitVec 8}
    {m : Memory} {P R : SepProp} (hm : m ⊨ P)
    (hf : P ⊢ (((sp - o8) ↦₃₂ lo) ∗ ((sp - o4) ↦₈ b0) ∗ ((sp - o3) ↦₈ b1) ∗
      ((sp - o2) ↦₈ b2) ∗ ((sp - o1) ↦₈ b3)) ∗ R := by sep_frame)
    (h4 : o8 - 4#64 = o4 := by rfl) (h1 : o4 - 1#64 = o3 := by rfl)
    (h2 : o4 - 2#64 = o2 := by rfl) (h3 : o4 - 3#64 = o1 := by rfl) :
    m ⊨ (((sp - o8) ↦₆₄ ((b3 ++ b2 ++ b1 ++ b0) ++ lo)) ∗ R) := by
  have hm' := Satisfies.mono hf hm
  rwa [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
    hbPointsTo8_combine32_sub sp o4 o3 o2 o1 b0 b1 b2 b3 R h1 h2 h3,
    pointsTo32_combine64_sub sp o8 o4 lo _ R h4] at hm'

scoped macro "hb_unpack_cells " k:num : tactic => `(tactic| (simp only [Nat.reduceMul]; cells_unfold; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate $k (apply SepWP.exists_left; intro _)))

scoped macro "hb_repack_cells" : tactic => `(tactic| (simp only [Nat.reduceMul]; cells_unfold; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail))

scoped macro "hb_repack_cells_split " hm:ident "," sp:term "," o8:term "," o4:term "," o3:term "," o2:term "," o1:term : tactic =>
  `(tactic| (replace $hm := hbCombine_cell_byte4_sat $sp $o8 $o4 $o3 $o2 $o1 $hm; hb_repack_cells))

scoped macro "hb_unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)

scoped macro "hb_close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])

theorem hbAlign32_of_mod {a : BitVec 64} (h : a.toNat % 4 = 0) : MemWidth.isAligned .W32 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 3 = 0; rwa [Nat.and_two_pow_sub_one_eq_mod _ 2]

theorem hbAlign64_of_mod {a : BitVec 64} (h : a.toNat % 8 = 0) : MemWidth.isAligned .X64 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 7 = 0; rwa [Nat.and_two_pow_sub_one_eq_mod _ 3]

theorem hbStdoutGlobal_split (stdoutAddr : BitVec 64) (v : BitVec 64) (bs : List (BitVec 8))
    (hbs : bs = unpack64 0#64 ++ (unpack64 0#64 ++ (unpack64 0#64 ++ (unpack64 0#64 ++
      (unpack64 v ++ (unpack64 0#64 ++ ([0#8] ++ List.replicate 7 0#8))))))) :
    (stdoutAddr ↦ₛ bs) = (stdoutAddr ↦₆₄ 0#64) ∗ ((stdoutAddr + 0x08#64) ↦₆₄ 0#64) ∗
      ((stdoutAddr + 0x10#64) ↦₆₄ 0#64) ∗ ((stdoutAddr + 0x18#64) ↦₆₄ 0#64) ∗
      ((stdoutAddr + 0x20#64) ↦₆₄ v) ∗ ((stdoutAddr + 0x28#64) ↦₆₄ 0#64) ∗
      ((stdoutAddr + 0x30#64) ↦₈ 0#8) ∗ ((stdoutAddr + 0x31#64) ↦ₛ List.replicate 7 0#8) := by
  rw [hbs]
  simp only [pointsToBytes_append, pointsToBytes_singleton, ← pointsTo64_eq_pointsToBytes,
    unpack64_length, List.length_cons, List.length_nil]
  simp (config := { decide := true }) only [BitVec.add_assoc, Nat.reduceAdd, BitVec.reduceAdd]

theorem hbStdoutOnceLockInitPost_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc sp0 notInitPtr : BitVec 64} {oldFlag haveLse : BitVec 8}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S) (hv : C.Valid) (hs : S.Valid C)
    (hpc : s.pc = C.std.stdoutOnceLockInitAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = notInitPtr) (hflag_nz : notInitPtr ≠ 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 →
      CalleeSavedPreserved s sf → ProcessFieldsPreserved s sf →
      SepWP P target_pc sf (((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗
        (C.std.stdoutGlobalAddr ↦ₛ stdoutDummyBytes) ∗ (notInitPtr ↦₈ 1#8) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.std.stdoutVtableAddr C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr ∗
        stackAt sp0 160 ∗ F) post) :
    SepWP P target_pc s (((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗
      (C.std.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗ (notInitPtr ↦₈ oldFlag) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo C.std.stdoutVtableAddr C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr ∗
      stackAt sp0 160 ∗ F) post := by
  subst hsp
  have hal_g38 : MemWidth.isAligned .W32 (C.std.stdoutGlobalAddr + 0x38#64) = true :=
    (hbValid_stdout_align hv).2.2.1
  have hal_vt20 : MemWidth.isAligned .X64 (C.std.stdoutVtableAddr + 0x20#64) = true :=
    hbAlign64_of_mod (by have := hs.stdoutVt_align; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  unfold StdVtableRo
  rw [stackAt_split_cells s.sp 96 8 (by decide)]; hb_unpack_cells 8
  rw [stackAt_eq_cells (s.sp - 64#64) 12]; hb_unpack_cells 12
  rw [pointsTo64_split32_sub (s.sp - 64#64) 88#64 84#64,
      hbPointsTo32_split8_sub (s.sp - 64#64) 84#64 83#64 82#64 81#64]
  refine hb_wp_step_proc C.std.cas4AcqAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbStdoutOnceLockPostChunks hc.stdoutOncePost
    hb_unpack_code_nosvc hbOnceCallPostChunks hc.onceCallPost
    wp_steps
    refine step_ldar32_words (C.std.stdoutOnceLockInitAddr + 0x08#64) _ 0
      (C.std.stdoutOnceLockInitAddr + 0x0c#64) hal_g38 (hnext := ?_)
    iterate 12 (wp_steps; hb_norm_jmp)
    conv => repeat rw [hbBv64_add_sub_cancel]
    refine step_ldar32_words C.std.onceCallAddr _ 7 (C.std.onceCallAddr + 0x20#64)
      hal_g38 (rt' := .gpr 22#5) (hnext := ?_)
    wp_steps; wp_steps; hb_norm_jmp; exact hb_done_proc) fun m1 hp1 => ?_
  refine call_stdCas4 hc.atomics.cas4Acq_ok (haveLse := haveLse)
    (ptr := C.std.stdoutGlobalAddr + 0x38#64) (v0 := 3#32) (exp := 3#32) (new := 1#32)
    (ret_pc := C.std.onceCallAddr + 0x64#64) (F := ?_) (by sep_frame)
    (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_) (halign := hal_g38)
  simp only [beq_self_eq_true, ↓reduceIte]
  have ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩ :
      s1.readReg64 .x19 = C.std.stdoutGlobalAddr + 0x38#64 ∧ s1.readReg64 .x20 = s.sp - 32#64 ∧
      s1.readReg64 .x21 = C.std.stdoutVtableAddr ∧ BitVec.truncate 32 (s1.readReg64 (.gpr 22#5)) = 3#32 ∧
      BitVec.truncate 32 (s1.readReg64 (.gpr 23#5)) = 3#32 :=
    ⟨by rw [hcs1.readReg64_x19]; exact hb_wp_a, by rw [hcs1.readReg64_x20]; exact hb_wp_a,
     by rw [hcs1.readReg64_x21]; exact hb_wp_a,
     by have := hcs1.readReg32_x22; simp [wp_norm, arm64_norm] at this; exact this,
     by have := hcs1.readReg32_x23; simp [wp_norm, arm64_norm] at this; exact this⟩
  have hsp1_eq : s1.sp = s.sp - 160#64 := by rw [hsp1]; exact hb_wp_a
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]; exact s.spAligned_sub 160#64 hsp_align
  refine hb_wp_step_proc C.std.swp4RelAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbStdoutOnceLockPostChunks hc.stdoutOncePost
    hb_unpack_code_nosvc hbOnceCallPostChunks hc.onceCallPost
    rw [hbStdoutGlobal_split C.std.stdoutGlobalAddr 0#64 _ (by decide)]
    wp_steps; wp_steps; wp_steps; wp_steps; hb_norm_jmp
    rw [← hbStdoutGlobal_split C.std.stdoutGlobalAddr 1#64 stdoutDummyBytes (by decide)]
    exact hb_done_proc) fun m2 hp2 => ?_
  refine call_stdSwp4 hc.atomics.swp4Rel_ok (haveLse := haveLse)
    (ptr := C.std.stdoutGlobalAddr + 0x38#64) (v0 := 1#32) (new := 0#32)
    (ret_pc := C.std.onceCallAddr + 0x128#64) (F := ?_) (by sep_frame)
    (fun s3 hpc3 hrun3 hsp3 hcs3 hx0_3 hstd3 => ?_) (halign := hal_g38)
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := by simpa [Reg.x0] using hx0_3
  have hsp3_eq : s3.sp = s.sp - 160#64 := by rw [hsp3]; exact hb_wp_a
  have hsp3_al : s3.spAligned = true := by
    simp only [State.spAligned, hsp3_eq]; exact s.spAligned_sub 160#64 hsp_align
  refine hb_wp_step_proc ret_pc hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbStdoutOnceLockPostChunks hc.stdoutOncePost
    hb_unpack_code_nosvc hbOnceCallPostChunks hc.onceCallPost
    wp_steps; wp_steps; wp_steps; exact hb_done_proc) fun m4 hp4 => ?_
  refine SepWP.weaken_pre_frame ?_ (hnext _ hb_wp_a (by simp [wp_norm, arm64_norm, hrun3]) hb_wp_a
    (by hb_unpack_cs hcs1; hb_unpack_cs hcs3; hb_close_cs)
    (hp1.trans ((hbStdState_toProcess hstd1).trans (hp2.trans ((hbStdState_toProcess hstd3).trans hp4)))))
  intro _ hm
  unfold StdVtableRo
  rw [stackAt_split_cells s.sp 96 8 (by decide), stackAt_eq_cells (s.sp - 64#64) 12]
  hb_repack_cells_split hm, (s.sp - 64#64), 88#64, 84#64, 83#64, 82#64, 81#64

theorem hbLift_hpre {P Q F : SepProp} (h : P ⊢ Q ∗ F) {m : Memory} :
    ∀ R, (m ⊨ P ∗ R) → (m ⊨ Q ∗ (F ∗ R)) :=
  fun _ hm => by rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left h) hm

theorem hbLineWriterDrop_wp {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {lim : MallocngLimits} (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {target_pc ret_pc sp0 bufPtr : BitVec 64} {lc blk : Nat} {e0 : BitVec 32}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : HbPostMainCode P C S)
    (hpc : s.pc = C.lineWriterDropAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = C.std.stdoutGlobalAddr + 0x18#64)
    (hbuf_nz : bufPtr ≠ 0#64)
    (hnext : ∀ (sf : State) (e1 : BitVec 32), sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 →
      CalleeSavedPreserved s sf → HbPostExitFields s sf →
      SepWP P target_pc sf (((C.std.stdoutGlobalAddr + 0x18#64) ↦₆₄ 1024#64) ∗
        ((C.std.stdoutGlobalAddr + 0x20#64) ↦₆₄ bufPtr) ∗
        ((C.std.stdoutGlobalAddr + 0x28#64) ↦₆₄ 0#64) ∗
        ((C.std.stdoutGlobalAddr + 0x30#64) ↦₈ 0#8) ∗
        M.Heap γ lc blk sf ∗ (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4144 ∗ F) post) :
    SepWP P target_pc s (((C.std.stdoutGlobalAddr + 0x18#64) ↦₆₄ 1024#64) ∗
      ((C.std.stdoutGlobalAddr + 0x20#64) ↦₆₄ bufPtr) ∗
      ((C.std.stdoutGlobalAddr + 0x28#64) ↦₆₄ 0#64) ∗
      ((C.std.stdoutGlobalAddr + 0x30#64) ↦₈ 0#8) ∗
      M.Heap γ (lc + mallocngBlockCost 1024) (blk + 1) s ∗
      M.Block γ bufPtr 1024 ∗ memRegion bufPtr 1024 ∗
      (muslErrnoAddr s ↦₃₂ e0) ∗ stackAt sp0 4144 ∗ F) post := by
  subst hsp
  rw [stackAt_split_cells s.sp 4096 6 (by decide)]; hb_unpack_cells 6
  refine hb_wp_step_proc C.bufWriterFlushBufAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbLineWriterDropChunks hc.lineWriterDrop
    wp_steps; wp_steps; hb_norm_jmp; exact hb_done_proc) fun m1 hp1 => ?_
  rw [hbStackAt_split (s.sp - 48#64) 112 3984]
  have hFlush := hbBufWriterFlushZero_ok hc.stdout hc.no_hooks
  have h28 : (C.std.stdoutGlobalAddr + 0x18#64) + 0x10#64 = C.std.stdoutGlobalAddr + 0x28#64 := by bv_lin
  refine SepWP.call_subroutine_frame (ret_pc := C.lineWriterDropAddr + 0x24#64) hFlush
    (x := C.std.stdoutGlobalAddr + 0x18#64) (F := ?_)
    hb_wp_a (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm]; exact hsp_align)
    hb_wp_a
    (hbLift_hpre (by dsimp only [hbBufWriterFlushZeroSpec]; simp only [wp_norm, arm64_norm]; sep_frame))
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun s1 hpc1 hrun1 hsp1 hcs1 => ?_
  dsimp only [hbBufWriterFlushZeroSpec]; rw [h28, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0_1, hproc_fl⟩
  refine SepWP.weaken_pre (P' := stackAt (s.sp - 48#64) 4096 ∗ ?_)
    (by simp only [wp_norm, arm64_norm]; rw [hbStackAt_split (s.sp - 48#64) 112 3984 (n := 4096)]; sep_frame) ?_
  have hx19_1 : s1.readReg64 .x19 = C.std.stdoutGlobalAddr + 0x18#64 := by
    rw [hcs1.readReg64_x19]; exact hb_wp_a
  have hsp1_eq : s1.sp = s.sp - 48#64 := by rw [hsp1]; exact hb_wp_a
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]; exact s.spAligned_sub 48#64 hsp_align
  refine hb_wp_step_proc C.mallocng.freeAddr hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbLineWriterDropChunks hc.lineWriterDrop
    have hf0 : (P.withSvc noSyscalls).fetch C.rustDeallocAddr = some (iB C.rustDeallocAddr C.rdlDeallocAddr) := by
      simpa [fetch_withSvc, rustDeallocInstrs] using hc.shims.dealloc 0 (Nat.zero_lt_succ _)
    have hf1 : (P.withSvc noSyscalls).fetch C.rdlDeallocAddr = some (iB C.rdlDeallocAddr C.mallocng.freeAddr) := by
      simpa [fetch_withSvc, rdlDeallocInstrs] using hc.shims.rdlDealloc 0 (Nat.zero_lt_succ _)
    wp_steps; wp_steps; hb_norm_jmp; wp_steps; hb_norm_jmp; wp_steps; hb_norm_jmp
    exact hb_done_proc) fun m2 hp2 => ?_
  have hp_sf := hp1.trans (hproc_fl.trans hp2)
  have hht := hbHeap_of_proc M hp_sf (γ := γ) (lc := lc + mallocngBlockCost 1024) (blk := blk + 1)
  refine SepWP.call_subroutine_frame (ret_pc := C.lineWriterDropAddr + 0x6c#64) (M.free_ok γ)
    (x := (lc + mallocngBlockCost 1024, blk + 1, some 1024, e0)) (F := ?_)
    hb_wp_a (by simp [wp_norm, arm64_norm, hrun1])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al) hb_wp_a
    (hbLift_hpre (by
      dsimp +zetaDelta only [MallocngStackBytes, muslErrnoAddr]; rw [hp_sf.2.2.1]
      conv => rhs; arg 1; arg 2; simp only [wp_norm, arm64_norm, hsp1_eq]
      rw [pure_sepConj_of_true hbuf_nz]
      exact Entails.trans (Q := M.Heap γ (lc + mallocngBlockCost 1024) (blk + 1) s ∗ _) (by sep_frame)
        (Entails.trans (sepConj_mono_left hht) (by sep_frame))))
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun s2 hpc2 hrun2 hsp2 hcs2 => ?_
  dsimp +zetaDelta only [MallocngStackBytes]; rw [Nat.add_sub_cancel, Nat.add_sub_cancel, sepConj_assoc]
  apply SepWP.pure_elim; intro hmal2
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro e1
  have hsp2_eq : s2.sp = s.sp - 48#64 := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1_eq]
  have hsp2_al : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq]; exact s.spAligned_sub 48#64 hsp_align
  refine hb_wp_step_proc ret_pc hc.no_hooks hc.svc_eq (by
    hb_unpack_code_nosvc hbLineWriterDropChunks hc.lineWriterDrop
    wp_steps; exact hb_done_proc) fun m3 hp3 => ?_
  have hex_all : HbPostExitFields s _ :=
    HbPostExitFields.trans ⟨hp_sf.1, hp_sf.2.1, hp_sf.2.2.1, hp_sf.2.2.2.1⟩
      (HbPostExitFields.trans (HbPostExitFields.ofMallocng hmal2) ⟨hp3.1, hp3.2.1, hp3.2.2.1, hp3.2.2.2.1⟩)
  refine SepWP.weaken_pre_frame ?_
    (hnext _ e1 hb_wp_a (by simp [wp_norm, arm64_norm, hrun2]) hb_wp_a
      (by hb_unpack_cs hcs1; hb_unpack_cs hcs2; hb_close_cs) hex_all)
  intro _ hm
  replace hm : _ ⊨ (M.Heap γ lc blk s2 ∗ _) ∗ _ := (by sep_frame : _ → _) hm
  replace hm := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hbHeap_of_proc M hp3))) hm
  dsimp only [muslErrnoAddr] at hm ⊢
  rw [← hmal2.2.2.2.1] at hm
  simp only [wp_norm, arm64_norm, hsp1_eq] at hm ⊢
  rw [stackAt_split_cells s.sp 4096 6 (by decide)]
  hb_repack_cells

theorem step_ldr8_lse_ro {P : Program} {C : HbCliLayout} {target_pc pc : BitVec 64}
    {haveLse : BitVec 8} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.ldr .W32 .B8 false .x16 (.Offset .x16 (pageLo12 C.std.haveLseAtomicsAddr))))
    (hx16 : s.readReg64 .x16 + pageLo12 C.std.haveLseAtomicsAddr = C.std.haveLseAtomicsAddr)
    (hro : RoPostFacts C haveLse s.mem)
    (hnext : SepWP P target_pc ((s.writeReg .W32 .x16 (haveLse.zeroExtend 64)).setPC (pc + 4#64)) Pre post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.step_pure (s' := (s.writeReg .W32 .x16 (haveLse.zeroExtend 64)).setPC (pc + 4#64))
    hpc hrun hfetch ?_ rfl hnext
  have hs_eq : s.setPC pc = s := by cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hea : evalAddrMode s (.Offset .x16 (pageLo12 C.std.haveLseAtomicsAddr)) = (C.std.haveLseAtomicsAddr, none) := by
    simp [evalAddrMode, hx16]
  have hsp : checkAddrSPAligned s (.Offset .x16 (pageLo12 C.std.haveLseAtomicsAddr)) = true := rfl
  rw [hs_eq]
  simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized,
    State.advancePC, State.setPC, hsp, hea, hro.1, hro.2.1, MemWidth.bytes, hpc]

theorem step_ldr64_panic_ro {P : Program} {C : HbCliLayout} {target_pc addr : BitVec 64}
    {words : List (BitVec 32)} {haveLse : BitVec 8} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (i : Nat) (next_pc : BitVec 64) (hro : RoPostFacts C haveLse s.mem)
    (hw : P.hasCode addr words := by with_reducible assumption)
    (hget : words[i]? = some 0xf94002a8#32 := by rfl)
    (hpc_next : addr + BitVec.ofNat 64 (4 * (i + 1)) = next_pc := by simp [bv_lin_norm]; try bv_lin)
    (hpc : s.pc = addr + BitVec.ofNat 64 (4 * i) := by exact hb_wp_a)
    (hrun : s.status = .Running := by simp [wp_norm, arm64_norm, *])
    (hx21 : s.readReg64 (.gpr 21#5) = C.globalPanicCountAddr := by exact hb_wp_a)
    (hnext : SepWP P target_pc ((s.writeReg64 (.gpr 8#5) 0#64).setPC next_pc) Pre post) :
    SepWP P target_pc s Pre post := by
  subst hpc_next
  have hdec : decode 0xf94002a8#32 = some (.ldr .W64 .X64 false (.gpr 8#5) (.Offset (.gpr 21#5) 0#64)) := by decide
  refine SepWP.step_pure (s' := (s.writeReg64 (.gpr 8#5) 0#64).setPC (addr + BitVec.ofNat 64 (4 * (i + 1))))
    hpc hrun (Program.fetch_of_hasWords_getElem_decode i _ hw rfl hget hdec) ?_ rfl hnext
  have hs_eq : s.setPC (addr + BitVec.ofNat 64 (4 * i)) = s := by
    cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hea : evalAddrMode s (.Offset (.gpr 21#5) 0#64) = (C.globalPanicCountAddr, none) := by
    simp [evalAddrMode, hx21]
  have hsp : checkAddrSPAligned s (.Offset (.gpr 21#5) 0#64) = true := rfl
  have hpc4 : s.pc + 4#64 = addr + BitVec.ofNat 64 (4 * (i + 1)) := by
    rw [hpc, Nat.mul_succ, BitVec.ofNat_add]; bv_lin
  rw [hs_eq]
  simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized,
    State.writeReg, State.advancePC, State.setPC, hsp, hea, hro.2.2.1, hro.2.2.2, MemWidth.bytes, hpc4]

def RoDisj (C : HbCliLayout) (a : BitVec 64) (n : Nat) : Prop :=
  ∀ x, InRegion a n x → x ≠ C.std.haveLseAtomicsAddr ∧ ¬ InRegion C.globalPanicCountAddr 8 x

theorem roSafe_disj32 {C : HbCliLayout} {Keep F : SepProp} (a : BitVec 64) {v : BitVec 32}
    (hSafe : RoSafe C Keep) (hent : Keep ⊢ (a ↦₃₂ v) ∗ F := by sep_frame) : RoDisj C a 4 :=
  fun x hx => hSafe x (OwnsRW.of_entails hent (ownsRW_sepConj_left (ownsRW_pointsTo32_at a v x hx)))

theorem roSafe_disj64 {C : HbCliLayout} {Keep F : SepProp} (a : BitVec 64) {v : BitVec 64}
    (hSafe : RoSafe C Keep) (hent : Keep ⊢ (a ↦₆₄ v) ∗ F := by sep_frame) : RoDisj C a 8 :=
  fun x hx => hSafe x (OwnsRW.of_entails hent (ownsRW_sepConj_left (ownsRW_pointsTo64_at a v x hx)))

theorem roSafe_disj_stack {C : HbCliLayout} {Keep F : SepProp} (sp : BitVec 64) (sz : Nat)
    (hSafe : RoSafe C Keep) (hent : Keep ⊢ stackAt sp sz ∗ F := by sep_frame) :
    RoDisj C (sp - BitVec.ofNat 64 sz) sz :=
  fun x hx => hSafe x (OwnsRW.of_entails hent (ownsRW_sepConj_left (ownsRW_memRegion _ sz x hx)))

theorem roDisj_sub {C : HbCliLayout} {base a : BitVec 64} {sz : Nat}
    (h : RoDisj C base sz) (off k : Nat)
    (ha : a = base + BitVec.ofNat 64 off := by bv_lin)
    (hle : off + k ≤ sz := by omega) (hfit : off + k ≤ 2 ^ 64 := by omega) :
    RoDisj C a k := fun x hx => h x (by
  unfold InRegion at hx ⊢
  rw [show x - base = (x - a) + BitVec.ofNat 64 off by subst ha; bv_omega]
  have hlt : (x - a).toNat < k := hx
  have hoff_mod : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add_of_lt (by omega), hoff_mod]; omega)

theorem step_str8_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea : BitVec 64} {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C ea 1)
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, RoPostFacts C haveLse m' → SepWP prog target_pc (s'.setMem m') P' post) :
    SepWP prog target_pc s P post := by
  apply SepWP.of_reaches_pc; intro R hm
  have htrunc : (s.readReg64 rt).truncate 8 = val := by rw [← bitvec_truncate8_truncate32]; exact hval
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem (s.mem.write8 ea val) := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hstore.writable hm, MemWidth.bytes, hpc]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext _ (roPostFacts_write8 (hd ea (by simp [InRegion])) hro)) (hstore.store hm)

theorem step_str64_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea val : BitVec 64} {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C ea 8)
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, RoPostFacts C haveLse m' → SepWP prog target_pc (s'.setMem m') P' post) :
    SepWP prog target_pc s P post := by
  apply SepWP.of_reaches_pc; intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem (s.mem.write64 ea val) := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hstore.writable hm, MemWidth.bytes, hpc]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext _ (roPostFacts_write64 hd hro)) (hstore.store hm)

theorem step_stp64_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea ea2 v1 v2 : BitVec 64} {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hro : RoPostFacts C haveLse s.mem) (hd1 : RoDisj C ea 8) (hd2 : RoDisj C ea2 8)
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, RoPostFacts C haveLse m' → SepWP prog target_pc (s'.setMem m') P2 post) :
    SepWP prog target_pc s P post := by
  apply SepWP.of_reaches_pc; intro R hm
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m2 (roPostFacts_write64 hd2 (roPostFacts_write64 hd1 hro))) hm2

private theorem fetch_at_ro {P : Program} {base off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (h : hasInstrs P base ls) (hi : ls[i]? = some inst := by rfl) (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (base + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off i off hlt hoff; rw [List.getElem?_eq_getElem hlt] at hi; cases hi; exact hf

private theorem fetch_at0_ro {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P base ls) (hi : ls[0]? = some inst := by rfl) : P.fetch base = some inst := by
  simpa using fetch_at_ro 0 h hi rfl

private theorem step_cas64_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea v0 new : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.cas .X64 true false .x0 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .X64 ea = true)
    (hexp : s.readReg64 .x0 = v0) (hnew : s.readReg64 .x1 = new)
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C ea 8)
    (hnext : ∀ m' : Memory, RoPostFacts C haveLse m' → m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.writeReg64 .x0 v0).setPC (pc + 4#64)).setMem m') ((ea ↦₆₄ new) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₆₄ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr := (IsBlock.pointsTo64 ea v0).canRead (by decide) hm'; have hcw := (IsBlock.pointsTo64 ea v0).canWrite (by decide) hm'
  have hrd := (IsBlock.pointsTo64 ea v0).read hm'; have hsp : checkRegSPAligned s .x2 = true := rfl
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Memory.readSized, hrd, hexp, beq_self_eq_true, Memory.writeSized, hnew]
  have hst : ((s.setMem (s.mem.write64 ea new)).writeReg .W64 .x0 v0).advancePC =
      ((s.writeReg64 .x0 v0).setPC (pc + 4#64)).setMem (s.mem.write64 ea new) := by
    cases s; simp [State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
  rw [hst]; refine SepWP.to_reaches_pc (hnext _ (roPostFacts_write64 hd hro) (Memory.perm_write64 s.mem ea new)) ?_
  rw [sepConj_assoc]; exact (IsBlock.pointsTo64 ea v0).write64 hm' new

private theorem step_cas32_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea : BitVec 64} {v0 new : BitVec 32} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.cas .W32 true false .x0 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .W32 ea = true)
    (hexp : s.readReg32 .x0 = v0) (hnew : s.readReg32 .x1 = new)
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C ea 4)
    (hnext : ∀ m' : Memory, RoPostFacts C haveLse m' → m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem m') ((ea ↦₃₂ new) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr := (IsBlock.pointsTo32 ea v0).canRead (by decide) hm'; have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have hrd := (IsBlock.pointsTo32 ea v0).read hm'; have hsp : checkRegSPAligned s .x2 = true := rfl
  have hexp' : ((s.readReg64 .x0).truncate 32).zeroExtend 64 = v0.zeroExtend 64 := by rw [← hexp]; rfl
  have hnew' : (s.readReg64 .x1).truncate 32 = new := hnew
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Memory.readSized, hrd, hexp', beq_self_eq_true, Memory.writeSized, hnew']
  have hst : ((s.setMem (s.mem.write32 ea new)).writeReg .W32 .x0 (v0.zeroExtend 64)).advancePC =
      ((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem (s.mem.write32 ea new) := by
    cases s; simp [State.writeReg, State.writeReg32, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
  rw [hst]; refine SepWP.to_reaches_pc (hnext _ (roPostFacts_write32 hd hro) (Memory.perm_write32 s.mem ea new)) ?_
  rw [sepConj_assoc]; exact (IsBlock.pointsTo32 ea v0).write32 hm' new

private theorem step_swp32_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea : BitVec 64} {v0 new : BitVec 32} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.atomicRmw .SWP .W32 false true .x0 .x1 .x0))
    (haddr : s.readReg64 .x1 = ea) (halign : MemWidth.isAligned .W32 ea = true) (hnew : s.readReg32 .x0 = new)
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C ea 4)
    (hnext : ∀ m' : Memory, RoPostFacts C haveLse m' → m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem m') ((ea ↦₃₂ new) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr := (IsBlock.pointsTo32 ea v0).canRead (by decide) hm'; have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have hrd := (IsBlock.pointsTo32 ea v0).read hm'; have hsp : checkRegSPAligned s .x1 = true := rfl
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have htrunc : (evalAtomicOp .SWP .W32 (v0.zeroExtend 64) (s.readReg64 .x0)).truncate 32 = new := by
    rw [← hnew]; dsimp [evalAtomicOp, State.readReg32]; bv_bits
  have hst : ((s.setMem (s.mem.write32 ea new)).writeReg .W32 .x0 (v0.zeroExtend 64)).advancePC =
      ((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem (s.mem.write32 ea new) := by
    cases s; simp [State.writeReg, State.writeReg32, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
  dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Memory.readSized, hrd, Memory.writeSized, htrunc, hst]
  refine SepWP.to_reaches_pc (hnext _ (roPostFacts_write32 hd hro) (Memory.perm_write32 s.mem ea new)) ?_
  rw [sepConj_assoc]; exact (IsBlock.pointsTo32 ea v0).write32 hm' new

private theorem step_stxr64_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea v0 val : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stxr .X64 false .x17 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .X64 ea = true) (hval : s.readReg64 .x1 = val)
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C ea 8)
    (hok : s.exclWillFail = false → ∀ m' : Memory, RoPostFacts C haveLse m' → m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem m') ((ea ↦₆₄ val) ∗ F) post)
    (hfail : s.exclWillFail = true → SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64)) ((ea ↦₆₄ v0) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₆₄ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw := (IsBlock.pointsTo64 ea v0).canWrite (by decide) hm'; have hsp : checkRegSPAligned s .x2 = true := rfl
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); cases hf : s.exclWillFail
  · have hstep : prog.evalInst (.stxr .X64 false .x17 .x2 .x1) s =
        ((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem (s.mem.write64 ea val) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, hval, MemWidth.bytes, hcw,
        Memory.writeSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hstep]
    refine SepWP.to_reaches_pc (hok hf _ (roPostFacts_write64 hd hro) (Memory.perm_write64 s.mem ea val)) ?_
    rw [sepConj_assoc]; exact (IsBlock.pointsTo64 ea v0).write64 hm' val
  · have hstep : prog.evalInst (.stxr .X64 false .x17 .x2 .x1) s = (s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, MemWidth.bytes, hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, hpc]
    rw [hstep]; exact SepWP.to_reaches_pc (hfail hf) (by simpa [State.stepExclOracle] using hm)

private theorem step_stxr32_ro {prog : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc pc ea : BitVec 64} {v0 val : BitVec 32} {rel : Bool} {rn rt : Reg}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stxr .W32 rel .x17 rn rt))
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea) (halign : MemWidth.isAligned .W32 ea = true)
    (hval : s.readReg32 rt = val) (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C ea 4)
    (hok : s.exclWillFail = false → ∀ m' : Memory, RoPostFacts C haveLse m' → m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem m') ((ea ↦₃₂ val) ∗ F) post)
    (hfail : s.exclWillFail = true → SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64)) ((ea ↦₃₂ v0) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'; have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); cases hf : s.exclWillFail
  · have hstep : prog.evalInst (.stxr .W32 rel .x17 rn rt) s =
        ((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem (s.mem.write32 ea val) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, htrunc, MemWidth.bytes, hcw,
        Memory.writeSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hstep]
    refine SepWP.to_reaches_pc (hok hf _ (roPostFacts_write32 hd hro) (Memory.perm_write32 s.mem ea val)) ?_
    rw [sepConj_assoc]; exact (IsBlock.pointsTo32 ea v0).write32 hm' val
  · have hstep : prog.evalInst (.stxr .W32 rel .x17 rn rt) s = (s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, MemWidth.bytes, hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, hpc]
    rw [hstep]; exact SepWP.to_reaches_pc (hfail hf) (by simpa [State.stepExclOracle] using hm)

private theorem exclFails_tail_lt_ro {s : State} {k : Nat} (hk : s.exclFails.length < k + 1) (hf : s.exclWillFail = true) :
    s.exclFails.tail.length < k := by
  cases h : s.exclFails with
  | nil => simp [State.exclWillFail_eq_headD, h] at hf
  | cons _ tl => simp [h] at hk ⊢; omega

private def LlscFrameRo (s0 s : State) : Prop :=
  s.sp = s0.sp ∧ s.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) ∧ CalleeSavedPreserved s0 s ∧ StdStatePreserved s0 s

private theorem LlscFrameRo.refl (s0 : State) : LlscFrameRo s0 s0 :=
  ⟨rfl, rfl, CalleeSavedPreserved.rfl s0, ProcessFieldsPreserved.refl s0⟩
private theorem LlscFrameRo.pc {s0 s : State} {p : BitVec 64} (h : LlscFrameRo s0 s) : LlscFrameRo s0 (s.setPC p) := by cases s; exact h
private theorem LlscFrameRo.ps {s0 s : State} {p : PState} (h : LlscFrameRo s0 s) : LlscFrameRo s0 (s.setPState p) := by cases s; exact h
private theorem LlscFrameRo.ex {s0 s : State} (h : LlscFrameRo s0 s) : LlscFrameRo s0 s.stepExclOracle := by cases s; exact h
private theorem LlscFrameRo.mem {s0 s : State} {m' : Memory} (hm : m'.perm = s.mem.perm) (h : LlscFrameRo s0 s) :
    LlscFrameRo s0 (s.setMem m') := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hp⟩
  cases s; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun a => (congrFun hm a).trans (hp a)⟩
private theorem LlscFrameRo.w64 {s0 s : State} {r : Reg} {v : BitVec 64}
    (hr : r = .gpr 0#5 ∨ r = .gpr 8#5 ∨ r = .gpr 9#5 ∨ r = .gpr 16#5 ∨ r = .gpr 17#5) (h : LlscFrameRo s0 s) :
    LlscFrameRo s0 (s.writeReg64 r v) := by
  rcases h with ⟨h1, h2, hcs, hst⟩
  have hlr : (s.writeReg64 r v).readReg64 (.gpr 30#5) = s.readReg64 (.gpr 30#5) := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact State.readReg64_writeReg64_ne s _ _ v (by decide)
  have hcs' : CalleeSavedPreserved s (s.writeReg64 r v) := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      exact State.readReg64_writeReg64_ne s _ _ v (by decide)
  have hsp : (s.writeReg64 r v).sp = s.sp := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> cases s <;> rfl
  have hpf : StdStatePreserved s (s.writeReg64 r v) := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> cases s <;> exact ProcessFieldsPreserved.refl _
  exact ⟨hsp.trans h1, hlr.trans h2, CalleeSavedPreserved.trans hcs hcs', ProcessFieldsPreserved.trans hst hpf⟩
private theorem LlscFrameRo.w32 {s0 s : State} {r : Reg} {v : BitVec 32}
    (hr : r = .gpr 0#5 ∨ r = .gpr 8#5 ∨ r = .gpr 9#5 ∨ r = .gpr 16#5 ∨ r = .gpr 17#5) (h : LlscFrameRo s0 s) :
    LlscFrameRo s0 (s.writeReg32 r v) := LlscFrameRo.w64 hr h
private theorem LlscFrameRo.w {s0 s : State} {w : RegWidth} {r : Reg} {v : BitVec 64}
    (hr : r = .gpr 0#5 ∨ r = .gpr 8#5 ∨ r = .gpr 9#5 ∨ r = .gpr 16#5 ∨ r = .gpr 17#5) (h : LlscFrameRo s0 s) :
    LlscFrameRo s0 (s.writeReg w r v) := by cases w <;> exact LlscFrameRo.w64 hr h

local macro "llsc_ro_inv" : tactic => `(tactic|
  repeat (
    first
    | assumption | exact LlscFrameRo.refl _ | apply LlscFrameRo.pc | apply LlscFrameRo.ps | apply LlscFrameRo.ex
    | refine LlscFrameRo.w64 (by decide) ?_ | refine LlscFrameRo.w32 (by decide) ?_ | refine LlscFrameRo.w (by decide) ?_
    | refine LlscFrameRo.mem (by simp [State.stepExclOracle, wp_norm, arm64_norm, *]) ?_))

scoped macro "wp_ro_simp" : tactic => `(tactic|
  simp (config := { decide := true }) [pageLo12, State.stepExclOracle, State.readReg32, wp_norm, arm64_norm, bv_lin_norm, *])

private theorem finish_ro {P : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc ret_pc x0v : BitVec 64} {s0 sf : State} {Q : SepProp} {post : State → SepProp → Prop}
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf → StdStatePreserved s0 sf → sf.readReg64 (.gpr 0#5) = x0v →
      RoPostFacts C haveLse sf.mem → SepWP P target_pc sf Q post)
    (hpc : sf.pc = ret_pc) (hrun : sf.status = .Running) (hinv : LlscFrameRo s0 sf)
    (hx0 : sf.readReg64 (.gpr 0#5) = x0v) (hro : RoPostFacts C haveLse sf.mem) :
    SepWP P target_pc sf Q post :=
  hnext sf hpc hrun hinv.1 hinv.2.2.1 hinv.2.2.2 hx0 hro

theorem call_cas8Acq_ro {P : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc ret_pc ptr v0 new : BitVec 64} {s0 : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (h : hasInstrs P C.std.cas8AcqAddr (cas8AcqInstrs C.std))
    (hro : RoPostFacts C haveLse s0.mem) (hd : RoDisj C ptr 8)
    (halign : MemWidth.isAligned .X64 ptr = true)
    (hpc : s0.pc = C.std.cas8AcqAddr := by exact hb_wp_a)
    (hrun : s0.status = .Running := by simp [wp_norm, arm64_norm, *])
    (hlr : s0.readReg64 (.gpr 30#5) = ret_pc := by exact hb_wp_a)
    (hx0 : s0.readReg64 (.gpr 0#5) = v0 := by exact hb_wp_a)
    (hx1 : s0.readReg64 (.gpr 1#5) = new := by exact hb_wp_a)
    (hx2 : s0.readReg64 (.gpr 2#5) = ptr := by exact hb_wp_a)
    (hfocus : Pre = (ptr ↦₆₄ v0) ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf → StdStatePreserved s0 sf → sf.readReg64 (.gpr 0#5) = v0 →
      RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf ((ptr ↦₆₄ new) ∗ F) post) :
    SepWP P target_pc s0 Pre post := by
  rw [hfocus]
  have hf0 := fetch_at0_ro h; have hf1 := fetch_at_ro 1 (off := 4#64) h
  have hf2 := fetch_at_ro 2 (off := 8#64) h; have hf3 := fetch_at_ro 3 (off := 12#64) h
  have hf4 := fetch_at_ro 4 (off := 16#64) h; have hf5 := fetch_at_ro 5 (off := 20#64) h
  have hf6 := fetch_at_ro 6 (off := 24#64) h; have hf7 := fetch_at_ro 7 (off := 28#64) h
  have hf8 := fetch_at_ro 8 (off := 32#64) h; have hf9 := fetch_at_ro 9 (off := 36#64) h
  have hf10 := fetch_at_ro 10 (off := 40#64) h; have hf11 := fetch_at_ro 11 (off := 44#64) h
  wp_step
  refine step_ldr8_lse_ro (by wp_ro_simp) (by wp_ro_simp) hf1 (by wp_ro_simp; bv_bits) hro ?_
  wp_step; wp_if hcbz
  · wp_step
    suffices hloop : ∀ (k : Nat) (st : State), st.exclFails.length < k →
        st.pc = C.std.cas8AcqAddr + 24#64 → st.status = .Running →
        st.readReg64 (.gpr 16#5) = v0 → st.readReg64 (.gpr 1#5) = new → st.readReg64 (.gpr 2#5) = ptr →
        RoPostFacts C haveLse st.mem → LlscFrameRo s0 st →
        SepWP P target_pc st ((ptr ↦₆₄ v0) ∗ F) post from
      hloop (_ + 1) _ (Nat.lt_succ_self _) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
        (by wp_ro_simp) (by wp_ro_simp) hro (by llsc_ro_inv)
    intro k; induction k with
    | zero => intro _ hk; omega
    | succ k ih =>
      intro st hk hpc_s hrun_s hx16_s hx1_s hx2_s hro_s hinv_s
      refine SepWP.step_ldxr64 hpc_s hrun_s hf6 rfl hx2_s halign (SepLoad64.left (SepLoad64.here rfl)) rfl ?_
      wp_steps 2
      refine step_stxr64_ro (ea := ptr) (val := new) (by wp_ro_simp) (by wp_ro_simp) hf9
        (by wp_ro_simp) halign (by wp_ro_simp) hro_s hd (fun _ m' hro' hm_p => ?_) (fun hfail => ?_)
      · wp_step; wp_step
        exact finish_ro hnext (by have := hinv_s.2.1; wp_ro_simp) (by wp_ro_simp) (by llsc_ro_inv) (by wp_ro_simp) hro'
      · wp_step
        exact ih _ (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using exclFails_tail_lt_ro (by simpa [wp_norm, arm64_norm] using hk) hfail)
          (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) hro_s (by llsc_ro_inv)
  · refine step_cas64_ro (ea := ptr) (new := new) (by wp_ro_simp) (by wp_ro_simp) hf3
      (by wp_ro_simp) halign (by wp_ro_simp) (by wp_ro_simp) hro hd fun m' hro' hm_p => ?_
    wp_step
    exact finish_ro hnext (by wp_ro_simp) (by wp_ro_simp) (by llsc_ro_inv) (by wp_ro_simp) hro'

theorem call_cas4Acq_ro {P : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc ret_pc ptr : BitVec 64} {v0 new : BitVec 32} {s0 : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (h : hasInstrs P C.std.cas4AcqAddr (cas4AcqInstrs C.std))
    (hro : RoPostFacts C haveLse s0.mem) (hd : RoDisj C ptr 4)
    (halign : MemWidth.isAligned .W32 ptr = true)
    (hpc : s0.pc = C.std.cas4AcqAddr := by exact hb_wp_a)
    (hrun : s0.status = .Running := by simp [wp_norm, arm64_norm, *])
    (hlr : s0.readReg64 (.gpr 30#5) = ret_pc := by exact hb_wp_a)
    (hx0 : (s0.readReg64 (.gpr 0#5)).truncate 32 = v0 := by simp [wp_norm, arm64_norm, *])
    (hx1 : (s0.readReg64 (.gpr 1#5)).truncate 32 = new := by simp [wp_norm, arm64_norm, *])
    (hx2 : s0.readReg64 (.gpr 2#5) = ptr := by exact hb_wp_a)
    (hfocus : Pre = (ptr ↦₃₂ v0) ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf → StdStatePreserved s0 sf → sf.readReg64 (.gpr 0#5) = v0.zeroExtend 64 →
      RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf ((ptr ↦₃₂ new) ∗ F) post) :
    SepWP P target_pc s0 Pre post := by
  rw [hfocus]
  have hf0 := fetch_at0_ro h; have hf1 := fetch_at_ro 1 (off := 4#64) h
  have hf2 := fetch_at_ro 2 (off := 8#64) h; have hf3 := fetch_at_ro 3 (off := 12#64) h
  have hf4 := fetch_at_ro 4 (off := 16#64) h; have hf5 := fetch_at_ro 5 (off := 20#64) h
  have hf6 := fetch_at_ro 6 (off := 24#64) h; have hf7 := fetch_at_ro 7 (off := 28#64) h
  have hf8 := fetch_at_ro 8 (off := 32#64) h; have hf9 := fetch_at_ro 9 (off := 36#64) h
  have hf10 := fetch_at_ro 10 (off := 40#64) h; have hf11 := fetch_at_ro 11 (off := 44#64) h
  wp_step
  refine step_ldr8_lse_ro (by wp_ro_simp) (by wp_ro_simp) hf1 (by wp_ro_simp; bv_bits) hro ?_
  wp_step; wp_if hcbz
  · wp_step
    suffices hloop : ∀ (k : Nat) (st : State), st.exclFails.length < k →
        st.pc = C.std.cas4AcqAddr + 24#64 → st.status = .Running →
        (st.readReg64 (.gpr 16#5)).truncate 32 = v0 → (st.readReg64 (.gpr 1#5)).truncate 32 = new →
        st.readReg64 (.gpr 2#5) = ptr → RoPostFacts C haveLse st.mem → LlscFrameRo s0 st →
        SepWP P target_pc st ((ptr ↦₃₂ v0) ∗ F) post from
      hloop (_ + 1) _ (Nat.lt_succ_self _) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp; try bv_bits)
        (by wp_ro_simp) (by wp_ro_simp) hro (by llsc_ro_inv)
    intro k; induction k with
    | zero => intro _ hk; omega
    | succ k ih =>
      intro st hk hpc_s hrun_s hx16_s hx1_s hx2_s hro_s hinv_s
      refine SepWP.step_ldxr32 hpc_s hrun_s hf6 rfl hx2_s halign (SepLoad32.left (SepLoad32.here rfl)) rfl ?_
      wp_steps 2
      refine step_stxr32_ro (ea := ptr) (val := new) (by wp_ro_simp) (by wp_ro_simp) hf9 rfl
        (by wp_ro_simp) halign (by wp_ro_simp) hro_s hd (fun _ m' hro' hm_p => ?_) (fun hfail => ?_)
      · wp_step; wp_step
        exact finish_ro hnext (by have := hinv_s.2.1; wp_ro_simp) (by wp_ro_simp) (by llsc_ro_inv) (by wp_ro_simp; try bv_bits) hro'
      · wp_step
        exact ih _ (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using exclFails_tail_lt_ro (by simpa [wp_norm, arm64_norm] using hk) hfail)
          (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) hro_s (by llsc_ro_inv)
  · refine step_cas32_ro (ea := ptr) (new := new) (by wp_ro_simp) (by wp_ro_simp) hf3
      (by wp_ro_simp) halign (by wp_ro_simp) (by wp_ro_simp) hro hd fun m' hro' hm_p => ?_
    wp_step
    exact finish_ro hnext (by wp_ro_simp) (by wp_ro_simp) (by llsc_ro_inv) (by wp_ro_simp; try bv_bits) hro'

theorem call_swp4Rel_ro {P : Program} {C : HbCliLayout} {haveLse : BitVec 8}
    {target_pc ret_pc ptr : BitVec 64} {v0 new : BitVec 32} {s0 : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (h : hasInstrs P C.std.swp4RelAddr (swp4RelInstrs C.std))
    (hro : RoPostFacts C haveLse s0.mem) (hd : RoDisj C ptr 4)
    (halign : MemWidth.isAligned .W32 ptr = true)
    (hpc : s0.pc = C.std.swp4RelAddr := by exact hb_wp_a)
    (hrun : s0.status = .Running := by simp [wp_norm, arm64_norm, *])
    (hlr : s0.readReg64 (.gpr 30#5) = ret_pc := by exact hb_wp_a)
    (hx0 : (s0.readReg64 (.gpr 0#5)).truncate 32 = new := by simp [wp_norm, arm64_norm, *])
    (hx1 : s0.readReg64 (.gpr 1#5) = ptr := by exact hb_wp_a)
    (hfocus : Pre = (ptr ↦₃₂ v0) ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf → StdStatePreserved s0 sf → sf.readReg64 (.gpr 0#5) = v0.zeroExtend 64 →
      RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf ((ptr ↦₃₂ new) ∗ F) post) :
    SepWP P target_pc s0 Pre post := by
  rw [hfocus]
  have hf0 := fetch_at0_ro h; have hf1 := fetch_at_ro 1 (off := 4#64) h
  have hf2 := fetch_at_ro 2 (off := 8#64) h; have hf3 := fetch_at_ro 3 (off := 12#64) h
  have hf4 := fetch_at_ro 4 (off := 16#64) h; have hf5 := fetch_at_ro 5 (off := 20#64) h
  have hf6 := fetch_at_ro 6 (off := 24#64) h; have hf7 := fetch_at_ro 7 (off := 28#64) h
  have hf8 := fetch_at_ro 8 (off := 32#64) h; have hf9 := fetch_at_ro 9 (off := 36#64) h
  wp_step
  refine step_ldr8_lse_ro (by wp_ro_simp) (by wp_ro_simp) hf1 (by wp_ro_simp; bv_bits) hro ?_
  wp_step; wp_if hcbz
  · wp_step
    suffices hloop : ∀ (k : Nat) (st : State), st.exclFails.length < k →
        st.pc = C.std.swp4RelAddr + 24#64 → st.status = .Running →
        (st.readReg64 (.gpr 16#5)).truncate 32 = new → st.readReg64 (.gpr 1#5) = ptr →
        RoPostFacts C haveLse st.mem → LlscFrameRo s0 st →
        SepWP P target_pc st ((ptr ↦₃₂ v0) ∗ F) post from
      hloop (_ + 1) _ (Nat.lt_succ_self _) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp; try bv_bits)
        (by wp_ro_simp) hro (by llsc_ro_inv)
    intro k; induction k with
    | zero => intro _ hk; omega
    | succ k ih =>
      intro st hk hpc_s hrun_s hx16_s hx1_s hro_s hinv_s
      refine SepWP.step_ldxr32 hpc_s hrun_s hf6 rfl hx1_s halign (SepLoad32.left (SepLoad32.here rfl)) rfl ?_
      refine step_stxr32_ro (ea := ptr) (val := new) (by wp_ro_simp) (by wp_ro_simp) hf7 rfl
        (by wp_ro_simp) halign (by wp_ro_simp) hro_s hd (fun _ m' hro' hm_p => ?_) (fun hfail => ?_)
      · wp_step; wp_step
        exact finish_ro hnext (by have := hinv_s.2.1; wp_ro_simp) (by wp_ro_simp) (by llsc_ro_inv) (by wp_ro_simp; try bv_bits) hro'
      · wp_step
        exact ih _ (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using exclFails_tail_lt_ro (by simpa [wp_norm, arm64_norm] using hk) hfail)
          (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) hro_s (by llsc_ro_inv)
  · refine step_swp32_ro (ea := ptr) (new := new) (by wp_ro_simp) (by wp_ro_simp) hf3
      (by wp_ro_simp) halign (by wp_ro_simp) hro hd fun m' hro' hm_p => ?_
    wp_step
    exact finish_ro hnext (by wp_ro_simp) (by wp_ro_simp) (by llsc_ro_inv) (by wp_ro_simp; try bv_bits) hro'

theorem hbAuxvLookup_eq_find (entries : List (BitVec 64 × BitVec 64)) (tag : BitVec 64) :
    hbAuxvLookup entries tag = ((entries.find? (·.1 == tag)).map Prod.snd).getD 0#64 := by
  unfold hbAuxvLookup; cases entries.find? (·.1 == tag) <;> rfl

theorem pointsToBytes_encodeAuxvBytes_nil (a : BitVec 64) :
    (a ↦ₛ encodeAuxvBytes []) = (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 0#64) := by
  have heq : encodeAuxvBytes [] = unpack64 0#64 ++ unpack64 0#64 := by simp [encodeAuxvBytes_eq_flatMap_bytesLE]; rfl
  rw [heq, pointsToBytes_append, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, unpack64_length]

theorem pointsToBytes_encodeAuxvBytes_cons (a t v : BitVec 64) (rest : List (BitVec 64 × BitVec 64)) :
    (a ↦ₛ encodeAuxvBytes ((t, v) :: rest)) = (a ↦₆₄ t) ∗ ((a + 8#64) ↦₆₄ v) ∗ ((a + 16#64) ↦ₛ encodeAuxvBytes rest) := by
  have heq : encodeAuxvBytes ((t, v) :: rest) = unpack64 t ++ (unpack64 v ++ encodeAuxvBytes rest) := by simp [encodeAuxvBytes_eq_flatMap_bytesLE]; rfl
  rw [heq, pointsToBytes_append, pointsToBytes_append, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, unpack64_length, BitVec.add_assoc]; rfl

theorem step_bl_to {prog : Program} {target_pc pc dst : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf : prog.fetch pc = some (.bl (dst - pc)))
    (hnext : SepWP prog target_pc ((s.writeReg64 .lr (pc + 4#64)).setPC dst) P post) :
    SepWP prog target_pc s P post :=
  SepWP.step_pure (s' := (s.writeReg64 .lr (pc + 4#64)).setPC dst) hpc hrun hf
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bl (dst - pc)) _ rfl]; simp [wp_norm, arm64_norm]; rw [show pc + (dst - pc) = dst by bv_omega])
    rfl hnext

@[local simp] theorem hbExitF_setSigAltStack (s0 s : State) (sas : SigAltStack) :
    HbPostExitFields s0 (s.setSigAltStack sas) ↔ HbPostExitFields s0 s := Iff.rfl

@[local simp, local wp_norm, local arm64_norm] theorem sigAltStack_w64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigAltStack = s.sigAltStack := by cases s; cases r <;> rfl
@[local simp, local wp_norm, local arm64_norm] theorem sigAltStack_w32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).sigAltStack = s.sigAltStack := by cases s; cases r <;> rfl
@[local simp, local wp_norm, local arm64_norm] theorem sigAltStack_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).sigAltStack = s.sigAltStack := by cases s; rfl
@[local simp, local wp_norm, local arm64_norm] theorem sigAltStack_setMem (s : State) (m : Memory) :
    (s.setMem m).sigAltStack = s.sigAltStack := by cases s; rfl
@[local simp, local wp_norm, local arm64_norm] theorem sigAltStack_wReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).sigAltStack = s.sigAltStack := by cases s; cases w <;> cases r <;> rfl
@[local simp, local wp_norm, local arm64_norm] theorem sigAltStack_pstate (s : State) (p : PState) :
    (s.setPState p).sigAltStack = s.sigAltStack := by cases s; rfl

private theorem step_getauxval_scan51 {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.getauxvalAddr (getauxvalInstrs L))
    (he : P.hasCode L.errnoLocationAddr errnoLocationWords)
    {target_pc tp : BitVec 64} {post : State → SepProp → Prop}
    (entries : List (BitVec 64 × BitVec 64)) (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64) :
    ∀ (ptr : BitVec 64) (errno0 : BitVec 32) (s : State) (F : SepProp),
      s.pc = L.getauxvalAddr + 0x1c#64 → s.status = .Running →
      s.readReg64 (.gpr 0#5) = 51#64 → s.readReg64 (.gpr 1#5) = ptr →
      s.tpidrEl0 = tp →
      (∀ (sf : State) (errno1 : BitVec 32), sf.pc = L.getauxvalAddr + 0x54#64 → sf.status = .Running → sf.sp = s.sp →
        sf.readReg64 (.gpr 19#5) = hbAuxvLookup entries 51#64 →
        CalleeSavedPreserved (s.writeReg64 (.gpr 19#5) (hbAuxvLookup entries 51#64)) sf →
        HbPostExitFields s sf → sf.sigAltStack = s.sigAltStack →
        SepWP P target_pc sf ((ptr ↦ₛ encodeAuxvBytes entries) ∗ ((tp - 164#64) ↦₃₂ errno1) ∗ F) post) →
      SepWP P target_pc s ((ptr ↦ₛ encodeAuxvBytes entries) ∗ ((tp - 164#64) ↦₃₂ errno0) ∗ F) post := by
  induction entries with
  | nil =>
    intro ptr errno0 s F hpc hrun hx0 hx1 htp hnext
    have_instrs hc 7 6; have_instrs hc 18 3
    rw [pointsToBytes_encodeAuxvBytes_nil]; wp_steps 3
    refine step_bl_to (pc := L.getauxvalAddr + 72#64) (dst := L.errnoLocationAddr) (by wp_ro_simp) (by wp_ro_simp) hf_18 ?_
    rw [show L.getauxvalAddr + 72#64 + 4#64 = L.getauxvalAddr + 76#64 by bv_lin]; wp_steps 3; clear he; wp_steps 2
    rw [← pointsToBytes_encodeAuxvBytes_nil]
    exact hnext _ 2#32 (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by simp [hbAuxvLookup, wp_norm, arm64_norm])
      (by simp [Arm64.CalleeSavedPreserved, hbAuxvLookup, wp_norm, arm64_norm]) hb_exit_rfl (by wp_ro_simp)
  | cons kv rest ih =>
    rcases kv with ⟨t, v⟩; intro ptr errno0 s F hpc hrun hx0 hx1 htp hnext
    have ht0 : t ≠ 0#64 := hnonull t v (List.mem_cons_self ..); have_instrs hc 7 6; have_instrs hc 16 2
    rw [pointsToBytes_encodeAuxvBytes_cons]; wp_steps 3; wp_if hcbz
    · exact absurd hcbz ht0
    · wp_step; wp_if hbeq
      · subst hbeq; wp_steps 2; rw [← pointsToBytes_encodeAuxvBytes_cons]
        have hfind_eq : hbAuxvLookup ((51#64, v) :: rest) 51#64 = v := by simp [hbAuxvLookup]
        rw [hfind_eq] at hnext
        exact hnext _ errno0 (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
          (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hb_exit_rfl (by wp_ro_simp)
      · have hne_beq : (t == 51#64) = false := beq_eq_false_iff_ne.mpr hbeq
        have hfind_ne : hbAuxvLookup ((t, v) :: rest) 51#64 = hbAuxvLookup rest 51#64 := by simp [hbAuxvLookup, hne_beq]
        wp_steps 2
        have hassoc : (((ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ ((ptr + 16#64) ↦ₛ encodeAuxvBytes rest)) ∗ ((tp - 164#64) ↦₃₂ errno0) ∗ F) =
          ((ptr + 16#64) ↦ₛ encodeAuxvBytes rest) ∗ ((tp - 164#64) ↦₃₂ errno0) ∗ ((ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ F) := by
          apply Entails.antisymm <;> sep_entail
        rw [hassoc]
        refine ih (fun t' v' hm => hnonull t' v' (List.mem_cons_of_mem _ hm)) (ptr + 16#64) errno0 _ _
          (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by simp [wp_norm, arm64_norm, htp])
          fun sf errno1 hpc_f hrun_f hsp_f hx19_f hcs_f hex_f hsas_f => ?_
        have hassoc2 : (((ptr + 16#64) ↦ₛ encodeAuxvBytes rest) ∗ ((tp - 164#64) ↦₃₂ errno1) ∗ ((ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ F)) =
          (ptr ↦ₛ encodeAuxvBytes ((t, v) :: rest)) ∗ ((tp - 164#64) ↦₃₂ errno1) ∗ F := by
          rw [pointsToBytes_encodeAuxvBytes_cons]; apply Entails.antisymm <;> sep_entail
        rw [hassoc2]; rw [hfind_ne] at hnext
        exact hnext sf errno1 hpc_f hrun_f (by simpa [wp_norm, arm64_norm] using hsp_f) hx19_f
          (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
          (HbPostExitFields.trans hb_exit_rfl hex_f) (by simpa [wp_norm, arm64_norm] using hsas_f)

theorem step_getauxval51 {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.getauxvalAddr (getauxvalInstrs L))
    (he : P.hasCode L.errnoLocationAddr errnoLocationWords)
    {target_pc ret_pc auxvAddr : BitVec 64} {entries : List (BitVec 64 × BitVec 64)}
    {errno0 : BitVec 32} {s0 : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hpre : ∀ R : SepProp, s0.mem ⊨ Pre ∗ R →
      s0.mem ⊨ (((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
        (muslErrnoAddr s0 ↦₃₂ errno0) ∗ stackAt s0.sp 0x20) ∗ (F ∗ R))
    (hpc : s0.pc = L.getauxvalAddr) (hrun : s0.status = .Running) (hsp_align : s0.spAligned = true)
    (hlr : s0.readReg64 .x30 = ret_pc) (hx0 : s0.readReg64 .x0 = 51#64)
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hnext : ∀ (sf : State) (errno1 : BitVec 32), sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp →
      sf.spAligned = true → sf.readReg64 .x0 = hbAuxvLookup entries 51#64 →
      CalleeSavedPreserved s0 sf → HbPostExitFields s0 sf → sf.sigAltStack = s0.sigAltStack →
      SepWP P target_pc sf ((((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
        (muslErrnoAddr sf ↦₃₂ errno1) ∗ stackAt s0.sp 0x20) ∗ F) post) :
    SepWP P target_pc s0 Pre post := by
  refine SepWP.weaken_pre_frame (P' := (((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      (muslErrnoAddr s0 ↦₃₂ errno0) ∗ stackAt s0.sp 0x20) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hc 0 7; have_instrs hc 21 4
  have hsp_sub_al : ((s0.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := by
    simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x20#64 hsp_align
  wp_conv_pre => rw [stackAt_eq_cells s0.sp 4]
  simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero,
    sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun w0 => SepWP.exists_elim fun w1 => SepWP.exists_elim fun w2 => SepWP.exists_elim fun w3 => ?_
  wp_steps 7; unfold muslErrnoAddr
  refine SepWP.weaken_pre_frame (P' := (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ ((s0.tpidrEl0 - 164#64) ↦₃₂ errno0) ∗ ?_)
    (fun R hm => by revert hm; sep_frame) ?_
  refine step_getauxval_scan51 hc he entries hnonull _ _ _ _
    (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp) (by simp [wp_norm, arm64_norm])
    fun sf errno1 hpc_f hrun_f hsp_f hx19_f hcs_f hex_f hsas_f => ?_
  have hsp_sf : sf.sp = s0.sp - 32#64 := by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp_f
  have hsp_al_cur : (sf.sp &&& 15#64 == 0#64) = true := by
    rw [hsp_sf]; simpa [State.spAligned, BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x20#64 hsp_align
  have hc0 : s0.sp - 32#64 = sf.sp := hsp_sf.symm
  have hc1 : s0.sp - 24#64 = sf.sp + 8#64 := by rw [hsp_sf]; bv_lin
  have hc2 : s0.sp - 16#64 = sf.sp + 16#64 := by rw [hsp_sf]; bv_lin
  have hsp_end : sf.sp + 32#64 = s0.sp := by rw [hsp_sf]; bv_lin
  have htp_sf : s0.tpidrEl0 = sf.tpidrEl0 := by
    have h := hex_f.2.2.1; simp only [wp_norm, arm64_norm] at h; exact h.symm
  clear he hsp_f hsp_sf; wp_conv_pre => rw [hc0, hc1, hc2, htp_sf]
  wp_steps 4; unfold muslErrnoAddr at hnext
  refine SepWP.weaken_pre_frame (P' := (((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
      ((sf.tpidrEl0 - 164#64) ↦₃₂ errno1) ∗ stackAt s0.sp 0x20) ∗ F)
    (fun R hm => by rw [← hc2, ← hc1, ← hc0] at hm; rw [stackAt_eq_cells s0.sp 4]; fold_stack_cells) ?_
  refine hnext _ errno1 (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    (by wp_ro_simp) ?_ (HbPostExitFields.trans hb_exit_rfl (HbPostExitFields.trans hex_f hb_exit_rfl))
    (by simpa [wp_norm, arm64_norm] using hsas_f)
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with ⟨_, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
  simp only [wp_norm, arm64_norm] at g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
  rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

@[local simp] theorem hbExitF_setPhysMemAvail (s0 s : State) (n : Nat) :
    HbPostExitFields s0 (s.setPhysMemAvail n) ↔ HbPostExitFields s0 s := Iff.rfl

@[local simp] theorem calleeSavedVRegs_setSigAltStack_ro (s : State) (sas : SigAltStack) :
    Arm64.calleeSavedVRegs (s.setSigAltStack sas) = Arm64.calleeSavedVRegs s := rfl

@[local simp] theorem calleeSavedVRegs_setPhysMemAvail_ro (s : State) (n : Nat) :
    Arm64.calleeSavedVRegs (s.setPhysMemAvail n) = Arm64.calleeSavedVRegs s := rfl

@[local simp, local wp_norm, local arm64_norm] theorem bv64_add_sub_cancel_local (a b : BitVec 64) :
    a + (b - a) = b := by bv_lin

@[local simp, local wp_norm, local arm64_norm] theorem bv64_add_add_sub_cancel_local (a b c : BitVec 64) :
    a + (b + (c - (a + b))) = c := by bv_lin

theorem allPerm_not_frozen_of_altstack {uBase : BitVec 64} {uRwSz : Nat} {m : Memory} {Q : SepProp}
    (hbnd : uBase.toNat + 4096 + uRwSz ≤ 2 ^ 64)
    (hm : m ⊨ memRegionProtNone uBase 4096 ∗ memRegion (uBase + 4096#64) uRwSz ∗ Q) :
    m.allPerm (fun p => !p.frozen) uBase (4096 + uRwSz) = true := by
  rw [Memory.allPerm_iff]
  intro i hi
  by_cases h4 : i < 4096
  · have hin4 : ((uBase + BitVec.ofNat 64 i) - uBase).toNat < 4096 := by
      rw [show uBase + BitVec.ofNat 64 i - uBase = BitVec.ofNat 64 i by bv_omega,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h4
    have hp := (IsBlockProtNone.memRegionProtNone uBase 4096).perm_protNone hm hin4
    rw [hp]; rfl
  · have hm_rw : m ⊨ memRegion (uBase + 4096#64) uRwSz ∗ (memRegionProtNone uBase 4096 ∗ Q) :=
      Satisfies.mono (by sep_entail) hm
    rw [memRegion_eq_exists_bytes (uBase + 4096#64) uRwSz (by omega),
        sepExists_sepConj_left, satisfies_sepExists] at hm_rw
    obtain ⟨bs, hm_bs⟩ := hm_rw
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_bs
    have hin : InRegion (uBase + 4096#64) bs.length (uBase + BitVec.ofNat 64 i) := by
      unfold InRegion
      rw [hm_bs.1, show uBase + BitVec.ofNat 64 i - (uBase + 4096#64) = BitVec.ofNat 64 (i - 4096) by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    have hp := (Memory.permNoLazy_eq_some_rw_iff.mp ((IsBlock.pointsToBytes _ _).permNoLazy_rw hm_bs.2 hin)).1
    rw [hp]; rfl

theorem step_syscallRet0 {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hcode : P.hasCode L.syscallRetAddr syscallRetNonnegWords)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x20 ∗ (F ∗ R))
    (hpc : s.pc = L.syscallRetAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbPostExitFields s sf →
      SepWP P target_pc sf (stackAt s.sp 0x20 ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have hhi : ConditionHolds CondCode.HI (addsPState64 0#64 4096#64) = false := by
    dsimp [addsPState64, AddWithCarry64, ConditionHolds]; decide
  have hsp_sub_al : ((s.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := by
    simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align
  rw [stackAt_eq_cells s.sp 4]; unfold_stack_cells 4
  wp_steps 9
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ F) (fun R hm => by rw [stackAt_eq_cells s.sp 4]; fold_stack_cells) ?_
  exact hnext _ (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_align)
    (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by wp_ro_simp) hb_exit_rfl

theorem step_syscallRet0_ro {P : Program} {C : HbCliLayout} {haveLse : BitVec 8} {target_pc ret_pc : BitVec 64}
    (hcode : P.hasCode C.std.syscallRetAddr syscallRetNonnegWords)
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hro : RoPostFacts C haveLse s.mem) (hd : RoDisj C (s.sp - 32#64) 32)
    (hpc : s.pc = C.std.syscallRetAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbPostExitFields s sf → RoPostFacts C haveLse sf.mem →
      SepWP P target_pc sf (stackAt s.sp 0x20 ∗ F) post) :
    SepWP P target_pc s (stackAt s.sp 0x20 ∗ F) post := by
  have hhi : ConditionHolds CondCode.HI (addsPState64 0#64 4096#64) = false := by
    dsimp [addsPState64, AddWithCarry64, ConditionHolds]; decide
  have hsp_sub_al : ((s.sp - 32#64) &&& 0xf#64 == 0#64) = true := by simpa using s.spAligned_sub 0x20#64 hsp_align
  rw [stackAt_eq_cells s.sp 4]; unfold_stack_cells 4
  have hf0 : P.fetch C.std.syscallRetAddr = some (.stp .W64 .x29 .lr (.PreIndex .sp 0xffffffffffffffe0#64)) :=
    Program.fetch_of_hasCode_decodeAt 0 hcode (by bv_lin) (by decide)
  have hf3 : P.fetch (C.std.syscallRetAddr + 12#64) = some (.str .X64 (.gpr 19#5) (.Offset .sp 16#64)) :=
    Program.fetch_of_hasCode_decodeAt 3 hcode (by bv_lin) (by decide)
  refine step_stp64_ro (ea := s.sp - 32#64) (ea2 := s.sp - 24#64) hro (roDisj_sub hd 0 8) (roDisj_sub hd 8 8)
    hpc hrun hf0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_align])
    (show evalAddrMode s (.PreIndex .sp 0xffffffffffffffe0#64) = (s.sp - 32#64, some (.sp, s.sp - 32#64)) by
      simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) rfl
    fun m1 hro1 => ?_
  wp_steps 2
  refine step_str64_ro (ea := s.sp - 16#64) (wb := none) (val := s.readReg64 (.gpr 19#5))
    hro1 (roDisj_sub hd 16 8) (by wp_ro_simp) (by wp_ro_simp) hf3
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al)
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by wp_ro_simp)
    (by wp_sep_access) rfl fun m2 hro2 => ?_
  wp_steps 5
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ F) (fun R hm => by rw [stackAt_eq_cells s.sp 4]; fold_stack_cells) ?_
  exact hnext _ (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_align)
    (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by wp_ro_simp) hb_exit_rfl hro2

theorem step_syscallRet_neg1 {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    {errno0 : BitVec 32}
    (herr : P.hasCode L.errnoLocationAddr errnoLocationWords)
    (hcode : P.hasCode L.syscallRetAddr syscallRetNonnegWords)
    (hbl : P.fetch (L.syscallRetAddr + 0x24#64) = some (.bl (L.errnoLocationAddr - (L.syscallRetAddr + 0x24#64))))
    (herr_w : P.hasCode (L.syscallRetAddr + 0x28#64)
      [0xaa0003e1#32, 0x4b1303f3#32, 0x92800000#32, 0xb9000033#32, 0x17fffff8#32])
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ (stackAt s.sp 0x20 ∗ (muslErrnoAddr s ↦₃₂ errno0)) ∗ (F ∗ R))
    (hpc : s.pc = L.syscallRetAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 0xffffffffffffffff#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → HbPostExitFields s sf →
      SepWP P target_pc sf ((stackAt s.sp 0x20 ∗ (muslErrnoAddr sf ↦₃₂ 1#32)) ∗ F) post) :
    SepWP P target_pc s Pre post := by
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ ((muslErrnoAddr s ↦₃₂ errno0) ∗ F))
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have hhi : ConditionHolds CondCode.HI (addsPState64 0xffffffffffffffff#64 4096#64) = true := by
    rw [conditionHolds_hi_addsPState64]; decide
  have hsp_sub_al : ((s.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := by
    simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align
  rw [stackAt_eq_cells s.sp 4]; unfold_stack_cells 4
  wp_steps 6
  refine step_bl_to (pc := L.syscallRetAddr + 0x24#64) (dst := L.errnoLocationAddr) (by wp_ro_simp) (by wp_ro_simp) hbl ?_
  rw [show L.syscallRetAddr + 0x24#64 + 4#64 = L.syscallRetAddr + 0x28#64 by bv_lin]
  unfold muslErrnoAddr
  wp_steps 3; clear herr; wp_steps 5; clear herr_w
  wp_steps 3
  unfold muslErrnoAddr at hnext
  refine SepWP.weaken_pre_frame (P' := (stackAt s.sp 0x20 ∗ ((s.tpidrEl0 - 164#64) ↦₃₂ 1#32)) ∗ F)
    (fun R hm => by rw [sepConj_assoc, sepConj_assoc] at hm ⊢; rw [stackAt_eq_cells s.sp 4]; fold_stack_cells) ?_
  exact hnext _ (by wp_ro_simp) (by wp_ro_simp) (by wp_ro_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_align)
    (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hb_exit_rfl

theorem step_svc_sigaltstack_eperm {P : Program} {target_pc pc uss ssSp ssSize : BitVec 64}
    {ssFlags pad : BitVec 32} {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 132#64)
    (huss : s.readReg64 .x0 = uss)
    (huss_ne : uss ≠ 0#64) (huss_fit : uss.toNat + 24 ≤ 2 ^ 64)
    (hon : s.sigAltStack.onSigStack s.sp = true)
    (hnext : SepWP P target_pc ((s.writeReg64 .x0 0xffffffffffffffff#64).setPC (pc + 4#64))
      (((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ ssFlags) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗ F) post) :
    SepWP P target_pc s
      (((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ ssFlags) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗ F) post := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  have heval : P.evalInst (.system false 0#16) s = execSigaltstack s := by
    rw [_root_.Arm64.Program.evalInst_svc0, hsvc, evalSvc_standard]
    simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
      Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable,
      wp_norm, arm64_norm, hx8]
  rw [heval]
  have hm_u : s.mem ⊨ ((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ ssFlags) ∗
      ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗ (F ∗ R) := by ac_nf at hm ⊢
  have h24 : ((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ ssFlags) ∗
      ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) =
      (uss ↦ₛ (unpack64 ssSp ++ (unpack32 ssFlags ++ (unpack32 pad ++ unpack64 ssSize)))) := by
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
    simp only [unpack64_length, unpack32_length, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo32_eq_pointsToBytes]
    have ha12 : uss + 8#64 + 4#64 = uss + 12#64 := by bv_omega
    have ha16 : uss + 12#64 + 4#64 = uss + 16#64 := by bv_omega
    rw [ha12, ha16]
  rw [h24] at hm_u
  have hlen24 : (unpack64 ssSp ++ (unpack32 ssFlags ++ (unpack32 pad ++ unpack64 ssSize))).length = 24 := by
    simp only [List.length_append, unpack64_length, unpack32_length]
  have hcr : s.mem.canRead uss 24 = true :=
    hlen24 ▸ (IsBlock.pointsToBytes uss _).canRead (by omega) hm_u
  have hap : s.mem.allPerm (·.r) uss 24 = true := ((Bool.and_eq_true _ _).mp hcr).1
  have hu_ne : (uss != 0#64) = true := bne_iff_ne.mpr huss_ne
  have hfit_d : decide (uss.toNat + 24 ≤ 2 ^ 64) = true := decide_eq_true huss_fit
  have hexec : execSigaltstack s = (s.writeReg64 .x0 0xffffffffffffffff#64).setPC (pc + 4#64) := by
    dsimp only [execSigaltstack]
    rw [huss, hu_ne, hfit_d, hap, hcr, hon]
    simp [EPERM, State.advancePC, State.setPC, hpc]
  rw [hexec]
  exact SepWP.to_reaches_pc hnext hm

end CaseStudies.Hashbrown.Proofs.StdCli
