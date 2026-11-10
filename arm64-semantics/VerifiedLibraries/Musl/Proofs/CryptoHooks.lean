/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.Common
public import VerifiedLibraries.Musl.Spec
public import VerifiedLibraries.Musl.Proofs.Code
public import VerifiedLibraries.Musl.Proofs.MemcmpProof
public import VerifiedLibraries.RustStd.Spec
public import ProofLib.Hoare.LibcHooks

/-!
# Downstream `crypto-verification`, `LibcHooks`, and `SubroutineHook` Bridges

Defines the external C hook contracts used by `crypto-verification`, proves `subroutine_ok`
implications from `MuslString`'s canonical specifications to `crypto*Spec`, `LibcHooks`, and
`RustStd.memcpySpec`, and lifts verified `muslStringLib` subroutines to cross-binary hooks via
`Spec.liftedSubroutineHook`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 ProofLib

/-! ## `crypto-verification` (`cExtern`) hook specifications -/

/-- Default stack allowance (`4096` bytes) for external C hooks in `crypto-verification`. -/
abbrev externStack : Nat := 4096

/-- External C hook wrapper for `crypto-verification`: pairs register preconditions `regs x s0`,
    spatial precondition `pre x`, and `stackAt s0.sp externStack` with postcondition
    `post x sf ∗ stackAt s0.sp externStack`. -/
def cExtern {α : Type} (regs : α → State → Prop) (pre : α → SepProp)
    (post : α → State → SepProp) : Spec α where
  pre x s0 := ⌜regs x s0⌝ ∗ pre x ∗ stackAt s0.sp externStack
  post x s0 sf := post x sf ∗ stackAt s0.sp externStack

/-- `crypto-verification`'s `memcpySpec` (`src ↦ₛ bs`). -/
def cryptoMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  cExtern
    (fun (dst, src, bs) s =>
      s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (fun (dst, src, bs) => memRegion dst bs.length ∗ (src ↦ₛ bs))
    (fun (dst, src, bs) sf => ⌜sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs))

/-- `crypto-verification`'s `memcpyROSpec` (`src ↦ᵣ bs`). -/
def cryptoMemcpyROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  cExtern
    (fun (dst, src, bs) s =>
      s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (fun (dst, src, bs) => memRegion dst bs.length ∗ (src ↦ᵣ bs))
    (fun (dst, src, bs) sf => ⌜sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs))

/-- `crypto-verification`'s `memmoveSpec` (with non-wrapping buffer bounds
    `base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63`). -/
def cryptoMemmoveSpec : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  cExtern
    (fun (base, buf, dst, src, len) s =>
      s.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧
      s.readReg64 .x1 = base + BitVec.ofNat 64 src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 len ∧
      dst + len ≤ buf.length ∧ src + len ≤ buf.length ∧
      base.toNat + buf.length ≤ 2 ^ 64 ∧ buf.length < 2 ^ 63)
    (fun (base, buf, _, _, _) => base ↦ₛ buf)
    (fun (base, buf, dst, src, len) sf =>
      ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst⌝ ∗
      (base ↦ₛ moveBytes buf dst src len))

/-- `crypto-verification`'s `memsetSpec`. -/
def cryptoMemsetSpec : Spec (BitVec 64 × BitVec 8 × Nat) :=
  cExtern
    (fun (p, c, n) s =>
      s.readReg64 .x0 = p ∧ (s.readReg32 .x1).truncate 8 = c ∧
      (s.readReg64 .x2).toNat = n)
    (fun (p, _, n) => memRegion p n)
    (fun (p, c, n) sf =>
      ⌜sf.readReg64 .x0 = p⌝ ∗ (p ↦ₛ List.replicate n c))

/-- `crypto-verification`'s `bcmpSpec` (`p ↦ₛ bs`, `q ↦ₛ cs`). -/
def cryptoBcmpSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
  cExtern
    (fun (p, q, bs, cs) s =>
      s.readReg64 .x0 = p ∧ s.readReg64 .x1 = q ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ cs.length = bs.length)
    (fun (p, q, bs, cs) => (p ↦ₛ bs) ∗ (q ↦ₛ cs))
    (fun (p, q, bs, cs) sf =>
      ⌜(sf.readReg32 .x0 = 0#32 ↔ bs = cs)⌝ ∗ (p ↦ₛ bs) ∗ (q ↦ₛ cs))

/-- `crypto-verification`'s read-only `bcmpROSpec` (`p ↦ᵣ bs`, `q ↦ᵣ cs`). -/
def cryptoBcmpROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
  cExtern
    (fun (p, q, bs, cs) s =>
      s.readReg64 .x0 = p ∧ s.readReg64 .x1 = q ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ cs.length = bs.length)
    (fun (p, q, bs, cs) => (p ↦ᵣ bs) ∗ (q ↦ᵣ cs))
    (fun (p, q, bs, cs) sf =>
      ⌜(sf.readReg32 .x0 = 0#32 ↔ bs = cs)⌝ ∗ (p ↦ᵣ bs) ∗ (q ↦ᵣ cs))

/-- `cryptoBcmpSpec` strengthened with `MemcmpStatePreserved s0 sf`
    (`sf.mem = s0.mem ∧ sf.vregs = s0.vregs ∧ ProcessFieldsPreserved s0 sf`). -/
abbrev cryptoBcmpPreservingSpec := withMemcmpPreserved cryptoBcmpSpec

/-- `cryptoBcmpROSpec` strengthened with `MemcmpStatePreserved s0 sf`
    (`sf.mem = s0.mem ∧ sf.vregs = s0.vregs ∧ ProcessFieldsPreserved s0 sf`). -/
abbrev cryptoBcmpROPreservingSpec := withMemcmpPreserved cryptoBcmpROSpec

/-! ## `subroutine_ok` implications -/

private theorem cryptoHooks_toNat_of_eq_ofNat {x : BitVec 64} {n : Nat}
    (hx : x = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) : x.toNat = n := by
  rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem cryptoMemcpy_ok_of_memcpy_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry memcpySpec) :
    subroutine_ok prog entry cryptoMemcpySpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  dsimp only [cryptoMemcpySpec, cExtern] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have hdst : s0.mem ⊨ memRegion dst bs.length ∗ (stackAt s0.sp externStack ∗ ((src ↦ₛ bs) ∗ R)) :=
    Satisfies.of_eq hmem
  have hlt : bs.length < 2 ^ 64 := len_lt_of_memRegion_hookFrame hdst
  refine ⟨(dst, src, s0.readReg64 .x2, bs), stackAt s0.sp externStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes,
      CType.SliceLen, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, cryptoHooks_toNat_of_eq_ofNat hx2 hlt, Satisfies.of_eq hmem⟩
  · dsimp only [memcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes] at hpost
    dsimp only [cryptoMemcpySpec, cExtern]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

theorem cryptoMemcpyRO_ok_of_memcpyRO_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry memcpyROSpec) :
    subroutine_ok prog entry cryptoMemcpyROSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  dsimp only [cryptoMemcpyROSpec, cExtern] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  have hdst : s0.mem ⊨ memRegion dst bs.length ∗ (stackAt s0.sp externStack ∗ ((src ↦ᵣ bs) ∗ R)) :=
    Satisfies.of_eq hmem
  have hlt : bs.length < 2 ^ 64 := len_lt_of_memRegion_hookFrame hdst
  refine ⟨(dst, src, s0.readReg64 .x2, bs), stackAt s0.sp externStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memcpyROSpec, CType.MutSlice8, CType.Bytes, RoSlice8,
      CType.SliceLen, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, cryptoHooks_toNat_of_eq_ofNat hx2 hlt, Satisfies.of_eq hmem⟩
  · dsimp only [memcpyROSpec, CType.MutSlice8, CType.Bytes, RoSlice8] at hpost
    dsimp only [cryptoMemcpyROSpec, cExtern]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

theorem cryptoMemmove_ok_of_memmove_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry memmoveSpec) :
    subroutine_ok prog entry cryptoMemmoveSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨base, buf, dst, src, len⟩ R s0 hpre
  dsimp only [cryptoMemmoveSpec, cExtern] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hdst, hsrc, hwrap, hsmall⟩, hmem⟩ := hpre
  have hx2n := cryptoHooks_toNat_of_eq_ofNat hx2 (by omega)
  refine ⟨(base + BitVec.ofNat 64 dst, base + BitVec.ofNat 64 src, s0.readReg64 .x2,
      base, buf, dst, src), stackAt s0.sp externStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memmoveSpec, CType.InteriorPtr, CType.SizeT, CType.scalarTy,
      CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, by omega, by omega, hwrap, hsmall, Satisfies.of_eq hmem⟩
  · dsimp only [memmoveSpec, CType.InteriorPtr] at hpost
    dsimp only [cryptoMemmoveSpec, cExtern]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj, hx2n] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

theorem cryptoMemset_ok_of_memset_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry memsetSpec) :
    subroutine_ok prog entry cryptoMemsetSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨p, c, n⟩ R s0 hpre
  dsimp only [cryptoMemsetSpec, cExtern] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  refine ⟨(p, s0.readReg32 .x1, s0.readReg64 .x2), stackAt s0.sp externStack ∗ R, ?_,
    fun sf hpost => ?_⟩
  · dsimp only [memsetSpec, CType.MutSlice8, CType.Bytes, CType.U32, CType.SizeT,
      CType.scalarTy, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, hx2]
    exact ⟨⟨hx0, trivial⟩, Satisfies.of_eq hmem⟩
  · dsimp only [memsetSpec, CType.MutSlice8, CType.Bytes] at hpost
    dsimp only [cryptoMemsetSpec, cExtern]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and] at hpost ⊢
    have hc : (s0.readReg32 .x1).setWidth 8 = c := hx1
    rw [hx2, hc] at hpost
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

theorem cryptoBcmp_ok_of_bcmp_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry bcmpSpec) :
    subroutine_ok prog entry cryptoBcmpSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨p, q, bs, cs⟩ R s0 hpre
  dsimp only [cryptoBcmpSpec, cExtern] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hcs⟩, hmem⟩ := hpre
  have hp : s0.mem ⊨ (p ↦ₛ bs) ∗ ((q ↦ₛ cs) ∗ (stackAt s0.sp externStack ∗ R)) :=
    Satisfies.of_eq hmem
  have hreg : s0.mem ⊨ memRegion p bs.length ∗ (stackAt s0.sp externStack ∗ ((q ↦ₛ cs) ∗ R)) :=
    Satisfies.of_eq (Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion p bs)) hp)
  have hx2n := cryptoHooks_toNat_of_eq_ofNat hx2 (len_lt_of_memRegion_hookFrame hreg)
  refine ⟨(p, q, s0.readReg64 .x2, bs, cs), stackAt s0.sp externStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [bcmpSpec, CType.ShrSlice8, CType.Bytes, SliceLenPair, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2n, by omega, Satisfies.of_eq hmem⟩
  · dsimp only [bcmpSpec, CType.ShrSlice8, CType.Bytes, CType.I32,
      CType.scalarTy, CType.SemType.valWf] at hpost
    dsimp only [cryptoBcmpSpec, cExtern]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨by rw [hpost.1]; exact memcmpBytes_eq_zero_iff hcs.symm, Satisfies.of_eq hpost.2⟩

theorem cryptoBcmpRO_ok_of_bcmpRO_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry bcmpROSpec) :
    subroutine_ok prog entry cryptoBcmpROSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨p, q, bs, cs⟩ R s0 hpre
  dsimp only [cryptoBcmpROSpec, cExtern] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hcs⟩, hmem⟩ := hpre
  have hp : s0.mem ⊨ (p ↦ᵣ bs) ∗ (stackAt s0.sp externStack ∗ ((q ↦ᵣ cs) ∗ R)) :=
    Satisfies.of_eq hmem
  have hx2n := cryptoHooks_toNat_of_eq_ofNat hx2
    (pointsToBytesRO_len_lt_of_sepConj_memRegion (by decide) hp)
  refine ⟨(p, q, s0.readReg64 .x2, bs, cs), stackAt s0.sp externStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [bcmpROSpec, RoSlice8, SliceLenPair, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2n, by omega, Satisfies.of_eq hmem⟩
  · dsimp only [bcmpROSpec, RoSlice8, CType.I32, CType.scalarTy, CType.SemType.valWf] at hpost
    dsimp only [cryptoBcmpROSpec, cExtern]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨by rw [hpost.1]; exact memcmpBytes_eq_zero_iff hcs.symm, Satisfies.of_eq hpost.2⟩

theorem cryptoBcmpPreserving_ok_of_bcmpPreserving_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry bcmpPreservingSpec) :
    subroutine_ok prog entry cryptoBcmpPreservingSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨p, q, bs, cs⟩ R s0 hpre
  dsimp only [cryptoBcmpPreservingSpec, withMemcmpPreserved, cryptoBcmpSpec, cExtern] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hcs⟩, hmem⟩ := hpre
  have hp : s0.mem ⊨ (p ↦ₛ bs) ∗ ((q ↦ₛ cs) ∗ (stackAt s0.sp externStack ∗ R)) :=
    Satisfies.of_eq hmem
  have hreg : s0.mem ⊨ memRegion p bs.length ∗ (stackAt s0.sp externStack ∗ ((q ↦ₛ cs) ∗ R)) :=
    Satisfies.of_eq (Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion p bs)) hp)
  have hx2n := cryptoHooks_toNat_of_eq_ofNat hx2 (len_lt_of_memRegion_hookFrame hreg)
  refine ⟨(p, q, s0.readReg64 .x2, bs, cs), stackAt s0.sp externStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [bcmpPreservingSpec, withMemcmpPreserved, bcmpSpec, CType.ShrSlice8, CType.Bytes,
      SliceLenPair, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2n, by omega, Satisfies.of_eq hmem⟩
  · dsimp only [bcmpPreservingSpec, withMemcmpPreserved, bcmpSpec, CType.ShrSlice8, CType.Bytes,
      CType.I32, CType.scalarTy, CType.SemType.valWf] at hpost
    dsimp only [cryptoBcmpPreservingSpec, withMemcmpPreserved, cryptoBcmpSpec, cExtern]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, by rw [hpost.2.1]; exact memcmpBytes_eq_zero_iff hcs.symm,
      Satisfies.of_eq hpost.2.2⟩

theorem cryptoBcmpROPreserving_ok_of_bcmpROPreserving_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry bcmpROPreservingSpec) :
    subroutine_ok prog entry cryptoBcmpROPreservingSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨p, q, bs, cs⟩ R s0 hpre
  dsimp only [cryptoBcmpROPreservingSpec, withMemcmpPreserved, cryptoBcmpROSpec, cExtern] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hcs⟩, hmem⟩ := hpre
  have hp : s0.mem ⊨ (p ↦ᵣ bs) ∗ (stackAt s0.sp externStack ∗ ((q ↦ᵣ cs) ∗ R)) :=
    Satisfies.of_eq hmem
  have hx2n := cryptoHooks_toNat_of_eq_ofNat hx2
    (pointsToBytesRO_len_lt_of_sepConj_memRegion (by decide) hp)
  refine ⟨(p, q, s0.readReg64 .x2, bs, cs), stackAt s0.sp externStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [bcmpROPreservingSpec, withMemcmpPreserved, bcmpROSpec, RoSlice8,
      SliceLenPair, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2n, by omega, Satisfies.of_eq hmem⟩
  · dsimp only [bcmpROPreservingSpec, withMemcmpPreserved, bcmpROSpec, RoSlice8,
      CType.I32, CType.scalarTy, CType.SemType.valWf] at hpost
    dsimp only [cryptoBcmpROPreservingSpec, withMemcmpPreserved, cryptoBcmpROSpec, cExtern]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, by rw [hpost.2.1]; exact memcmpBytes_eq_zero_iff hcs.symm,
      Satisfies.of_eq hpost.2.2⟩

theorem libcMemcpy_ok_of_memcpy_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := 4096) (h : subroutine_ok prog entry memcpySpec) :
    subroutine_ok prog entry (ProofLib.libcMemcpySpec hookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  dsimp only [ProofLib.libcMemcpySpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  refine ⟨(dst, src, s0.readReg64 .x2, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes,
      CType.SliceLen, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2, Satisfies.of_eq hmem⟩
  · dsimp only [memcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes] at hpost
    dsimp only [ProofLib.libcMemcpySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

theorem libcMemcpyRO_ok_of_memcpyRO_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := 4096) (h : subroutine_ok prog entry memcpyROSpec) :
    subroutine_ok prog entry (ProofLib.libcMemcpyROSpec hookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  dsimp only [ProofLib.libcMemcpyROSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  refine ⟨(dst, src, s0.readReg64 .x2, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memcpyROSpec, CType.MutSlice8, CType.Bytes, RoSlice8,
      CType.SliceLen, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2, Satisfies.of_eq hmem⟩
  · dsimp only [memcpyROSpec, CType.MutSlice8, CType.Bytes, RoSlice8] at hpost
    dsimp only [ProofLib.libcMemcpyROSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

theorem libcMemset_ok_of_memset_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := 4096) (h : subroutine_ok prog entry memsetSpec) :
    subroutine_ok prog entry (ProofLib.libcMemsetSpec hookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨ptr, c, len⟩ R s0 hpre
  dsimp only [ProofLib.libcMemsetSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  refine ⟨(ptr, s0.readReg32 .x1, s0.readReg64 .x2), stackAt s0.sp hookStack ∗ R, ?_,
    fun sf hpost => ?_⟩
  · dsimp only [memsetSpec, CType.MutSlice8, CType.Bytes, CType.U32, CType.SizeT,
      CType.scalarTy, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, hx2]
    exact ⟨⟨hx0, trivial⟩, Satisfies.of_eq hmem⟩
  · dsimp only [memsetSpec, CType.MutSlice8, CType.Bytes] at hpost
    dsimp only [ProofLib.libcMemsetSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and] at hpost ⊢
    have hc : (s0.readReg32 .x1).setWidth 8 = c := hx1
    rw [hx2, hc] at hpost
    exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

theorem vecMemcpy_ok_of_memcpy_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry memcpySpec) :
    subroutine_ok prog entry VerifiedLibraries.RustStd.memcpySpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs, sp⟩ R s0 hpre
  dsimp only [VerifiedLibraries.RustStd.memcpySpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩ := hpre
  have hdst : s0.mem ⊨ memRegion dst bs.length ∗ (VerifiedLibraries.RustStd.hookFrame sp ∗ ((src ↦ₛ bs) ∗ R)) :=
    Satisfies.of_eq hmem
  have hlt : bs.length < 2 ^ 64 := len_lt_of_memRegion_hookFrame hdst (by decide)
  refine ⟨(dst, src, s0.readReg64 .x2, bs), VerifiedLibraries.RustStd.hookFrame sp ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes,
      CType.SliceLen, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, cryptoHooks_toNat_of_eq_ofNat hx2 hlt, Satisfies.of_eq hmem⟩
  · dsimp only [memcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes] at hpost
    dsimp only [VerifiedLibraries.RustStd.memcpySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and] at hpost ⊢
    exact Satisfies.of_eq hpost.2

/-! ## `Spec.liftedSubroutineHook` bridges for `muslStringLib` -/

private theorem cryptoHooks_placeable_baseValid {pl : Obj.Placement}
    (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    (muslStringProg pl hooks).base.toNat % 4 = 0 ∧
      (muslStringProg pl hooks).base.toNat + (muslStringProg pl hooks).code.length ≤ 2 ^ 64 := by
  rw [muslStringProg, Obj.PlacedLib.program_base, Obj.PlacedLib.program_code,
    Obj.CodeBlock.length_patched_of_aligned pl hP.text.len_aligned]
  exact ⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hP.text.align_pos.2)
    (Nat.dvd_of_mod_eq_zero hP.text.base_aligned)), hP.text.no_wrap⟩

private theorem cryptoHooks_noRO_stackFrameSlotsCont (sp : BitVec 64) (k : Nat) :
    ∀ (n : Nat) (cont : SepProp → SepProp),
      (∀ P, SepProp.NoRO P → SepProp.NoRO (cont P)) →
      SepProp.NoRO (stackFrameSlotsCont sp k n cont)
  | 0, _, hcont => hcont _ SepProp.NoRO.emp
  | 1, _, hcont => SepProp.NoRO.sepExists fun _ => hcont _ (SepProp.NoRO.pointsTo64 _ _)
  | n + 2, _, hcont =>
    SepProp.NoRO.sepExists fun _ =>
      cryptoHooks_noRO_stackFrameSlotsCont sp k (n + 1) _ fun _ hP =>
        hcont _ (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo64 _ _) hP)

private theorem cryptoHooks_noRO_stackFrameAt (sp : BitVec 64) (n : Nat) :
    SepProp.NoRO (stackFrameAt sp n) := by
  unfold stackFrameAt stackFrameSlotsFrom
  split
  · exact SepProp.NoRO.emp
  · split
    · exact cryptoHooks_noRO_stackFrameSlotsCont sp 0 (n / 8) id fun _ h => h
    · exact SepProp.NoRO.memRegion _ _

/-- Lift any verified subroutine `name` of `muslStringProg pl hooks` with a `SepProp.NoRO`
    postcondition to a cross-binary hook satisfying
    `Spec.liftedSubroutineHook (muslStringProg pl hooks) name spec`. -/
theorem muslStringLiftedSubroutineHook_ok {S β : Type} [ToBaseSpec S β]
    {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (name : String) (spec : S)
    (h_sub : subroutine_ok (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr name)
      (ToBaseSpec.toSpec spec pl.base))
    (h_noRO : ∀ y s0' sf', SepProp.NoRO ((ToBaseSpec.toSpec spec pl.base).post y s0' sf'))
    (h_pan : ∀ y s0' sf', (ToBaseSpec.toSpec spec pl.base).onPanic y s0' sf' = ⌜False⌝ := by
      intros; rfl)
    (h_ex : ∀ y code s0' sf', (ToBaseSpec.toSpec spec pl.base).onExit y code s0' sf' = ⌜False⌝ := by
      intros; rfl)
    (h_oom : ∀ y s0' sf', (ToBaseSpec.toSpec spec pl.base).onOom y s0' sf' = ⌜False⌝ := by
      intros; rfl) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr name))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) name spec) := by
  obtain ⟨hal, hlen⟩ := cryptoHooks_placeable_baseValid hooks hP
  have hpos : 0 < VerifiedLibraries.muslStringLib.text.code.length := by
    have hchk : VerifiedLibraries.muslStringLib.text.checkSegment 0 memcpyWords [] = true := by
      decide +kernel
    simp only [Obj.CodeBlock.checkSegment, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨_, hpos'⟩, _⟩, _⟩, hwords⟩ := hchk
    have ⟨hlen', _⟩ := Obj.CodeBlock.segWordsOk_spec hwords
    rw [List.length_drop] at hlen'
    omega
  have hext : (muslStringProg pl hooks).externAt? ((muslStringProg pl hooks).base + 1#64) = none := by
    rw [muslStringProg, Obj.PlacedLib.program_base]
    exact Obj.PlacedLib.externAt?_base_add_one_of_pos hP.text hpos
  exact subroutineHook_ok_with_codeRegion hal hlen hext
    h_sub (fun _ _ => Entails.refl _)
    (fun _ _ sf' => Entails.sepExists_right sf' (Entails.pure_right rfl (Entails.refl _)))
    (fun y _ sf' => h_noRO y _ sf')
    (fun y _ _ sf' _ hp => by rw [h_pan] at hp; exact not_satisfies_false_sepConj hp)
    (fun y code _ _ sf' _ he => by rw [h_ex] at he; exact not_satisfies_false_sepConj he)
    (fun y _ _ _ sf' _ _ _ ho => by rw [h_oom] at ho; exact (not_satisfies_false_sepConj ho).elim)

local macro "prove_musl_string_noRO" : tactic =>
  `(tactic| (
    intro y s0' sf'
    dsimp only [ToBaseSpec.toSpec,
      memcpySpec, memmoveSpec, memsetSpec, memcmpSpec, bcmpSpec,
      memchrSpec, memrchrSpec, memccpySpec, mempcpySpec, memmemSpec,
      cryptoMemcpySpec, cryptoMemmoveSpec, cryptoMemsetSpec, cryptoBcmpSpec, cExtern,
      CType.MutSlice8, CType.ShrSlice8, CType.Bytes, CType.InteriorPtr,
      CType.I32, CType.scalarTy, PrefixBuf]
    repeat' first
      | apply SepProp.NoRO.sepConj
      | apply SepProp.NoRO.pointsToBytes
      | apply SepProp.NoRO.memRegion
      | apply cryptoHooks_noRO_stackFrameAt
      | apply SepProp.NoRO.pure
      | apply SepProp.NoRO.emp))

theorem memcpyLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memcpy" memcpySpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memcpy"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memcpy" memcpySpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memcpy" memcpySpec h_sub (by prove_musl_string_noRO)

theorem memmoveLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memmove" memmoveSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memmove"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memmove" memmoveSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memmove" memmoveSpec h_sub (by prove_musl_string_noRO)

theorem memsetLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memset" memsetSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memset"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memset" memsetSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memset" memsetSpec h_sub (by prove_musl_string_noRO)

theorem memcmpLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memcmp" memcmpSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memcmp"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memcmp" memcmpSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memcmp" memcmpSpec h_sub (by prove_musl_string_noRO)

theorem bcmpLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "bcmp" bcmpSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "bcmp"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "bcmp" bcmpSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "bcmp" bcmpSpec h_sub (by prove_musl_string_noRO)

theorem memchrLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memchr" memchrSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memchr"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memchr" memchrSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memchr" memchrSpec h_sub (by prove_musl_string_noRO)

theorem memrchrLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memrchr" memrchrSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memrchr"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memrchr" memrchrSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memrchr" memrchrSpec h_sub (by prove_musl_string_noRO)

theorem memccpyLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memccpy" memccpySpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memccpy"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memccpy" memccpySpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memccpy" memccpySpec h_sub (by prove_musl_string_noRO)

theorem mempcpyLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "mempcpy" mempcpySpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "mempcpy"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "mempcpy" mempcpySpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "mempcpy" mempcpySpec h_sub (by prove_musl_string_noRO)

theorem memmemLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memmem" memmemSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memmem"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memmem" memmemSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memmem" memmemSpec h_sub (by prove_musl_string_noRO)

theorem cryptoMemcpyLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memcpy" memcpySpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memcpy"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memcpy" cryptoMemcpySpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memcpy" cryptoMemcpySpec
    (cryptoMemcpy_ok_of_memcpy_ok h_sub) (by prove_musl_string_noRO)

theorem cryptoMemmoveLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memmove" memmoveSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memmove"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memmove" cryptoMemmoveSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memmove" cryptoMemmoveSpec
    (cryptoMemmove_ok_of_memmove_ok h_sub) (by prove_musl_string_noRO)

theorem cryptoMemsetLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "memset" memsetSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "memset"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "memset" cryptoMemsetSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "memset" cryptoMemsetSpec
    (cryptoMemset_ok_of_memset_ok h_sub) (by prove_musl_string_noRO)

theorem cryptoBcmpLiftedHook_ok {pl : Obj.Placement} (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "bcmp" bcmpSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "bcmp"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "bcmp" cryptoBcmpSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "bcmp" cryptoBcmpSpec
    (cryptoBcmp_ok_of_bcmp_ok h_sub) (by prove_musl_string_noRO)

theorem cryptoBcmpPreservingLiftedHook_ok {pl : Obj.Placement}
    (hooks : String → Option (State → State))
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (h_sub : (muslStringProg pl hooks).subroutineOk "bcmp" bcmpPreservingSpec) :
    HookOk (subroutineHook (muslStringProg pl hooks) ((muslStringProg pl hooks).fnAddr "bcmp"))
      (Spec.liftedSubroutineHook (muslStringProg pl hooks) "bcmp" cryptoBcmpPreservingSpec) :=
  muslStringLiftedSubroutineHook_ok hooks hP "bcmp" cryptoBcmpPreservingSpec
    (cryptoBcmpPreserving_ok_of_bcmpPreserving_ok h_sub) (by prove_musl_string_noRO)

end VerifiedLibraries.Musl
