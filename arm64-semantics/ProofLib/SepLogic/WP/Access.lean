/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.Abi.Aapcs
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Safety
public import ProofLib.VCGen
public import ProofLib.LitNorm
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.CondClassify
public import ProofLib.BV.Arith
public import ProofLib.SepLogic.ByteRegion

/-!
# Spatial Load and Store Witnesses

Constructors for `SepLoad8`/`16`/`32`/`64` and `SepStore8`/`16`/`32`/`64` over typed cells,
read-only byte regions (`↦ᵣ`), lazy-free cells (`↦ₗ`), and writable byte slices (`↦ₛ`), together
with structural spine lemmas (`.left`, `.right`, `.here`) and symbolic byte-offset normalization
used by `wp_sep_access`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Focused Spatial Context Witnesses -/

theorem SepLoad8.of_eq {a : BitVec 64} {v : BitVec 8} {P F : SepProp}
    (h : P = (a ↦₈ v) ∗ F) : SepLoad8 a P v :=
  ⟨fun hm => (IsBlock.pointsTo8 a v).read (by rw [h, sepConj_assoc] at hm; exact hm),
   fun hm => (IsBlock.pointsTo8 a v).canRead (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad64.of_eq {a v : BitVec 64} {P F : SepProp}
    (h : P = (a ↦₆₄ v) ∗ F) : SepLoad64 a P v :=
  ⟨fun hm => (IsBlock.pointsTo64 a v).read (by rw [h, sepConj_assoc] at hm; exact hm),
   fun hm => (IsBlock.pointsTo64 a v).canRead (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepStore8.of_eq {a : BitVec 64} {v v' : BitVec 8} {P P' F : SepProp}
    (h : P = (a ↦₈ v) ∗ F) (h' : P' = (a ↦₈ v') ∗ F) : SepStore8 a v' P P' :=
  ⟨fun hm => by
    rw [h, sepConj_assoc] at hm
    rw [h', sepConj_assoc]
    exact (IsBlock.pointsTo8 a v).write8 hm v',
   fun hm => (IsBlock.pointsTo8 a v).canWrite (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepStore64.of_eq {a v v' : BitVec 64} {P P' F : SepProp}
    (h : P = (a ↦₆₄ v) ∗ F) (h' : P' = (a ↦₆₄ v') ∗ F) : SepStore64 a v' P P' :=
  ⟨fun hm => by
    rw [h, sepConj_assoc] at hm
    rw [h', sepConj_assoc]
    exact (IsBlock.pointsTo64 a v).write64 hm v',
   fun hm => (IsBlock.pointsTo64 a v).canWrite (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad8.of_eq_addr {a a' : BitVec 64} {v : BitVec 8} {P F : SepProp}
    (h : P = (a' ↦₈ v) ∗ F) (ha : a' = a) : SepLoad8 a P v :=
  ha ▸ SepLoad8.of_eq h

theorem SepLoad64.of_eq_addr {a a' v : BitVec 64} {P F : SepProp}
    (h : P = (a' ↦₆₄ v) ∗ F) (ha : a' = a) : SepLoad64 a P v :=
  ha ▸ SepLoad64.of_eq h

theorem SepStore8.of_eq_addr {a a' : BitVec 64} {v v' : BitVec 8} {P P' F : SepProp}
    (h : P = (a' ↦₈ v) ∗ F) (h' : P' = (a' ↦₈ v') ∗ F) (ha : a' = a) : SepStore8 a v' P P' :=
  ha ▸ SepStore8.of_eq h h'

theorem SepStore64.of_eq_addr {a a' v v' : BitVec 64} {P P' F : SepProp}
    (h : P = (a' ↦₆₄ v) ∗ F) (h' : P' = (a' ↦₆₄ v') ∗ F) (ha : a' = a) : SepStore64 a v' P P' :=
  ha ▸ SepStore64.of_eq h h'

theorem SepLoad16.of_eq {a : BitVec 64} {v : BitVec 16} {P F : SepProp}
    (h : P = (a ↦₁₆ v) ∗ F) : SepLoad16 a P v :=
  ⟨fun hm => (IsBlock.pointsTo16 a v).read (by rw [h, sepConj_assoc] at hm; exact hm),
   fun hm => (IsBlock.pointsTo16 a v).canRead (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad16.of_eq_addr {a a' : BitVec 64} {v : BitVec 16} {P F : SepProp}
    (h : P = (a' ↦₁₆ v) ∗ F) (ha : a' = a) : SepLoad16 a P v :=
  ha ▸ SepLoad16.of_eq h

theorem SepStore16.of_eq {a : BitVec 64} {v v' : BitVec 16} {P P' F : SepProp}
    (h : P = (a ↦₁₆ v) ∗ F) (h' : P' = (a ↦₁₆ v') ∗ F) : SepStore16 a v' P P' :=
  ⟨fun hm => by
    rw [h, sepConj_assoc] at hm
    rw [h', sepConj_assoc]
    exact (IsBlock.pointsTo16 a v).write16 hm v',
   fun hm => (IsBlock.pointsTo16 a v).canWrite (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepStore16.of_eq_addr {a a' : BitVec 64} {v v' : BitVec 16} {P P' F : SepProp}
    (h : P = (a' ↦₁₆ v) ∗ F) (h' : P' = (a' ↦₁₆ v') ∗ F) (ha : a' = a) : SepStore16 a v' P P' :=
  ha ▸ SepStore16.of_eq h h'

theorem bitvec_truncate16_truncate32 (x : BitVec 64) :
    (x.truncate 32).truncate 16 = x.truncate 16 := by
  bv_bits

theorem SepLoad32.of_eq {a : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a ↦₃₂ v) ∗ F) : SepLoad32 a P v :=
  ⟨fun hm => (IsBlock.pointsTo32 a v).read (by rw [h, sepConj_assoc] at hm; exact hm),
   fun hm => (IsBlock.pointsTo32 a v).canRead (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

/-- `SepLoad32` from an atom `a' ↦₃₂ v` whose address is (arithmetically) equal to the access
    address `a`, e.g. `a' = sp - 36#64` and `a = (sp - 48#64) + 12#64`. -/
theorem SepLoad32.of_eq_addr {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ v) ∗ F) (ha : a' = a) : SepLoad32 a P v :=
  ha ▸ SepLoad32.of_eq h

theorem SepStore32.of_eq {a : BitVec 64} {v v' : BitVec 32} {P P' F : SepProp}
    (h : P = (a ↦₃₂ v) ∗ F) (h' : P' = (a ↦₃₂ v') ∗ F) : SepStore32 a v' P P' :=
  ⟨fun hm => by
    rw [h, sepConj_assoc] at hm
    rw [h', sepConj_assoc]
    exact (IsBlock.pointsTo32 a v).write32 hm v',
   fun hm => (IsBlock.pointsTo32 a v).canWrite (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

/-- `SepStore32` into an atom `a' ↦₃₂ v` whose address is (arithmetically) equal to the access
    address `a`; the updated atom keeps the address form `a'` used by the spatial context. -/
theorem SepStore32.of_eq_addr {a a' : BitVec 64} {v v' : BitVec 32} {P P' F : SepProp}
    (h : P = (a' ↦₃₂ v) ∗ F) (h' : P' = (a' ↦₃₂ v') ∗ F) (ha : a' = a) : SepStore32 a v' P P' :=
  ha ▸ SepStore32.of_eq h h'

private theorem read8_of_read32_0 {m : Memory} {a : BitVec 64} {v : BitVec 32}
    (h : m.read32 a = v) : m.read8 a = v.extractLsb' 0 8 := by
  subst h
  simp only [Memory.read32]
  have h0 : a + 0#64 = a := by bv_decide
  rw [h0]
  generalize m.read8 a = x0
  generalize m.read8 (a + 1#64) = x1
  generalize m.read8 (a + 2#64) = x2
  generalize m.read8 (a + 3#64) = x3
  bv_decide

private theorem read8_of_read32_1 {m : Memory} {a : BitVec 64} {v : BitVec 32}
    (h : m.read32 a = v) : m.read8 (a + 1#64) = v.extractLsb' 8 8 := by
  subst h
  simp only [Memory.read32]
  generalize m.read8 (a + 0#64) = x0
  generalize m.read8 (a + 1#64) = x1
  generalize m.read8 (a + 2#64) = x2
  generalize m.read8 (a + 3#64) = x3
  bv_decide

private theorem read8_of_read32_2 {m : Memory} {a : BitVec 64} {v : BitVec 32}
    (h : m.read32 a = v) : m.read8 (a + 2#64) = v.extractLsb' 16 8 := by
  subst h
  simp only [Memory.read32]
  generalize m.read8 (a + 0#64) = x0
  generalize m.read8 (a + 1#64) = x1
  generalize m.read8 (a + 2#64) = x2
  generalize m.read8 (a + 3#64) = x3
  bv_decide

private theorem read8_of_read32_3 {m : Memory} {a : BitVec 64} {v : BitVec 32}
    (h : m.read32 a = v) : m.read8 (a + 3#64) = v.extractLsb' 24 8 := by
  subst h
  simp only [Memory.read32]
  generalize m.read8 (a + 0#64) = x0
  generalize m.read8 (a + 1#64) = x1
  generalize m.read8 (a + 2#64) = x2
  generalize m.read8 (a + 3#64) = x3
  bv_decide

theorem SepLoad8.of_pointsTo32_0 {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ v) ∗ F) (ha : a' = a) :
    SepLoad8 a P (v.extractLsb' 0 8) := by
  subst ha
  refine ⟨fun hm => read8_of_read32_0 ((IsBlock.pointsTo32 a' v).read (by rw [h, sepConj_assoc] at hm; exact hm)),
    fun hm => (IsBlock.pointsTo32 a' v).canRead_sub (by rw [h, sepConj_assoc] at hm; exact hm) (by bv_omega) (by decide)⟩

theorem SepLoad8.of_pointsTo32_1 {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ v) ∗ F) (ha : a' + 1#64 = a) :
    SepLoad8 a P (v.extractLsb' 8 8) := by
  subst ha
  refine ⟨fun hm => read8_of_read32_1 ((IsBlock.pointsTo32 a' v).read (by rw [h, sepConj_assoc] at hm; exact hm)),
    fun hm => (IsBlock.pointsTo32 a' v).canRead_sub (by rw [h, sepConj_assoc] at hm; exact hm) (by bv_omega) (by decide)⟩

theorem SepLoad8.of_pointsTo32_2 {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ v) ∗ F) (ha : a' + 2#64 = a) :
    SepLoad8 a P (v.extractLsb' 16 8) := by
  subst ha
  refine ⟨fun hm => read8_of_read32_2 ((IsBlock.pointsTo32 a' v).read (by rw [h, sepConj_assoc] at hm; exact hm)),
    fun hm => (IsBlock.pointsTo32 a' v).canRead_sub (by rw [h, sepConj_assoc] at hm; exact hm) (by bv_omega) (by decide)⟩

theorem SepLoad8.of_pointsTo32_3 {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ v) ∗ F) (ha : a' + 3#64 = a) :
    SepLoad8 a P (v.extractLsb' 24 8) := by
  subst ha
  refine ⟨fun hm => read8_of_read32_3 ((IsBlock.pointsTo32 a' v).read (by rw [h, sepConj_assoc] at hm; exact hm)),
    fun hm => (IsBlock.pointsTo32 a' v).canRead_sub (by rw [h, sepConj_assoc] at hm; exact hm) (by bv_omega) (by decide)⟩

@[simp, arm64_norm, wp_norm]
theorem extractLsb8_0_zext64 (v : BitVec 32) :
    (v.extractLsb' 0 8).zeroExtend 64 = (v &&& 0xff#32).zeroExtend 64 := by bv_bits

@[simp, arm64_norm, wp_norm]
theorem extractLsb8_8_zext64 (v : BitVec 32) :
    (v.extractLsb' 8 8).zeroExtend 64 = ((v >>> 8) &&& 0xff#32).zeroExtend 64 := by bv_bits

@[simp, arm64_norm, wp_norm]
theorem extractLsb8_16_zext64 (v : BitVec 32) :
    (v.extractLsb' 16 8).zeroExtend 64 = ((v >>> 16) &&& 0xff#32).zeroExtend 64 := by bv_bits

@[simp, arm64_norm, wp_norm]
theorem extractLsb8_24_zext64 (v : BitVec 32) :
    (v.extractLsb' 24 8).zeroExtend 64 = ((v >>> 24) &&& 0xff#32).zeroExtend 64 := by bv_bits

/-! ### Read-only (`↦ᵣ`) and byte-list (`↦ᵣ` / `↦ₛ`) `SepLoad` witnesses -/

theorem SepLoad8.congr_val {a : BitVec 64} {P : SepProp} {v v' : BitVec 8}
    (h : SepLoad8 a P v) (hv : v = v') : SepLoad8 a P v' :=
  hv ▸ h

theorem SepLoad16.congr_val {a : BitVec 64} {P : SepProp} {v v' : BitVec 16}
    (h : SepLoad16 a P v) (hv : v = v') : SepLoad16 a P v' :=
  hv ▸ h

theorem SepLoad32.congr_val {a : BitVec 64} {P : SepProp} {v v' : BitVec 32}
    (h : SepLoad32 a P v) (hv : v = v') : SepLoad32 a P v' :=
  hv ▸ h

theorem SepLoad64.congr_val {a : BitVec 64} {P : SepProp} {v v' : BitVec 64}
    (h : SepLoad64 a P v) (hv : v = v') : SepLoad64 a P v' :=
  hv ▸ h

theorem SepLoad8.of_ro_eq {a : BitVec 64} {v : BitVec 8} {P F : SepProp}
    (h : P = (a ↦₈ᵣ v) ∗ F) : SepLoad8 a P v :=
  ⟨fun hm => (IsBlockRO.pointsTo8RO a v).read (by rw [h, sepConj_assoc] at hm; exact hm),
   fun hm => (IsBlockRO.pointsTo8RO a v).canRead (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad8.of_ro_eq_addr {a a' : BitVec 64} {v : BitVec 8} {P F : SepProp}
    (h : P = (a' ↦₈ᵣ v) ∗ F) (ha : a' = a) : SepLoad8 a P v :=
  ha ▸ SepLoad8.of_ro_eq h

theorem SepLoad16.of_ro_eq {a : BitVec 64} {v : BitVec 16} {P F : SepProp}
    (h : P = (a ↦₁₆ᵣ v) ∗ F) : SepLoad16 a P v :=
  ⟨fun hm => (IsBlockRO.pointsTo16RO a v).read (by rw [h, sepConj_assoc] at hm; exact hm),
   fun hm => (IsBlockRO.pointsTo16RO a v).canRead (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad16.of_ro_eq_addr {a a' : BitVec 64} {v : BitVec 16} {P F : SepProp}
    (h : P = (a' ↦₁₆ᵣ v) ∗ F) (ha : a' = a) : SepLoad16 a P v :=
  ha ▸ SepLoad16.of_ro_eq h

theorem SepLoad32.of_ro_eq {a : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a ↦₃₂ᵣ v) ∗ F) : SepLoad32 a P v :=
  ⟨fun hm => (IsBlockRO.pointsTo32RO a v).read (by rw [h, sepConj_assoc] at hm; exact hm),
   fun hm => (IsBlockRO.pointsTo32RO a v).canRead (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad32.of_ro_eq_addr {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ᵣ v) ∗ F) (ha : a' = a) : SepLoad32 a P v :=
  ha ▸ SepLoad32.of_ro_eq h

theorem SepLoad64.of_ro_eq {a v : BitVec 64} {P F : SepProp}
    (h : P = (a ↦₆₄ᵣ v) ∗ F) : SepLoad64 a P v :=
  ⟨fun hm => (IsBlockRO.pointsTo64RO a v).read (by rw [h, sepConj_assoc] at hm; exact hm),
   fun hm => (IsBlockRO.pointsTo64RO a v).canRead (by decide) (by rw [h, sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad64.of_ro_eq_addr {a a' v : BitVec 64} {P F : SepProp}
    (h : P = (a' ↦₆₄ᵣ v) ∗ F) (ha : a' = a) : SepLoad64 a P v :=
  ha ▸ SepLoad64.of_ro_eq h

theorem SepLoad8.of_pointsTo32RO_0 {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ᵣ v) ∗ F) (ha : a' = a) :
    SepLoad8 a P (v.extractLsb' 0 8) := by
  subst ha
  refine ⟨fun hm => read8_of_read32_0 ((IsBlockRO.pointsTo32RO a' v).read (by rw [h, sepConj_assoc] at hm; exact hm)),
    fun hm => (IsBlockRO.pointsTo32RO a' v).canRead_sub (by rw [h, sepConj_assoc] at hm; exact hm) (by bv_omega) (by decide)⟩

theorem SepLoad8.of_pointsTo32RO_1 {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ᵣ v) ∗ F) (ha : a' + 1#64 = a) :
    SepLoad8 a P (v.extractLsb' 8 8) := by
  subst ha
  refine ⟨fun hm => read8_of_read32_1 ((IsBlockRO.pointsTo32RO a' v).read (by rw [h, sepConj_assoc] at hm; exact hm)),
    fun hm => (IsBlockRO.pointsTo32RO a' v).canRead_sub (by rw [h, sepConj_assoc] at hm; exact hm) (by bv_omega) (by decide)⟩

theorem SepLoad8.of_pointsTo32RO_2 {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ᵣ v) ∗ F) (ha : a' + 2#64 = a) :
    SepLoad8 a P (v.extractLsb' 16 8) := by
  subst ha
  refine ⟨fun hm => read8_of_read32_2 ((IsBlockRO.pointsTo32RO a' v).read (by rw [h, sepConj_assoc] at hm; exact hm)),
    fun hm => (IsBlockRO.pointsTo32RO a' v).canRead_sub (by rw [h, sepConj_assoc] at hm; exact hm) (by bv_omega) (by decide)⟩

theorem SepLoad8.of_pointsTo32RO_3 {a a' : BitVec 64} {v : BitVec 32} {P F : SepProp}
    (h : P = (a' ↦₃₂ᵣ v) ∗ F) (ha : a' + 3#64 = a) :
    SepLoad8 a P (v.extractLsb' 24 8) := by
  subst ha
  refine ⟨fun hm => read8_of_read32_3 ((IsBlockRO.pointsTo32RO a' v).read (by rw [h, sepConj_assoc] at hm; exact hm)),
    fun hm => (IsBlockRO.pointsTo32RO a' v).canRead_sub (by rw [h, sepConj_assoc] at hm; exact hm) (by bv_omega) (by decide)⟩

theorem SepLoad8.of_pointsToBytesRO {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ᵣ bs) ∗ F) (hoff : off + 1 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad8 a P (bs.getD off 0#8) := by
  have h1 : (bs.drop off).take 1 = [bs.getD off 0#8] := by
    rw [List.drop_eq_getD_cons bs off 0#8 (by omega)]
    rfl
  have hsplit := pointsToBytesRO_split3 base bs off 1 hoff
  rw [h1, pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp] at hsplit
  exact SepLoad8.of_ro_eq_addr (by rw [h, hsplit, sepConj_assoc]) ha

theorem SepLoad8.of_pointsToBytes {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 1 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad8 a P (bs.getD off 0#8) := by
  have h1 : (bs.drop off).take 1 = [bs.getD off 0#8] := by
    rw [List.drop_eq_getD_cons bs off 0#8 (by omega)]
    rfl
  have hsplit := pointsToBytes_split3 base bs off 1 hoff
  rw [h1, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp] at hsplit
  exact SepLoad8.of_eq_addr (by rw [h, hsplit, sepConj_assoc]) ha

theorem SepLoad16.of_pointsToBytesRO {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ᵣ bs) ∗ F) (hoff : off + 2 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad16 a P (pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)) := by
  have h2 := pointsToBytesRO_take2_eq_pointsTo16RO (base + BitVec.ofNat 64 off) bs off hoff
  have hsplit := pointsToBytesRO_split3 base bs off 2 hoff
  rw [h2] at hsplit
  exact SepLoad16.of_ro_eq_addr (by rw [h, hsplit, sepConj_assoc]) ha

theorem SepLoad16.of_pointsToBytes {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 2 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad16 a P (pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)) := by
  have h2 := pointsToBytes_take2_eq_pointsTo16 (base + BitVec.ofNat 64 off) bs off hoff
  have hsplit := pointsToBytes_split3 base bs off 2 hoff
  rw [h2] at hsplit
  exact SepLoad16.of_eq_addr (by rw [h, hsplit, sepConj_assoc]) ha

theorem SepLoad32.of_pointsToBytesRO {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ᵣ bs) ∗ F) (hoff : off + 4 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad32 a P (pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)) := by
  have h4 := pointsToBytesRO_take4_eq_pointsTo32RO (base + BitVec.ofNat 64 off) bs off hoff
  have hsplit := pointsToBytesRO_split3 base bs off 4 hoff
  rw [h4] at hsplit
  exact SepLoad32.of_ro_eq_addr (by rw [h, hsplit, sepConj_assoc]) ha

theorem SepLoad32.of_pointsToBytes {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 4 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad32 a P (pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)) := by
  have h4 := pointsToBytes_take4_eq_pointsTo32 (base + BitVec.ofNat 64 off) bs off hoff
  have hsplit := pointsToBytes_split3 base bs off 4 hoff
  rw [h4] at hsplit
  exact SepLoad32.of_eq_addr (by rw [h, hsplit, sepConj_assoc]) ha

theorem SepLoad64.of_pointsToBytesRO {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ᵣ bs) ∗ F) (hoff : off + 8 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad64 a P (pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
      (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)) := by
  have h8 := pointsToBytesRO_take8_eq_pointsTo64RO (base + BitVec.ofNat 64 off) bs off hoff
  have hsplit := pointsToBytesRO_split3 base bs off 8 hoff
  rw [h8] at hsplit
  exact SepLoad64.of_ro_eq_addr (by rw [h, hsplit, sepConj_assoc]) ha

theorem SepLoad64.of_pointsToBytes {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 8 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad64 a P (pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
      (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)) := by
  have h8 := pointsToBytes_take8_eq_pointsTo64 (base + BitVec.ofNat 64 off) bs off hoff
  have hsplit := pointsToBytes_split3 base bs off 8 hoff
  rw [h8] at hsplit
  exact SepLoad64.of_eq_addr (by rw [h, hsplit, sepConj_assoc]) ha

/-- Introduce a read-only byte-list assertion `base ↦ᵣ bytes` into `m ⊨ P` from
    `Obj.HoldsBytes m base bytes (fun _ => .ro)`. Because `.ro` heap cells cannot overlap `.rw`
    heap cells (`w = false`), no `DisjointRegions` hypothesis is required. -/
theorem Satisfies.of_holdsBytes_ro {m : Memory} {base : BitVec 64} {bytes : List (BitVec 8)} {P : SepProp}
    (hbytes : Arm64.Obj.HoldsBytes m base bytes (fun _ => .ro))
    (hlen : bytes.length ≤ 2 ^ 64 := by decide) (hP : m ⊨ P) :
    m ⊨ (base ↦ᵣ bytes) ∗ P := by
  obtain ⟨hro, hread⟩ := holdsBytes_ro hbytes
  exact Satisfies.rodata_intro hro hread hlen hP

/-- Introduce a `.rodata` section `((img.base + secOff) ↦ᵣ (li.data.drop (secOff - dataOff)).take secLen)`
    into `m ⊨ P` directly from `Obj.Loads li img` and `img.RoDataLoaded m`. No `DisjointRegions`
    side condition is needed because `.rodata` is mapped `Perm.ro` (`w = false`), which is
    automatically disjoint from all writable heap cells. -/
theorem Satisfies.of_rodata_loads {li : Arm64.Obj.LinkedImage} {img : Arm64.Obj.Image}
    {m : Memory} {P : SepProp} (himg : Arm64.Obj.Loads li img)
    {dataOff : Nat} (hdo : li.dataOff = dataOff := by rfl)
    {secOff secLen : Nat} (hsec : (secOff, secLen) ∈ li.roData)
    (hoff : dataOff ≤ secOff := by decide) (hlen : secLen < 2 ^ 32 := by decide)
    (hdlen : secOff - dataOff + secLen ≤ li.data.length := by decide)
    (hrel : li.relocs.all
      (fun r => decide (r.off + r.width ≤ secOff - dataOff ∨ secOff - dataOff + secLen ≤ r.off)) = true := by decide)
    (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + BitVec.ofNat 64 secOff) ↦ᵣ (li.data.drop (secOff - dataOff)).take secLen) ∗ P := by
  obtain ⟨hro_mem, hread⟩ := rodata_readBytes_disjoint himg hdo hsec hoff hlen hdlen hrel m hro
  have htake_len : ((li.data.drop (secOff - dataOff)).take secLen).length = secLen := by
    rw [List.length_take, List.length_drop]; omega
  refine Satisfies.rodata_intro ?_ ?_ ?_ hP
  · rwa [htake_len]
  · rwa [htake_len]
  · omega

/-- Introduce a `.rodata` section `((img.base + secOff) ↦ᵣ (li.data.drop (secOff - dataOff)).take secLen)`
    into the `SepWP` spatial context `P` from `Obj.Loads li img` and `img.RoDataLoaded s.mem`. -/
theorem SepWP.rodata_intro {li : Arm64.Obj.LinkedImage} {img : Arm64.Obj.Image}
    {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (himg : Arm64.Obj.Loads li img)
    {dataOff : Nat} (hdo : li.dataOff = dataOff := by rfl)
    {secOff secLen : Nat} (hsec : (secOff, secLen) ∈ li.roData)
    (hoff : dataOff ≤ secOff := by decide) (hlen : secLen < 2 ^ 32 := by decide)
    (hdlen : secOff - dataOff + secLen ≤ li.data.length := by decide)
    (hrel : li.relocs.all
      (fun r => decide (r.off + r.width ≤ secOff - dataOff ∨ secOff - dataOff + secLen ≤ r.off)) = true := by decide)
    (hro : img.RoDataLoaded s.mem)
    (h : SepWP prog target_pc s
      (((img.base + BitVec.ofNat 64 secOff) ↦ᵣ (li.data.drop (secOff - dataOff)).take secLen) ∗ P) post) :
    SepWP prog target_pc s P post := by
  intro R hm
  apply h R
  rw [sepConj_assoc]
  exact Satisfies.of_rodata_loads himg hdo hsec hoff hlen hdlen hrel hro hm

/-- Introduce a read-only byte region `(base ↦ᵣ bytes)` into the `SepWP` spatial context `P`
    from `Obj.HoldsBytes s.mem base bytes (fun _ => .ro)`. -/
theorem SepWP.holdsBytes_ro_intro {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {base : BitVec 64} {bytes : List (BitVec 8)}
    (hbytes : Arm64.Obj.HoldsBytes s.mem base bytes (fun _ => .ro))
    (hlen : bytes.length ≤ 2 ^ 64 := by decide)
    (h : SepWP prog target_pc s ((base ↦ᵣ bytes) ∗ P) post) :
    SepWP prog target_pc s P post := by
  intro R hm
  apply h R
  rw [sepConj_assoc]
  exact Satisfies.of_holdsBytes_ro hbytes hlen hm

/-! ## Structural Spine Lemmas -/

theorem SepLoad8.left {a : BitVec 64} {v : BitVec 8} {L R : SepProp} (h : SepLoad8 a L v) :
    SepLoad8 a (L ∗ R) v :=
  ⟨fun hm => h.load (by rw [sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad8.right {a : BitVec 64} {v : BitVec 8} {L R : SepProp} (h : SepLoad8 a R v) :
    SepLoad8 a (L ∗ R) v :=
  ⟨fun hm => h.load (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm)⟩

theorem SepStore8.left {a : BitVec 64} {v' : BitVec 8} {L L' R : SepProp} (h : SepStore8 a v' L L') :
    SepStore8 a v' (L ∗ R) (L' ∗ R) :=
  ⟨fun hm => by
    rw [sepConj_assoc] at hm ⊢
    exact h.store hm,
   fun hm => h.writable (by rw [sepConj_assoc] at hm; exact hm)⟩

theorem SepStore8.right {a : BitVec 64} {v' : BitVec 8} {L R R' : SepProp} (h : SepStore8 a v' R R') :
    SepStore8 a v' (L ∗ R) (L ∗ R') :=
  ⟨fun hm => by
    rw [sepConj_comm L R, sepConj_assoc] at hm
    rw [sepConj_comm L R', sepConj_assoc]
    exact h.store hm,
   fun hm => h.writable (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm)⟩

/-- Leaf: the atom `a' ↦₈ v` itself, for an access address `a` with `a' = a`. -/
theorem SepLoad8.here {a a' : BitVec 64} {v : BitVec 8} (ha : a' = a) : SepLoad8 a (a' ↦₈ v) v :=
  SepLoad8.of_eq_addr (sepConj_emp _).symm ha

/-- Leaf: the read-only atom `a' ↦₈ᵣ v`, for an access address `a` with `a' = a`. -/
theorem SepLoad8.here_ro {a a' : BitVec 64} {v : BitVec 8} (ha : a' = a) : SepLoad8 a (a' ↦₈ᵣ v) v :=
  SepLoad8.of_ro_eq_addr (sepConj_emp _).symm ha

/-- Leaf: storing `v'` into the atom `a' ↦₈ v`, for an access address `a` with `a' = a`. -/
theorem SepStore8.here {a a' : BitVec 64} {v v' : BitVec 8} (ha : a' = a) :
    SepStore8 a v' (a' ↦₈ v) (a' ↦₈ v') :=
  SepStore8.of_eq_addr (sepConj_emp _).symm (sepConj_emp _).symm ha

theorem SepLoad16.left {a : BitVec 64} {v : BitVec 16} {L R : SepProp} (h : SepLoad16 a L v) :
    SepLoad16 a (L ∗ R) v :=
  ⟨fun hm => h.load (by rw [sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad16.right {a : BitVec 64} {v : BitVec 16} {L R : SepProp} (h : SepLoad16 a R v) :
    SepLoad16 a (L ∗ R) v :=
  ⟨fun hm => h.load (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm)⟩

theorem SepStore16.left {a : BitVec 64} {v' : BitVec 16} {L L' R : SepProp} (h : SepStore16 a v' L L') :
    SepStore16 a v' (L ∗ R) (L' ∗ R) :=
  ⟨fun hm => by
    rw [sepConj_assoc] at hm ⊢
    exact h.store hm,
   fun hm => h.writable (by rw [sepConj_assoc] at hm; exact hm)⟩

theorem SepStore16.right {a : BitVec 64} {v' : BitVec 16} {L R R' : SepProp} (h : SepStore16 a v' R R') :
    SepStore16 a v' (L ∗ R) (L ∗ R') :=
  ⟨fun hm => by
    rw [sepConj_comm L R, sepConj_assoc] at hm
    rw [sepConj_comm L R', sepConj_assoc]
    exact h.store hm,
   fun hm => h.writable (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm)⟩

/-- Leaf: the atom `a' ↦₁₆ v` itself, for an access address `a` with `a' = a`. -/
theorem SepLoad16.here {a a' : BitVec 64} {v : BitVec 16} (ha : a' = a) : SepLoad16 a (a' ↦₁₆ v) v :=
  SepLoad16.of_eq_addr (sepConj_emp _).symm ha

/-- Leaf: the read-only atom `a' ↦₁₆ᵣ v`, for an access address `a` with `a' = a`. -/
theorem SepLoad16.here_ro {a a' : BitVec 64} {v : BitVec 16} (ha : a' = a) : SepLoad16 a (a' ↦₁₆ᵣ v) v :=
  SepLoad16.of_ro_eq_addr (sepConj_emp _).symm ha

/-- Leaf: storing `v'` into the atom `a' ↦₁₆ v`, for an access address `a` with `a' = a`. -/
theorem SepStore16.here {a a' : BitVec 64} {v v' : BitVec 16} (ha : a' = a) :
    SepStore16 a v' (a' ↦₁₆ v) (a' ↦₁₆ v') :=
  SepStore16.of_eq_addr (sepConj_emp _).symm (sepConj_emp _).symm ha

theorem SepLoad32.left {a : BitVec 64} {v : BitVec 32} {L R : SepProp} (h : SepLoad32 a L v) :
    SepLoad32 a (L ∗ R) v :=
  ⟨fun hm => h.load (by rw [sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad32.right {a : BitVec 64} {v : BitVec 32} {L R : SepProp} (h : SepLoad32 a R v) :
    SepLoad32 a (L ∗ R) v :=
  ⟨fun hm => h.load (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm)⟩

theorem SepStore32.left {a : BitVec 64} {v' : BitVec 32} {L L' R : SepProp} (h : SepStore32 a v' L L') :
    SepStore32 a v' (L ∗ R) (L' ∗ R) :=
  ⟨fun hm => by
    rw [sepConj_assoc] at hm ⊢
    exact h.store hm,
   fun hm => h.writable (by rw [sepConj_assoc] at hm; exact hm)⟩

theorem SepStore32.right {a : BitVec 64} {v' : BitVec 32} {L R R' : SepProp} (h : SepStore32 a v' R R') :
    SepStore32 a v' (L ∗ R) (L ∗ R') :=
  ⟨fun hm => by
    rw [sepConj_comm L R, sepConj_assoc] at hm
    rw [sepConj_comm L R', sepConj_assoc]
    exact h.store hm,
   fun hm => h.writable (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm)⟩

/-- Leaf: the atom `a' ↦₃₂ v` itself, for an access address `a` with `a' = a`. -/
theorem SepLoad32.here {a a' : BitVec 64} {v : BitVec 32} (ha : a' = a) : SepLoad32 a (a' ↦₃₂ v) v :=
  SepLoad32.of_eq_addr (sepConj_emp _).symm ha

/-- Leaf: the read-only atom `a' ↦₃₂ᵣ v`, for an access address `a` with `a' = a`. -/
theorem SepLoad32.here_ro {a a' : BitVec 64} {v : BitVec 32} (ha : a' = a) : SepLoad32 a (a' ↦₃₂ᵣ v) v :=
  SepLoad32.of_ro_eq_addr (sepConj_emp _).symm ha

/-- Leaf: storing `v'` into the atom `a' ↦₃₂ v`, for an access address `a` with `a' = a`. -/
theorem SepStore32.here {a a' : BitVec 64} {v v' : BitVec 32} (ha : a' = a) :
    SepStore32 a v' (a' ↦₃₂ v) (a' ↦₃₂ v') :=
  SepStore32.of_eq_addr (sepConj_emp _).symm (sepConj_emp _).symm ha

theorem SepLoad64.left {a : BitVec 64} {v : BitVec 64} {L R : SepProp} (h : SepLoad64 a L v) :
    SepLoad64 a (L ∗ R) v :=
  ⟨fun hm => h.load (by rw [sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_assoc] at hm; exact hm)⟩

theorem SepLoad64.right {a : BitVec 64} {v : BitVec 64} {L R : SepProp} (h : SepLoad64 a R v) :
    SepLoad64 a (L ∗ R) v :=
  ⟨fun hm => h.load (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm)⟩

theorem SepStore64.left {a : BitVec 64} {v' : BitVec 64} {L L' R : SepProp} (h : SepStore64 a v' L L') :
    SepStore64 a v' (L ∗ R) (L' ∗ R) :=
  ⟨fun hm => by
    rw [sepConj_assoc] at hm ⊢
    exact h.store hm,
   fun hm => h.writable (by rw [sepConj_assoc] at hm; exact hm)⟩

theorem SepStore64.right {a : BitVec 64} {v' : BitVec 64} {L R R' : SepProp} (h : SepStore64 a v' R R') :
    SepStore64 a v' (L ∗ R) (L ∗ R') :=
  ⟨fun hm => by
    rw [sepConj_comm L R, sepConj_assoc] at hm
    rw [sepConj_comm L R', sepConj_assoc]
    exact h.store hm,
   fun hm => h.writable (by rw [sepConj_comm L R, sepConj_assoc] at hm; exact hm)⟩

/-- Leaf: the atom `a' ↦₆₄ v` itself, for an access address `a` with `a' = a`. -/
theorem SepLoad64.here {a a' : BitVec 64} {v : BitVec 64} (ha : a' = a) : SepLoad64 a (a' ↦₆₄ v) v :=
  SepLoad64.of_eq_addr (sepConj_emp _).symm ha

/-- Leaf: the read-only atom `a' ↦₆₄ᵣ v`, for an access address `a` with `a' = a`. -/
theorem SepLoad64.here_ro {a a' : BitVec 64} {v : BitVec 64} (ha : a' = a) : SepLoad64 a (a' ↦₆₄ᵣ v) v :=
  SepLoad64.of_ro_eq_addr (sepConj_emp _).symm ha

/-- Leaf: storing `v'` into the atom `a' ↦₆₄ v`, for an access address `a` with `a' = a`. -/
theorem SepStore64.here {a a' : BitVec 64} {v v' : BitVec 64} (ha : a' = a) :
    SepStore64 a v' (a' ↦₆₄ v) (a' ↦₆₄ v') :=
  SepStore64.of_eq_addr (sepConj_emp _).symm (sepConj_emp _).symm ha

/-! ### Lazy-free (`MADV_FREE`) store leaf witnesses (`here_lazy`)

Storing to a lazy-free cell (`a' ↦₈ₗ` .. `a' ↦₆₄ₗ`) cancels lazy reclaim on the written bytes and
upgrades the cell in place to a normal readable-and-writable cell (`a' ↦₈ v'` .. `a' ↦₆₄ v'`). -/

theorem SepStore8.of_eq_lazy {a : BitVec 64} {v' : BitVec 8} {P P' F : SepProp}
    (h : P = (a ↦₈ₗ) ∗ F) (h' : P' = (a ↦₈ v') ∗ F) : SepStore8 a v' P P' :=
  ⟨fun hm => by
    rw [h, sepConj_assoc] at hm
    rw [h', sepConj_assoc]
    exact Satisfies.write8_pointsTo8Lazy v' hm,
   fun hm => by
    rw [h, sepConj_assoc, pointsTo8Lazy_eq_memRegionLazy] at hm
    exact Satisfies.canWrite_of_memRegionLazy (by decide) hm⟩

theorem SepStore16.of_eq_lazy {a : BitVec 64} {v' : BitVec 16} {P P' F : SepProp}
    (h : P = (a ↦₁₆ₗ) ∗ F) (h' : P' = (a ↦₁₆ v') ∗ F) : SepStore16 a v' P P' :=
  ⟨fun hm => by
    rw [h, sepConj_assoc] at hm
    rw [h', sepConj_assoc]
    exact Satisfies.write16_pointsTo16Lazy v' hm,
   fun hm => by
    rw [h, sepConj_assoc, pointsTo16Lazy_eq_memRegionLazy] at hm
    exact Satisfies.canWrite_of_memRegionLazy (by decide) hm⟩

theorem SepStore32.of_eq_lazy {a : BitVec 64} {v' : BitVec 32} {P P' F : SepProp}
    (h : P = (a ↦₃₂ₗ) ∗ F) (h' : P' = (a ↦₃₂ v') ∗ F) : SepStore32 a v' P P' :=
  ⟨fun hm => by
    rw [h, sepConj_assoc] at hm
    rw [h', sepConj_assoc]
    exact Satisfies.write32_pointsTo32Lazy v' hm,
   fun hm => by
    rw [h, sepConj_assoc, pointsTo32Lazy_eq_memRegionLazy] at hm
    exact Satisfies.canWrite_of_memRegionLazy (by decide) hm⟩

theorem SepStore64.of_eq_lazy {a v' : BitVec 64} {P P' F : SepProp}
    (h : P = (a ↦₆₄ₗ) ∗ F) (h' : P' = (a ↦₆₄ v') ∗ F) : SepStore64 a v' P P' :=
  ⟨fun hm => by
    rw [h, sepConj_assoc] at hm
    rw [h', sepConj_assoc]
    exact Satisfies.write64_pointsTo64Lazy v' hm,
   fun hm => by
    rw [h, sepConj_assoc, pointsTo64Lazy_eq_memRegionLazy] at hm
    exact Satisfies.canWrite_of_memRegionLazy (by decide) hm⟩

/-- Leaf: storing `v'` into the lazy-free atom `a' ↦₈ₗ` (`a' = a`), upgrading it to `a' ↦₈ v'`. -/
theorem SepStore8.here_lazy {a a' : BitVec 64} {v' : BitVec 8} (ha : a' = a) :
    SepStore8 a v' (a' ↦₈ₗ) (a' ↦₈ v') :=
  ha ▸ SepStore8.of_eq_lazy (sepConj_emp _).symm (sepConj_emp _).symm

/-- Leaf: storing `v'` into the lazy-free atom `a' ↦₁₆ₗ` (`a' = a`), upgrading it to `a' ↦₁₆ v'`. -/
theorem SepStore16.here_lazy {a a' : BitVec 64} {v' : BitVec 16} (ha : a' = a) :
    SepStore16 a v' (a' ↦₁₆ₗ) (a' ↦₁₆ v') :=
  ha ▸ SepStore16.of_eq_lazy (sepConj_emp _).symm (sepConj_emp _).symm

/-- Leaf: storing `v'` into the lazy-free atom `a' ↦₃₂ₗ` (`a' = a`), upgrading it to `a' ↦₃₂ v'`. -/
theorem SepStore32.here_lazy {a a' : BitVec 64} {v' : BitVec 32} (ha : a' = a) :
    SepStore32 a v' (a' ↦₃₂ₗ) (a' ↦₃₂ v') :=
  ha ▸ SepStore32.of_eq_lazy (sepConj_emp _).symm (sepConj_emp _).symm

/-- Leaf: storing `v'` into the lazy-free atom `a' ↦₆₄ₗ` (`a' = a`), upgrading it to `a' ↦₆₄ v'`. -/
theorem SepStore64.here_lazy {a a' : BitVec 64} {v' : BitVec 64} (ha : a' = a) :
    SepStore64 a v' (a' ↦₆₄ₗ) (a' ↦₆₄ v') :=
  ha ▸ SepStore64.of_eq_lazy (sepConj_emp _).symm (sepConj_emp _).symm

/-! ## Byte-List Stores and Little-Endian Loads at a Byte Offset -/

theorem SepLoad64.of_pointsToBytes_readLE {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 8 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad64 a P (ByteSlice.readLE bs off 8) :=
  ByteSlice.pack64_eq_readLE_8 bs off ▸ SepLoad64.of_pointsToBytes h hoff ha

theorem SepLoad64.of_pointsToBytes_readLE_RO {a base : BitVec 64} {bs : List (BitVec 8)}
    {off : Nat} {P F : SepProp} (h : P = (base ↦ᵣ bs) ∗ F) (hoff : off + 8 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad64 a P (ByteSlice.readLE bs off 8) :=
  ByteSlice.pack64_eq_readLE_8 bs off ▸ SepLoad64.of_pointsToBytesRO h hoff ha

/-! ### Symbolic Byte Offsets and Length Normalization -/

theorem sepBytesOff_toNat (t : BitVec 64) : BitVec.ofNat 64 t.toNat = t := by
  simp

theorem sepBytesOff_termAdd {s k : Nat} {t u : BitVec 64} (h : BitVec.ofNat 64 s = t)
    (hk : BitVec.ofNat 64 k = u) : BitVec.ofNat 64 (s + k) = t + u := by
  rw [BitVec.ofNat_add, h, hk]

theorem sepBytesOff_add (d : Nat) {s : Nat} {t : BitVec 64} (h : BitVec.ofNat 64 s = t) :
    BitVec.ofNat 64 (s + d) = t + BitVec.ofNat 64 d := by
  rw [BitVec.ofNat_add, h]

theorem sepBytesOff_sub {s d : Nat} {t : BitVec 64} (h : BitVec.ofNat 64 s = t) (hd : d ≤ s) :
    BitVec.ofNat 64 (s - d) = t - BitVec.ofNat 64 d := by
  subst h
  conv => rhs; rw [show s = (s - d) + d by omega, BitVec.ofNat_add]
  exact (BitVec.add_sub_cancel _ _).symm

theorem sepBytesAddr_of_off {base a t : BitVec 64} {off : Nat} (h : BitVec.ofNat 64 off = t)
    (ha : base + t = a) : base + BitVec.ofNat 64 off = a := by
  rw [h, ha]

theorem sepBytesBound_of_len {bs : List (BitVec 8)} {len k : Nat} (hlen : bs.length = len)
    (h : k ≤ len) : k ≤ bs.length := by
  rw [hlen]; exact h

theorem sepBytesLen_write8 (v : BitVec 8) {bs : List (BitVec 8)} {len off : Nat}
    (hlen : bs.length = len) (h : off + 1 ≤ len) : (ByteSlice.write8 bs off v).length = len := by
  rw [ByteSlice.write8_length bs off v (by rw [hlen]; exact h), hlen]

theorem sepBytesLen_write16 (v : BitVec 16) {bs : List (BitVec 8)} {len off : Nat}
    (hlen : bs.length = len) (h : off + 2 ≤ len) : (ByteSlice.write16 bs off v).length = len := by
  rw [ByteSlice.write16_length bs off v (by rw [hlen]; exact h), hlen]

theorem sepBytesLen_write32 (v : BitVec 32) {bs : List (BitVec 8)} {len off : Nat}
    (hlen : bs.length = len) (h : off + 4 ≤ len) : (ByteSlice.write32 bs off v).length = len := by
  rw [ByteSlice.write32_length bs off v (by rw [hlen]; exact h), hlen]

theorem sepBytesLen_write64 (v : BitVec 64) {bs : List (BitVec 8)} {len off : Nat}
    (hlen : bs.length = len) (h : off + 8 ≤ len) : (ByteSlice.write64 bs off v).length = len := by
  rw [ByteSlice.write64_length bs off v (by rw [hlen]; exact h), hlen]

theorem sepBytesLen_copySet (src : List (BitVec 8)) (p : Nat → Bool) {old : List (BitVec 8)}
    {len : Nat} (hlen : old.length = len) : (ByteSlice.copySet old src p).length = len := by
  rw [ByteSlice.copySet_length, hlen]

theorem sepBytesLen_fillSet (b : BitVec 8) (p : Nat → Bool) {bs : List (BitVec 8)} {len : Nat}
    (hlen : bs.length = len) : (ByteSlice.fillSet bs b p).length = len := by
  rw [ByteSlice.fillSet_length, hlen]

/-- Store a byte into `base ↦ₛ bs` at byte offset `off`. -/
theorem SepStore8.of_pointsToBytes {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {v : BitVec 8} {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 1 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepStore8 a v P ((base ↦ₛ ByteSlice.write8 bs off v) ∗ F) := by
  subst ha
  refine SepStore8.of_eq (v := bs.getD off 0#8)
    (F := (base ↦ₛ bs.take off) ∗ (((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1)) ∗ F))
    ?_ ?_
  · rw [h, pointsToBytes_focus8 base bs off (by omega)]
    simp only [sepConj_assoc]
  · rw [← pointsToBytes_update8 base bs off v hoff]
    simp only [sepConj_assoc]

/-- Store a 16-bit halfword into `base ↦ₛ bs` at byte offset `off`. -/
theorem SepStore16.of_pointsToBytes {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {v : BitVec 16} {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 2 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepStore16 a v P ((base ↦ₛ ByteSlice.write16 bs off v) ∗ F) := by
  subst ha
  refine SepStore16.of_eq (v := pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8))
    (F := (base ↦ₛ bs.take off) ∗ (((base + BitVec.ofNat 64 (off + 2)) ↦ₛ bs.drop (off + 2)) ∗ F))
    ?_ ?_
  · rw [h, pointsToBytes_focus16 base bs off hoff]
    simp only [sepConj_assoc]
  · rw [← pointsToBytes_update16 base bs off v hoff]
    simp only [sepConj_assoc]

/-- Store a 32-bit word into `base ↦ₛ bs` at byte offset `off`. -/
theorem SepStore32.of_pointsToBytes {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {v : BitVec 32} {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 4 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepStore32 a v P ((base ↦ₛ ByteSlice.write32 bs off v) ∗ F) := by
  subst ha
  refine SepStore32.of_eq (v := pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8))
    (F := (base ↦ₛ bs.take off) ∗ (((base + BitVec.ofNat 64 (off + 4)) ↦ₛ bs.drop (off + 4)) ∗ F))
    ?_ ?_
  · rw [h, pointsToBytes_focus32 base bs off hoff]
    simp only [sepConj_assoc]
  · rw [← pointsToBytes_update32 base bs off v hoff]
    simp only [sepConj_assoc]

/-- Store a 64-bit word into `base ↦ₛ bs` at byte offset `off`. -/
theorem SepStore64.of_pointsToBytes {a base : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {v : BitVec 64} {P F : SepProp} (h : P = (base ↦ₛ bs) ∗ F) (hoff : off + 8 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepStore64 a v P ((base ↦ₛ ByteSlice.write64 bs off v) ∗ F) := by
  subst ha
  refine SepStore64.of_eq (v := ByteSlice.readLE bs off 8)
    (F := (base ↦ₛ bs.take off) ∗ (((base + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)) ∗ F))
    ?_ ?_
  · rw [h, pointsToBytes_focus64_le base bs off hoff]
    simp only [sepConj_assoc]
  · rw [← pointsToBytes_update64 base bs off v hoff]
    simp only [sepConj_assoc]

/-- Leaf: storing a byte into the atom `base ↦ₛ bs` itself (for spine lifting). -/
theorem SepStore8.of_pointsToBytes_here (a base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 8) (hoff : off + 1 ≤ bs.length) (ha : base + BitVec.ofNat 64 off = a) :
    SepStore8 a v (base ↦ₛ bs) (base ↦ₛ ByteSlice.write8 bs off v) := by
  have := SepStore8.of_pointsToBytes (v := v) (sepConj_emp _).symm hoff ha
  rwa [sepConj_emp] at this

/-- Leaf: storing a halfword into the atom `base ↦ₛ bs` itself (for spine lifting). -/
theorem SepStore16.of_pointsToBytes_here (a base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 16) (hoff : off + 2 ≤ bs.length) (ha : base + BitVec.ofNat 64 off = a) :
    SepStore16 a v (base ↦ₛ bs) (base ↦ₛ ByteSlice.write16 bs off v) := by
  have := SepStore16.of_pointsToBytes (v := v) (sepConj_emp _).symm hoff ha
  rwa [sepConj_emp] at this

/-- Leaf: storing a word into the atom `base ↦ₛ bs` itself (for spine lifting). -/
theorem SepStore32.of_pointsToBytes_here (a base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 32) (hoff : off + 4 ≤ bs.length) (ha : base + BitVec.ofNat 64 off = a) :
    SepStore32 a v (base ↦ₛ bs) (base ↦ₛ ByteSlice.write32 bs off v) := by
  have := SepStore32.of_pointsToBytes (v := v) (sepConj_emp _).symm hoff ha
  rwa [sepConj_emp] at this

/-- Leaf: storing a doubleword into the atom `base ↦ₛ bs` itself (for spine lifting). -/
theorem SepStore64.of_pointsToBytes_here (a base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 64) (hoff : off + 8 ≤ bs.length) (ha : base + BitVec.ofNat 64 off = a) :
    SepStore64 a v (base ↦ₛ bs) (base ↦ₛ ByteSlice.write64 bs off v) := by
  have := SepStore64.of_pointsToBytes (v := v) (sepConj_emp _).symm hoff ha
  rwa [sepConj_emp] at this

end ProofLib
