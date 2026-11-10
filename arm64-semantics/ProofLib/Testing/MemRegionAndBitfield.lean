/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Arm64
import ProofLib

/-!
# `memRegion` Framing and Bitfield `Nat` Normalization Tests

Regression tests for `memRegion` splitting and subcell carving (`wp_frame_split`, `sep_focus`,
`sep_entail`), out-of-range rejection diagnostics, bitfield `Nat` normalization (`width_norm`),
and `memMapped` virtual-address reservation laws.
-/

namespace Examples.Testing.ProofLib.MemRegionAndBitfield

open Arm64 _root_.ProofLib

/-! ## Region Splitting and Conversion -/

theorem memRegion_split_roundtrip (p : BitVec 64) (a b : Nat) (h : a + b ≤ 2 ^ 64) :
    memRegion p (a + b) = memRegion p a ∗ memRegion (p + BitVec.ofNat 64 a) b :=
  memRegion_split p a b h

theorem memRegion_iff_bytes4 (m : Memory) (buf : BitVec 64) :
    (m ⊨ memRegion buf 4) ↔
      ∃ bs : List (BitVec 8), bs.length = 4 ∧ (m ⊨ (buf ↦ₛ bs)) := by
  rw [memRegion_eq_exists_bytes buf 4 (by decide)]
  simp only [satisfies_sepExists, satisfies_pure_sepConj]

theorem memRegion_cells_stack80 (m : Memory) (sp : BitVec 64)
    (h : m ⊨ memRegion (sp - 80#64) 80) :
    m ⊨ cells (sp - 80#64) 10 := by
  rwa [show (80 : Nat) = 8 * 10 by rfl, memRegion_cells (sp - 80#64) 10 (by decide)] at h

/-! ## Subcell Carving and Merging -/

theorem stack_scratch_cells_entail_memRegion80 (m : Memory) (sp : BitVec 64)
    (w0 w1 canary : BitVec 64)
    (h : m ⊨
      (sp - 80#64) ↦₆₄ 0#64 ∗
      (sp - 72#64) ↦₆₄ 0#64 ∗
      (sp - 64#64) ↦₆₄ 0#64 ∗
      (sp - 56#64) ↦₆₄ 0#64 ∗
      (sp - 48#64) ↦₈ 0#8 ∗
      (sp - 47#64) ↦₈ 0#8 ∗
      memRegion (sp - 46#64) 14 ∗
      (sp - 32#64) ↦₆₄ w0 ∗
      (sp - 24#64) ↦₆₄ w1 ∗
      (sp - 16#64) ↦₆₄ 0#64 ∗
      (sp - 8#64) ↦₆₄ canary) :
    m ⊨ memRegion (sp - 80#64) 80 := by
  sep_entail

theorem wp_frame_split_byte_from_memRegion (m : Memory) (buf : BitVec 64) (R : SepProp)
    (hpre : m ⊨ memRegion buf 16 ∗ R) :
    ∃ (v : BitVec 8) (F : SepProp),
      m ⊨ (buf ↦₈ v) ∗ F ∧
      ∀ m' : Memory, m' ⊨ (buf ↦₈ 120#8) ∗ F → m' ⊨ memRegion buf 16 ∗ R := by
  have ⟨F, hsplit, hrestore⟩ :
      ∃ F, (m ⊨ (∃∗ v : BitVec 8, buf ↦₈ v) ∗ F) ∧
        ∀ m' : Memory, m' ⊨ (buf ↦₈ 120#8) ∗ F → m' ⊨ memRegion buf 16 ∗ R :=
    ⟨memRegion (buf + 1#64) 15 ∗ R, by wp_frame_split, fun m' hm' => by sep_entail⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hsplit
  rcases hsplit with ⟨v, hv⟩
  exact ⟨v, F, hv, hrestore⟩

theorem wp_frame_split_interior_word16 (m : Memory) (sp : BitVec 64)
    (hpre : m ⊨ memRegion (sp - 80#64) 80) :
    m ⊨ (∃∗ v : BitVec 16, (sp - 48#64) ↦₁₆ v) ∗
        (memRegion (sp - 80#64) 32 ∗ memRegion (sp - 46#64) 30) := by
  wp_frame_split

theorem wp_frame_split_symbolic_offset (m : Memory) (buf : BitVec 64) (idx : Nat) (hidx : idx < 16)
    (hpre : m ⊨ memRegion buf 16) :
    ∃ F : SepProp, m ⊨ (∃∗ v : BitVec 8, (buf + BitVec.ofNat 64 idx) ↦₈ v) ∗ F :=
  ⟨_, by wp_frame_split⟩

/-! ### Negative `#guard_msgs` out-of-range checks -/

/--
error: frame_split: no match for (buf + 16#64) ↦₈ b in precondition
hint: context contains region/slice atom `memRegion buf
  16` at the same base; carve or split the window with `pointsToBytes_focus` / `memRegion_split_le` / `stackFrameAt_split_close`
candidates: memRegion buf 16
-/
#guard_msgs in
theorem wp_frame_split_rejects_oob (m : Memory) (buf : BitVec 64) (b : BitVec 8)
    (hpre : m ⊨ memRegion buf 16) :
    m ⊨ ((buf + 16#64) ↦₈ b) ∗ emp := by
  wp_frame_split

/--
error: frame_split: no match for (buf + 13#64) ↦₃₂ w in precondition (also unmatched: memRegion buf 13)
hint: context contains region/slice atom `memRegion buf
  16` at the same base; carve or split the window with `pointsToBytes_focus` / `memRegion_split_le` / `stackFrameAt_split_close`
candidates: memRegion buf 16
-/
#guard_msgs in
theorem wp_frame_split_rejects_straddle (m : Memory) (buf : BitVec 64) (w : BitVec 32)
    (hpre : m ⊨ memRegion buf 16) :
    m ⊨ ((buf + 13#64) ↦₃₂ w) ∗ memRegion buf 13 := by
  wp_frame_split

set_option maxHeartbeats 20000 in
/--
error: frame_split: no match for (sp - 96#64) ↦₆₄ w in precondition
hint: context contains region/slice atom `memRegion (sp - 80#64)
  80` at the same base; carve or split the window with `pointsToBytes_focus` / `memRegion_split_le` / `stackFrameAt_split_close`
candidates: memRegion p0
  64, memRegion p1
  64, memRegion p2 64, memRegion p3 64, memRegion p4 64, memRegion p5 64, memRegion p6 64, memRegion p7 64, … (+1 more)
-/
#guard_msgs in
theorem wp_frame_split_many_regions_fast_fail
    (m : Memory) (sp p0 p1 p2 p3 p4 p5 p6 p7 : BitVec 64) (w : BitVec 64)
    (hpre : m ⊨
      memRegion p0 64 ∗ memRegion p1 64 ∗ memRegion p2 64 ∗ memRegion p3 64 ∗
      memRegion p4 64 ∗ memRegion p5 64 ∗ memRegion p6 64 ∗ memRegion p7 64 ∗
      memRegion (sp - 80#64) 80) :
    m ⊨ ((sp - 96#64) ↦₆₄ w) ∗ emp := by
  wp_frame_split

theorem sep_entail_weaken_single (p v : BitVec 64) :
    (p ↦₆₄ v) ⊢ memRegion p 8 := by
  sep_entail

theorem sep_entail_weaken_framed (p v : BitVec 64) (R : SepProp) :
    (p ↦₆₄ v) ∗ R ⊢ memRegion p 8 ∗ R := by
  sep_entail

theorem sep_entail_let_bound_subblock (p : BitVec 64) :
    let q := p + 8#64
    memRegion p 16 ⊢ memRegion p 8 ∗ memRegion q 8 := by
  intro q
  sep_entail

/-! ## Bit-Accumulator `Nat` Normalization -/

/-- Minimal bit-reader state holding a 64-bit shift register `hold` and bit count `bits`. -/
structure BitStreamState where
  hold : BitVec 64
  bits : Nat

def peekBits (k : Nat) (st : BitStreamState) : Nat :=
  (st.hold >>> 0).toNat % 2 ^ k

def dropBits (k : Nat) (st : BitStreamState) : BitStreamState :=
  { st with hold := st.hold >>> k, bits := st.bits - k }

theorem bit_accumulator_nibble_extract (st : BitStreamState) :
    st.hold.toNat / 16 % 16 = peekBits 4 (dropBits 4 st) ∧
    (st.hold.extractLsb' 4 4).toNat = st.hold.toNat / 16 % 16 := by
  simp [peekBits, dropBits]

theorem header_byte_high_nibble_omega (st : BitStreamState) (hdrByte : BitVec 8)
    (hhdr : hdrByte.toNat = st.hold.toNat % 256) :
    hdrByte.toNat / 16 < 16 ∧
    hdrByte.toNat / 16 = peekBits 4 (dropBits 4 st) := by
  have hlt : hdrByte.toNat < 2 ^ 8 := hdrByte.toNat_lt
  have hdiv : hdrByte.toNat / 2 ^ 4 < 2 ^ (8 - 4) := BitVec.toNat_div_pow_lt hdrByte 4
  simp [peekBits, dropBits] at *
  omega

theorem bitfield_three_way_equiv {n : Nat} (x : BitVec n) (k w : Nat) :
    (x >>> k).toNat % 2 ^ w = (x.toNat / 2 ^ k) % 2 ^ w ∧
    (x.extractLsb' k w).toNat = (x.toNat / 2 ^ k) % 2 ^ w := by
  simp [BitVec.toNat_shiftRight_mod]

/-! ## Virtual-Address Mapping Reservations (`memMapped`) -/

theorem memMapped_split_roundtrip (p : BitVec 64) (a b : Nat) (h : a + b ≤ 2 ^ 64) :
    memMapped p (a + b) = (memMapped p a ∗ memMapped (p + BitVec.ofNat 64 a) b) :=
  memMapped_split p a b h

theorem memMapped_disjointRegions_test {a₁ a₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (memMapped a₁ n₁ ∗ memMapped a₂ n₂) ⊢
      ⌜DisjointRegions a₁ n₁ a₂ n₂⌝ ∗ memMapped a₁ n₁ ∗ memMapped a₂ n₂ :=
  memMapped_disjointRegions hn₁ hn₂

theorem mapZero_mapped_unmapNonFrozen_roundtrip {m : Memory} {P : SepProp}
    {a : BitVec 64} {n : Nat}
    (hP : m ⊨ P) (hmap : m.canMap a n = true) :
    (m.mapZero a n).unmapNonFrozen a n ⊨ P :=
  Satisfies.unmapNonFrozen (Satisfies.mapZero_mapped hP hmap)

end Examples.Testing.ProofLib.MemRegionAndBitfield
