/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import ProofLib

/-!
# Stack-Frame and `Vec` Header Bridges

Re-exports `ProofLib` stack-region and cell lemmas into `VerifiedLibraries.RustStd`, splits
`wrapperFrame` into callee stack space and local 8-byte slots, and relates 24-byte `memRegion`
blocks to `vecHeader` triples.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 ProofLib

export ProofLib (stackAt stackAt_eq_stackFrameAt cells cells_zero cells_succ cells_split
  cells_split_sub cells_sub_succ cells_sub_succ_entails memRegion_cells stackAt_eq_cells
  stackAt_split_cells stackAt_split_bottom spAligned_sub spAligned_sub_beq)

theorem vecWrapperFrame_split (sp : BitVec 64) (calleeBytes k : Nat)
    (hk : calleeBytes + 8 * k ≤ wrapperStack := by decide) :
    wrapperFrame sp =
      memRegion (sp - 4352#64) (wrapperStack - calleeBytes - 8 * k) ∗
        stackAt (sp - BitVec.ofNat 64 (8 * k)) calleeBytes ∗
        cells (sp - BitVec.ofNat 64 (8 * k)) k :=
  ProofLib.wrapperFrame_split sp (wrapperStack := wrapperStack) (hookStack := calleeBytes) k hk
    (by decide)

theorem vecWrapperFrame_split_hook (sp : BitVec 64) (k : Nat)
    (hk : 8 * k ≤ 256 := by decide) :
    wrapperFrame sp =
      memRegion (sp - 4352#64) (256 - 8 * k) ∗
        hookFrame (sp - BitVec.ofNat 64 (8 * k)) ∗
        cells (sp - BitVec.ofNat 64 (8 * k)) k :=
  vecWrapperFrame_split sp hookStack k (by unfold hookStack wrapperStack; omega)

theorem memRegion24_eq_vecHeader (v : BitVec 64) :
    memRegion v 24 = ∃∗ c : BitVec 64, ∃∗ p : BitVec 64, ∃∗ l : BitVec 64, vecHeader v c p l := by
  rw [show (24 : Nat) = 8 * 3 by rfl, memRegion_cells v 3 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right, vecHeader]
  have h16 : v + 8#64 + 8#64 = v + 16#64 := by bv_arith
  rw [h16]

theorem memRegion_header (v : BitVec 64) :
    memRegion v 24 = ∃∗ c : BitVec 64, ∃∗ p : BitVec 64, ∃∗ l : BitVec 64, vecHeader v c p l :=
  memRegion24_eq_vecHeader v

theorem vecHeader_entails_memRegion24 (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len ⊢ memRegion v 24 := by
  rw [memRegion24_eq_vecHeader]
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (Entails.sepExists_right len (Entails.refl _)))

theorem vecHeader_entails_memRegion (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len ⊢ memRegion v 24 :=
  vecHeader_entails_memRegion24 v cap ptr len

theorem wrapperFrame_split (sp : BitVec 64) (k : Nat) (hk : hookStack + 8 * k ≤ wrapperStack) :
    wrapperFrame sp =
      memRegion (sp - BitVec.ofNat 64 wrapperStack) (wrapperStack - hookStack - 8 * k) ∗
        hookFrame (sp - BitVec.ofNat 64 (8 * k)) ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k :=
  ProofLib.wrapperFrame_split sp k hk (by decide)

end VerifiedLibraries.RustStd
