/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.Basic
import ProofLib.SepLogic.WP

/-!
# Relocatable `VmPreserved` Proofs for `Bytes::from(Vec<u8>)` and `static_clone`

Verifies relocatable `[LibsignalPlacement]` `VmPreserved` contracts for `<Bytes as From<Vec<u8>>>::from`
(Block `250`) and `bytes::bytes::static_clone` (Block `226`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement blkPC_226 blkPl_226 blkLib_eq_226 blkPC_226_pairStep_0x0
  blkPC_250 blkPl_250 blkLib_eq_250
)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  bytesFromVecStack bytesPtr bytesData bytesBoxU8Buf bytesHeader
  staticVtableSym promotableOddVtableName promotableEvenVtableName
  staticVtablePlacedAddr promotableOddVtablePlacedAddr promotableEvenVtablePlacedAddr
  bytesPlacedVtable bytesPlacedAt
  stackAt_48_eq_cells memRegion_32_eq_pointsTo64 getLsbD_zero_iff not_getLsbD_zero_iff
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget (
  bytesFromVecPlacedSpec bytesStaticClonePlacedSpec
)

private theorem toVm {s0 s1 : State}
    (h : ProofLib.NonSyscallPreserved s0 s1) (htp : s1.tpidrEl0 = s0.tpidrEl0) :
    VmPreserved s0 s1 :=
  h.toVmPreserved htp

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved

theorem bytesFromVec_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_250).rebase (blkPl_250).base H) (blkPl_250).base
      (bytesFromVecPlacedSpec A) := by
  unfold bytesFromVecPlacedSpec vecU8At vecHeader bytesPlacedAt bytesHeader bytesBoxU8Buf
    bytesFromVecStack
  simp only [memRegion_32_eq_pointsTo64, stackAt_48_eq_cells]
  cells_unfold
  wp_init x s0
  obtain ⟨v, out, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcap_eq : BitVec.ofNat 64 bs.length = cap := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ‹cap.toNat = bs.length›]
  have hif : (if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    rw [‹cap.toNat = bs.length›]
    by_cases hbs : bs = []
    · subst hbs
      have hc0 : cap = 0 := by rw [← hcap_eq]; rfl
      simp [hc0]
    · have hc0 : cap ≠ 0 := by
        intro hc
        have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
        have h0 : cap.toNat = 0 := by simp [hc]
        omega
      simp only [hbs, hc0, ↓reduceIte, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  rw [hif, hcap_eq]
  apply sepWP_seg_ls_vm (Q := (blkPC_250).rebase (blkPl_250).base (hooksException H))
    blkLib_eq_250 (mid := s0.readReg64 .lr)
  intro _m_strip
  wp_steps
  wp_if hlen0
  · have hbs_len0 : bs.length = 0 := by
      rw [← ‹cap.toNat = bs.length›, hlen0]; rfl
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm, *]) (by assumption) fun _m_real _hnsp => ?_
    have hvm : VmPreserved s0 _ := toVm _hnsp (by simp [wp_norm, arm64_norm])
    simp only [wp_norm, arm64_norm] at hvm
    simp only [bytesPlacedVtable, staticVtablePlacedAddr, staticVtableSym,
      hbs_len0, bytesPtr, bytesData, ite_true]
    wp_done
  · have hbs_len_ne : bs.length ≠ 0 := by
      intro h0
      apply hlen0
      rw [← hcap_eq, h0]
    wp_steps
    wp_if hodd
    · have hodd64 : (ptr &&& 1#64) ≠ 0#64 := getLsbD_zero_iff.mp hodd
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm, *]) (by assumption) fun _m_real _hnsp => ?_
      have hvm : VmPreserved s0 _ := toVm _hnsp (by simp [wp_norm, arm64_norm])
      simp only [wp_norm, arm64_norm] at hvm
      simp only [bytesPlacedVtable, promotableOddVtablePlacedAddr, promotableOddVtableName,
        hbs_len_ne, hodd64, bytesPtr, bytesData, ite_false]
      wp_done
    · have heven : (ptr &&& 1#64) = 0#64 := not_getLsbD_zero_iff.mp hodd
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm, *]) (by assumption) fun _m_real _hnsp => ?_
      have hvm : VmPreserved s0 _ := toVm _hnsp (by simp [wp_norm, arm64_norm])
      simp only [wp_norm, arm64_norm] at hvm
      simp only [bytesPlacedVtable, promotableEvenVtablePlacedAddr, promotableEvenVtableName,
        hbs_len_ne, heven, bytesPtr, bytesData, ite_false, ite_true]
      wp_done

theorem bytesStaticClone_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_226).rebase (blkPl_226).base H) (blkPl_226).base
      bytesStaticClonePlacedSpec := by
  unfold bytesStaticClonePlacedSpec bytesHeader
  simp only [memRegion_32_eq_pointsTo64]
  wp_init x s0
  obtain ⟨out, ptr, len⟩ := x
  dsimp only at *
  apply sepWP_seg_ls_vm (Q := (blkPC_226).rebase (blkPl_226).base (hooksException H))
    blkLib_eq_226 (mid := s0.readReg64 .lr)
  intro _m_strip
  apply blkPC_226_pairStep_0x0 _ _ rfl (by simp [*]) (by assumption)
  wp_steps
  refine SepWP.done (by simp [wp_norm, arm64_norm, *]) (by assumption) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s0 _ := toVm _hnsp (by simp [wp_norm, arm64_norm])
  simp only [wp_norm, arm64_norm] at hvm
  wp_done

end LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget
