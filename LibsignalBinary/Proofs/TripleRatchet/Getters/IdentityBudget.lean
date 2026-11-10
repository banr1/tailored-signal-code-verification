/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.SepLogic.WP.Apply

/-!
# `VmPreserved` Relocatable Contracts for `Getters/Identity`

Establishes `[LibsignalPlacement]` contracts with `VmPreserved` and panic-freedom for
`<PublicKey as TryFrom<&[u8]>>::try_from`, `SessionState::local_identity_key`, and
`SessionState::remote_identity_key`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement lsLogFilterAddr
  ls_subroutine_ok_of_block lsmpl sepWP_seq_lscl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (
  lsLogOff pkTryFromPlacedSpec pkTryFromResultAt pkTryFromSpec
)
open CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom (
  badLen_pre_weaken memRegion_40_split_badLen memRegion_40_split_badType
  memRegion_40_split_nil memRegion_40_split_ok nil_pre_weaken pointsToBytes_ok_split
  publicKey_deserialize_badKeyLength publicKey_deserialize_badKeyType
  publicKey_deserialize_nil publicKey_deserialize_ok_of_ge32
  ult_sub_of_ge33 ult_sub_of_lt32
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  blkLib_eq_28 blkPC_28 blkPl_28 blkLib_eq_29 blkPC_29 blkPl_29
  blkLib_eq_211 blkPC_211 blkPl_211
  deserialize_length_ge_33 exists_localKeyChunks_of_length_32
  localIdentityKeyStack localIdentityOkAt localKeyChunks remoteIdentityKeyStack
  remoteIdentityOkAt remoteKeyChunks stackAt_localIdentityKey_post_split
  vecGhostAt_eq_of_pos
)
open CryptoVerification.LibsignalTripleRatchet.Getters.IdentityBitVecFacts (
  add_add_eq_add add_add_ofNat_eq_add add_ofNat_eq_add extractLsb'_append_hi
  extractLsb'_append_lo le_of_eq32 sub_add_ofNat_eq_sub
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  localIdentityKeyPlacedSpec remoteIdentityKeyPlacedSpec
)

private abbrev ibv_sub_add_eq_sub :=
  @CryptoVerification.LibsignalTripleRatchet.Getters.IdentityBitVecFacts.sub_add_eq_sub

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved

/-! ## `<PublicKey as TryFrom<&[u8]>>::try_from` with `VmPreserved` -/

def pkTryFromPlacedBudgetSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved pkTryFromPlacedSpec

set_option maxHeartbeats 1600000 in
theorem pkTryFrom_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedBudgetSpec := by
  simp only [pkTryFromPlacedBudgetSpec, withVmPreserved, pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff]
  wp_init g s0
  obtain ⟨ptr, bs, out⟩ := g
  dsimp only at *
  subst h_1 h
  apply sepWP_seg_ls_vm (Q := (blkPC_211).rebase (blkPl_211).base (hooksException H))
    blkLib_eq_211 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip
  rcases bs with _ | ⟨b0, rest⟩
  · have hx1 : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using h_2
    rw [publicKey_deserialize_nil, pkTryFromResultAt,
      memRegion_40_split_nil (s0.readReg64 (Reg.gpr 8#5))]
    wp_pull_exists
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
    have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm ⊢
    refine SepWP.weaken_pre
      (nil_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
        lsLogFilterAddr) ?_
    simp only [sepConj_assoc, *]
    wp_done
  · have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
      intro heq; rw [heq] at h_2; simp at h_2
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen : rest.length < 32
      · have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = true :=
          ult_sub_of_lt32 (by simp only [List.length_cons] at h_2; omega)
            (by simp only [List.length_cons] at h_2; omega)
        rw [publicKey_deserialize_badKeyLength rest hlen, pkTryFromResultAt,
          pointsToBytes_cons, memRegion_40_split_badLen (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
        have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
        simp only [State.setMem_setMem] at hvm ⊢
        have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (rest.length + 1) := by
          apply BitVec.eq_of_toNat_eq
          simp only [List.length_cons] at h_2
          rw [h_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hx1_eq] at hvm ⊢
        refine SepWP.weaken_pre
          (badLen_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
            (BitVec.ofNat 64 (rest.length + 1)) lsLogFilterAddr rest) ?_
        try simp only [sepConj_assoc, *]
        wp_done
      · have hge32 : 32 ≤ rest.length := by omega
        have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = false :=
          ult_sub_of_ge33 (by simp only [List.length_cons] at h_2; omega)
        obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
          exists_unpack64_of_length_32 (bs := rest.take 32)
            (by simp [List.length_take, Nat.min_eq_left hge32])
        rw [publicKey_deserialize_ok_of_ge32 rest hge32, pkTryFromResultAt]
        simp only [List.Vector.toList_mk, Reg.x8]
        rw [pointsToBytes_ok_split (s0.readReg64 (Reg.gpr 0#5)) hge32,
          hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
          memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        wp_steps
        wp_if hcbz9
        · wp_steps
          refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
          have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
          simp only [State.setMem_setMem] at hvm ⊢
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, *]
          wp_done
        · wp_steps
          refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
          have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
          simp only [State.setMem_setMem] at hvm ⊢
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, *]
          wp_done
    · rw [publicKey_deserialize_badKeyType rest hb0, pkTryFromResultAt,
        pointsToBytes_cons, memRegion_40_split_badType (s0.readReg64 (Reg.gpr 8#5))]
      wp_pull_exists
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
      have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
      simp only [State.setMem_setMem] at hvm ⊢
      try simp only [sepConj_assoc, *]
      wp_done

def pkTryFromOkPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64 × BitVec 64) where
  pre := fun (p, bs, pk, out, out33) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = out ∧ PublicKey.deserialize bs = .ok pk ∧ out + 33#64 = out33⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 33 ∗ memRegion out33 15 ∗ (lsLogFilterAddr ↦₆₄ 0#64)
  post := fun (p, bs, pk, out, out33) s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion out33 15 ∗ (lsLogFilterAddr ↦₆₄ 0#64)

theorem pkTryFromOk_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (lsmpl.base 211) pkTryFromOkPlacedSpec := by
  refine subroutine_ok_map (pkTryFrom_placed_ok H) ?_
  rintro ⟨p, bs, pk, out, out33⟩ R s0 hpre
  simp only [pkTryFromOkPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes, hout33⟩, hmem⟩
  subst hout33
  refine ⟨(p, bs, out), memRegion (out + 40#64) 8 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromPlacedBudgetSpec, withVmPreserved, pkTryFromPlacedSpec, pkTryFromSpec,
      lsLogOff, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8⟩, ?_⟩
    rw [ProofLib.memRegion_split' (b := out) (n := 33) (k := 7) (b' := out + 33#64)
          rfl (by bv_omega) (by decide)]
    rw [ProofLib.memRegion_split' (b := out + 33#64) (n := 7) (k := 8) (b' := out + 40#64)
          rfl (by bv_omega) (by decide)] at hmem
    convert hmem using 1; sep_ac_rfl
  · simp only [pkTryFromPlacedBudgetSpec, withVmPreserved, pkTryFromPlacedSpec, pkTryFromSpec,
      lsLogOff, hdes, pkTryFromResultAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, htr, hpost⟩
    simp only [pkTryFromOkPlacedSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hvm, htr⟩, ?_⟩
    rw [ProofLib.memRegion_split' (b := out + 33#64) (n := 7) (k := 8) (b' := out + 40#64)
          rfl (by bv_omega) (by decide)]
    convert hpost using 1; sep_ac_rfl

/-! ## Stack Layout Splitting Helpers -/

private theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off k : Nat)
    (h : off + k ≤ bs.length) :
    (a ↦ₛ bs.drop off) =
      (a ↦ₛ (bs.drop off).take k) ∗ ((a + BitVec.ofNat 64 k) ↦ₛ bs.drop (off + k)) := by
  conv => lhs; rw [← List.take_append_drop k (bs.drop off)]
  have hlen : ((bs.drop off).take k).length = k := by
    simp [List.length_take, List.length_drop]
    omega
  rw [pointsToBytes_append, hlen, List.drop_drop]

private theorem memRegion_33_localKeyChunks (ret : BitVec 64) :
    memRegion ret 33 =
      (∃∗ b0 : BitVec 8, ret ↦₈ b0) ∗
      (∃∗ v0 : BitVec 64, (ret + 1#64) ↦₆₄ v0) ∗
      (∃∗ v8 : BitVec 8, (ret + 9#64) ↦₈ v8) ∗
      (∃∗ v9 : BitVec 32, (ret + 10#64) ↦₃₂ v9) ∗
      (∃∗ v13 : BitVec 16, (ret + 14#64) ↦₁₆ v13) ∗
      (∃∗ v15 : BitVec 64, (ret + 16#64) ↦₆₄ v15) ∗
      (∃∗ v23 : BitVec 64, (ret + 24#64) ↦₆₄ v23) ∗
      (∃∗ v31 : BitVec 8, (ret + 32#64) ↦₈ v31) := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 1) (k := 32)
        (b' := ret + 1#64) rfl (add_ofNat_eq_add ret 1#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 1#64) (n := 8) (k := 24)
        (b' := ret + 9#64) rfl (add_add_ofNat_eq_add ret 1#64 9#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 9#64) (n := 1) (k := 23)
        (b' := ret + 10#64) rfl (add_add_ofNat_eq_add ret 9#64 10#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 10#64) (n := 4) (k := 19)
        (b' := ret + 14#64) rfl (add_add_ofNat_eq_add ret 10#64 14#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 14#64) (n := 2) (k := 17)
        (b' := ret + 16#64) rfl (add_add_ofNat_eq_add ret 14#64 16#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 9)
        (b' := ret + 24#64) rfl (add_add_ofNat_eq_add ret 16#64 24#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 1)
        (b' := ret + 32#64) rfl (add_add_ofNat_eq_add ret 24#64 32#64 8 rfl) (by decide),
      memRegion_one ret, memRegion_eight (ret + 1#64), memRegion_one (ret + 9#64),
      memRegion_four (ret + 10#64), memRegion_two (ret + 14#64),
      memRegion_eight (ret + 16#64), memRegion_eight (ret + 24#64),
      memRegion_one (ret + 32#64)]

private theorem stackAt_localIdentityKey_split (sp : BitVec 64) :
    stackAt sp localIdentityKeyStack =
      memRegion (sp - 80#64) 33 ∗ memRegion (sp - 47#64) 15 ∗
      cells (sp - 32#64) 3 ∗
      (∃∗ w : BitVec 32, (sp - 8#64) ↦₃₂ w) ∗
      (∃∗ h : BitVec 16, (sp - 4#64) ↦₁₆ h) ∗
      memRegion (sp - 2#64) 2 := by
  simp only [stackAt, localIdentityKeyStack]
  rw [show BitVec.ofNat 64 80 = 80#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 33) (k := 47)
        (b' := sp - 47#64) rfl (sub_add_ofNat_eq_sub sp 80#64 47#64 33 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 47#64) (n := 15) (k := 32)
        (b' := sp - 32#64) rfl (sub_add_ofNat_eq_sub sp 47#64 32#64 15 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 24) (k := 8)
        (b' := sp - 8#64) rfl (sub_add_ofNat_eq_sub sp 32#64 8#64 24 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 8#64) (n := 4) (k := 4)
        (b' := sp - 4#64) rfl (sub_add_ofNat_eq_sub sp 8#64 4#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 2) (k := 2)
        (b' := sp - 2#64) rfl (sub_add_ofNat_eq_sub sp 4#64 2#64 2 rfl) (by decide),
      (memRegion_cells (sp - 32#64) 3 (by decide) :
        memRegion (sp - 32#64) 24 = cells (sp - 32#64) 3),
      memRegion_four (sp - 8#64),
      memRegion_two (sp - 4#64)]

private theorem vecGhostAt_eq_of_nil (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hnil : g.bytes = []) :
    vecGhostAt A g a =
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A g.cap g.ptr g.bytes := by
  unfold vecGhostAt
  rw [vecU8At_eq_header_sep_buf, hnil]
  change ((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      vecU8Buf A g.cap g.ptr [] =
    (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A g.cap g.ptr []
  simp only [sepConj_assoc]

private theorem pointsTo16_zero (a : BitVec 64) :
    (a ↦₁₆ 0#16) = (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 0#8) := by
  simp only [pointsTo16, BitVec.add_zero]
  rfl

private theorem pointsTo16_256 (a : BitVec 64) :
    (a ↦₁₆ 256#16) = (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 1#8) := by
  simp only [pointsTo16, BitVec.add_zero]
  rfl

private theorem memRegion_34_none_split (ret : BitVec 64) :
    memRegion ret 34 = (∃∗ h0 : BitVec 16, ret ↦₁₆ h0) ∗ memRegion (ret + 2#64) 32 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 2) (k := 32)
        (b' := ret + 2#64) rfl (by bv_omega) (by decide),
      memRegion_two ret]

private theorem stackAt_remoteIdentityKey_none_split (sp : BitVec 64) :
    stackAt sp remoteIdentityKeyStack =
      memRegion (sp - 144#64) 112 ∗ cells (sp - 32#64) 3 ∗ memRegion (sp - 8#64) 8 := by
  simp only [stackAt, remoteIdentityKeyStack]
  rw [show BitVec.ofNat 64 144 = 144#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 112) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 24) (k := 8)
        (b' := sp - 8#64) rfl (by bv_omega) (by decide),
      (memRegion_cells (sp - 32#64) 3 (by decide) :
        memRegion (sp - 32#64) 24 = cells (sp - 32#64) 3)]

private theorem sevenLo_eq_sevenHi (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
  rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sevenLo_eq_sevenHi' (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ rest) =
      ((a ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) := by
  subst h1 h2 h3 h4 h5 h6
  simpa only [sepConj_assoc] using
    congrArg (· ∗ rest) (sevenLo_eq_sevenHi a b0 b1 b2 b3 b4 b5 b6)

private theorem pointsTo16_32_16_eq_pointsTo64 (a : BitVec 64)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) :
    ((a ↦₁₆ v7) ∗ ((a + 2#64) ↦₃₂ v9) ∗ ((a + 6#64) ↦₁₆ v13)) =
      (a ↦₆₄ (v13 ++ v9 ++ v7)) := by
  simp only [pointsTo16, pointsTo32, pointsTo64,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have e0 : v7.extractLsb' 0 8 = (v13 ++ v9 ++ v7).extractLsb' 0 8 :=
    (extractLsb'_append_lo (v13 ++ v9) v7 0 8 (by decide)).symm
  have e1 : v7.extractLsb' 8 8 = (v13 ++ v9 ++ v7).extractLsb' 8 8 :=
    (extractLsb'_append_lo (v13 ++ v9) v7 8 8 (by decide)).symm
  have e2 : v9.extractLsb' 0 8 = (v13 ++ v9 ++ v7).extractLsb' 16 8 :=
    ((extractLsb'_append_hi (v13 ++ v9) v7 16 8 (by decide)).trans
      (extractLsb'_append_lo v13 v9 0 8 (by decide))).symm
  have e3 : v9.extractLsb' 8 8 = (v13 ++ v9 ++ v7).extractLsb' 24 8 :=
    ((extractLsb'_append_hi (v13 ++ v9) v7 24 8 (by decide)).trans
      (extractLsb'_append_lo v13 v9 8 8 (by decide))).symm
  have e4 : v9.extractLsb' 16 8 = (v13 ++ v9 ++ v7).extractLsb' 32 8 :=
    ((extractLsb'_append_hi (v13 ++ v9) v7 32 8 (by decide)).trans
      (extractLsb'_append_lo v13 v9 16 8 (by decide))).symm
  have e5 : v9.extractLsb' 24 8 = (v13 ++ v9 ++ v7).extractLsb' 40 8 :=
    ((extractLsb'_append_hi (v13 ++ v9) v7 40 8 (by decide)).trans
      (extractLsb'_append_lo v13 v9 24 8 (by decide))).symm
  have e6 : v13.extractLsb' 0 8 = (v13 ++ v9 ++ v7).extractLsb' 48 8 :=
    ((extractLsb'_append_hi (v13 ++ v9) v7 48 8 (by decide)).trans
      (extractLsb'_append_hi v13 v9 32 8 (by decide))).symm
  have e7 : v13.extractLsb' 8 8 = (v13 ++ v9 ++ v7).extractLsb' 56 8 :=
    ((extractLsb'_append_hi (v13 ++ v9) v7 56 8 (by decide)).trans
      (extractLsb'_append_hi v13 v9 40 8 (by decide))).symm
  rw [e0, e1, e2, e3, e4, e5, e6, e7]

private theorem pointsTo16_32_16_eq_pointsTo64' (a a2 a6 : BitVec 64)
    (h2 : a + 2#64 = a2) (h6 : a + 6#64 = a6)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (rest : SepProp) :
    ((a ↦₁₆ v7) ∗ (a2 ↦₃₂ v9) ∗ (a6 ↦₁₆ v13) ∗ rest) =
      ((a ↦₆₄ (v13 ++ v9 ++ v7)) ∗ rest) := by
  subst h2 h6
  simpa only [sepConj_assoc] using
    congrArg (· ∗ rest) (pointsTo16_32_16_eq_pointsTo64 a v7 v9 v13)

private theorem truncate16_zeroExtend32 (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32 : i < 32 := by omega
  simp [hi, hi32]

private theorem vecGhostAt_ss_24_of_nil (A : RustAlloc) (g : VecGhost) (ss : BitVec 64)
    (hnil : g.bytes = []) :
    vecGhostAt A g (ss + 24#64) =
      ((ss + 24#64) ↦₆₄ g.cap) ∗ ((ss + 32#64) ↦₆₄ g.ptr) ∗ ((ss + 40#64) ↦₆₄ 0#64) ∗
      vecU8Buf A g.cap g.ptr g.bytes := by
  rw [vecGhostAt_eq_of_nil A g (ss + 24#64) hnil]
  have h32 : ss + 24#64 + 8#64 = ss + 32#64 := by bv_omega
  have h40 : ss + 24#64 + 16#64 = ss + 40#64 := by bv_omega
  rw [h32, h40]

private theorem vecGhostAt_ss_24_of_pos (A : RustAlloc) (g : VecGhost) (ss : BitVec 64)
    (hpos : 0 < g.bytes.length) :
    vecGhostAt A g (ss + 24#64) =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      ((ss + 24#64) ↦₆₄ g.cap) ∗ ((ss + 32#64) ↦₆₄ g.ptr) ∗
      ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      A.live g.ptr g.cap.toNat 1 ∗
      (g.ptr ↦ₛ g.bytes) ∗
      memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) := by
  rw [vecGhostAt_eq_of_pos A g (ss + 24#64) hpos]
  have h32 : ss + 24#64 + 8#64 = ss + 32#64 := by bv_omega
  have h40 : ss + 24#64 + 16#64 = ss + 40#64 := by bv_omega
  rw [h32, h40]
  sep_ac_rfl

private theorem remoteKeyChunks_ret_2 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunks (ret + 2#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((ret + 2#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((ret + 6#64) ↦₈ b4) ∗ ((ret + 7#64) ↦₈ b5) ∗ ((ret + 8#64) ↦₈ b6) ∗
      ((ret + 9#64) ↦₁₆ v7) ∗ ((ret + 11#64) ↦₃₂ v9) ∗ ((ret + 15#64) ↦₁₆ v13) ∗
      ((ret + 17#64) ↦₆₄ v15) ∗ ((ret + 25#64) ↦₆₄ v23) ∗ ((ret + 33#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunks]
  have hr6 : ret + 2#64 + 4#64 = ret + 6#64 := add_add_eq_add ret 2#64 6#64 4#64 rfl
  have hr7 : ret + 2#64 + 5#64 = ret + 7#64 := add_add_eq_add ret 2#64 7#64 5#64 rfl
  have hr8 : ret + 2#64 + 6#64 = ret + 8#64 := add_add_eq_add ret 2#64 8#64 6#64 rfl
  have hr9 : ret + 2#64 + 7#64 = ret + 9#64 := add_add_eq_add ret 2#64 9#64 7#64 rfl
  have hr11 : ret + 2#64 + 9#64 = ret + 11#64 := add_add_eq_add ret 2#64 11#64 9#64 rfl
  have hr15 : ret + 2#64 + 13#64 = ret + 15#64 := add_add_eq_add ret 2#64 15#64 13#64 rfl
  have hr17 : ret + 2#64 + 15#64 = ret + 17#64 := add_add_eq_add ret 2#64 17#64 15#64 rfl
  have hr25 : ret + 2#64 + 23#64 = ret + 25#64 := add_add_eq_add ret 2#64 25#64 23#64 rfl
  have hr33 : ret + 2#64 + 31#64 = ret + 33#64 := add_add_eq_add ret 2#64 33#64 31#64 rfl
  rw [hr6, hr7, hr8, hr9, hr11, hr15, hr17, hr25, hr33]

private theorem remoteKeyChunks_sp_79 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunks (sp - 79#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((sp - 79#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 75#64) ↦₈ b4) ∗ ((sp - 74#64) ↦₈ b5) ∗ ((sp - 73#64) ↦₈ b6) ∗
      ((sp - 72#64) ↦₁₆ v7) ∗ ((sp - 70#64) ↦₃₂ v9) ∗ ((sp - 66#64) ↦₁₆ v13) ∗
      ((sp - 64#64) ↦₆₄ v15) ∗ ((sp - 56#64) ↦₆₄ v23) ∗ ((sp - 48#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunks]
  have h75 : sp - 79#64 + 4#64 = sp - 75#64 := ibv_sub_add_eq_sub sp 79#64 75#64 4#64 rfl
  have h74 : sp - 79#64 + 5#64 = sp - 74#64 := ibv_sub_add_eq_sub sp 79#64 74#64 5#64 rfl
  have h73 : sp - 79#64 + 6#64 = sp - 73#64 := ibv_sub_add_eq_sub sp 79#64 73#64 6#64 rfl
  have h72 : sp - 79#64 + 7#64 = sp - 72#64 := ibv_sub_add_eq_sub sp 79#64 72#64 7#64 rfl
  have h70 : sp - 79#64 + 9#64 = sp - 70#64 := ibv_sub_add_eq_sub sp 79#64 70#64 9#64 rfl
  have h66 : sp - 79#64 + 13#64 = sp - 66#64 := ibv_sub_add_eq_sub sp 79#64 66#64 13#64 rfl
  have h64 : sp - 79#64 + 15#64 = sp - 64#64 := ibv_sub_add_eq_sub sp 79#64 64#64 15#64 rfl
  have h56 : sp - 79#64 + 23#64 = sp - 56#64 := ibv_sub_add_eq_sub sp 79#64 56#64 23#64 rfl
  have h48 : sp - 79#64 + 31#64 = sp - 48#64 := ibv_sub_add_eq_sub sp 79#64 48#64 31#64 rfl
  rw [h75, h74, h73, h72, h70, h66, h64, h56, h48]

private theorem sevenLo_sp_79 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 79#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 75#64) ↦₈ b4) ∗ ((sp - 74#64) ↦₈ b5) ∗ ((sp - 73#64) ↦₈ b6) ∗ rest) =
      (((sp - 79#64) ↦₈ b0) ∗ ((sp - 78#64) ↦₈ b1) ∗ ((sp - 77#64) ↦₈ b2) ∗
       ((sp - 76#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 79#64) (sp - 78#64) (sp - 77#64) (sp - 76#64)
    (sp - 75#64) (sp - 74#64) (sp - 73#64)
    (ibv_sub_add_eq_sub sp 79#64 78#64 1#64 rfl)
    (ibv_sub_add_eq_sub sp 79#64 77#64 2#64 rfl)
    (ibv_sub_add_eq_sub sp 79#64 76#64 3#64 rfl)
    (ibv_sub_add_eq_sub sp 79#64 75#64 4#64 rfl)
    (ibv_sub_add_eq_sub sp 79#64 74#64 5#64 rfl)
    (ibv_sub_add_eq_sub sp 79#64 73#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_sp_96 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 96#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 92#64) ↦₈ b4) ∗ ((sp - 91#64) ↦₈ b5) ∗ ((sp - 90#64) ↦₈ b6) ∗ rest) =
      (((sp - 96#64) ↦₈ b0) ∗ ((sp - 95#64) ↦₈ b1) ∗ ((sp - 94#64) ↦₈ b2) ∗
       ((sp - 93#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 96#64) (sp - 95#64) (sp - 94#64) (sp - 93#64)
    (sp - 92#64) (sp - 91#64) (sp - 90#64)
    (ibv_sub_add_eq_sub sp 96#64 95#64 1#64 rfl)
    (ibv_sub_add_eq_sub sp 96#64 94#64 2#64 rfl)
    (ibv_sub_add_eq_sub sp 96#64 93#64 3#64 rfl)
    (ibv_sub_add_eq_sub sp 96#64 92#64 4#64 rfl)
    (ibv_sub_add_eq_sub sp 96#64 91#64 5#64 rfl)
    (ibv_sub_add_eq_sub sp 96#64 90#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_sp_136 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 136#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 132#64) ↦₈ b4) ∗ ((sp - 131#64) ↦₈ b5) ∗ ((sp - 130#64) ↦₈ b6) ∗ rest) =
      (((sp - 136#64) ↦₈ b0) ∗ ((sp - 135#64) ↦₈ b1) ∗ ((sp - 134#64) ↦₈ b2) ∗
       ((sp - 133#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 136#64) (sp - 135#64) (sp - 134#64) (sp - 133#64)
    (sp - 132#64) (sp - 131#64) (sp - 130#64)
    (ibv_sub_add_eq_sub sp 136#64 135#64 1#64 rfl)
    (ibv_sub_add_eq_sub sp 136#64 134#64 2#64 rfl)
    (ibv_sub_add_eq_sub sp 136#64 133#64 3#64 rfl)
    (ibv_sub_add_eq_sub sp 136#64 132#64 4#64 rfl)
    (ibv_sub_add_eq_sub sp 136#64 131#64 5#64 rfl)
    (ibv_sub_add_eq_sub sp 136#64 130#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_ret_2 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((ret + 2#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((ret + 6#64) ↦₈ b4) ∗ ((ret + 7#64) ↦₈ b5) ∗ ((ret + 8#64) ↦₈ b6) ∗ rest) =
      (((ret + 2#64) ↦₈ b0) ∗ ((ret + 3#64) ↦₈ b1) ∗ ((ret + 4#64) ↦₈ b2) ∗
       ((ret + 5#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (ret + 2#64) (ret + 3#64) (ret + 4#64) (ret + 5#64)
    (ret + 6#64) (ret + 7#64) (ret + 8#64)
    (add_add_eq_add ret 2#64 3#64 1#64 rfl)
    (add_add_eq_add ret 2#64 4#64 2#64 rfl)
    (add_add_eq_add ret 2#64 5#64 3#64 rfl)
    (add_add_eq_add ret 2#64 6#64 4#64 rfl)
    (add_add_eq_add ret 2#64 7#64 5#64 rfl)
    (add_add_eq_add ret 2#64 8#64 6#64 rfl)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem pointsTo16_32_16_sp_89 (sp : BitVec 64)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (rest : SepProp) :
    (((sp - 89#64) ↦₁₆ v7) ∗ ((sp - 87#64) ↦₃₂ v9) ∗ ((sp - 83#64) ↦₁₆ v13) ∗ rest) =
      (((sp - 89#64) ↦₆₄ (v13 ++ v9 ++ v7)) ∗ rest) :=
  pointsTo16_32_16_eq_pointsTo64' (sp - 89#64) (sp - 87#64) (sp - 83#64)
    (ibv_sub_add_eq_sub sp 89#64 87#64 2#64 rfl)
    (ibv_sub_add_eq_sub sp 89#64 83#64 6#64 rfl) v7 v9 v13 rest

private theorem pointsTo16_32_16_ret_9 (ret : BitVec 64)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (rest : SepProp) :
    (((ret + 9#64) ↦₁₆ v7) ∗ ((ret + 11#64) ↦₃₂ v9) ∗ ((ret + 15#64) ↦₁₆ v13) ∗ rest) =
      (((ret + 9#64) ↦₆₄ (v13 ++ v9 ++ v7)) ∗ rest) :=
  pointsTo16_32_16_eq_pointsTo64' (ret + 9#64) (ret + 11#64) (ret + 15#64)
    (add_add_eq_add ret 9#64 11#64 2#64 rfl)
    (add_add_eq_add ret 9#64 15#64 6#64 rfl) v7 v9 v13 rest

private theorem exists_remoteKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
      (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
      (v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = remoteKeyChunks a b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 := by
  refine ⟨bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8,
    bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8,
    pack16 (bs.getD 7 0#8) (bs.getD 8 0#8),
    pack32 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8),
    pack16 (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 4 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 4 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 5 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 6 1 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 7 2 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 9 4 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 13 2 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 15 8 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 23 8 (le_of_eq32 h (by decide)),
      pointsToBytes_drop_split _ bs 31 1 (le_of_eq32 h (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 4 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 5 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (le_of_eq32 h (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 7 (le_of_eq32 h (by decide)),
      pointsToBytes_take4_eq_pointsTo32 _ bs 9 (le_of_eq32 h (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 13 (le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (le_of_eq32 h (by decide))]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
  rw [h8, h1, h4, h2]
  simp only [remoteKeyChunks, pack32, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion_34_remoteKeyChunks (ret : BitVec 64) :
    memRegion ret 34 =
      (∃∗ h0 : BitVec 16, ret ↦₁₆ h0) ∗
      (∃∗ r2 : BitVec 32, (ret + 2#64) ↦₃₂ r2) ∗
      (∃∗ r6 : BitVec 8, (ret + 6#64) ↦₈ r6) ∗
      (∃∗ r7 : BitVec 8, (ret + 7#64) ↦₈ r7) ∗
      (∃∗ r8 : BitVec 8, (ret + 8#64) ↦₈ r8) ∗
      (∃∗ r9 : BitVec 64, (ret + 9#64) ↦₆₄ r9) ∗
      (∃∗ r17 : BitVec 64, (ret + 17#64) ↦₆₄ r17) ∗
      (∃∗ r25 : BitVec 64, (ret + 25#64) ↦₆₄ r25) ∗
      (∃∗ r33 : BitVec 8, (ret + 33#64) ↦₈ r33) := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 2) (k := 32)
        (b' := ret + 2#64) rfl (add_ofNat_eq_add ret 2#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 2#64) (n := 4) (k := 28)
        (b' := ret + 6#64) rfl (add_add_ofNat_eq_add ret 2#64 6#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 6#64) (n := 1) (k := 27)
        (b' := ret + 7#64) rfl (add_add_ofNat_eq_add ret 6#64 7#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 7#64) (n := 1) (k := 26)
        (b' := ret + 8#64) rfl (add_add_ofNat_eq_add ret 7#64 8#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 1) (k := 25)
        (b' := ret + 9#64) rfl (add_add_ofNat_eq_add ret 8#64 9#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 9#64) (n := 8) (k := 17)
        (b' := ret + 17#64) rfl (add_add_ofNat_eq_add ret 9#64 17#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 17#64) (n := 8) (k := 9)
        (b' := ret + 25#64) rfl (add_add_ofNat_eq_add ret 17#64 25#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := ret + 25#64) (n := 8) (k := 1)
        (b' := ret + 33#64) rfl (add_add_ofNat_eq_add ret 25#64 33#64 8 rfl) (by decide),
      memRegion_two ret, memRegion_four (ret + 2#64),
      memRegion_one (ret + 6#64), memRegion_one (ret + 7#64), memRegion_one (ret + 8#64),
      memRegion_eight (ret + 9#64), memRegion_eight (ret + 17#64),
      memRegion_eight (ret + 25#64), memRegion_one (ret + 33#64)]

private theorem stackAt_remoteIdentityKey_some_split (sp : BitVec 64) :
    stackAt sp remoteIdentityKeyStack =
      memRegion (sp - 144#64) 8 ∗
      (∃∗ s8 : BitVec 8, (sp - 136#64) ↦₈ s8) ∗
      (∃∗ s9 : BitVec 8, (sp - 135#64) ↦₈ s9) ∗
      (∃∗ s10 : BitVec 8, (sp - 134#64) ↦₈ s10) ∗
      (∃∗ s11 : BitVec 32, (sp - 133#64) ↦₃₂ s11) ∗
      memRegion (sp - 129#64) 1 ∗
      (∃∗ s16 : BitVec 64, (sp - 128#64) ↦₆₄ s16) ∗
      (∃∗ s24 : BitVec 8, (sp - 120#64) ↦₈ s24) ∗
      memRegion (sp - 119#64) 7 ∗
      (∃∗ s32 : BitVec 64, (sp - 112#64) ↦₆₄ s32) ∗
      (∃∗ s40 : BitVec 8, (sp - 104#64) ↦₈ s40) ∗
      memRegion (sp - 103#64) 7 ∗
      (∃∗ s48 : BitVec 32, (sp - 96#64) ↦₃₂ s48) ∗
      (∃∗ s52 : BitVec 8, (sp - 92#64) ↦₈ s52) ∗
      (∃∗ s53 : BitVec 8, (sp - 91#64) ↦₈ s53) ∗
      (∃∗ s54 : BitVec 8, (sp - 90#64) ↦₈ s54) ∗
      (∃∗ s55 : BitVec 16, (sp - 89#64) ↦₁₆ s55) ∗
      (∃∗ s57 : BitVec 32, (sp - 87#64) ↦₃₂ s57) ∗
      (∃∗ s61 : BitVec 16, (sp - 83#64) ↦₁₆ s61) ∗
      memRegion (sp - 81#64) 1 ∗
      memRegion (sp - 80#64) 33 ∗
      memRegion (sp - 47#64) 15 ∗
      cells (sp - 32#64) 3 ∗
      (∃∗ w : BitVec 32, (sp - 8#64) ↦₃₂ w) ∗
      (∃∗ h : BitVec 16, (sp - 4#64) ↦₁₆ h) ∗
      memRegion (sp - 2#64) 2 := by
  simp only [stackAt, remoteIdentityKeyStack]
  rw [show BitVec.ofNat 64 144 = 144#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 136)
        (b' := sp - 136#64) rfl (sub_add_ofNat_eq_sub sp 144#64 136#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 1) (k := 135)
        (b' := sp - 135#64) rfl (sub_add_ofNat_eq_sub sp 136#64 135#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 135#64) (n := 1) (k := 134)
        (b' := sp - 134#64) rfl (sub_add_ofNat_eq_sub sp 135#64 134#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 134#64) (n := 1) (k := 133)
        (b' := sp - 133#64) rfl (sub_add_ofNat_eq_sub sp 134#64 133#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 133#64) (n := 4) (k := 129)
        (b' := sp - 129#64) rfl (sub_add_ofNat_eq_sub sp 133#64 129#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 129#64) (n := 1) (k := 128)
        (b' := sp - 128#64) rfl (sub_add_ofNat_eq_sub sp 129#64 128#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 120)
        (b' := sp - 120#64) rfl (sub_add_ofNat_eq_sub sp 128#64 120#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 1) (k := 119)
        (b' := sp - 119#64) rfl (sub_add_ofNat_eq_sub sp 120#64 119#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 119#64) (n := 7) (k := 112)
        (b' := sp - 112#64) rfl (sub_add_ofNat_eq_sub sp 119#64 112#64 7 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 8) (k := 104)
        (b' := sp - 104#64) rfl (sub_add_ofNat_eq_sub sp 112#64 104#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 1) (k := 103)
        (b' := sp - 103#64) rfl (sub_add_ofNat_eq_sub sp 104#64 103#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 103#64) (n := 7) (k := 96)
        (b' := sp - 96#64) rfl (sub_add_ofNat_eq_sub sp 103#64 96#64 7 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 4) (k := 92)
        (b' := sp - 92#64) rfl (sub_add_ofNat_eq_sub sp 96#64 92#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 92#64) (n := 1) (k := 91)
        (b' := sp - 91#64) rfl (sub_add_ofNat_eq_sub sp 92#64 91#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 91#64) (n := 1) (k := 90)
        (b' := sp - 90#64) rfl (sub_add_ofNat_eq_sub sp 91#64 90#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 90#64) (n := 1) (k := 89)
        (b' := sp - 89#64) rfl (sub_add_ofNat_eq_sub sp 90#64 89#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 89#64) (n := 2) (k := 87)
        (b' := sp - 87#64) rfl (sub_add_ofNat_eq_sub sp 89#64 87#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 87#64) (n := 4) (k := 83)
        (b' := sp - 83#64) rfl (sub_add_ofNat_eq_sub sp 87#64 83#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 83#64) (n := 2) (k := 81)
        (b' := sp - 81#64) rfl (sub_add_ofNat_eq_sub sp 83#64 81#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 81#64) (n := 1) (k := 80)
        (b' := sp - 80#64) rfl (sub_add_ofNat_eq_sub sp 81#64 80#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 33) (k := 47)
        (b' := sp - 47#64) rfl (sub_add_ofNat_eq_sub sp 80#64 47#64 33 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 47#64) (n := 15) (k := 32)
        (b' := sp - 32#64) rfl (sub_add_ofNat_eq_sub sp 47#64 32#64 15 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 24) (k := 8)
        (b' := sp - 8#64) rfl (sub_add_ofNat_eq_sub sp 32#64 8#64 24 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 8#64) (n := 4) (k := 4)
        (b' := sp - 4#64) rfl (sub_add_ofNat_eq_sub sp 8#64 4#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 2) (k := 2)
        (b' := sp - 2#64) rfl (sub_add_ofNat_eq_sub sp 4#64 2#64 2 rfl) (by decide),
      memRegion_one (sp - 136#64), memRegion_one (sp - 135#64), memRegion_one (sp - 134#64),
      memRegion_four (sp - 133#64), memRegion_eight (sp - 128#64), memRegion_one (sp - 120#64),
      memRegion_eight (sp - 112#64), memRegion_one (sp - 104#64),
      memRegion_four (sp - 96#64), memRegion_one (sp - 92#64),
      memRegion_one (sp - 91#64), memRegion_one (sp - 90#64),
      memRegion_two (sp - 89#64), memRegion_four (sp - 87#64), memRegion_two (sp - 83#64),
      (memRegion_cells (sp - 32#64) 3 (by decide) :
        memRegion (sp - 32#64) 24 = cells (sp - 32#64) 3),
      memRegion_four (sp - 8#64), memRegion_two (sp - 4#64)]

private theorem memRegion_sp_80_33_remoteKeyChunks (sp : BitVec 64) :
    memRegion (sp - 80#64) 33 =
      (∃∗ k_tag : BitVec 8, (sp - 80#64) ↦₈ k_tag) ∗
      (∃∗ k0 : BitVec 8, (sp - 79#64) ↦₈ k0) ∗
      (∃∗ k1 : BitVec 8, (sp - 78#64) ↦₈ k1) ∗
      (∃∗ k2 : BitVec 8, (sp - 77#64) ↦₈ k2) ∗
      (∃∗ k3 : BitVec 32, (sp - 76#64) ↦₃₂ k3) ∗
      (∃∗ k7 : BitVec 16, (sp - 72#64) ↦₁₆ k7) ∗
      (∃∗ k9 : BitVec 32, (sp - 70#64) ↦₃₂ k9) ∗
      (∃∗ k13 : BitVec 16, (sp - 66#64) ↦₁₆ k13) ∗
      (∃∗ k15 : BitVec 64, (sp - 64#64) ↦₆₄ k15) ∗
      (∃∗ k23 : BitVec 64, (sp - 56#64) ↦₆₄ k23) ∗
      (∃∗ k31 : BitVec 8, (sp - 48#64) ↦₈ k31) := by
  rw [ProofLib.memRegion_split' (b := sp - 80#64) (n := 1) (k := 32)
        (b' := sp - 79#64) rfl (sub_add_ofNat_eq_sub sp 80#64 79#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 79#64) (n := 1) (k := 31)
        (b' := sp - 78#64) rfl (sub_add_ofNat_eq_sub sp 79#64 78#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 78#64) (n := 1) (k := 30)
        (b' := sp - 77#64) rfl (sub_add_ofNat_eq_sub sp 78#64 77#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 77#64) (n := 1) (k := 29)
        (b' := sp - 76#64) rfl (sub_add_ofNat_eq_sub sp 77#64 76#64 1 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 76#64) (n := 4) (k := 25)
        (b' := sp - 72#64) rfl (sub_add_ofNat_eq_sub sp 76#64 72#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 2) (k := 23)
        (b' := sp - 70#64) rfl (sub_add_ofNat_eq_sub sp 72#64 70#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 70#64) (n := 4) (k := 19)
        (b' := sp - 66#64) rfl (sub_add_ofNat_eq_sub sp 70#64 66#64 4 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 66#64) (n := 2) (k := 17)
        (b' := sp - 64#64) rfl (sub_add_ofNat_eq_sub sp 66#64 64#64 2 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 9)
        (b' := sp - 56#64) rfl (sub_add_ofNat_eq_sub sp 64#64 56#64 8 rfl) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 1)
        (b' := sp - 48#64) rfl (sub_add_ofNat_eq_sub sp 56#64 48#64 8 rfl) (by decide),
      memRegion_one (sp - 80#64), memRegion_one (sp - 79#64),
      memRegion_one (sp - 78#64), memRegion_one (sp - 77#64),
      memRegion_four (sp - 76#64), memRegion_two (sp - 72#64),
      memRegion_four (sp - 70#64), memRegion_two (sp - 66#64),
      memRegion_eight (sp - 64#64), memRegion_eight (sp - 56#64),
      memRegion_one (sp - 48#64)]

/-! ## `SessionState` Identity-Key Getters -/

set_option maxHeartbeats 1600000 in
theorem local_identity_key_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_28).rebase (blkPl_28).base H) (blkPl_28).base
      (withLsCodeLoaded lsmpl (localIdentityKeyPlacedSpec A)) := by
  simp only [withLsCodeLoaded, localIdentityKeyPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Getters.localIdentityKeyPlacedSpec]
  have htry := ls_subroutine_ok_of_block (callerProg := (blkPC_28).rebase (blkPl_28).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (pkTryFromOk_placed_ok H))
  simp only [withLsCodeLoaded, pkTryFromOkPlacedSpec] at htry
  wp_init x s0; obtain ⟨ss, g, ik, ret⟩ := x; dsimp only at *; subst h_2 h_3
  have hge33 := deserialize_length_ge_33 h_1
  have hpos : 0 < g.bytes.length := by omega
  have hbs32 : ik.publicKey.bytes.toList.length = 32 := by simp
  obtain ⟨v0, v8, v9, v13, v15, v23, v31, hchunks⟩ := exists_localKeyChunks_of_length_32 hbs32
  rw [vecGhostAt_eq_of_pos A g (s0.readReg64 (Reg.gpr 0#5)) hpos,
      memRegion_33_localKeyChunks (s0.readReg64 (Reg.gpr 8#5)),
      localIdentityOkAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  nth_rw 1 [stackAt_localIdentityKey_split s0.sp]
  rw [stackAt_localIdentityKey_post_split s0.sp]
  dsimp only [localKeyChunks]; cells_unfold; wp_pull_exists
  refine SepWP.pure_elim ?_; rintro ⟨hlen_cap, hcap_lt, hptr_ne⟩
  have hlen_toNat : (BitVec.ofNat 64 g.bytes.length).toNat = g.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp47 : s0.sp - 80#64 + 33#64 = s0.sp - 47#64 := by bv_omega
  apply sepWP_seq_lscl h (mid := lsmpl.base 211)
  apply sepWP_seg_ls_vm (Q := (blkPC_28).rebase (blkPl_28).base (hooksException H))
    blkLib_eq_28 (mid := lsmpl.base 211)
  intro _m_strip1
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
  have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  wp_apply
  have hvm_call : VmPreserved _ sf := ‹_›
  have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
  rw [hchunks (s0.sp - 79#64)]; dsimp only [localKeyChunks]
  rw [ibv_sub_add_eq_sub s0.sp 79#64 71#64 8#64 rfl,
      ibv_sub_add_eq_sub s0.sp 79#64 70#64 9#64 rfl,
      ibv_sub_add_eq_sub s0.sp 79#64 66#64 13#64 rfl,
      ibv_sub_add_eq_sub s0.sp 79#64 64#64 15#64 rfl,
      ibv_sub_add_eq_sub s0.sp 79#64 56#64 23#64 rfl,
      ibv_sub_add_eq_sub s0.sp 79#64 48#64 31#64 rfl,
      add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 9#64 8#64 rfl,
      add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 10#64 9#64 rfl,
      add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 14#64 13#64 rfl,
      add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 16#64 15#64 rfl,
      add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 24#64 23#64 rfl,
      add_add_eq_add (s0.readReg64 (Reg.gpr 8#5)) 1#64 32#64 31#64 rfl]
  apply sepWP_seg_ls_vm (Q := (blkPC_28).rebase (blkPl_28).base (hooksException H))
    blkLib_eq_28 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
  have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm2 ⊢
  have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
  clear hvm1 hvm_call hvm_after_call hvm2
  simp only [sepConj_assoc, *]
  wp_done

set_option maxHeartbeats 1600000 in
theorem remote_identity_key_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_29).rebase (blkPl_29).base H) (blkPl_29).base
      (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)) := by
  simp only [withLsCodeLoaded, remoteIdentityKeyPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyPlacedSpec]
  have htry := ls_subroutine_ok_of_block (callerProg := (blkPC_29).rebase (blkPl_29).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (pkTryFromOk_placed_ok H))
  simp only [withLsCodeLoaded, pkTryFromOkPlacedSpec] at htry
  wp_init x s0; obtain ⟨ss, g, rem, ret⟩ := x; dsimp only at *; subst h_2 h_3
  cases rem with
  | none =>
    dsimp only at h_1
    rw [vecGhostAt_ss_24_of_nil A g (s0.readReg64 (Reg.gpr 0#5)) h_1,
        memRegion_34_none_split (s0.readReg64 (Reg.gpr 8#5)),
        remoteIdentityOkAt, stackAt_remoteIdentityKey_none_split s0.sp]
    cells_unfold; wp_pull_exists
    apply sepWP_seg_ls_vm (Q := (blkPC_29).rebase (blkPl_29).base (hooksException H))
      blkLib_eq_29 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip0
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real0 hnsp0 => ?_
    have hvm_final : VmPreserved s0 _ := hnsp0.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm_final ⊢
    rw [pointsTo16_zero (s0.readReg64 (Reg.gpr 8#5))]
    simp only [sepConj_assoc, *]
    wp_done
  | some ik =>
    dsimp only at h_1
    have hge33 := deserialize_length_ge_33 h_1
    have hpos : 0 < g.bytes.length := by omega
    have hbs32 : ik.publicKey.bytes.toList.length = 32 := by simp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
      exists_remoteKeyChunks_of_length_32 hbs32
    rw [vecGhostAt_ss_24_of_pos A g (s0.readReg64 (Reg.gpr 0#5)) hpos,
        memRegion_34_remoteKeyChunks (s0.readReg64 (Reg.gpr 8#5)),
        remoteIdentityOkAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 2#64),
        remoteKeyChunks_ret_2 (s0.readReg64 (Reg.gpr 8#5)),
        stackAt_remoteIdentityKey_some_split s0.sp]
    cells_unfold; wp_pull_exists; refine SepWP.pure_elim ?_; rintro ⟨hlen_cap, hcap_lt, hptr_ne⟩
    have hlen_toNat : (BitVec.ofNat 64 g.bytes.length).toNat = g.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsp47 : s0.sp - 80#64 + 33#64 = s0.sp - 47#64 := by bv_omega
    have hlen_ne : (BitVec.ofNat 64 g.bytes.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h0
      have h0' := congrArg BitVec.toNat h0
      rw [hlen_toNat] at h0'; change g.bytes.length = 0 at h0'; omega
    apply sepWP_seq_lscl h (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_29).rebase (blkPl_29).base (hooksException H))
      blkLib_eq_29 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hvm_call : VmPreserved _ sf := ‹_›
    have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
    apply sepWP_seg_ls_vm (Q := (blkPC_29).rebase (blkPl_29).base (hooksException H))
      blkLib_eq_29 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    rw [hchunks (s0.sp - 79#64), remoteKeyChunks_sp_79 s0.sp]; wp_steps
    rw [sevenLo_sp_79 s0.sp]; wp_steps
    rw [sevenLo_sp_96 s0.sp]; wp_steps
    rw [← sevenLo_sp_96 s0.sp]; wp_steps
    rw [sevenLo_sp_96 s0.sp]; wp_steps
    rw [← sevenLo_sp_136 s0.sp]; wp_steps
    rw [sevenLo_sp_136 s0.sp]; wp_steps
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    rw [pointsTo16_32_16_sp_89 s0.sp, sevenLo_ret_2 (s0.readReg64 (Reg.gpr 8#5))]; wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    clear hvm1 hvm_call hvm_after_call hvm2
    try rw [pointsTo16_256 (s0.readReg64 (Reg.gpr 8#5))]
    try rw [← sevenLo_ret_2 (s0.readReg64 (Reg.gpr 8#5))]
    try rw [← pointsTo16_32_16_ret_9 (s0.readReg64 (Reg.gpr 8#5))]
    try rw [← sevenLo_sp_96 s0.sp]
    try rw [← pointsTo16_32_16_sp_89 s0.sp]
    try rw [memRegion_sp_80_33_remoteKeyChunks s0.sp]
    simp only [sepConj_assoc, *]
    wp_done

end LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
