/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.InternalTop
public import VerifiedLibraries.SwissTable.Proofs.Neon
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.SymWP
import ProofLib.SepLogic.LoopTactics
import ProofLib.BV.ReflectROBDD

/-!
# Key Probing and `SwissTableInv` Lookup Bridges

`hashbrown` `U64Map` specializations of `VerifiedLibraries.SwissTable`, covering the static empty
control group, `probePos` and `slotAddr` identities, and `SwissTableInv` lookup bridges to
`cliMapLookup`.
-/
set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 ProofLib

export VerifiedLibraries.SwissTable (
  getLane8 getLane8_pack64 ctrlGroupWord getLane8_ctrlGroupWord getLane8_ctrlGroupWord_eq_getElem
  ctrlGroupAt_length ctrlGroupAt_getElem ctrlGroupAt_getElem? mem_ctrlGroupAt_iff
  unpack64_ctrlGroupWord ctrlGroupWord_empty8 getLane8_allOnes sepLoad64_ctrlGroupWord
  sepLoad64_ctrlGroupWord_here ValidBucketMask.and_toNat_eq_mod ValidBucketMask.and_lt_buckets
  ValidBucketMask.buckets_cases ValidBucketMask.numGroups_pow2 ValidBucketMask.buckets_bounds_dvd
  ValidBucketMask.add_and_eq ValidBucketMask.laneIdx_bv CtrlMirrorInv.lane_eq_mod_of_ge8
  CtrlMirrorInv.lane_of_eq4 CtrlMirrorInv.lane_full_eq_mod CtrlMirrorInv.empty_in_group_of_eq4
  ofBits8 packPred8 getLsbD_packPred8 eqBits8 specialBits8 fullBits8 getLsbD_eqBits8
  getLsbD_specialBits8 getLsbD_fullBits8 byteMaskOfBits highBitMaskOfBits
  byteMaskOfBits_and_highBits highBitMaskOfBits_zero byteMaskOfBits_zero
  highBitMaskOfBits_eq_zero_iff byteMaskOfBits_eq_zero_iff bv8_eq_zero_iff_forall
  bv8_ne_zero_iff_exists getLane8_byteMaskOfBits getLane8_highBitMaskOfBits bv8_ctz_spec
  bv8_clz_spec highBitMaskOfBits_lowestLane byteMaskOfBits_lowestLane byteMaskOfBits_clz_lsr3
  highBitMaskOfBits_clz_lsr3 highBitMaskOfBits_clear_lowest bv8_clear_lowest_lt
  bv8_clear_lowest_eq bv8_getLsbD_clear_lowest simd_cmeq_dup8_truncate64 simd_cmeq_dup8_highMask
  simd_cmeq_allOnes8 simdUmaxv8 simdUmaxv8_byteMaskOfBits simd_cmlt_zero8 simd_cmge_zero8
  getLane8_byteMask_special_orr_0x80 triGroupIdx_inj_mod_pow2 cntTrue cntTrue_congr cntTrue_set
  cntTrue_lt_of_false exists_triGroupIdx_mod_pow2)

theorem sepLoad64_hbRodata_emptyCtrl {ea : BitVec 64} (pl : Obj.Placement)
    (hea : pl.ρ hbEmptyCtrlSym = ea) :
    SepLoad64 ea (hbRodata pl) 0xffffffffffffffff#64 := by
  have h0 :
      SepLoad64 ea (hbRodata pl) (ctrlGroupWord (List.replicate 8 tagEmpty) 0) :=
    SepLoad64.of_pointsToBytesRO (base := pl.ρ hbEmptyCtrlSym) (off := 0)
      rfl (by simp) (by simp [hea])
  exact SepLoad64.congr_val h0 ctrlGroupWord_empty8

theorem probePos_eq_swissTable (bm k : BitVec 64) (step : Nat) :
    probePos bm k step = VerifiedLibraries.SwissTable.probePos bm (fxHash k) step := rfl

@[simp]
theorem probePos_zero (bm k : BitVec 64) : probePos bm k 0 = (fxHash k &&& bm).toNat :=
  VerifiedLibraries.SwissTable.probePos_zero bm (fxHash k)

theorem probePos_lt_buckets {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (k : BitVec 64) (step : Nat) : probePos bm k step < bm.toNat + 1 :=
  VerifiedLibraries.SwissTable.probePos_lt_buckets hbm (fxHash k) step

theorem probePos_bv_eq (bm k : BitVec 64) (step : Nat) :
    ((fxHash k + BitVec.ofNat 64 (triByteOff step)) &&& bm) =
      BitVec.ofNat 64 (probePos bm k step) :=
  VerifiedLibraries.SwissTable.probePos_bv_eq bm (fxHash k) step

theorem probePos_step_bv {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (k : BitVec 64) (step : Nat) :
    ((BitVec.ofNat 64 (probePos bm k step) + (BitVec.ofNat 64 (8 * step) + 8#64)) &&& bm) =
      BitVec.ofNat 64 (probePos bm k (step + 1)) :=
  VerifiedLibraries.SwissTable.probePos_step_bv hbm (fxHash k) step

theorem probePos_eq_add_mod {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (k : BitVec 64) (step : Nat) :
    probePos bm k step = (probePos bm k 0 + 8 * triGroupIdx step) % (bm.toNat + 1) :=
  VerifiedLibraries.SwissTable.probePos_eq_add_mod hbm (fxHash k) step

private theorem ofNat_lsl4_eq (idx : Nat) :
    BitVec.ofNat 64 idx <<< 4 = BitVec.ofNat 64 (16 * idx) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  change ((idx % 2 ^ 64) * 16) % 2 ^ 64 = (16 * idx) % 2 ^ 64
  rw [Nat.mul_comm _ 16, Nat.mul_mod_mod]

theorem slotAddr_sub_lsl4_sub16 (ctrlPtr : BitVec 64) (idx : Nat) :
    (ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64 = slotAddr ctrlPtr idx := by
  unfold slotAddr
  rw [ofNat_lsl4_eq, show 16 * (idx + 1) = 16 * idx + 16 by omega, BitVec.ofNat_add]
  bv_lin

theorem slotAddr_sub_lsl4_sub8 (ctrlPtr : BitVec 64) (idx : Nat) :
    (ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64 =
      slotAddr ctrlPtr idx + 8#64 := by
  unfold slotAddr
  rw [ofNat_lsl4_eq, show 16 * (idx + 1) = 16 * idx + 16 by omega, BitVec.ofNat_add]
  bv_lin

theorem exists_empty_probe_group_of_empty_slot {bm : BitVec 64} {ctrl : List (BitVec 8)}
    (hbm : ValidBucketMask bm) (hm : CtrlMirrorInv (bm.toNat + 1) ctrl)
    (hemp : ∃ (e : Nat) (_ : e < bm.toNat + 1),
      ctrl[e]'(by have hlen := hm.1; omega) = tagEmpty)
    (k : BitVec 64) :
    ∃ step < numGroups bm, tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k step) :=
  VerifiedLibraries.SwissTable.exists_empty_probe_group_of_empty_slot hbm hm hemp (fxHash k)


theorem SwissTableInv.exists_empty_probe_group {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm gl items ctrl slots m) (k : BitVec 64) :
    ∃ step < numGroups bm, tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k step) :=
  exists_empty_probe_group_of_empty_slot h.validMask h.mirror h.exists_empty_slot k

theorem SwissTableInv.items_eq_zero_iff_nil {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm gl items ctrl slots m) :
    items = 0#64 ↔ m = [] :=
  h.toGeneric.items_eq_zero_iff_nil

theorem SwissTableInv.lookup_eq_some_of_lane_match {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm gl items ctrl slots m) {k : BitVec 64} {pos j : Nat}
    (hpos : pos < bm.toNat + 1) (hj : j < 8)
    (htag : getLane8 (ctrlGroupWord ctrl pos) j = h2Tag k)
    (hkey : (slots[(pos + j) % (bm.toNat + 1)]'(by
      have hsl := h.slots_len; have := Nat.mod_lt (pos + j) (by omega : 0 < bm.toNat + 1); omega)).1 = k) :
    cliMapLookup k m = some (slots[(pos + j) % (bm.toNat + 1)]'(by
      have hsl := h.slots_len; have := Nat.mod_lt (pos + j) (by omega : 0 < bm.toNat + 1); omega)).2 := by
  have hidx_lt : (pos + j) % (bm.toNat + 1) < bm.toNat + 1 := Nat.mod_lt _ (by omega)
  have hfull_lane : isFullTag (getLane8 (ctrlGroupWord ctrl pos) j) = true := by
    rw [htag]; exact isFullTag_h2Tag k
  have hctrl := CtrlMirrorInv.lane_full_eq_mod h.validMask h.mirror hpos hj hfull_lane
  have hfull_ctrl : isFullTag (ctrl[(pos + j) % (bm.toNat + 1)]'(by
      have := h.mirror.1; omega)) = true := by
    rw [← hctrl]; exact hfull_lane
  have hsound := (h.full_sound _ hidx_lt hfull_ctrl).2.1
  rwa [hkey] at hsound

theorem SwissTableInv.lookup_eq_none_of_probe_empty {bm gl items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (h : SwissTableInv bm gl items ctrl slots m) {k : BitVec 64} {step : Nat}
    (hemp : tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k step))
    (hmiss : ∀ s ≤ step, ∀ j < 8,
      getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k →
      (slots[(probePos bm k s + j) % (bm.toNat + 1)]'(by
        have hsl := h.slots_len
        have := Nat.mod_lt (probePos bm k s + j) (by omega : 0 < bm.toNat + 1); omega)).1 ≠ k) :
    cliMapLookup k m = none := by
  cases hlook : cliMapLookup k m with
  | none => rfl
  | some v =>
    exact absurd (mem_of_cliMapLookup_eq_some hlook)
      (h.toGeneric.not_mem_of_probe_empty (x := (k, v)) hemp
        (fun s hs j hj htag => hmiss s hs j hj (htag.trans (h2Tag_eq_tagOfHash k).symm)))

end CaseStudies.Hashbrown.Proofs
