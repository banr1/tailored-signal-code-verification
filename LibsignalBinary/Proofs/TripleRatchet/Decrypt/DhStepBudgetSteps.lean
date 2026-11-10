/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStep
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import ProofLib.RegChain

/-!
# `VmPreserved` Key-Generation Sub-Steps (`+0x70c → +0x7d4`) for `DhStep`

Threads `VmPreserved` across basic blocks and external hooks (`rng_fill`, `derive_public_key_bytes`,
`StaticSecret::drop`) from `+0x70c` to the second `RootKey::create_chain` call at `+0x7d4`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps

open Arm64 ProofLib
open CryptoGames.Ratchet (clampScalar keyToBytesVec32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ChainKey Crypto RootKey)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes length_keyToBytes32)
open CryptoVerification.LibsignalTripleRatchetRepr (coinsOf tapeAfter)
open CryptoVerification.LibsignalTripleRatchet (
  DerivePublicKeyBytesCall derivePublicKeyBytesSpec zeroizeSecretSpec
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (tryDecryptMidMetaPlaced)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (
  fold_32_four_64 fold_after_778 keyVec_coinsOf_toList length_chainKeyBytes
  pointsToBytes_4_eq_pointsTo32
  pointsTo_16_as_two_64 pointsTo_32_as_4_8_8_8_4 pointsTo_32_as_four_64
  pointsTo_36_as_8_8_4_8_8 pointsTo_vec32_clamp_fold pointsTo_vec32_split_ends
  rngFillAtSpec split_1a0_56 split_1d8_for_stepA split_32_four_64 split_sp_20_for_stepA
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  derivePublicKeyBytesBudgetSpec subroutine_ok_withVmPreserved_of_derivePublicKeyBytes
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (DhStepBlockVmWp)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

abbrev lsStaticDropSym : String :=
  "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop"

abbrev rngFillAtBudgetSpec (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    Spec (BitVec 64 × Nat) :=
  withVmPreserved (rngFillAtSpec ctl cur rest)

abbrev zeroizeSecretBudgetSpec : Spec (BitVec 64) :=
  withVmPreserved zeroizeSecretSpec

theorem dhStep_step_70c_to_778_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (rk1 : RootKey) (rck : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 0x70c#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (_hx28 : s.readReg64 .x28 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64) 0x20 ∗
      ((s0.sp - 1504#64 + 0x190#64) ↦₃₂ 0#32) ∗
      ((s0.sp - 1504#64 + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
      ((s0.sp - 1504#64 + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗
      memRegion (s0.sp - 1504#64 + 0x1d8#64) 0x3a8 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s1, Steps prog s s1 ∧ VmPreserved s s1 ∧
      s1.pc = entry + 1912#64 ∧
      tryDecryptMidMetaPlaced s0 s1 ∧
      s1.readReg64 .x0 = sp + 0x190#64 ∧
      s1.readReg64 .x1 = 32#64 ∧
      s1.readReg64 .x19 = s.readReg64 .x19 ∧
      s1.readReg64 .x20 = s.readReg64 .x20 ∧
      s1.readReg64 .x21 = s.readReg64 .x21 ∧
      s1.readReg64 .x22 = s.readReg64 .x22 ∧
      s1.readReg64 .x23 = sp + 0x500#64 ∧
      s1.readReg64 .x25 = sp + 0x190#64 ∧
      s1.readReg64 .x26 = s.readReg64 .x26 ∧
      s1.readReg64 .x27 = s.readReg64 .x27 ∧
      s1.readReg64 .x28 = sp + 0x3d0#64 ∧
      s1.readVReg128 0#5 = 0#128 ∧
      (s1.mem ⊨
        memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
        memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ (s.readReg64 .x24).setWidth 32) ∗
        memRegion (sp + 0x190#64) 0x20 ∗
        memRegion (sp + 0x1b0#64) 0x220 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
        memRegion (sp + 0x3f4#64) 12 ∗
        memRegion (sp + 0x400#64) 0xa0 ∗
        ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
        ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
        memRegion (sp + 0x4e0#64) 0x20 ∗
        memRegion (sp + 0x500#64) 0x80 ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hrk1_len : (keyToBytes32 rk1).length = 32 := length_keyToBytes32 rk1
  have hrck_len : (chainKeyBytes rck).length = 36 := length_chainKeyBytes rck
  obtain ⟨r0, hr0⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack32 ((keyToBytes32 rk1).take 4) = v := ⟨_, rfl⟩
  obtain ⟨r1, hr1⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (((keyToBytes32 rk1).drop 4).take 8) = v := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (((keyToBytes32 rk1).drop 12).take 8) = v := ⟨_, rfl⟩
  obtain ⟨r3, hr3⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (((keyToBytes32 rk1).drop 20).take 8) = v := ⟨_, rfl⟩
  obtain ⟨r4, hr4⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack32 ((keyToBytes32 rk1).drop 28) = v := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((chainKeyBytes rck).take 8) = v := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (((chainKeyBytes rck).drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack32 (((chainKeyBytes rck).drop 16).take 4) = v := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (((chainKeyBytes rck).drop 20).take 8) = v := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((chainKeyBytes rck).drop 28) = v := ⟨_, rfl⟩
  have h194_split : ((sp + 0x194#64) ↦ₛ keyToBytes32 rk1) =
      (((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
       ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗
       ((sp + 0x1b0#64) ↦₃₂ r4)) := by
    rw [pointsTo_32_as_4_8_8_8_4 (sp + 0x194#64) (keyToBytes32 rk1) hrk1_len,
        hr0, hr1, hr2, hr3, hr4,
        show sp + 0x194#64 + 4#64 = sp + 0x198#64 by bv_arith,
        show sp + 0x194#64 + 12#64 = sp + 0x1a0#64 by bv_arith,
        show sp + 0x194#64 + 20#64 = sp + 0x1a8#64 by bv_arith,
        show sp + 0x194#64 + 28#64 = sp + 0x1b0#64 by bv_arith]
  have h1b4_split : ((sp + 0x1b4#64) ↦ₛ chainKeyBytes rck) =
      (((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗
       ((sp + 0x1c4#64) ↦₃₂ c2) ∗ ((sp + 0x1c8#64) ↦₆₄ c3) ∗
       ((sp + 0x1d0#64) ↦₆₄ c4)) := by
    rw [pointsTo_36_as_8_8_4_8_8 (sp + 0x1b4#64) (chainKeyBytes rck) hrck_len,
        hc0, hc1, hc2, hc3, hc4,
        show sp + 0x1b4#64 + 8#64 = sp + 0x1bc#64 by bv_arith,
        show sp + 0x1b4#64 + 16#64 = sp + 0x1c4#64 by bv_arith,
        show sp + 0x1b4#64 + 20#64 = sp + 0x1c8#64 by bv_arith,
        show sp + 0x1b4#64 + 28#64 = sp + 0x1d0#64 by bv_arith]
  rw [split_sp_20_for_stepA sp, h194_split, h1b4_split, split_1d8_for_stepA sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u510, u508, u500, u4d8, u4d0, u4c8, u4c0, u4bc, u4b4, u4ac, u4a4, u4a0,
    u448, u440, u408, u400, u3ec, u3e4, u3e0, u3d8, u3d0, u1c, u10, hmem⟩
  have hwp1 := hwp.wpp_70c_to_778 s0 s r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510 r1 r2 r3 c0 c1 c3 c4
    u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448 u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508
    hpc hrun hsp hsp_al hx29 hx23 hx25 hx26 htrace hvregs
  have hmem_in : s.mem ⊨
      (((sp + 0x10#64) ↦₃₂ u10) ∗ ((sp + 0x1c#64) ↦₃₂ u1c) ∗
       ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
       ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗
       ((sp + 0x1b0#64) ↦₃₂ r4) ∗
       ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗
       ((sp + 0x1c4#64) ↦₃₂ c2) ∗ ((sp + 0x1c8#64) ↦₆₄ c3) ∗
       ((sp + 0x1d0#64) ↦₆₄ c4) ∗
       ((sp + 0x3d0#64) ↦₆₄ u3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u3d8) ∗
       ((sp + 0x3e0#64) ↦₃₂ u3e0) ∗ ((sp + 0x3e4#64) ↦₆₄ u3e4) ∗
       ((sp + 0x3ec#64) ↦₆₄ u3ec) ∗
       ((sp + 0x400#64) ↦₆₄ u400) ∗ ((sp + 0x408#64) ↦₆₄ u408) ∗
       ((sp + 0x440#64) ↦₆₄ u440) ∗ ((sp + 0x448#64) ↦₆₄ u448) ∗
       ((sp + 0x4a0#64) ↦₃₂ u4a0) ∗ ((sp + 0x4a4#64) ↦₆₄ u4a4) ∗
       ((sp + 0x4ac#64) ↦₆₄ u4ac) ∗ ((sp + 0x4b4#64) ↦₆₄ u4b4) ∗
       ((sp + 0x4bc#64) ↦₃₂ u4bc) ∗
       ((sp + 0x4c0#64) ↦₆₄ u4c0) ∗ ((sp + 0x4c8#64) ↦₆₄ u4c8) ∗
       ((sp + 0x4d0#64) ↦₆₄ u4d0) ∗ ((sp + 0x4d8#64) ↦₆₄ u4d8) ∗
       ((sp + 0x500#64) ↦₆₄ u500) ∗ ((sp + 0x508#64) ↦₆₄ u508) ∗
       ((sp + 0x510#64) ↦₃₂ u510)) ∗
      (memRegion sp 0x10 ∗ memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       memRegion (sp + 0x1d8#64) 0x1f8 ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       memRegion (sp + 0x410#64) 0x30 ∗
       memRegion (sp + 0x450#64) 0x50 ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗
       memRegion (sp + 0x514#64) 0x6c ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem
  obtain ⟨s1, hsteps1, hout1⟩ := hwp1.elim hmem_in hcode
  obtain ⟨hpc1, hrun1, P1, hmem1, hvm1, hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hv0_1, htrace1, hvregs1, hent1⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al1 : s1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp1, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmeta1 : tryDecryptMidMetaPlaced s0 s1 :=
    ⟨hrun1, hsp1, hsp0_al, hsp_al1, hx29_1, htrace1, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1⟩
  have hmem1_0 := hent1 s1.mem _ hmem1
  have h10_fold : ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) = ((sp + 0x10#64) ↦₃₂ c2) := by
    rw [pointsToBytes_4_eq_pointsTo32 _ _ (by simp [hrck_len]), hc2]
  have h3d0_fold : ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) =
      (((sp + 0x3d0#64) ↦₆₄ c0) ∗ ((sp + 0x3d8#64) ↦₆₄ c1) ∗
       ((sp + 0x3e0#64) ↦₃₂ c2) ∗ ((sp + 0x3e4#64) ↦₆₄ c3) ∗
       ((sp + 0x3ec#64) ↦₆₄ c4)) := by
    rw [pointsTo_36_as_8_8_4_8_8 (sp + 0x3d0#64) (chainKeyBytes rck) hrck_len,
        hc0, hc1, hc2, hc3, hc4,
        show sp + 0x3d0#64 + 8#64 = sp + 0x3d8#64 by bv_arith,
        show sp + 0x3d0#64 + 16#64 = sp + 0x3e0#64 by bv_arith,
        show sp + 0x3d0#64 + 20#64 = sp + 0x3e4#64 by bv_arith,
        show sp + 0x3d0#64 + 28#64 = sp + 0x3ec#64 by bv_arith]
  have h4a0_fold : ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) =
      (((sp + 0x4a0#64) ↦₃₂ r0) ∗ ((sp + 0x4a4#64) ↦₆₄ r1) ∗
       ((sp + 0x4ac#64) ↦₆₄ r2) ∗ ((sp + 0x4b4#64) ↦₆₄ r3) ∗
       ((sp + 0x4bc#64) ↦₃₂ r4)) := by
    rw [pointsTo_32_as_4_8_8_8_4 (sp + 0x4a0#64) (keyToBytes32 rk1) hrk1_len,
        hr0, hr1, hr2, hr3, hr4,
        show sp + 0x4a0#64 + 4#64 = sp + 0x4a4#64 by bv_arith,
        show sp + 0x4a0#64 + 12#64 = sp + 0x4ac#64 by bv_arith,
        show sp + 0x4a0#64 + 20#64 = sp + 0x4b4#64 by bv_arith,
        show sp + 0x4a0#64 + 28#64 = sp + 0x4bc#64 by bv_arith]
  have h4c0_fold : ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) =
      (((sp + 0x4c0#64) ↦₆₄ c3) ∗ ((sp + 0x4c8#64) ↦₆₄ c4)) := by
    rw [pointsTo_16_as_two_64 (sp + 0x4c0#64) ((chainKeyBytes rck).drop 20) (by simp [hrck_len]),
        List.drop_drop, hc3, hc4,
        show sp + 0x4c0#64 + 8#64 = sp + 0x4c8#64 by bv_arith]
  have h4d0_fold : ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) =
      (((sp + 0x4d0#64) ↦₆₄ c0) ∗ ((sp + 0x4d8#64) ↦₆₄ c1)) := by
    have htake : ((chainKeyBytes rck).take 16).take 8 = (chainKeyBytes rck).take 8 := by
      rw [List.take_take, Nat.min_eq_left (by decide)]
    have hdrop : ((chainKeyBytes rck).take 16).drop 8 = ((chainKeyBytes rck).drop 8).take 8 := by
      rw [List.drop_take]
    rw [pointsTo_16_as_two_64 (sp + 0x4d0#64) ((chainKeyBytes rck).take 16) (by simp [hrck_len]),
        htake, hdrop, hc0, hc1,
        show sp + 0x4d0#64 + 8#64 = sp + 0x4d8#64 by bv_arith]
  have hmem1_1 : s1.mem ⊨
      (((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
       ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗
       ((sp + 0x1b0#64) ↦₃₂ r4) ∗
       ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗
       ((sp + 0x1c4#64) ↦₃₂ c2) ∗ ((sp + 0x1c8#64) ↦₆₄ c3) ∗
       ((sp + 0x1d0#64) ↦₆₄ c4) ∗
       memRegion (sp + 0x1d8#64) 0x1f8 ∗
       ((sp + 0x400#64) ↦₆₄ c0) ∗ ((sp + 0x408#64) ↦₆₄ c1) ∗
       memRegion (sp + 0x410#64) 0x30 ∗
       ((sp + 0x440#64) ↦₆₄ c3) ∗ ((sp + 0x448#64) ↦₆₄ c4) ∗
       memRegion (sp + 0x450#64) 0x50 ∗
       ((sp + 0x500#64) ↦₆₄ r2) ∗ ((sp + 0x508#64) ↦₆₄ r3) ∗
       ((sp + 0x510#64) ↦₃₂ r4) ∗
       memRegion (sp + 0x514#64) 0x6c) ∗
      (memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ (s.readReg64 .x24).setWidth 32) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
       memRegion (sp + 0x4e0#64) 0x20 ∗ Rest) := by
    rw [h10_fold, h3d0_fold, h4a0_fold, h4c0_fold, h4d0_fold]
    exact Eq.mp (congrArg (s1.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem1_0
  have hmem1_2 := Satisfies.mono (sepConj_mono_left (fold_after_778 sp r0 r4 c2 r1 r2 r3 c0 c1 c3 c4)) hmem1_1
  exact ⟨s1, hsteps1, hvm1, hpc1, hmeta1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hv0_1,
    Eq.mp (congrArg (s1.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem1_2⟩

theorem dhStep_step_778_to_780_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry ctl : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (cur : BitVec 64) (rest : List (BitVec 8)) (Rest : SepProp) (s0 s : State)
    (hrng : subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl cur rest))
    (hpc : s.pc = entry + 1912#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx0 : s.readReg64 .x0 = s0.sp - 1504#64 + 0x190#64)
    (hx1 : s.readReg64 .x1 = 32#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hv0 : s.readVReg128 0#5 = 0#128)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64 + 0x190#64) 0x20 ∗
      tapeAfter ctl cur rest 0 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧
      s'.pc = entry + 1920#64 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        ((sp + 0x190#64) ↦ₛ (keyToBytesVec32 (coinsOf rest)).toList) ∗
        tapeAfter ctl cur rest (min 32 rest.length) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  rw [split_32_four_64 (sp + 0x190#64)] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3, u2, u1, u0, hmem⟩
  have hwp1 := hwp.wpp_778_to_rng s0 s u0 u1 u2 u3 hpc hrun hsp hsp_al hx0 hx1 hx25 hv0 htrace
  have hmem_in : s.mem ⊨
      (((sp + 0x190#64) ↦₆₄ u0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ u1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ u3)) ∗
      (tapeAfter ctl cur rest 0 ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hmem
  obtain ⟨sc, hsteps1, hout1⟩ := hwp1.elim hmem_in hcode
  obtain ⟨hpcc, hrunc, P_c, hmem_c, hvm1, hsp_c, hx0_c, hx1_c, hx30_c, hcs_c, htrace_c, hent_c⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c : sc.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmem_c0 := hent_c sc.mem _ hmem_c
  have hmem_c1 := Satisfies.mono (sepConj_mono_left (fold_32_four_64 (sp + 0x190#64) 0#64 0#64 0#64 0#64)) hmem_c0
  have hpre_rng : sc.mem ⊨ (rngFillAtBudgetSpec ctl cur rest).pre (sp + 0x190#64, 32) sc ∗ Rest := by
    dsimp only [rngFillAtBudgetSpec, withVmPreserved, rngFillAtSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c, by rw [hx1_c]; rfl⟩, hmem_c1⟩
  obtain ⟨s', hsteps2, ⟨hret', hpres', hpost'⟩ | ⟨_, hpost'⟩ | ⟨_, -, hpost'⟩ | ⟨_, hpost'⟩, -⟩ :=
    hrng.no_fault_before_outcome (sp + 0x190#64, 32) Rest sc hpcc hrunc hpre_rng hsp_al_c
      (hsteps1.codeLoaded hcode)
  · have hsteps12 := Steps.trans hsteps1 hsteps2
    dsimp only [rngFillAtBudgetSpec, withVmPreserved, rngFillAtSpec] at hpost'
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hvm2, htrace_s', hpost'⟩
    rw [← keyVec_coinsOf_toList rest] at hpost'
    have hcs' : CalleeSavedPreserved s s' := CalleeSavedPreserved.trans hcs_c hpres'.2
    have hsp' : s'.sp = sp := hpres'.1.trans hsp_c
    have hsp_al' : s'.spAligned = true := by
      unfold State.spAligned at hsp_al_c ⊢
      rw [hpres'.1]
      exact hsp_al_c
    have hx29' : s'.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
    have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
      ⟨hret'.2.2, hsp', hsp0_al, hsp_al', hx29', htrace_s'.trans htrace_c,
       hcl.of_keepsFrozen hsteps12.keepsFrozen, by reg_chain⟩
    exact ⟨s', hsteps12, hvm1.trans hvm2, hret'.1.trans hx30_c, hmeta', hcs', hpost'⟩
  · dsimp only [rngFillAtBudgetSpec, withVmPreserved, rngFillAtSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [rngFillAtBudgetSpec, withVmPreserved, rngFillAtSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [rngFillAtBudgetSpec, withVmPreserved, rngFillAtSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1

theorem dhStep_step_780_to_7a8_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (v : List.Vector (BitVec 8) 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1920#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨ ((s0.sp - 1504#64 + 0x190#64) ↦ₛ v.toList) ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧
      s'.pc = entry + 1960#64 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      s'.readReg64 .x0 = sp + 0x500#64 ∧
      s'.readReg64 .x8 = sp + 0x400#64 ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧
      s'.readReg64 .x20 = s.readReg64 .x20 ∧
      s'.readReg64 .x21 = s.readReg64 .x21 ∧
      s'.readReg64 .x22 = s.readReg64 .x22 ∧
      s'.readReg64 .x23 = s.readReg64 .x23 ∧
      s'.readReg64 .x24 = sp + 0x400#64 ∧
      s'.readReg64 .x25 = s.readReg64 .x25 ∧
      s'.readReg64 .x26 = s.readReg64 .x26 ∧
      s'.readReg64 .x27 = s.readReg64 .x27 ∧
      s'.readReg64 .x28 = s.readReg64 .x28 ∧
      (s'.mem ⊨ ((sp + 0x190#64) ↦ₛ (clampScalar v).toList) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  set b0 := v.get ⟨0, by decide⟩
  set b31 := v.get ⟨31, by decide⟩
  rw [pointsTo_vec32_split_ends (sp + 0x190#64) v,
      show sp + 0x190#64 + 1#64 = sp + 0x191#64 by bv_arith,
      show sp + 0x190#64 + 31#64 = sp + 0x1af#64 by bv_arith] at hmem
  have hwp1 := hwp.wpp_780_to_7a8 s0 s b0 b31 hpc hrun hsp hsp_al hx29 hx23 hx25 htrace hvregs
  have hmem_in : s.mem ⊨
      (((sp + 0x190#64) ↦₈ b0) ∗ ((sp + 0x1af#64) ↦₈ b31)) ∗
      (((sp + 0x191#64) ↦ₛ (v.toList.drop 1).take 30) ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem
  obtain ⟨s', hsteps, hout⟩ := hwp1.elim hmem_in hcode
  obtain ⟨hpc', hrun', P', hmem', hvm1, hsp', hx0', hx8', hx19', hx20', hx21', hx22', hx23',
    hx24', hx25', hx26', hx27', hx28', hx29', htrace', hvregs', hent'⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al' : s'.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp', ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
    ⟨hrun', hsp', hsp0_al, hsp_al', hx29', htrace', hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs'⟩
  have hmem'_0 := hent' s'.mem _ hmem'
  have hmem'_1 : s'.mem ⊨
      (((sp + 0x190#64) ↦₈ (b0 &&& 0xf8#8)) ∗
       ((sp + 0x190#64 + 1#64) ↦ₛ (v.toList.drop 1).take 30) ∗
       ((sp + 0x190#64 + 31#64) ↦₈ ((b31 &&& 0x7f#8) ||| 0x40#8))) ∗ Rest := by
    rw [show sp + 0x190#64 + 1#64 = sp + 0x191#64 by bv_arith,
        show sp + 0x190#64 + 31#64 = sp + 0x1af#64 by bv_arith]
    exact Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem'_0
  rw [pointsTo_vec32_clamp_fold (sp + 0x190#64) v] at hmem'_1
  exact ⟨s', hsteps, hvm1, hpc', hmeta', hx0', hx8', hx19', hx20', hx21', hx22', hx23',
    hx24', hx25', hx26', hx27', hx28', hmem'_1⟩

theorem dhStep_step_7a8_to_7b4_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (sec : List.Vector (BitVec 8) 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1960#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx0 : s.readReg64 .x0 = s0.sp - 1504#64 + 0x500#64)
    (hx8 : s.readReg64 .x8 = s0.sp - 1504#64 + 0x400#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨
      ((s0.sp - 1504#64 + 0x190#64) ↦ₛ sec.toList) ∗
      memRegion (s0.sp - 1504#64 + 0x400#64) 32 ∗
      memRegion (s0.sp - 1504#64 + 0x500#64) 32 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧
      s'.pc = entry + 1972#64 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        memRegion (sp + 0x190#64) 32 ∗
        ((sp + 0x400#64) ↦ₛ (C.pubKey sec).toList) ∗
        ((sp + 0x500#64) ↦ₛ sec.toList) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hsec_len : sec.toList.length = 32 := sec.2
  obtain ⟨p0, hp0⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (sec.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((sec.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((sec.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (sec.toList.drop 24) = v := ⟨_, rfl⟩
  have h190_split : ((sp + 0x190#64) ↦ₛ sec.toList) =
      (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x190#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  have h500_fold : ((sp + 0x500#64) ↦ₛ sec.toList) =
      (((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x500#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  rw [h190_split, split_32_four_64 (sp + 0x500#64)] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3, u2, u1, u0, hmem⟩
  have hwp1 := hwp.wpp_7a8_to_dpk s0 s p0 p1 p2 p3 u0 u1 u2 u3 hpc hrun hsp hsp_al hx0 hx8 hx23 hx25 htrace
  have hmem_in : s.mem ⊨
      (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3) ∗
       ((sp + 0x500#64) ↦₆₄ u0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ u1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ u3)) ∗
      (memRegion (sp + 0x400#64) 32 ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem
  obtain ⟨sc, hsteps1, hout1⟩ := hwp1.elim hmem_in hcode
  obtain ⟨hpcc, hrunc, P_c, hmem_c, hvm1, hsp_c, hx0_c, hx8_c, hx30_c, hcs_c, htrace_c, hent_c⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c : sc.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmem_c0 := hent_c sc.mem _ hmem_c
  have hmem_c1 : sc.mem ⊨
      (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3)) ∗
      (((sp + 0x500#64) ↦ₛ sec.toList) ∗ memRegion (sp + 0x400#64) 32 ∗ Rest) := by
    rw [h500_fold]
    exact Eq.mp (congrArg (sc.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem_c0
  have hmem_c2 := Satisfies.mono (sepConj_mono_left (fold_32_four_64 (sp + 0x190#64) p0 p1 p2 p3)) hmem_c1
  have hdpk_vm := subroutine_ok_withVmPreserved_of_derivePublicKeyBytes hdpk
  let dpkG : DerivePublicKeyBytesCall := { secret := sp + 0x500#64, sec := sec, out := sp + 0x400#64 }
  have hpre_dpk : sc.mem ⊨ (withVmPreserved (derivePublicKeyBytesSpec C.pubKey)).pre dpkG sc ∗ (memRegion (sp + 0x190#64) 32 ∗ Rest) := by
    dsimp only [withVmPreserved, derivePublicKeyBytesSpec, dpkG]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c, hx8_c⟩, Eq.mp (congrArg (sc.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem_c2⟩
  obtain ⟨s', hsteps2, ⟨hret', hpres', hpost'⟩ | ⟨_, hpost'⟩ | ⟨_, -, hpost'⟩ | ⟨_, hpost'⟩, -⟩ :=
    hdpk_vm.no_fault_before_outcome dpkG (memRegion (sp + 0x190#64) 32 ∗ Rest) sc hpcc hrunc hpre_dpk hsp_al_c
      (hsteps1.codeLoaded hcode)
  · have hsteps12 := Steps.trans hsteps1 hsteps2
    dsimp only [withVmPreserved, derivePublicKeyBytesSpec, dpkG] at hpost'
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hvm2, htrace_s', hpost'⟩
    have hcs' : CalleeSavedPreserved s s' := CalleeSavedPreserved.trans hcs_c hpres'.2
    have hsp' : s'.sp = sp := hpres'.1.trans hsp_c
    have hsp_al' : s'.spAligned = true := by
      unfold State.spAligned at hsp_al_c ⊢
      rw [hpres'.1]
      exact hsp_al_c
    have hx29' : s'.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
    have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
      ⟨hret'.2.2, hsp', hsp0_al, hsp_al', hx29', htrace_s'.trans htrace_c,
       hcl.of_keepsFrozen hsteps12.keepsFrozen, by reg_chain⟩
    exact ⟨s', hsteps12, hvm1.trans hvm2, hret'.1.trans hx30_c, hmeta', hcs',
      Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hpost'⟩
  · dsimp only [withVmPreserved, derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [withVmPreserved, derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [withVmPreserved, derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1

theorem dhStep_step_7b4_to_7d4_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (msgA : BitVec 64) (sec : List.Vector (BitVec 8) 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1972#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 1504#64 + 0x400#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 1504#64 + 0x3d0#64)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64 + 0x420#64) 32 ∗
      ((s0.sp - 1504#64 + 0x500#64) ↦ₛ sec.toList) ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧
      s'.pc = lsmpl.base 40 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      s'.readReg64 .x0 = sp + 0x4a0#64 ∧
      s'.readReg64 .x1 = msgA + 56#64 ∧
      s'.readReg64 .x2 = sp + 0x420#64 ∧
      s'.readReg64 .x8 = sp + 0x190#64 ∧
      s'.readReg64 .x30 = entry + 2008#64 ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        ((sp + 0x420#64) ↦ₛ sec.toList) ∗
        memRegion (sp + 0x500#64) 32 ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hsec_len : sec.toList.length = 32 := sec.2
  obtain ⟨p0, hp0⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (sec.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((sec.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((sec.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (sec.toList.drop 24) = v := ⟨_, rfl⟩
  have h500_split : ((sp + 0x500#64) ↦ₛ sec.toList) =
      (((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x500#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  have h420_fold : ((sp + 0x420#64) ↦ₛ sec.toList) =
      (((sp + 0x420#64) ↦₆₄ p0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x420#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x420#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  rw [split_32_four_64 (sp + 0x420#64), h500_split] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3, u2, u1, u0, hmem⟩
  have hwp1 := hwp.wpp_7b4_to_sd s0 s p0 p1 p2 p3 u0 u1 u2 u3 hpc hrun hsp hsp_al hx29 hx23 hx28 htrace
  have hmem_in : s.mem ⊨
      (((sp + 0x420#64) ↦₆₄ u0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ u1) ∗
       ((sp + 0x420#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ u3) ∗
       ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) ∗ Rest :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem
  obtain ⟨sc, hsteps1, hout1⟩ := hwp1.elim hmem_in hcode
  obtain ⟨hpcc, hrunc, P_c, hmem_c, hvm1, hsp_c, hx0_c, hx30_c, hcs_c, htrace_c, hent_c⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c : sc.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmem_c0 := hent_c sc.mem _ hmem_c
  have hmem_c1 : sc.mem ⊨
      (((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) ∗
      (((sp + 0x420#64) ↦ₛ sec.toList) ∗ Rest) := by
    rw [h420_fold]
    exact Eq.mp (congrArg (sc.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem_c0
  have hmem_c2 := Satisfies.mono (sepConj_mono_left (fold_32_four_64 (sp + 0x500#64) p0 p1 p2 p3)) hmem_c1
  have hpre_sd : sc.mem ⊨ zeroizeSecretBudgetSpec.pre (sp + 0x500#64) sc ∗ (((sp + 0x420#64) ↦ₛ sec.toList) ∗ Rest) := by
    dsimp only [zeroizeSecretBudgetSpec, withVmPreserved, zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0_c, hmem_c2⟩
  obtain ⟨s2, hsteps2, ⟨hret2, hpres2, hpost2⟩ | ⟨_, hpost2⟩ | ⟨_, -, hpost2⟩ | ⟨_, hpost2⟩, -⟩ :=
    hsd.no_fault_before_outcome (sp + 0x500#64) (((sp + 0x420#64) ↦ₛ sec.toList) ∗ Rest) sc
      hpcc hrunc hpre_sd hsp_al_c (hsteps1.codeLoaded hcode)
  · have hsteps12 := Steps.trans hsteps1 hsteps2
    dsimp only [zeroizeSecretBudgetSpec, withVmPreserved, zeroizeSecretSpec] at hpost2
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    rcases hpost2 with ⟨hvm2, htrace2, hpost2⟩
    have h500_reg : ((sp + 0x500#64) ↦ₛ List.replicate 32 0#8) ⊢ memRegion (sp + 0x500#64) 32 := by
      simpa using pointsToBytes_entails_memRegion (sp + 0x500#64) (List.replicate 32 0#8)
    have hmem2 := Satisfies.mono (sepConj_mono_left h500_reg) hpost2
    have hpc2 : s2.pc = entry + 1988#64 := hret2.1.trans hx30_c
    have hrun2 : s2.status = .Running := hret2.2.2
    have hsp2 : s2.sp = sp := hpres2.1.trans hsp_c
    have hsp_al2 : s2.spAligned = true := by
      unfold State.spAligned at hsp_al_c ⊢
      rw [hpres2.1]
      exact hsp_al_c
    have hcs12 : CalleeSavedPreserved s s2 := CalleeSavedPreserved.trans hcs_c hpres2.2
    have hx22_2 : s2.readReg64 .x22 = msgA := hcs12.2.2.2.1.trans hx22
    have hx24_2 : s2.readReg64 .x24 = sp + 0x400#64 := hcs12.2.2.2.2.2.1.trans hx24
    have hx28_2 : s2.readReg64 .x28 = sp + 0x3d0#64 := hcs12.2.2.2.2.2.2.2.2.2.1.trans hx28
    have hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64 := hcs12.2.2.2.2.2.2.2.2.2.2.1.trans hx29
    have hwp2 := hwp.wpp_7c4_to_cc2 s0 s2 msgA hpc2 hrun2 hsp2 hsp_al2 hx22_2 hx24_2 hx29_2
      (htrace2.trans htrace_c)
    have hmem2_in : s2.mem ⊨ emp ∗ (((sp + 0x420#64) ↦ₛ sec.toList) ∗ memRegion (sp + 0x500#64) 32 ∗ Rest) := by
      rw [emp_sepConj]
      exact Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem2
    obtain ⟨s', hsteps3, hout3⟩ :=
      hwp2.elim hmem2_in (hsteps12.codeLoaded hcode)
    obtain ⟨hpc', hrun', P', hmem', hvm3, hsp', hx0', hx1', hx2', hx8', hx30', hcs3, htrace', hent'⟩ :=
      hout3.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
    have hsteps123 := Steps.trans hsteps12 hsteps3
    have hsp_al' : s'.spAligned = true := by
      unfold State.spAligned at hsp_al ⊢
      rw [hsp', ← show s.sp = s0.sp - 1504#64 from hsp]
      exact hsp_al
    have hcs' : CalleeSavedPreserved s s' := CalleeSavedPreserved.trans hcs12 hcs3
    have hx29' : s'.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
    have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
      ⟨hrun', hsp', hsp0_al, hsp_al', hx29', htrace', hcl.of_keepsFrozen hsteps123.keepsFrozen, by reg_chain⟩
    exact ⟨s', hsteps123, (hvm1.trans hvm2).trans hvm3, hpc', hmeta', hx0', hx1', hx2', hx8', hx30', hcs', hent' s'.mem _ hmem'⟩
  · dsimp only [zeroizeSecretBudgetSpec, withVmPreserved, zeroizeSecretSpec] at hpost2
    rw [satisfies_pure_sepConj] at hpost2
    exact False.elim hpost2.1
  · dsimp only [zeroizeSecretBudgetSpec, withVmPreserved, zeroizeSecretSpec] at hpost2
    rw [satisfies_pure_sepConj] at hpost2
    exact False.elim hpost2.1
  · dsimp only [zeroizeSecretBudgetSpec, withVmPreserved, zeroizeSecretSpec] at hpost2
    rw [satisfies_pure_sepConj] at hpost2
    exact False.elim hpost2.1
end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps
