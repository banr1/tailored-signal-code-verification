/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP
  ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32
  ProofLib.reduceStateReadReg

theorem bv_sub_eq_add_neg (x y : BitVec 64) : x - y = x + (-y) :=
  BitVec.sub_eq_add_neg x y

theorem sevenLo_ro_x21_24 (x21 : BitVec 64)
    (b8 b9 b10 b11 b12 b13 b14 : BitVec 8) (rest : SepProp) :
    (((x21 + 24#64) ↦₃₂ᵣ (b11 ++ b10 ++ b9 ++ b8)) ∗
     ((x21 + 28#64) ↦₈ᵣ b12) ∗ ((x21 + 29#64) ↦₈ᵣ b13) ∗ ((x21 + 30#64) ↦₈ᵣ b14) ∗ rest) =
      (((x21 + 24#64) ↦₈ᵣ b8) ∗ ((x21 + 25#64) ↦₈ᵣ b9) ∗ ((x21 + 26#64) ↦₈ᵣ b10) ∗
       ((x21 + 27#64) ↦₃₂ᵣ (b14 ++ b13 ++ b12 ++ b11)) ∗ rest) := by
  have h := congrArg (· ∗ rest) (sevenLo_eq_sevenHi_ro (x21 + 24#64) b8 b9 b10 b11 b12 b13 b14)
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem sevenLo_rw_x29_136 (x29 : BitVec 64)
    (b8 b9 b10 b11 r12 r13 r14 : BitVec 8) (rest : SepProp) :
    (((x29 + bv% (2 ^ 64 - 136)) ↦₃₂ (b11 ++ b10 ++ b9 ++ b8)) ∗
     ((x29 + bv% (2 ^ 64 - 132)) ↦₈ r12) ∗
     ((x29 + bv% (2 ^ 64 - 131)) ↦₈ r13) ∗
     ((x29 + bv% (2 ^ 64 - 130)) ↦₈ r14) ∗ rest) =
      (((x29 + bv% (2 ^ 64 - 136)) ↦₈ b8) ∗
       ((x29 + bv% (2 ^ 64 - 135)) ↦₈ b9) ∗
       ((x29 + bv% (2 ^ 64 - 134)) ↦₈ b10) ∗
       ((x29 + bv% (2 ^ 64 - 133)) ↦₃₂ (r14 ++ r13 ++ r12 ++ b11)) ∗ rest) := by
  have h := congrArg (· ∗ rest)
    (sevenLo_eq_sevenHi (x29 + bv% (2 ^ 64 - 136)) b8 b9 b10 b11 r12 r13 r14)
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem role_privB0_clamp64 (r : Role) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 r.privB0 &&& 1065151889656#64) = r.privB0 := by
  cases r <;> rfl

theorem role_privB31_clamp64 (r : Role) :
    BitVec.zeroExtend 8
      (Arm64.evalBitfield .W32 .BFM 64#64
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 r.privB31))) 0 5) = r.privB31 := by
  cases r <;> rfl

theorem role_privB31_clamp64' (r : Role) :
    BitVec.zeroExtend 8
      (Arm64.evalBitfield .W32 .BFM 64#64 (BitVec.zeroExtend 64 r.privB31) 0 5) = r.privB31 := by
  cases r <;> rfl

theorem role_privB31_clamp64'' (r : Role) :
    BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 r.privB31 >>> 0 &&& 63#64) = r.privB31 := by
  cases r <;> rfl

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

/-! ## Segment 3 Framing and Composition Helpers -/

theorem memRegion_open_0x170_split40 (sp : BitVec 64) :
    memRegion (sp + 0x170#64) 0x170 =
      memRegion (sp + 0x170#64) 40 ∗ memRegion (sp + 0x198#64) 0x148 := by
  exact memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x198#64)
    (N := 0x170) (n := 40) (k := 0x148) (by decide) (by bv_lin) (by decide)

theorem memRegion_open_0x340_join (sp : BitVec 64) :
    memRegion (sp + 0x340#64) 0x20 ∗ memRegion (sp + 0x360#64) 0x30 =
      memRegion (sp + 0x340#64) 0x50 := by
  exact (memRegion_split' (b := sp + 0x340#64) (b' := sp + 0x360#64)
    (N := 0x50) (n := 0x20) (k := 0x30) (by decide) (by bv_lin) (by decide)).symm

theorem memRegion_open_0x080_split (sp : BitVec 64) :
    memRegion (sp + 0x170#64) 0x220 =
      memRegion (sp + 0x170#64) 0x170 ∗
      memRegion (sp + 0x2e0#64) 0x40 ∗
      memRegion (sp + 0x320#64) 0x20 ∗
      memRegion (sp + 0x340#64) 0x50 := by
  rw [memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x2e0#64)
        (N := 0x220) (n := 0x170) (k := 0xb0) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x2e0#64) (b' := sp + 0x320#64)
        (N := 0xb0) (n := 0x40) (k := 0x70) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x320#64) (b' := sp + 0x340#64)
        (N := 0x70) (n := 0x20) (k := 0x50) (by decide) (by bv_lin) (by decide)]

theorem x29_sub_offsets_open {sp sp0 x29 : BitVec 64}
    (hsp : sp = sp0 - 0x3f0#64) (hx29 : x29 = sp0 - 0x60#64) :
    x29 - 176#64 = sp + 0x2e0#64 ∧
    x29 - 168#64 = sp + 0x2e0#64 + 8#64 ∧
    x29 - 160#64 = sp + 0x2e0#64 + 16#64 ∧
    x29 - 152#64 = sp + 0x2e0#64 + 24#64 ∧
    x29 - 144#64 = sp + 0x300#64 ∧
    x29 - 143#64 = sp + 0x300#64 + 1#64 ∧
    x29 - 139#64 = sp + 0x300#64 + 5#64 ∧
    x29 - 137#64 = sp + 0x300#64 + 7#64 ∧
    x29 - 136#64 = sp + 0x300#64 + 8#64 ∧
    x29 - 132#64 = sp + 0x300#64 + 12#64 ∧
    x29 - 131#64 = sp + 0x300#64 + 13#64 ∧
    x29 - 130#64 = sp + 0x300#64 + 14#64 ∧
    x29 - 129#64 = sp + 0x300#64 + 15#64 ∧
    x29 - 121#64 = sp + 0x300#64 + 23#64 ∧
    x29 - 113#64 = sp + 0x300#64 + 31#64 ∧
    x29 - 112#64 = sp + 0x320#64 ∧
    x29 - 104#64 = sp + 0x320#64 + 8#64 ∧
    x29 - 96#64 = sp + 0x320#64 + 16#64 ∧
    x29 - 88#64 = sp + 0x320#64 + 24#64 ∧
    sp + 0x2e0#64 + 32#64 = x29 - 144#64 := by
  subst hsp hx29
  refine ⟨by bv_lin, by bv_lin, by bv_lin, by bv_lin, by bv_lin,
    by bv_lin, by bv_lin, by bv_lin, by bv_lin, by bv_lin,
    by bv_lin, by bv_lin, by bv_lin, by bv_lin, by bv_lin,
    by bv_lin, by bv_lin, by bv_lin, by bv_lin, by bv_lin⟩

theorem memRegion_open_0x2e0_x29_split {sp sp0 x29 : BitVec 64}
    (hsp : sp = sp0 - 0x3f0#64) (hx29 : x29 = sp0 - 0x60#64) :
    memRegion (sp + 0x2e0#64) 0x40 =
      (∃∗ q0 : BitVec 64, (x29 - 176#64) ↦₆₄ q0) ∗
      (∃∗ q1 : BitVec 64, (x29 - 168#64) ↦₆₄ q1) ∗
      (∃∗ q2 : BitVec 64, (x29 - 160#64) ↦₆₄ q2) ∗
      (∃∗ q3 : BitVec 64, (x29 - 152#64) ↦₆₄ q3) ∗
      ((∃∗ r0 : BitVec 8, (x29 - 144#64) ↦₈ r0) ∗
       (∃∗ r1 : BitVec 32, (x29 - 143#64) ↦₃₂ r1) ∗
       (∃∗ r5 : BitVec 16, (x29 - 139#64) ↦₁₆ r5) ∗
       (∃∗ r7 : BitVec 8, (x29 - 137#64) ↦₈ r7) ∗
       (∃∗ r8 : BitVec 32, (x29 - 136#64) ↦₃₂ r8) ∗
       (∃∗ r12 : BitVec 8, (x29 - 132#64) ↦₈ r12) ∗
       (∃∗ r13 : BitVec 8, (x29 - 131#64) ↦₈ r13) ∗
       (∃∗ r14 : BitVec 8, (x29 - 130#64) ↦₈ r14) ∗
       (∃∗ r15 : BitVec 64, (x29 - 129#64) ↦₆₄ r15) ∗
       (∃∗ r23 : BitVec 64, (x29 - 121#64) ↦₆₄ r23) ∗
       (∃∗ r31 : BitVec 8, (x29 - 113#64) ↦₈ r31)) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, _⟩ :=
    x29_sub_offsets_open hsp hx29
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14,
      memRegion_split' (b := sp + 0x2e0#64) (b' := sp + 0x300#64)
        (N := 0x40) (n := 32) (k := 32) (by decide) (by bv_lin) (by decide),
      memRegion_32_four_64 (sp + 0x2e0#64),
      memRegion_32_privKey_split (sp + 0x300#64)]
  simp only [sepConj_assoc]

theorem memRegion_open_0x320_x29_split {sp sp0 x29 : BitVec 64}
    (hsp : sp = sp0 - 0x3f0#64) (hx29 : x29 = sp0 - 0x60#64) :
    memRegion (sp + 0x320#64) 0x20 =
      (∃∗ p0 : BitVec 64, (x29 - 112#64) ↦₆₄ p0) ∗
      (∃∗ p1 : BitVec 64, (x29 - 104#64) ↦₆₄ p1) ∗
      (∃∗ p2 : BitVec 64, (x29 - 96#64) ↦₆₄ p2) ∗
      (∃∗ p3 : BitVec 64, (x29 - 88#64) ↦₆₄ p3) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e15, e16, e17, e18, _⟩ :=
    x29_sub_offsets_open hsp hx29
  rw [e15, e16, e17, e18, show (0x20 : Nat) = 32 from rfl, memRegion_32_four_64 (sp + 0x320#64)]

theorem open_keys_mid_combine (role : Role) {sp sp0 x29 : BitVec 64}
    (hsp : sp = sp0 - 0x3f0#64) (hx29 : x29 = sp0 - 0x60#64)
    (w0 w1 w2 w3 : BitVec 64)
    (v1 : BitVec 32) (v5 : BitVec 16) (b7 : BitVec 8)
    (b8 b9 b10 b11 b12 b13 b14 : BitVec 8)
    (v15 v23 : BitVec 64)
    (hpk1 : ∀ a : BitVec 64,
      (a ↦ₛ role.idKey.publicKey.bytes.toList) =
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))
    (hpriv_rw : ∀ a : BitVec 64,
      (a ↦ₛ role.idPrivBytes) =
        privKeyChunksRW a role.privB0 v1 v5 b7 b8 b9 b10 b11 b12 b13 b14 v15 v23 role.privB31) :
    ((((sp + 0x170#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((sp + 0x178#64) ↦₆₄ w0) ∗ ((sp + 0x180#64) ↦₆₄ w1) ∗
      ((sp + 0x188#64) ↦₆₄ w2) ∗ ((sp + 0x190#64) ↦₆₄ w3)) ∗
     (((x29 - 176#64) ↦₆₄ w0) ∗
      ((x29 - 168#64) ↦₆₄ w1) ∗
      ((x29 - 160#64) ↦₆₄ w2) ∗
      ((x29 - 152#64) ↦₆₄ w3) ∗
      privKeyChunksRW (x29 - 144#64)
        role.privB0 v1 v5 b7 b8 b9 b10 b11 b12 b13 b14 v15 v23 role.privB31)) ⊢
      memRegion (sp + 0x170#64) 40 ∗ ((sp + 0x2e0#64) ↦ₛ role.keyPairBytes) := by
  obtain ⟨e0, e1, e2, e3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e19⟩ :=
    x29_sub_offsets_open hsp hx29
  have hkp :
      (((x29 - 176#64) ↦₆₄ w0) ∗
       ((x29 - 168#64) ↦₆₄ w1) ∗
       ((x29 - 160#64) ↦₆₄ w2) ∗
       ((x29 - 152#64) ↦₆₄ w3) ∗
       privKeyChunksRW (x29 - 144#64)
         role.privB0 v1 v5 b7 b8 b9 b10 b11 b12 b13 b14 v15 v23 role.privB31) =
        ((sp + 0x2e0#64) ↦ₛ role.keyPairBytes) := by
    rw [e0, e1, e2, e3, role_keyPairBytes_pointsTo role (sp + 0x2e0#64),
        hpk1 (sp + 0x2e0#64), e19, hpriv_rw (x29 - 144#64)]
    simp only [sepConj_assoc]
  rw [hkp]
  have h40 := pointsTo64_5_entails_memRegion_40 (sp + 0x170#64) 0xfffffffffffffffe#64 w0 w1 w2 w3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h40
  exact sepConj_mono_left h40

theorem open_keys_post2_combine (role : Role) {sp sp0 x29 : BitVec 64}
    (hsp : sp = sp0 - 0x3f0#64) (hx29 : x29 = sp0 - 0x60#64)
    (u0 u1 u2 u3 : BitVec 64)
    (hpk2 : ∀ a : BitVec 64,
      (a ↦ₛ role.peer.idKey.publicKey.bytes.toList) =
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3)) :
    ((((sp + 0x170#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((sp + 0x178#64) ↦₆₄ u0) ∗ ((sp + 0x180#64) ↦₆₄ u1) ∗
      ((sp + 0x188#64) ↦₆₄ u2) ∗ ((sp + 0x190#64) ↦₆₄ u3)) ∗
     (memRegion (sp + 0x198#64) 0x148 ∗
      (((x29 - 112#64) ↦₆₄ u0) ∗
       ((x29 - 104#64) ↦₆₄ u1) ∗
       ((x29 - 96#64) ↦₆₄ u2) ∗
       ((x29 - 88#64) ↦₆₄ u3)))) ⊢
      memRegion (sp + 0x170#64) 0x170 ∗
      ((sp + 0x320#64) ↦ₛ role.peer.idKey.publicKey.bytes.toList) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e15, e16, e17, e18, _⟩ :=
    x29_sub_offsets_open hsp hx29
  have hpeer :
      (((x29 - 112#64) ↦₆₄ u0) ∗
       ((x29 - 104#64) ↦₆₄ u1) ∗
       ((x29 - 96#64) ↦₆₄ u2) ∗
       ((x29 - 88#64) ↦₆₄ u3)) =
        ((sp + 0x320#64) ↦ₛ role.peer.idKey.publicKey.bytes.toList) := by
    rw [e15, e16, e17, e18, hpk2 (sp + 0x320#64)]
  rw [hpeer, memRegion_open_0x170_split40 sp]
  have h40 := pointsTo64_5_entails_memRegion_40 (sp + 0x170#64) 0xfffffffffffffffe#64 u0 u1 u2 u3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h40
  exact Entails.trans (sepConj_mono_left h40) (Entails.of_eq (by ac_rfl))

theorem exists_words4_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  have hle : ∀ k, k ≤ 32 → k ≤ bs.length := fun k hk => h ▸ hk
  refine ⟨pack64 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
            (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8),
          pack64 (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8)
            (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8),
          pack64 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)
            (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8),
          pack64 (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8) (bs.getD 27 0#8)
            (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8) (bs.getD 31 0#8),
          fun a => ?_⟩
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 8 (hle 8 (by decide)),
      pointsToBytes_drop_split _ bs 8 8 (hle 16 (by decide)),
      pointsToBytes_drop_split _ bs 16 8 (hle 24 (by decide)),
      pointsToBytes_drop_split _ bs 24 8 (hle 32 (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take8_eq_pointsTo64 _ bs 0 (hle 8 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 8 (hle 16 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 16 (hle 24 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 24 (hle 32 (by decide))]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  rw [h8]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem extract_open_0x320_x29 {m : Memory} {sp sp0 x29 : BitVec 64} {R : SepProp}
    (hsp : sp = sp0 - 0x3f0#64) (hx29 : x29 = sp0 - 0x60#64)
    (h : m ⊨ memRegion (sp + 0x320#64) 0x20 ∗ R) :
    ∃ p0 p1 p2 p3 : BitVec 64,
      m ⊨ (((x29 - 112#64) ↦₆₄ p0) ∗ ((x29 - 104#64) ↦₆₄ p1) ∗
           ((x29 - 96#64) ↦₆₄ p2) ∗ ((x29 - 88#64) ↦₆₄ p3)) ∗ R := by
  rw [memRegion_open_0x320_x29_split hsp hx29] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h
  rcases h with ⟨p3, p2, p1, p0, h⟩
  exact ⟨p0, p1, p2, p3, by ac_sat h⟩

theorem extract_open_0x2e0_x29 {m : Memory} {sp sp0 x29 : BitVec 64} {R : SepProp}
    (hsp : sp = sp0 - 0x3f0#64) (hx29 : x29 = sp0 - 0x60#64)
    (h : m ⊨ memRegion (sp + 0x2e0#64) 0x40 ∗ R) :
    ∃ (q0 q1 q2 q3 : BitVec 64)
      (r0 : BitVec 8) (r1 : BitVec 32) (r5 : BitVec 16) (r7 : BitVec 8)
      (r8 : BitVec 32) (r12 r13 r14 : BitVec 8) (r15 r23 : BitVec 64) (r31 : BitVec 8),
      m ⊨ (((x29 - 176#64) ↦₆₄ q0) ∗
           ((x29 - 168#64) ↦₆₄ q1) ∗
           ((x29 - 160#64) ↦₆₄ q2) ∗
           ((x29 - 152#64) ↦₆₄ q3) ∗
           (((x29 - 144#64) ↦₈ r0) ∗
            ((x29 - 143#64) ↦₃₂ r1) ∗
            ((x29 - 139#64) ↦₁₆ r5) ∗
            ((x29 - 137#64) ↦₈ r7) ∗
            ((x29 - 136#64) ↦₃₂ r8) ∗
            ((x29 - 132#64) ↦₈ r12) ∗
            ((x29 - 131#64) ↦₈ r13) ∗
            ((x29 - 130#64) ↦₈ r14) ∗
            ((x29 - 129#64) ↦₆₄ r15) ∗
            ((x29 - 121#64) ↦₆₄ r23) ∗
            ((x29 - 113#64) ↦₈ r31))) ∗ R := by
  rw [memRegion_open_0x2e0_x29_split hsp hx29] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h
  rcases h with ⟨r31, r23, r15, r14, r13, r12, r8, r7, r5, r1, r0, q3, q2, q1, q0, h⟩
  exact ⟨q0, q1, q2, q3, r0, r1, r5, r7, r8, r12, r13, r14, r15, r23, r31, by ac_sat h⟩

end CryptoVerification.E2E.Bin

