/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.ResponderWireCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.KeyPairCalleesDecode
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# `KeyPair` and `IdentityKey` Callee Proofs for PQXDH Initiator

Proves `subroutine_ok` on `tripleRatchetProgAt` and `[LibsignalPlacement]` for
`<KeyPair>::from_public_and_private` (`0x3e738`), `<IdentityKeyPair as TryFrom<PrivateKey>>::try_from`
(`0x28704`), and `<IdentityKey as TryFrom<&[u8]>>::try_from` (`0x2c530`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-! ## Multi-byte `↦₈` Load/Store Support for Unaligned Overlapping Copies -/

export CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom (
  pointsTo16_eq_bytes2 pointsTo32_eq_bytes4 pointsTo64_eq_bytes8
  proveSepLoadBytes proveSepStoreBytes
  bv16_extract_0 bv16_extract_8
  bv32_extract_0 bv32_extract_8 bv32_extract_16 bv32_extract_24
  bv64_extract_0 bv64_extract_8 bv64_extract_16 bv64_extract_24
  bv64_extract_32 bv64_extract_40 bv64_extract_48 bv64_extract_56
  bv16_setWidth_8 bv32_setWidth_8 bv32_setWidth_16
  bv64_setWidth_8 bv64_setWidth_16 bv64_setWidth_32
  zext64_bv16_setWidth_8 zext64_bv16_setWidth_16 zext64_bv16_setWidth_32
  zext32_bv16_setWidth_8 zext32_bv16_setWidth_16
  zext64_bv32_setWidth_8 zext64_bv32_setWidth_16 zext64_bv32_setWidth_32
)

export Shared (zext64_bv8_setWidth_8)

section ByteAccess

@[local simp, local arm64_norm, local wp_norm]
theorem bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

open Lean Meta Elab Tactic in
local elab_rules : tactic
  | `(tactic| wp_sep_access) => do
    let g ← getMainGoal
    g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let tyClean := ty.consumeMData
      let args := tyClean.getAppArgs
      let prf ←
        if tyClean.isAppOf ``SepLoad16 then
          try proveSepLoadBytes 2 args[0]! args[1]! args[2]!
          catch _ => sepAccess16Proof ty
        else if tyClean.isAppOf ``SepStore16 then
          try proveSepStoreBytes 2 args[0]! args[1]! args[2]! args[3]!
          catch _ => sepAccess16Proof ty
        else if tyClean.isAppOf ``SepLoad32 then
          try proveSepLoadBytes 4 args[0]! args[1]! args[2]!
          catch _ => sepAccess32Proof ty
        else if tyClean.isAppOf ``SepStore32 then
          try proveSepStoreBytes 4 args[0]! args[1]! args[2]! args[3]!
          catch _ => sepAccess32Proof ty
        else if tyClean.isAppOf ``SepLoad64 then
          try proveSepLoadBytes 8 args[0]! args[1]! args[2]!
          catch _ => sepAccessProof ty
        else if tyClean.isAppOf ``SepStore64 then
          try proveSepStoreBytes 8 args[0]! args[1]! args[2]! args[3]!
          catch _ => sepAccessProof ty
        else
          sepAccessProof ty
      unless ← isDefEq (← inferType prf) ty do throwError "wp_sep_access: type mismatch"
      g.assign prf
    replaceMainGoal []

attribute [local simp, local arm64_norm, local wp_norm]
  bv16_extract_0 bv16_extract_8
  bv32_extract_0 bv32_extract_8 bv32_extract_16 bv32_extract_24
  bv64_extract_0 bv64_extract_8 bv64_extract_16 bv64_extract_24
  bv64_extract_32 bv64_extract_40 bv64_extract_48 bv64_extract_56
  bv16_setWidth_8 bv32_setWidth_8 bv32_setWidth_16
  bv64_setWidth_8 bv64_setWidth_16 bv64_setWidth_32
  zext64_bv16_setWidth_8 zext64_bv16_setWidth_16 zext64_bv16_setWidth_32
  zext32_bv16_setWidth_8 zext32_bv16_setWidth_16
  zext64_bv32_setWidth_8 zext64_bv32_setWidth_16 zext64_bv32_setWidth_32
  zext64_bv8_setWidth_8

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_lo_byte_zext8_mask (b0 : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b0 &&& 1065151889656#64) = b0 &&& 0xf8#8 := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_lo_byte_norm (b0 : BitVec 8) :
    (((b0.zeroExtend 32 &&& 4294967288#32).zeroExtend 64).setWidth 8) = b0 &&& 0xf8#8 := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_lo_byte_norm' (b0 : BitVec 8) :
    (((b0.zeroExtend 64).setWidth 32 &&& 4294967288#32).zeroExtend 64).setWidth 8 =
      b0 &&& 0xf8#8 := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_hi_byte_norm (b31 : BitVec 8) :
    ((((0x40#32 &&& 4294967232#32) ||| (b31.zeroExtend 32 &&& 0x3f#32)).zeroExtend 64).setWidth 8) =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_hi_byte_norm' (b31 : BitVec 8) :
    ((((64#32 &&& 4294967232#32) |||
      (((b31.zeroExtend 64).setWidth 32) &&& 63#32)).zeroExtend 64).setWidth 8) =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_bits
@[local simp, local arm64_norm, local wp_norm]
theorem clamp_hi_byte_norm'' (b31 : BitVec 8) :
    ((64#32 ||| (b31.zeroExtend 32 &&& 63#32)).zeroExtend 64).setWidth 8 =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_hi_bfm_norm (b31 : BitVec 8) :
    ((64#64 ||| (b31.zeroExtend 64 >>> 0 &&& 63#64)).setWidth 32).zeroExtend 64 =
      ((b31 &&& 0x7f#8) ||| 0x40#8).zeroExtend 64 := by
  bv_bits

private theorem bv64_mask_low32_orr_zext32_32 (w_hi w_lo u : BitVec 32) :
    ((w_hi ++ w_lo) &&& 18446744069414584320#64) ||| u.zeroExtend 64 = w_hi ++ u := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem bv64_mask_low32_orr_zext32
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 : BitVec 8) :
    ((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) &&& 18446744069414584320#64) |||
      (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 =
      a7 ++ a6 ++ a5 ++ a4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  have h1 : a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0 =
      (a7 ++ a6 ++ a5 ++ a4) ++ (a3 ++ a2 ++ a1 ++ a0) := by bv_bits
  have h2 : a7 ++ a6 ++ a5 ++ a4 ++ b3 ++ b2 ++ b1 ++ b0 =
      (a7 ++ a6 ++ a5 ++ a4) ++ (b3 ++ b2 ++ b1 ++ b0) := by bv_bits
  rw [h1, h2]
  exact bv64_mask_low32_orr_zext32_32
    (a7 ++ a6 ++ a5 ++ a4) (a3 ++ a2 ++ a1 ++ a0) (b3 ++ b2 ++ b1 ++ b0)

private theorem bv64_extract_hi32_of_bytes8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    BitVec.extractLsb' 32 32 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      b7 ++ b6 ++ b5 ++ b4 := by
  bv_bits

private theorem bv64_reconstruct8 (w : BitVec 64) :
    BitVec.extractLsb' 56 8 w ++ BitVec.extractLsb' 48 8 w ++ BitVec.extractLsb' 40 8 w ++
      BitVec.extractLsb' 32 8 w ++ BitVec.extractLsb' 24 8 w ++ BitVec.extractLsb' 16 8 w ++
      BitVec.extractLsb' 8 8 w ++ BitVec.extractLsb' 0 8 w = w := by
  bv_bits

private theorem bv64_mask_high32_orr_lsl32_32 (w_hi w_lo u : BitVec 32) :
    ((w_hi ++ w_lo) &&& 4294967295#64) ||| (u.zeroExtend 64 <<< 32) = u ++ w_lo := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem bv64_mask_high32_orr_lsl32
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 : BitVec 8) :
    ((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) &&& 4294967295#64) |||
      ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 <<< 32) =
      b3 ++ b2 ++ b1 ++ b0 ++ a3 ++ a2 ++ a1 ++ a0 := by
  have h1 : a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0 =
      (a7 ++ a6 ++ a5 ++ a4) ++ (a3 ++ a2 ++ a1 ++ a0) := by bv_bits
  have h2 : b3 ++ b2 ++ b1 ++ b0 ++ a3 ++ a2 ++ a1 ++ a0 =
      (b3 ++ b2 ++ b1 ++ b0) ++ (a3 ++ a2 ++ a1 ++ a0) := by bv_bits
  rw [h1, h2]
  exact bv64_mask_high32_orr_lsl32_32
    (a7 ++ a6 ++ a5 ++ a4) (a3 ++ a2 ++ a1 ++ a0) (b3 ++ b2 ++ b1 ++ b0)

private theorem bv64_mask_low16_orr_zext16_16 (w_hi : BitVec 48) (w_lo u : BitVec 16) :
    ((w_hi ++ w_lo) &&& 18446744073709486080#64) ||| u.zeroExtend 64 = w_hi ++ u := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem bv64_mask_low16_orr_zext16
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 : BitVec 8) :
    ((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) &&& 18446744073709486080#64) |||
      (b1 ++ b0).zeroExtend 64 =
      a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ b1 ++ b0 := by
  have h1 : a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0 =
      (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2) ++ (a1 ++ a0) := by bv_bits
  have h2 : a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ b1 ++ b0 =
      (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2) ++ (b1 ++ b0) := by bv_bits
  rw [h1, h2]
  exact bv64_mask_low16_orr_zext16_16 (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2) (a1 ++ a0) (b1 ++ b0)

def bytes32At (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
  ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
  ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗ ((a + 15#64) ↦₈ b15) ∗
  ((a + 16#64) ↦₈ b16) ∗ ((a + 17#64) ↦₈ b17) ∗ ((a + 18#64) ↦₈ b18) ∗ ((a + 19#64) ↦₈ b19) ∗
  ((a + 20#64) ↦₈ b20) ∗ ((a + 21#64) ↦₈ b21) ∗ ((a + 22#64) ↦₈ b22) ∗ ((a + 23#64) ↦₈ b23) ∗
  ((a + 24#64) ↦₈ b24) ∗ ((a + 25#64) ↦₈ b25) ∗ ((a + 26#64) ↦₈ b26) ∗ ((a + 27#64) ↦₈ b27) ∗
  ((a + 28#64) ↦₈ b28) ∗ ((a + 29#64) ↦₈ b29) ∗ ((a + 30#64) ↦₈ b30) ∗ ((a + 31#64) ↦₈ b31)

theorem exists_bytes32_of_vector32 (v : List.Vector (BitVec 8) 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
       b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8),
      (∀ a : BitVec 64, (a ↦ₛ v.toList) =
        bytes32At a b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
          b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31) ∧
      (∀ a : BitVec 64, (a ↦ₛ (Ratchet.clampScalar v).toList) =
        bytes32At a (b0 &&& 0xf8#8) b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
          b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30
          ((b31 &&& 0x7f#8) ||| 0x40#8)) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  have hclamp :
    (Ratchet.clampScalar ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], hl⟩).toList =
    [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
     b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
     (b31 &&& 0x7f#8) ||| 0x40#8] := rfl
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31,
    fun a => ?_, fun a => ?_⟩
  · change (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]) = _
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd, bytes32At]
  · rw [hclamp]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd, bytes32At]

theorem pointsTo64_eq_extract_bytes8 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ w.extractLsb' 8 8) ∗
      ((a + 2#64) ↦₈ w.extractLsb' 16 8) ∗ ((a + 3#64) ↦₈ w.extractLsb' 24 8) ∗
      ((a + 4#64) ↦₈ w.extractLsb' 32 8) ∗ ((a + 5#64) ↦₈ w.extractLsb' 40 8) ∗
      ((a + 6#64) ↦₈ w.extractLsb' 48 8) ∗ ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hw : w = w.extractLsb' 56 8 ++ w.extractLsb' 48 8 ++ w.extractLsb' 40 8 ++
      w.extractLsb' 32 8 ++ w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++
      w.extractLsb' 8 8 ++ w.extractLsb' 0 8 := by bv_bits
  conv => lhs; rw [hw]
  exact pointsTo64_eq_bytes8 a _ _ _ _ _ _ _ _

theorem memRegion_8_bytes (a : BitVec 64) :
    memRegion a 8 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ b1 : BitVec 8, (a + 1#64) ↦₈ b1) ∗
      (∃∗ b2 : BitVec 8, (a + 2#64) ↦₈ b2) ∗
      (∃∗ b3 : BitVec 8, (a + 3#64) ↦₈ b3) ∗
      (∃∗ b4 : BitVec 8, (a + 4#64) ↦₈ b4) ∗
      (∃∗ b5 : BitVec 8, (a + 5#64) ↦₈ b5) ∗
      (∃∗ b6 : BitVec 8, (a + 6#64) ↦₈ b6) ∗
      (∃∗ b7 : BitVec 8, (a + 7#64) ↦₈ b7) := by
  rw [memRegion_split a 1 7 (by decide),
    memRegion_split (a + 1#64) 1 6 (by decide),
    memRegion_split (a + 1#64 + 1#64) 1 5 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64) 1 4 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64) 1 3 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 2 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 1 (by decide)]
  simp only [memRegion_one, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_7_bytes (a : BitVec 64) :
    memRegion a 7 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ b1 : BitVec 8, (a + 1#64) ↦₈ b1) ∗
      (∃∗ b2 : BitVec 8, (a + 2#64) ↦₈ b2) ∗
      (∃∗ b3 : BitVec 8, (a + 3#64) ↦₈ b3) ∗
      (∃∗ b4 : BitVec 8, (a + 4#64) ↦₈ b4) ∗
      (∃∗ b5 : BitVec 8, (a + 5#64) ↦₈ b5) ∗
      (∃∗ b6 : BitVec 8, (a + 6#64) ↦₈ b6) := by
  rw [memRegion_split a 1 6 (by decide),
    memRegion_split (a + 1#64) 1 5 (by decide),
    memRegion_split (a + 1#64 + 1#64) 1 4 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64) 1 3 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64) 1 2 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 1 (by decide)]
  simp only [memRegion_one, BitVec.add_assoc, BitVec.reduceAdd]

abbrev memRegion_8_bytes_mr_rhs (a : BitVec 64) : SepProp :=
  memRegion a 1 ∗
  memRegion (a + 1#64) 1 ∗
  memRegion (a + 2#64) 1 ∗
  memRegion (a + 3#64) 1 ∗
  memRegion (a + 4#64) 1 ∗
  memRegion (a + 5#64) 1 ∗
  memRegion (a + 6#64) 1 ∗
  memRegion (a + 7#64) 1

theorem memRegion_8_bytes_mr (a : BitVec 64) :
    memRegion a 8 =
      memRegion a 1 ∗
      memRegion (a + 1#64) 1 ∗
      memRegion (a + 2#64) 1 ∗
      memRegion (a + 3#64) 1 ∗
      memRegion (a + 4#64) 1 ∗
      memRegion (a + 5#64) 1 ∗
      memRegion (a + 6#64) 1 ∗
      memRegion (a + 7#64) 1 := by
  rw [memRegion_8_bytes a]
  simp only [← ProofLib.memRegion_one]

theorem memRegion_65_cells (a : BitVec 64) :
    memRegion a 65 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      cells (a + 1#64) 8 := by
  rw [memRegion_split a 1 64 (by decide), memRegion_one,
    (ProofLib.memRegion_cells (a + 1#64) 8 (by decide) :
      memRegion (a + 1#64) 64 = cells (a + 1#64) 8)]

theorem memRegion_65_words (a : BitVec 64) :
    memRegion a 65 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ w0 : BitVec 64, (a + 1#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 9#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 17#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 25#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 33#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 41#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (a + 49#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (a + 57#64) ↦₆₄ w7) := by
  rw [memRegion_split a 1 64 (by decide),
    memRegion_split (a + 1#64) 8 56 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 48 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [memRegion_one, ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]

theorem memRegion_40_words (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 32#64) ↦₆₄ w4) := by
  rw [memRegion_split a 8 32 (by decide),
    memRegion_split (a + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ### 1. `<libsignal_core::curve::KeyPair>::from_public_and_private`
  (`0x3e738`, 106 instructions) -/

@[simp, arm64_norm]
abbrev keyPairFromPubPrivName : String :=
  "<libsignal_core::curve::KeyPair>::from_public_and_private"

def keyPairFromPubPrivSpec :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 ×
      List.Vector (BitVec 8) 32 × BitVec 64) where
  pre := fun (pubPtr, pk, privPtr, sk, outPtr) s =>
    ⌜s.readReg64 .x0 = pubPtr ∧ s.readReg64 .x1 = 33#64 ∧
      s.readReg64 .x2 = privPtr ∧ s.readReg64 .x3 = 32#64 ∧
      s.readReg64 .x8 = outPtr⌝ ∗
    (pubPtr ↦ₛ (5#8 :: pk.toList)) ∗
    (privPtr ↦ₛ sk.toList) ∗
    memRegion outPtr 65 ∗
    cells (s.sp - 64#64) 8
  post := fun (pubPtr, pk, privPtr, sk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (pubPtr ↦ₛ (5#8 :: pk.toList)) ∗
    (privPtr ↦ₛ sk.toList) ∗
    (outPtr ↦₈ 0#8) ∗
    ((outPtr + 1#64) ↦ₛ pk.toList) ∗
    ((outPtr + 33#64) ↦ₛ (Ratchet.clampScalar sk).toList) ∗
    cells (s0.sp - 64#64) 8

theorem keyPairFromPubPriv_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr keyPairFromPubPrivName)
      keyPairFromPubPrivSpec := by
  unfold keyPairFromPubPrivSpec
  simp only [memRegion_65_cells, cells, sepConj_emp, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  code_fetches CryptoVerification.libsignalSessionCode keyPairFromPubPriv b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3e81c 0x3e81c 424
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  rcases x with ⟨pubPtr, pk, privPtr, sk, outPtr⟩
  dsimp only at *
  subst h_1 h_3 h
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_vector32 pk
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    hsk, hsk_clamp⟩ := exists_bytes32_of_vector32 sk
  wp_pull_exists
  rw [pointsToBytes_cons, hpk (s0.readReg64 (.gpr 0#5) + 1#64),
    hsk (s0.readReg64 (.gpr 2#5)),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  dsimp only [bytes32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-! ### 2. `<IdentityKeyPair as TryFrom<PrivateKey>>::try_from` (`0x28704`, 73 instructions) -/

@[simp, arm64_norm]
abbrev identityKeyPairTryFromName : String :=
  "<libsignal_protocol::identity_key::IdentityKeyPair as \
core::convert::TryFrom<libsignal_core::curve::PrivateKey>>::try_from"

private theorem cells_12_identityKeyPair_pre (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 8 ∗
      memRegion (sp - 80#64) 33 ∗
      memRegion (sp - 47#64) 7 ∗
      memRegion (sp - 40#64) 8 ∗
      (∃∗ w_32 : BitVec 64, (sp - 32#64) ↦₆₄ w_32) ∗
      (∃∗ w_24 : BitVec 64, (sp - 24#64) ↦₆₄ w_24) ∗
      (∃∗ w_16 : BitVec 64, (sp - 16#64) ↦₆₄ w_16) ∗
      (∃∗ w_8 : BitVec 64, (sp - 8#64) ↦₆₄ w_8) := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    memRegion_split (sp - 96#64) 8 88 (by decide),
    memRegion_split (sp - 96#64 + 8#64) 8 80 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64) 33 47 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 33#64) 7 40 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 33#64 + 7#64) 8 32 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 33#64 + 7#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 33#64 + 7#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 33#64 + 7#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  rw [ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64),
      ProofLib.memRegion_eight (sp - 8#64)]

private theorem cells_12_identityKeyPair_post (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion_8_bytes_mr_rhs (sp - 96#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 88#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 80#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 72#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 64#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 56#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 48#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 40#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 32#64) ∗
      memRegion (sp - 24#64) 8 ∗
      memRegion (sp - 16#64) 8 ∗
      memRegion (sp - 8#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    memRegion_split (sp - 96#64) 8 88 (by decide),
    memRegion_split (sp - 96#64 + 8#64) 8 80 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64) 8 72 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split
      (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split
      (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split
      (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
      8 8 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  rw [memRegion_8_bytes_mr (sp - 96#64),
      memRegion_8_bytes_mr (sp - 88#64),
      memRegion_8_bytes_mr (sp - 80#64),
      memRegion_8_bytes_mr (sp - 72#64),
      memRegion_8_bytes_mr (sp - 64#64),
      memRegion_8_bytes_mr (sp - 56#64),
      memRegion_8_bytes_mr (sp - 48#64),
      memRegion_8_bytes_mr (sp - 40#64),
      memRegion_8_bytes_mr (sp - 32#64)]
  simp only [memRegion_8_bytes_mr_rhs, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]

def identityKeyPairTryFromSpec (pubKey : PubKeyFn) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) where
  pre := fun (privPtr, sk, outPtr) s =>
    ⌜s.readReg64 .x0 = privPtr ∧ s.readReg64 .x8 = outPtr⌝ ∗
      (privPtr ↦ₛ sk.toList) ∗ memRegion outPtr 65 ∗
      cells (s.sp - 160#64) 8 ∗ cells (s.sp - 96#64) 12
  post := fun (privPtr, sk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (privPtr ↦ₛ sk.toList) ∗
      (outPtr ↦₈ 0#8) ∗
      ((outPtr + 1#64) ↦ₛ (pubKey (Ratchet.clampScalar sk)).toList) ∗
      ((outPtr + 33#64) ↦ₛ sk.toList) ∗
      cells (s0.sp - 160#64) 8 ∗ cells (s0.sp - 96#64) 12

set_option maxHeartbeats 1600000 in
theorem identityKeyPairTryFrom_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr identityKeyPairTryFromName)
      (identityKeyPairTryFromSpec C.pubKey) := by
  unfold identityKeyPairTryFromSpec
  have hpub : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr identityKeyPairTryFromName + BitVec.ofNat 64 89744)
      (privateKeyPublicKeySpec C.pubKey) :=
    inImage_ok_at
      (by simp only [libsignalSessionCode_fnOff_0x287e8, libsignalSessionCode_fnOff_0x3e678])
      privateKeyPublicKey_ok
  simp only [privateKeyPublicKeySpec] at hpub
  code_fetches CryptoVerification.libsignalSessionCode identityKeyPairTryFrom b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x287e8 0x287e8 292
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  rcases x with ⟨privPtr, sk, outPtr⟩
  dsimp only at *
  subst h_1 h
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_vector32 (C.pubKey (Ratchet.clampScalar sk))
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    hsk, _⟩ := exists_bytes32_of_vector32 sk
  rw (occs := .pos [1]) [cells_12_identityKeyPair_pre s0.sp]
  wp_pull_exists
  wp_steps
  wp_call hpub (s0.readReg64 (.gpr 0#5), sk, s0.sp - 80#64)
  rw [memRegion_65_words (s0.readReg64 (.gpr 8#5)),
      memRegion_8_bytes (s0.sp - 96#64),
      memRegion_8_bytes (s0.sp - 88#64),
      memRegion_7_bytes (s0.sp - 47#64),
      memRegion_8_bytes (s0.sp - 40#64)]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  rw [hpk (s0.sp - 79#64),
      hsk (s0.readReg64 (.gpr 0#5)),
      hpk (s0.readReg64 (.gpr 8#5) + 1#64),
      hsk (s0.readReg64 (.gpr 8#5) + 33#64),
      pointsTo64_eq_extract_bytes8 (s0.sp - 32#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64),
      cells_12_identityKeyPair_post s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  simp only [bv64_extract_hi32_of_bytes8, bv64_mask_low32_orr_zext32,
    bv64_extract_56, bv64_extract_48, bv64_extract_40, bv64_reconstruct8]
  wp_done

/-! ### 3. `<IdentityKey as TryFrom<&[u8]>>::try_from` (`0x2c530`, 66 instructions) -/

@[simp, arm64_norm]
abbrev identityKeyTryFromSliceName : String :=
  "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from"

private theorem cells_12_identityKey_pre (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      memRegion (sp - 48#64) 8 ∗
      memRegion (sp - 40#64) 8 ∗
      (∃∗ w_32 : BitVec 64, (sp - 32#64) ↦₆₄ w_32) ∗
      (∃∗ w_24 : BitVec 64, (sp - 24#64) ↦₆₄ w_24) ∗
      (∃∗ w_16 : BitVec 64, (sp - 16#64) ↦₆₄ w_16) ∗
      memRegion (sp - 8#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    memRegion_split (sp - 96#64) 8 88 (by decide),
    memRegion_split (sp - 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64) 8 40 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64) 8 32 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  rw [ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64)]

private theorem cells_12_identityKey_post (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion_8_bytes_mr_rhs (sp - 96#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 88#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 80#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 72#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 64#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 56#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 48#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 40#64) ∗
      memRegion (sp - 32#64) 8 ∗
      memRegion (sp - 24#64) 8 ∗
      memRegion (sp - 16#64) 8 ∗
      memRegion_8_bytes_mr_rhs (sp - 8#64) := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    memRegion_split (sp - 96#64) 8 88 (by decide),
    memRegion_split (sp - 96#64 + 8#64) 8 80 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64) 8 72 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split
      (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split
      (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split
      (sp - 96#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
      8 8 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  rw [memRegion_8_bytes_mr (sp - 96#64),
      memRegion_8_bytes_mr (sp - 88#64),
      memRegion_8_bytes_mr (sp - 80#64),
      memRegion_8_bytes_mr (sp - 72#64),
      memRegion_8_bytes_mr (sp - 64#64),
      memRegion_8_bytes_mr (sp - 56#64),
      memRegion_8_bytes_mr (sp - 48#64),
      memRegion_8_bytes_mr (sp - 40#64),
      memRegion_8_bytes_mr (sp - 8#64)]
  simp only [memRegion_8_bytes_mr_rhs, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]

private def pkTryFromOk40Spec (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = out ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 40 ∗ logOff img
  post := fun (p, bs, pk, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion (out + 33#64) 7 ∗ logOff img

private theorem pkTryFromOk40_ok_at {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr identityKeyTryFromSliceName +
        BitVec.ofNat 64 75180)
      (pkTryFromOk40Spec img) := by
  have hk : libsignalSessionCode.fnOff identityKeyTryFromSliceName + 75180 =
      libsignalSessionCode.fnOff pkTryFromName := by
    simp only [libsignalSessionCode_fnOff_0x2c614, libsignalSessionCode_fnOff_0x3ebc0]
  refine subroutine_ok_map
    (pk_try_from_ok_at img C ctl abs himg identityKeyTryFromSliceName 75180 hk) ?_
  rintro ⟨p, bs, pk, out⟩ R s0 hpre
  simp only [pkTryFromOk40Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [pkTryFromOk40Spec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hpost⟩

def identityKeyTryFromSliceOkSpec (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, outPtr) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = outPtr ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion outPtr 40 ∗ logOff img ∗
      cells (s.sp - 96#64) 12
  post := fun (p, bs, pk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((outPtr + 8#64) ↦ₛ pk.bytes.toList) ∗
      logOff img ∗
      cells (s0.sp - 96#64) 12

theorem identityKeyTryFromSlice_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceOkSpec img) := by
  unfold identityKeyTryFromSliceOkSpec
  have hpk := pkTryFromOk40_ok_at (C := C) (ctl := ctl) (abs := abs) himg
  simp only [pkTryFromOk40Spec, sepConj_assoc] at hpk
  code_fetches CryptoVerification.libsignalSessionCode identityKeyTryFromSlice img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x2c614 0x2c614 264
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  rcases x with ⟨p, bs, pk, outPtr⟩
  dsimp only at *
  subst h_1 h_3
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk_bytes, _⟩ := exists_bytes32_of_vector32 pk.bytes
  rw (occs := .pos [1]) [cells_12_identityKey_pre s0.sp]
  wp_pull_exists
  wp_steps
  wp_call hpk (s0.readReg64 (.gpr 0#5), bs, pk, s0.sp - 88#64)
  rw [memRegion_40_words (s0.readReg64 (.gpr 8#5)),
      memRegion_8_bytes (s0.sp - 96#64),
      memRegion_7_bytes (s0.sp - 55#64),
      memRegion_8_bytes (s0.sp - 48#64),
      memRegion_8_bytes (s0.sp - 40#64),
      memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  rw [hpk_bytes (s0.sp - 87#64),
      hpk_bytes (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 16#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 24#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 32#64),
      cells_12_identityKey_post s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

/-! ## Relocatable `[LibsignalPlacement]` Contracts -/

theorem keyPairFromPubPriv_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_209).rebase (blkPl_209).base H) (blkPl_209).base
      keyPairFromPubPrivSpec := by
  unfold keyPairFromPubPrivSpec
  simp only [memRegion_65_cells, cells, sepConj_emp, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_init x s0; rcases x with ⟨pubPtr, pk, privPtr, sk, outPtr⟩; dsimp only at *
  subst h_1 h_3 h
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_vector32 pk
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    hsk, hsk_clamp⟩ := exists_bytes32_of_vector32 sk
  wp_pull_exists
  rw [pointsToBytes_cons, hpk (s0.readReg64 (.gpr 0#5) + 1#64),
    hsk (s0.readReg64 (.gpr 2#5)),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  dsimp only [bytes32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps; wp_done

private def pkTryFromOk40PlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = out ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 40 ∗ lsLogOff
  post := fun (p, bs, pk, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion (out + 33#64) 7 ∗ lsLogOff

private theorem pkTryFromOk40_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (blkPl_211).base
      pkTryFromOk40PlacedSpec := by
  refine subroutine_ok_map (pkTryFrom_placed_ok H) ?_
  rintro ⟨p, bs, pk, out⟩ R s0 hpre
  simp only [pkTryFromOk40PlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromPlacedSpec, pkTryFromSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  · simp only [pkTryFromPlacedSpec, pkTryFromSpec, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [pkTryFromOk40PlacedSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hpost⟩

def identityKeyTryFromSliceOkPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, outPtr) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = outPtr ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion outPtr 40 ∗ lsLogOff ∗
      cells (s.sp - 96#64) 12
  post := fun (p, bs, pk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((outPtr + 8#64) ↦ₛ pk.bytes.toList) ∗
      lsLogOff ∗
      cells (s0.sp - 96#64) 12

theorem identityKeyTryFromSlice_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_116).rebase (blkPl_116).base H) (blkPl_116).base
      (withLsCodeLoaded lsmpl identityKeyTryFromSliceOkPlacedSpec) := by
  unfold withLsCodeLoaded identityKeyTryFromSliceOkPlacedSpec
  have hpk := ls_subroutine_ok_of_block (callerProg := (blkPC_116).rebase (blkPl_116).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (pkTryFromOk40_placed_ok H))
  change subroutine_ok _ (lsmpl.base 211) _ at hpk
  dsimp only [withLsCodeLoaded, pkTryFromOk40PlacedSpec] at hpk
  simp only [sepConj_assoc] at hpk
  wp_init x s0; rcases x with ⟨p, bs, pk, outPtr⟩; dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst p outPtr
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk_bytes, _⟩ := exists_bytes32_of_vector32 pk.bytes
  rw (occs := .pos [1]) [cells_12_identityKey_pre s0.sp]
  wp_pull_exists
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hcl1
  wp_call hpk (s0.readReg64 (.gpr 0#5), bs, pk, s0.sp - 88#64)
  rw [memRegion_40_words (s0.readReg64 (.gpr 8#5)),
      memRegion_8_bytes (s0.sp - 96#64),
      memRegion_7_bytes (s0.sp - 55#64),
      memRegion_8_bytes (s0.sp - 48#64),
      memRegion_8_bytes (s0.sp - 40#64),
      memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  rw [hpk_bytes (s0.sp - 87#64),
      hpk_bytes (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 16#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 24#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 32#64),
      cells_12_identityKey_post s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps; wp_done

end ByteAccess

end CryptoVerification.E2E.Pqxdh
