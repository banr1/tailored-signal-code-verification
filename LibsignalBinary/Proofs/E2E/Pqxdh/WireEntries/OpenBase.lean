/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Specs
public import LibsignalBinary.Proofs.E2E.Bin.SegCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.CalleeProofs
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsEpilogue -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsStoreSession -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsStoresInitSaveIdentity -- shake: keep

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux
open ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec
open CryptoVerification.E2E.InMem

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

/-! ## `.rodata` Role Strings (`0x87888`, `0x878ac`) -/

section PqxdhNameRoDataFacts
set_option maxRecDepth 2000000

end PqxdhNameRoDataFacts

/-! ## 36-Byte Word Decompositions and `meBytes` Clamping -/

theorem exists_words4_word32_of_length_36 {bs : List (BitVec 8)} (h : bs.length = 36) :
    ∃ (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32),
      (∀ a : BitVec 64,
        (a ↦ᵣ bs) =
          (a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗
          ((a + 24#64) ↦₆₄ᵣ w3) ∗ ((a + 32#64) ↦₃₂ᵣ w4)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
          ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₃₂ w4)) := by
  have hle : ∀ k, k ≤ 36 → k ≤ bs.length := fun k hk => h ▸ hk
  refine ⟨pack64 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
            (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8),
          pack64 (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8)
            (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8),
          pack64 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)
            (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8),
          pack64 (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8) (bs.getD 27 0#8)
            (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8) (bs.getD 31 0#8),
          pack32 (bs.getD 32 0#8) (bs.getD 33 0#8) (bs.getD 34 0#8) (bs.getD 35 0#8),
          fun a => ?_, fun a => ?_⟩
  · change (a ↦ᵣ bs.drop 0) = _
    rw [pointsToBytesRO_drop_split a bs 0 8 (hle 8 (by decide)),
        pointsToBytesRO_drop_split _ bs 8 8 (hle 16 (by decide)),
        pointsToBytesRO_drop_split _ bs 16 8 (hle 24 (by decide)),
        pointsToBytesRO_drop_split _ bs 24 8 (hle 32 (by decide)),
        pointsToBytesRO_drop_split _ bs 32 4 (hle 36 (by decide))]
    have hdrop36 : bs.drop 36 = [] := by simp [h]
    rw [hdrop36, pointsToBytesRO_nil, sepConj_emp,
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 0 (hle 8 (by decide)),
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 8 (hle 16 (by decide)),
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 16 (hle 24 (by decide)),
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 24 (hle 32 (by decide)),
        pointsToBytesRO_take4_eq_pointsTo32RO _ bs 32 (hle 36 (by decide))]
    have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
    rw [h8]
    simp only [pack32, BitVec.add_assoc, BitVec.reduceAdd]
  · change (a ↦ₛ bs.drop 0) = _
    rw [pointsToBytes_drop_split a bs 0 8 (hle 8 (by decide)),
        pointsToBytes_drop_split _ bs 8 8 (hle 16 (by decide)),
        pointsToBytes_drop_split _ bs 16 8 (hle 24 (by decide)),
        pointsToBytes_drop_split _ bs 24 8 (hle 32 (by decide)),
        pointsToBytes_drop_split _ bs 32 4 (hle 36 (by decide))]
    have hdrop36 : bs.drop 36 = [] := by simp [h]
    rw [hdrop36, pointsToBytes_nil, sepConj_emp,
        pointsToBytes_take8_eq_pointsTo64 _ bs 0 (hle 8 (by decide)),
        pointsToBytes_take8_eq_pointsTo64 _ bs 8 (hle 16 (by decide)),
        pointsToBytes_take8_eq_pointsTo64 _ bs 16 (hle 24 (by decide)),
        pointsToBytes_take8_eq_pointsTo64 _ bs 24 (hle 32 (by decide)),
        pointsToBytes_take4_eq_pointsTo32 _ bs 32 (hle 36 (by decide))]
    have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
    rw [h8]
    simp only [pack32, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_36_words4_word32_split (a : BitVec 64) :
    memRegion a 36 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 32, (a + 32#64) ↦₃₂ d4) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 4)
        (b' := a + 32#64) rfl (by bv_omega) (by decide),
      memRegion_32_four_64 a,
      memRegion_four (a + 32#64)]
  simp only [sepConj_assoc]

theorem pointsToBytes_meBytes_split (a : BitVec 64) {meBytes : List (BitVec 8)}
    (hlen : meBytes.length = 36) :
    (a ↦ₛ meBytes) =
      (a ↦ₛ meBytes.take 32) ∗ ((a + 32#64) ↦₃₂ meRegId meBytes) := by
  have hle : ∀ k, k ≤ 36 → k ≤ meBytes.length := fun k hk => hlen ▸ hk
  change (a ↦ₛ meBytes.drop 0) = _
  rw [pointsToBytes_drop_split a meBytes 0 32 (hle 32 (by decide)),
      pointsToBytes_drop_split _ meBytes 32 4 (hle 36 (by decide))]
  have hdrop36 : meBytes.drop 36 = [] := by simp [hlen]
  rw [hdrop36, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ meBytes 32 (hle 36 (by decide))]
  rfl

def meSkVec (meBytes : List (BitVec 8)) (hlen : meBytes.length = 36) : List.Vector (BitVec 8) 32 :=
  ⟨meBytes.take 32, by simp [hlen]⟩

def meClampedVec (meBytes : List (BitVec 8)) (hlen : meBytes.length = 36) : List.Vector (BitVec 8)
  32 :=
  Ratchet.clampScalar (meSkVec meBytes hlen)

theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  apply Subtype.ext
  change [(b0 &&& 0xf8#8) &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
    b15,
          b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
          (((b31 &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8] =
         [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
          b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
          (b31 &&& 0x7f#8) ||| 0x40#8]
  have h0 : (b0 &&& 0xf8#8) &&& 0xf8#8 = b0 &&& 0xf8#8 := by
    rw [BitVec.and_assoc]; rfl
  have h31 : (((b31 &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8 = (b31 &&& 0x7f#8) ||| 0x40#8 := by
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
      show (0x7f#8 : BitVec 8) &&& 0x7f#8 = 0x7f#8 from rfl,
      show (0x40#8 : BitVec 8) &&& 0x7f#8 = 0x40#8 from rfl,
      BitVec.or_assoc,
      show (0x40#8 : BitVec 8) ||| 0x40#8 = 0x40#8 from rfl]
  rw [h0, h31]

theorem meKeyPairBytes_eq_of_length_36 (pubKey : PubKeyFn) {meBytes : List (BitVec 8)}
    (hlen : meBytes.length = 36) :
    meKeyPairBytes pubKey meBytes =
      (pubKey (meClampedVec meBytes hlen)).toList ++ (meClampedVec meBytes hlen).toList := by
  have h32 : (meBytes.take 32).length = 32 := by simp [hlen]
  unfold meKeyPairBytes meClampedVec meSkVec
  simp only [h32, ↓reduceDIte]

theorem pointsToBytes_meKeyPairBytes_eq (pubKey : PubKeyFn) {meBytes : List (BitVec 8)}
    (hlen : meBytes.length = 36) (a : BitVec 64) :
    ((a ↦ₛ (pubKey (Ratchet.clampScalar (meClampedVec meBytes hlen))).toList) ∗
     ((a + 32#64) ↦ₛ (meClampedVec meBytes hlen).toList)) =
      (a ↦ₛ meKeyPairBytes pubKey meBytes) := by
  rw [meKeyPairBytes_eq_of_length_36 pubKey hlen]
  unfold meClampedVec
  rw [clampScalar_idem (meSkVec meBytes hlen), pointsToBytes_append,
      List.Vector.toList_length]

/-! ## `<IdentityKey>::decode` (`0x0ae58`) -/

def pkTryFromLen33AnySpec : Spec (BitVec 64 × BitVec 64 × IdentityKey) where
  pre := fun (out, keyPtr, k) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = keyPtr ∧ s.readReg64 .x1 = 33#64⌝ ∗
      (keyPtr ↦ₛ (0x05#8 :: k.publicKey.bytes.toList)) ∗ memRegion out 40
  post := fun (out, keyPtr, k) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (keyPtr ↦ₛ (0x05#8 :: k.publicKey.bytes.toList)) ∗
      (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (out + 33#64) 7

theorem pkTryFrom_len33_any_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr pkTryFromName) pkTryFromLen33AnySpec := by
  simp only [pkTryFromLen33AnySpec]
  code_fetches_range libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom.pkTryFrom b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.libsignalSessionCode_fnOff_0x3ebc0 0x3ebc0 0 48
  code_fetches_range libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom.pkTryFrom b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.libsignalSessionCode_fnOff_0x3ebc0 0x3ebc0 196 76
  wp_init g s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, keyPtr, k⟩ := g
  dsimp only at *
  subst out keyPtr
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := k.publicKey.bytes.toList) k.publicKey.bytes.2
  rw [pointsToBytes_cons,
      hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
      PublicKeyTryFrom.memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
  wp_pull_exists
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_done

theorem pk_try_from_len33_any_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pkTryFromName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) pkTryFromLen33AnySpec :=
  inImage_ok_at hk (pkTryFrom_len33_any_ok b C ctl abs)

private def remoteKeyChunksAny (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₁₆ v7) ∗ ((a + 9#64) ↦₃₂ v9) ∗ ((a + 13#64) ↦₁₆ v13) ∗
  ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

private theorem exists_remoteKeyChunksAny_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
      (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
      (v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = remoteKeyChunksAny a b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 := by
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
  have hle : ∀ k, k ≤ 32 → k ≤ bs.length := fun k hk => h ▸ hk
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 4 (hle 4 (by decide)),
      pointsToBytes_drop_split _ bs 4 1 (hle 5 (by decide)),
      pointsToBytes_drop_split _ bs 5 1 (hle 6 (by decide)),
      pointsToBytes_drop_split _ bs 6 1 (hle 7 (by decide)),
      pointsToBytes_drop_split _ bs 7 2 (hle 9 (by decide)),
      pointsToBytes_drop_split _ bs 9 4 (hle 13 (by decide)),
      pointsToBytes_drop_split _ bs 13 2 (hle 15 (by decide)),
      pointsToBytes_drop_split _ bs 15 8 (hle 23 (by decide)),
      pointsToBytes_drop_split _ bs 23 8 (hle 31 (by decide)),
      pointsToBytes_drop_split _ bs 31 1 (hle 32 (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (hle 4 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 4 (hle 5 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 5 (hle 6 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (hle 7 (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 7 (hle 9 (by decide)),
      pointsToBytes_take4_eq_pointsTo32 _ bs 9 (hle 13 (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 13 (hle 15 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (hle 23 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (hle 31 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (hle 32 (by decide))]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
  rw [h8, h1, h4, h2]
  simp only [remoteKeyChunksAny, pack32, BitVec.add_assoc, BitVec.reduceAdd]

private theorem remoteKeyChunksAny_ret_8 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunksAny (ret + 8#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗
      ((ret + 15#64) ↦₁₆ v7) ∗ ((ret + 17#64) ↦₃₂ v9) ∗ ((ret + 21#64) ↦₁₆ v13) ∗
      ((ret + 23#64) ↦₆₄ v15) ∗ ((ret + 31#64) ↦₆₄ v23) ∗ ((ret + 39#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunksAny]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem remoteKeyChunksAny_sp_87 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunksAny (sp - 87#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗
      ((sp - 80#64) ↦₁₆ v7) ∗ ((sp - 78#64) ↦₃₂ v9) ∗ ((sp - 74#64) ↦₁₆ v13) ∗
      ((sp - 72#64) ↦₆₄ v15) ∗ ((sp - 64#64) ↦₆₄ v23) ∗ ((sp - 56#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunksAny]
  have h83 : sp - 87#64 + 4#64 = sp - 83#64 := by bv_omega
  have h82 : sp - 87#64 + 5#64 = sp - 82#64 := by bv_omega
  have h81 : sp - 87#64 + 6#64 = sp - 81#64 := by bv_omega
  have h80 : sp - 87#64 + 7#64 = sp - 80#64 := by bv_omega
  have h78 : sp - 87#64 + 9#64 = sp - 78#64 := by bv_omega
  have h74 : sp - 87#64 + 13#64 = sp - 74#64 := by bv_omega
  have h72 : sp - 87#64 + 15#64 = sp - 72#64 := by bv_omega
  have h64 : sp - 87#64 + 23#64 = sp - 64#64 := by bv_omega
  have h56 : sp - 87#64 + 31#64 = sp - 56#64 := by bv_omega
  rw [h83, h82, h81, h80, h78, h74, h72, h64, h56]

private theorem sevenLo_sp_87_any (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗ rest) =
      (((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗
       ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 87#64) (sp - 86#64) (sp - 85#64) (sp - 84#64)
    (sp - 83#64) (sp - 82#64) (sp - 81#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_ret_8_any (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗ rest) =
      (((ret + 8#64) ↦₈ b0) ∗ ((ret + 9#64) ↦₈ b1) ∗ ((ret + 10#64) ↦₈ b2) ∗
       ((ret + 11#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (ret + 8#64) (ret + 9#64) (ret + 10#64) (ret + 11#64)
    (ret + 12#64) (ret + 13#64) (ret + 14#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sp_88_four_bytes_any (sp : BitVec 64) (b0 b1 b2 : BitVec 8) (rest : SepProp) :
    (((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗
    rest) =
      (((sp - 88#64) ↦₃₂ (b2 ++ b1 ++ b0 ++ 0#8)) ∗ rest) := by
  have h87 : sp - 87#64 = sp - 88#64 + 1#64 := by bv_omega
  have h86 : sp - 86#64 = sp - 88#64 + 2#64 := by bv_omega
  have h85 : sp - 85#64 = sp - 88#64 + 3#64 := by bv_omega
  rw [h87, h86, h85, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sp_84_split_16_any (sp : BitVec 64) (b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) =
      (((sp - 84#64) ↦₁₆ (b4 ++ b3)) ∗ ((sp - 82#64) ↦₁₆ (b6 ++ b5)) ∗ rest) := by
  have h82 : sp - 82#64 = sp - 84#64 + 2#64 := by bv_omega
  rw [h82, ← pointsToBytes4_eq_pointsTo32, ← pointsToBytes2_eq_pointsTo16,
    ← pointsToBytes2_eq_pointsTo16]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion_40_identityKeyDecode_split_any (ret : BitVec 64) :
    memRegion ret 40 =
      (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗
      (∃∗ r8 : BitVec 32, (ret + 8#64) ↦₃₂ r8) ∗
      (∃∗ r12 : BitVec 8, (ret + 12#64) ↦₈ r12) ∗
      (∃∗ r13 : BitVec 8, (ret + 13#64) ↦₈ r13) ∗
      (∃∗ r14 : BitVec 8, (ret + 14#64) ↦₈ r14) ∗
      (∃∗ r15 : BitVec 16, (ret + 15#64) ↦₁₆ r15) ∗
      (∃∗ r17 : BitVec 32, (ret + 17#64) ↦₃₂ r17) ∗
      (∃∗ r21 : BitVec 16, (ret + 21#64) ↦₁₆ r21) ∗
      (∃∗ r23 : BitVec 64, (ret + 23#64) ↦₆₄ r23) ∗
      (∃∗ r31 : BitVec 64, (ret + 31#64) ↦₆₄ r31) ∗
      (∃∗ r39 : BitVec 8, (ret + 39#64) ↦₈ r39) := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 32)
        (b' := ret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 4) (k := 28)
        (b' := ret + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 12#64) (n := 1) (k := 27)
        (b' := ret + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 13#64) (n := 1) (k := 26)
        (b' := ret + 14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 14#64) (n := 1) (k := 25)
        (b' := ret + 15#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 15#64) (n := 2) (k := 23)
        (b' := ret + 17#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 17#64) (n := 4) (k := 19)
        (b' := ret + 21#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 21#64) (n := 2) (k := 17)
        (b' := ret + 23#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 23#64) (n := 8) (k := 9)
        (b' := ret + 31#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 31#64) (n := 8) (k := 1)
        (b' := ret + 39#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret, memRegion_four (ret + 8#64),
      memRegion_one (ret + 12#64), memRegion_one (ret + 13#64), memRegion_one (ret + 14#64),
      memRegion_two (ret + 15#64), memRegion_four (ret + 17#64), memRegion_two (ret + 21#64),
      ProofLib.memRegion_eight (ret + 23#64), ProofLib.memRegion_eight (ret + 31#64),
        memRegion_one (ret + 39#64)]

private theorem stackAt_identityKeyDecode_split_any (sp : BitVec 64) :
    stackAt sp 0x60 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      (∃∗ s48 : BitVec 64, (sp - 48#64) ↦₆₄ s48) ∗
      (∃∗ s56 : BitVec 8, (sp - 40#64) ↦₈ s56) ∗
      memRegion (sp - 39#64) 7 ∗
      cells (sp - 32#64) 3 ∗
      (∃∗ s88 : BitVec 32, (sp - 8#64) ↦₃₂ s88) ∗
      (∃∗ s92 : BitVec 16, (sp - 4#64) ↦₁₆ s92) ∗
      memRegion (sp - 2#64) 2 := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x60 = 96#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 40) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 1) (k := 39)
        (b' := sp - 39#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 39#64) (n := 7) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 24) (k := 8)
        (b' := sp - 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 8#64) (n := 4) (k := 4)
        (b' := sp - 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 2) (k := 2)
        (b' := sp - 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 48#64), memRegion_one (sp - 40#64),
      (ProofLib.memRegion_cells (sp - 32#64) 3 (by decide) :
        memRegion (sp - 32#64) 24 = cells (sp - 32#64) 3),
      memRegion_four (sp - 8#64), memRegion_two (sp - 4#64)]

private theorem memRegion_sp_88_40_split_any (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      (∃∗ k0 : BitVec 32, (sp - 88#64) ↦₃₂ k0) ∗
      (∃∗ k4 : BitVec 16, (sp - 84#64) ↦₁₆ k4) ∗
      (∃∗ k6 : BitVec 16, (sp - 82#64) ↦₁₆ k6) ∗
      (∃∗ k8 : BitVec 16, (sp - 80#64) ↦₁₆ k8) ∗
      (∃∗ k10 : BitVec 32, (sp - 78#64) ↦₃₂ k10) ∗
      (∃∗ k14 : BitVec 16, (sp - 74#64) ↦₁₆ k14) ∗
      (∃∗ k16 : BitVec 64, (sp - 72#64) ↦₆₄ k16) ∗
      (∃∗ k24 : BitVec 64, (sp - 64#64) ↦₆₄ k24) ∗
      (∃∗ k32 : BitVec 8, (sp - 56#64) ↦₈ k32) ∗
      memRegion (sp - 55#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 4) (k := 36)
        (b' := sp - 84#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 84#64) (n := 2) (k := 34)
        (b' := sp - 82#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 2) (k := 32)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 2) (k := 30)
        (b' := sp - 78#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 78#64) (n := 4) (k := 26)
        (b' := sp - 74#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 24)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 8)
        (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 1) (k := 7)
        (b' := sp - 55#64) rfl (by bv_omega) (by decide),
      memRegion_four (sp - 88#64), memRegion_two (sp - 84#64), memRegion_two (sp - 82#64),
      memRegion_two (sp - 80#64), memRegion_four (sp - 78#64), memRegion_two (sp - 74#64),
      ProofLib.memRegion_eight (sp - 72#64), ProofLib.memRegion_eight (sp - 64#64),
        memRegion_one (sp - 56#64)]

set_option maxHeartbeats 800000 in
theorem identityKey_decode_any_sp2_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr identityKeyDecodeName)
      identityKeyDecodeAnySpec := by
  simp only [identityKeyDecodeAnySpec]
  have htry := pk_try_from_len33_any_ok_at b C ctl abs
    identityKeyDecodeName (k := 212328)
    (by rw [identityKeyDecode_fnOff, libsignalSessionCode_fnOff_0x3ebc0])
  simp only [pkTryFromLen33AnySpec] at htry
  code_fetches_range libsignalSessionCode CryptoVerification.E2E.Bin.identityKeyDecode b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.libsignalSessionCode_fnOff_0xae58 0xae58 0 40
  code_fetches_range libsignalSessionCode CryptoVerification.E2E.Bin.identityKeyDecode b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.libsignalSessionCode_fnOff_0xae58 0xae58 64 108
  dsimp only [tripleRatchetProgAt, identityKeyDecodeName, BitVec.ofNat_eq_ofNat] at htry ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl
    abs))).fnAddr "<libsignal_protocol::identity_key::IdentityKey>::decode" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨ret, keyPtr, ik⟩ := x
  dsimp only at *
  subst ret keyPtr
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
    exists_remoteKeyChunksAny_of_length_32 (List.Vector.toList_length ik.publicKey.bytes)
  rw [memRegion_40_identityKeyDecode_split_any (s0.readReg64 (Reg.gpr 8#5)),
      hchunks (s0.readReg64 (Reg.gpr 8#5) + 8#64),
      remoteKeyChunksAny_ret_8 (s0.readReg64 (Reg.gpr 8#5)),
      stackAt_identityKeyDecode_split_any s0.sp]
  cells_unfold
  wp_pull_exists
  wp_steps
  wp_call htry (s0.sp - 88#64, s0.readReg64 (Reg.gpr 0#5), ik)
  rw [hchunks (s0.sp - 87#64), remoteKeyChunksAny_sp_87 s0.sp]
  wp_steps
  rw [sevenLo_sp_87_any s0.sp]
  wp_steps
  simp only [sepConj_assoc]
  rw [sevenLo_ret_8_any (s0.readReg64 (Reg.gpr 8#5)),
      sp_88_four_bytes_any s0.sp,
      sp_84_split_16_any s0.sp]
  wp_steps
  try rw [truncate16_zeroExtend32]
  try rw [truncate16_zeroExtend32]
  try rw [← sevenLo_ret_8_any (s0.readReg64 (Reg.gpr 8#5))]
  try rw [memRegion_sp_88_40_split_any s0.sp]
  wp_done

/-! ## `inMemIdentityStoreAtP` and `callAtP` Detach Lemmas -/

theorem inMemIdentityStoreAtP_detach {A : RustAlloc} {img : Obj.Image} {mp : BitVec 64}
    {me : Role} {kpBytes : List (BitVec 8)} {regId : BitVec 32} {ik : IdentityKey}
    {m : Memory} {R : SepProp}
    (hm : m ⊨ inMemIdentityStoreAtP A img mp me kpBytes regId (some ik) ∗ R) :
    ∃ (ws : List (BitVec 64)) (H : SepProp),
      ws.length = 15 ∧
      (m ⊨ words64At mp ws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d ws ∗ H ⊢ inMemIdentityStoreAtP A img d me kpBytes regId (some
      ik)) := by
  dsimp only [inMemIdentityStoreAtP] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hkp_len, hm⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k0, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k1, hm⟩ := hm
  have hm1 : m ⊨ (∃∗ idx : Nat, ∃∗ gAddr : AddrGhost,
      ⌜gAddr.val = me.peer.addrVal⌝ ∗
      InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride mp k0 k1 idx
        me.peer.nameBytes 1#8
        (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList)) ∗
      (((mp + 48#64) ↦ₛ kpBytes) ∗ ((mp + 112#64) ↦₃₂ regId) ∗ memRegion (mp + 116#64) 4 ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; obtain ⟨idx, hm1⟩ := hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; obtain ⟨gAddr, hm1⟩ := hm1
  have hm2 : m ⊨ InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride mp k0
    k1 idx me.peer.nameBytes 1#8
      (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList) ∗
      (⌜gAddr.val = me.peer.addrVal⌝ ∗ ((mp + 48#64) ↦ₛ kpBytes) ∗
       ((mp + 112#64) ↦₃₂ regId) ∗ memRegion (mp + 116#64) 4 ∗ R) :=
    Satisfies.of_eq hm1 (by ac_rfl)
  obtain ⟨ws0, H_tbl, hlen0, hm3, htbl⟩ := table4SingleAt_detach hm2
  obtain ⟨ws1, hlen1, hkp_eq⟩ := pointsToBytes_eq_words64At 8 kpBytes hkp_len
  have hm4 : m ⊨ ((mp + 112#64) ↦₃₂ regId) ∗ memRegion (mp + 112#64 + 4#64) 4 ∗
      (words64At mp ws0 ∗ ((mp + 48#64) ↦ₛ kpBytes) ∗ ⌜gAddr.val = me.peer.addrVal⌝ ∗ H_tbl ∗ R) :=
      by
    rw [show mp + 112#64 + 4#64 = mp + 116#64 by bv_lin]
    exact Satisfies.of_eq hm3 (by ac_rfl)
  obtain ⟨w_last, hm5, hw_last⟩ := word32_memRegion4_detach hm4
  have hcomb : ∀ d : BitVec 64,
      words64At d (ws0 ++ (ws1 ++ [w_last])) =
        words64At d ws0 ∗ ((d + 48#64) ↦ₛ kpBytes) ∗ ((d + 112#64) ↦₆₄ w_last) := by
    intro d
    rw [words64At_append ws0 (ws1 ++ [w_last]) d,
        words64At_append ws1 [w_last] (d + BitVec.ofNat 64 (8 * ws0.length)),
        hlen0, hlen1,
        show d + BitVec.ofNat 64 (8 * 6) = d + 48#64 by bv_lin,
        show d + 48#64 + BitVec.ofNat 64 (8 * 8) = d + 112#64 by bv_lin,
        ← hkp_eq (d + 48#64)]
    dsimp only [words64At]
    simp only [sepConj_emp]
  refine ⟨ws0 ++ (ws1 ++ [w_last]), ⌜gAddr.val = me.peer.addrVal⌝ ∗ H_tbl,
    by simp [hlen0, hlen1], ?_, fun d => ?_⟩
  · rw [hcomb mp]
    exact Satisfies.of_eq hm5 (by ac_rfl)
  · dsimp only [inMemIdentityStoreAtP]
    refine Entails.pure_right hkp_len ?_
    refine Entails.sepExists_right k0 (Entails.sepExists_right k1 ?_)
    rw [hcomb d,
        show (words64At d ws0 ∗ ((d + 48#64) ↦ₛ kpBytes) ∗ ((d + 112#64) ↦₆₄ w_last)) ∗
          (⌜gAddr.val = me.peer.addrVal⌝ ∗ H_tbl) =
          ((d + 48#64) ↦ₛ kpBytes) ∗ (((d + 112#64) ↦₆₄ w_last) ∗
          (⌜gAddr.val = me.peer.addrVal⌝ ∗ (words64At d ws0 ∗ H_tbl))) by ac_rfl,
        show ((d + 48#64) ↦ₛ kpBytes) ∗ ((d + 112#64) ↦₃₂ regId) ∗ memRegion (d + 116#64) 4 ∗
          (∃∗ idx : Nat, ∃∗ gAddr : AddrGhost,
            ⌜gAddr.val = me.peer.addrVal⌝ ∗
            InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride d k0 k1 idx
              me.peer.nameBytes 1#8
              (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList)) =
          ((d + 48#64) ↦ₛ kpBytes) ∗
          ((((d + 112#64) ↦₃₂ regId) ∗ memRegion (d + 112#64 + 4#64) 4) ∗
           (∃∗ idx : Nat, ∃∗ gAddr : AddrGhost,
             ⌜gAddr.val = me.peer.addrVal⌝ ∗
             InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride d k0 k1 idx
               me.peer.nameBytes 1#8
               (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList))) by
          rw [show d + 112#64 + 4#64 = d + 116#64 by bv_lin]; ac_rfl]
    refine sepConj_mono_right (sepConj_mono (hw_last (d + 112#64)) ?_)
    refine Entails.sepExists_right idx (Entails.sepExists_right gAddr ?_)
    exact sepConj_mono_right (htbl d)

theorem callAtP_detach {A : RustAlloc} {img : Obj.Image} {ptr : BitVec 64}
    {role : Role} {kpBytes : List (BitVec 8)} {regId : BitVec 32}
    {s : Session (List (BitVec 8))} {m : Memory} {R : SepProp}
    (hm : m ⊨ callAtP A img ptr role kpBytes regId s ∗ R) :
    ∃ (bws : List (BitVec 64)) (H : SepProp),
      bws.length = 29 ∧
      (m ⊨ words64At ptr bws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d bws ∗ H ⊢ callAtP A img d role kpBytes regId s) := by
  dsimp only [callAtP] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gMe, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gPeer, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨peerKey, hm⟩ := hm
  have hm1 : m ⊨ protocolAddressAt A gMe ptr ∗
      (protocolAddressAt A gPeer (ptr + 0x20#64) ∗
       inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some s) ∗
       inMemIdentityStoreAtP A img (ptr + 0x70#64) role kpBytes regId (some peerKey) ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
         s.state.remoteIdentity = some peerKey⌝ ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  obtain ⟨ws0, H0, hlen0, hm2, h0⟩ := protocolAddressAt_detach hm1
  have hm3 : m ⊨ protocolAddressAt A gPeer (ptr + 0x20#64) ∗
      (inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some s) ∗
       inMemIdentityStoreAtP A img (ptr + 0x70#64) role kpBytes regId (some peerKey) ∗
       words64At ptr ws0 ∗ H0 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
         s.state.remoteIdentity = some peerKey⌝ ∗ R) :=
    Satisfies.of_eq hm2 (by ac_rfl)
  obtain ⟨ws1, H1, hlen1, hm4, h1⟩ := protocolAddressAt_detach hm3
  have hm5 : m ⊨ inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some s) ∗
      (inMemIdentityStoreAtP A img (ptr + 0x70#64) role kpBytes regId (some peerKey) ∗
       words64At ptr ws0 ∗ words64At (ptr + 0x20#64) ws1 ∗ H0 ∗ H1 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
         s.state.remoteIdentity = some peerKey⌝ ∗ R) :=
    Satisfies.of_eq hm4 (by ac_rfl)
  obtain ⟨ws2, H2, hlen2, hm6, h2⟩ := inMemSessionStoreAt_detach hm5
  have hm7 : m ⊨ inMemIdentityStoreAtP A img (ptr + 0x70#64) role kpBytes regId (some peerKey) ∗
      (words64At ptr ws0 ∗ words64At (ptr + 0x20#64) ws1 ∗
       words64At (ptr + 0x40#64) ws2 ∗ H0 ∗ H1 ∗ H2 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
         s.state.remoteIdentity = some peerKey⌝ ∗ R) :=
    Satisfies.of_eq hm6 (by ac_rfl)
  obtain ⟨ws3, H3, hlen3, hm8, h3⟩ := inMemIdentityStoreAtP_detach hm7
  have hcomb : ∀ d : BitVec 64,
      words64At d (ws0 ++ (ws1 ++ (ws2 ++ ws3))) =
        words64At d ws0 ∗ words64At (d + 0x20#64) ws1 ∗
        words64At (d + 0x40#64) ws2 ∗ words64At (d + 0x70#64) ws3 := by
    intro d
    rw [words64At_append ws0 (ws1 ++ (ws2 ++ ws3)) d,
        words64At_append ws1 (ws2 ++ ws3) (d + BitVec.ofNat 64 (8 * ws0.length)),
        words64At_append ws2 ws3 (d + BitVec.ofNat 64 (8 * ws0.length) + BitVec.ofNat 64 (8 *
          ws1.length)),
        hlen0, hlen1, hlen2,
        show d + BitVec.ofNat 64 (8 * 4) = d + 0x20#64 by bv_lin,
        show d + 0x20#64 + BitVec.ofNat 64 (8 * 4) = d + 0x40#64 by bv_lin,
        show d + 0x40#64 + BitVec.ofNat 64 (8 * 6) = d + 0x70#64 by bv_lin]
  let H_all : SepProp :=
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
      s.state.remoteIdentity = some peerKey⌝ ∗
    H0 ∗ H1 ∗ H2 ∗ H3
  refine ⟨ws0 ++ (ws1 ++ (ws2 ++ ws3)), H_all, by simp [hlen0, hlen1, hlen2, hlen3], ?_,
    fun d => ?_⟩
  · rw [hcomb ptr]
    exact Satisfies.of_eq hm8 (by dsimp only [H_all]; ac_rfl)
  · dsimp only [callAtP]
    refine Entails.sepExists_right gMe (Entails.sepExists_right gPeer (Entails.sepExists_right
      peerKey ?_))
    rw [hcomb d,
        show (words64At d ws0 ∗ words64At (d + 0x20#64) ws1 ∗
          words64At (d + 0x40#64) ws2 ∗ words64At (d + 0x70#64) ws3) ∗ H_all =
          ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
            gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
            s.state.remoteIdentity = some peerKey⌝ ∗
          (words64At d ws0 ∗ H0) ∗ (words64At (d + 0x20#64) ws1 ∗ H1) ∗
          (words64At (d + 0x40#64) ws2 ∗ H2) ∗ (words64At (d + 0x70#64) ws3 ∗ H3) by
            dsimp only [H_all]; ac_rfl]
    exact sepConj_mono_right (sepConj_mono (h0 d)
      (sepConj_mono (h1 (d + 0x20#64))
        (sepConj_mono (h2 (d + 0x40#64)) (h3 (d + 0x70#64)))))

theorem callAtP_head_word {A : RustAlloc} {img : Obj.Image} {callPtr : BitVec 64}
    {role : Role} {kpBytes : List (BitVec 8)} {regId : BitVec 32}
    {sess : Session (List (BitVec 8))} {m : Memory} {F : SepProp}
    (hm : m ⊨ callAtP A img callPtr role kpBytes regId sess ∗ F) :
    ∃ (w : BitVec 64) (R_call : SepProp),
      (w + 1#64 == 0#64) = false ∧ m ⊨ (callPtr ↦₆₄ w) ∗ (R_call ∗ F) ∧
      ((callPtr ↦₆₄ w) ∗ R_call ⊢ callAtP A img callPtr role kpBytes regId sess) := by
  dsimp only [callAtP] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gMe, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gPeer, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨peerKey, hm⟩ := hm
  let R_me : SepProp :=
    ((callPtr + 8#64) ↦₆₄ gMe.name.ptr) ∗ ((callPtr + 16#64) ↦₆₄ BitVec.ofNat 64
    gMe.name.bytes.length) ∗
    ⌜gMe.name.bytes.length ≤ gMe.name.cap.toNat ∧ gMe.name.cap.toNat < 2 ^ 63 ∧
      gMe.name.ptr ≠ 0#64⌝ ∗
    (if gMe.name.cap = 0#64 then emp
     else A.live gMe.name.ptr gMe.name.cap.toNat 1 ∗ (gMe.name.ptr ↦ₛ gMe.name.bytes) ∗
       memRegion (gMe.name.ptr + BitVec.ofNat 64 gMe.name.bytes.length) (gMe.name.cap.toNat -
         gMe.name.bytes.length)) ∗
    ((callPtr + asm64% addrDeviceOff) ↦₈ gMe.device) ∗
    memRegion (callPtr + asm64% (addrDeviceOff + 1)) (asm% (protocolAddressSize - (addrDeviceOff +
      1)))
  have hvec : protocolAddressAt A gMe callPtr = (callPtr ↦₆₄ gMe.name.cap) ∗ R_me := by
    dsimp only [protocolAddressAt, vecGhostAt, vecU8At, vecHeader, R_me]; ac_rfl
  let R_call : SepProp :=
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
      sess.state.remoteIdentity = some peerKey⌝ ∗ R_me ∗
    protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
    inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer (some sess) ∗
    inMemIdentityStoreAtP A img (callPtr + 0x70#64) role kpBytes regId (some peerKey)
  have hm1 : m ⊨ (callPtr ↦₆₄ gMe.name.cap) ∗ (R_call ∗ F) := by
    rw [hvec] at hm; exact Satisfies.of_eq hm (by dsimp only [R_call]; ac_rfl)
  have hcap : gMe.name.cap.toNat < 2 ^ 63 := by
    have hm2 : m ⊨ ⌜gMe.name.bytes.length ≤ gMe.name.cap.toNat ∧ gMe.name.cap.toNat < 2 ^ 63 ∧
      gMe.name.ptr ≠ 0#64⌝ ∗
      ((callPtr ↦₆₄ gMe.name.cap) ∗ ((callPtr + 8#64) ↦₆₄ gMe.name.ptr) ∗
       ((callPtr + 16#64) ↦₆₄ BitVec.ofNat 64 gMe.name.bytes.length) ∗
       (if gMe.name.cap = 0#64 then emp
        else A.live gMe.name.ptr gMe.name.cap.toNat 1 ∗ (gMe.name.ptr ↦ₛ gMe.name.bytes) ∗
          memRegion (gMe.name.ptr + BitVec.ofNat 64 gMe.name.bytes.length) (gMe.name.cap.toNat -
            gMe.name.bytes.length)) ∗
       ((callPtr + asm64% addrDeviceOff) ↦₈ gMe.device) ∗
       memRegion (callPtr + asm64% (addrDeviceOff + 1)) (asm% (protocolAddressSize - (addrDeviceOff
         + 1))) ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
         sess.state.remoteIdentity = some peerKey⌝ ∗
       protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
       inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer (some sess) ∗
       inMemIdentityStoreAtP A img (callPtr + 0x70#64) role kpBytes regId (some peerKey) ∗ F) :=
      Satisfies.of_eq hm1 (by dsimp only [R_call, R_me]; ac_rfl)
    rw [satisfies_pure_sepConj] at hm2; exact hm2.1.2.1
  refine ⟨gMe.name.cap, R_call, cap_add_one_beq_zero_false hcap, hm1, ?_⟩
  dsimp only [callAtP]
  refine Entails.sepExists_right gMe (Entails.sepExists_right gPeer (Entails.sepExists_right peerKey
    ?_))
  have h1 : (callPtr ↦₆₄ gMe.name.cap) ∗ R_call =
      ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
        gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
        sess.state.remoteIdentity = some peerKey⌝ ∗
      protocolAddressAt A gMe callPtr ∗ protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
      inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer (some sess) ∗
      inMemIdentityStoreAtP A img (callPtr + 0x70#64) role kpBytes regId (some peerKey) := by
    rw [hvec]; dsimp only [R_call]; ac_rfl
  rw [h1]; exact Entails.refl _

/-! ## Empty-State `Call` Layout and `openEmptySpecP` -/

/-- 232-byte `Call` struct at `callPtr` populated by `libsignal_pqxdh_e2e::open` when `state = []`
(`x5 = 0#64`, used by `session_initiate` and `session_recv_prekey`):
- `+0x00`: `me : ProtocolAddress` (32 B, `role.addrVal`)
- `+0x20`: `peer : ProtocolAddress` (32 B, `role.peer.addrVal`)
- `+0x40`: `sessions : InMemSessionStore` (48 B, `none`)
- `+0x70`: `identities : InMemIdentityKeyStore` (120 B, `none`). -/
def callEmptyAtP (A : RustAlloc) (img : Obj.Image) (callPtr : BitVec 64) (role : Role)
    (keyPairBytes : List (BitVec 8)) (regId : BitVec 32) : SepProp :=
  ∃∗ gMe : AddrGhost, ∃∗ gPeer : AddrGhost,
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
    protocolAddressAt A gMe callPtr ∗
    protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
    inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer none ∗
    inMemIdentityStoreAtP A img (callPtr + 0x70#64) role keyPairBytes regId none

def openEmptyResultAtP (A : RustAlloc) (img : Obj.Image) (outPtr : BitVec 64)
    (keyPairBytes : List (BitVec 8)) (regId : BitVec 32) :
    Option Role → SepProp
  | some r => callEmptyAtP A img outPtr r keyPairBytes regId
  | none   => (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (outPtr + 8#64) 224

structure OpenEmptyGhostP where
  outPtr  : BitVec 64
  who     : BitVec 32
  mePtr   : BitVec 64
  meBytes : List (BitVec 8)
  tlsInit : Option (BitVec 64 × BitVec 64)

/-- `libsignal_pqxdh_e2e::open(who, me, &[])` (`0x75f48..0x760fc -> 0x761ec..0x76278`) when `x5 =
0#64`
(empty session state slice, used by `session_initiate` and `session_recv_prekey`). Note `x4` is
never
dereferenced when `x5 = 0#64`. -/
def openEmptySpecP (C : Crypto) (A : RustAlloc) (img : Obj.Image) : Spec OpenEmptyGhostP :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x0 = g.outPtr ∧ s.readReg32 .x1 = g.who ∧
          s.readReg64 .x2 = g.mePtr ∧ s.readReg64 .x3 = 36#64 ∧
          g.meBytes.length = 36 ∧
          s.readReg64 .x5 = 0#64 ∧
          s.spAligned = true ∧ openPqxdhStack ≤ s.sp.toNat ∧
          ExecOnlyIn (Program.ofImage img) s.mem⌝ ∗
        memRegion g.outPtr 232 ∗ (g.mePtr ↦ₛ g.meBytes) ∗
        logOff img ∗ tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗ A.pool ∗
          stackAt s.sp openPqxdhStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          openEmptyResultAtP A img g.outPtr (meKeyPairBytes C.pubKey g.meBytes) (meRegId g.meBytes)
            (Role.ofWho g.who) ∗
          (g.mePtr ↦ₛ g.meBytes) ∗
          logOff img ∗ (∃∗ tlsFinal, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsFinal) ∗
          A.pool ∗ stackAt s0.sp openPqxdhStack ∗ anyHeap
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

theorem emptyHashMapAt_eq_words64At (ctrlPtr out k0 k1 : BitVec 64) :
    emptyHashMapAt ctrlPtr out k0 k1 = words64At out [ctrlPtr, 0#64, 0#64, 0#64, k0, k1] := by
  unfold emptyHashMapAt StoreNew.emptyHashMapAt StoreNew.emptyRawTableAt StoreNew.randomStateAt
  dsimp only [words64At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  ac_rfl

theorem inMemIdentityStoreEmptyAtP_detach {A : RustAlloc} {img : Obj.Image} {mp : BitVec 64}
    {me : Role} {kpBytes : List (BitVec 8)} {regId : BitVec 32}
    {m : Memory} {R : SepProp}
    (hm : m ⊨ inMemIdentityStoreAtP A img mp me kpBytes regId none ∗ R) :
    ∃ (ws : List (BitVec 64)) (H : SepProp),
      ws.length = 15 ∧
      (m ⊨ words64At mp ws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d ws ∗ H ⊢ inMemIdentityStoreAtP A img d me kpBytes regId none)
      := by
  dsimp only [inMemIdentityStoreAtP] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hkp_len, hm⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k0, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k1, hm⟩ := hm
  let ws0 : List (BitVec 64) := [img.base + emptyCtrlOff, 0#64, 0#64, 0#64, k0, k1]
  have hlen0 : ws0.length = 6 := rfl
  obtain ⟨ws1, hlen1, hkp_eq⟩ := pointsToBytes_eq_words64At 8 kpBytes hkp_len
  have hm3 : m ⊨ ((mp + 112#64) ↦₃₂ regId) ∗ memRegion (mp + 112#64 + 4#64) 4 ∗
      (words64At mp ws0 ∗ ((mp + 48#64) ↦ₛ kpBytes) ∗ R) := by
    rw [show mp + 112#64 + 4#64 = mp + 116#64 by bv_lin,
        ← emptyHashMapAt_eq_words64At (img.base + emptyCtrlOff) mp k0 k1]
    exact Satisfies.of_eq hm (by ac_rfl)
  obtain ⟨w_last, hm5, hw_last⟩ := word32_memRegion4_detach hm3
  have hcomb : ∀ d : BitVec 64,
      words64At d (ws0 ++ (ws1 ++ [w_last])) =
        words64At d ws0 ∗ ((d + 48#64) ↦ₛ kpBytes) ∗ ((d + 112#64) ↦₆₄ w_last) := by
    intro d
    rw [words64At_append ws0 (ws1 ++ [w_last]) d,
        words64At_append ws1 [w_last] (d + BitVec.ofNat 64 (8 * ws0.length)),
        hlen0, hlen1,
        show d + BitVec.ofNat 64 (8 * 6) = d + 48#64 by bv_lin,
        show d + 48#64 + BitVec.ofNat 64 (8 * 8) = d + 112#64 by bv_lin,
        ← hkp_eq (d + 48#64)]
    dsimp only [words64At]
    simp only [sepConj_emp]
  refine ⟨ws0 ++ (ws1 ++ [w_last]), emp, by simp [hlen0, hlen1], ?_, fun d => ?_⟩
  · rw [hcomb mp]
    exact Satisfies.of_eq hm5 (by ac_rfl)
  · dsimp only [inMemIdentityStoreAtP]
    refine Entails.pure_right hkp_len ?_
    refine Entails.sepExists_right k0 (Entails.sepExists_right k1 ?_)
    rw [sepConj_emp, hcomb d,
        ← emptyHashMapAt_eq_words64At (img.base + emptyCtrlOff) d k0 k1,
        show (emptyHashMapAt (img.base + emptyCtrlOff) d k0 k1 ∗ ((d + 48#64) ↦ₛ kpBytes) ∗
          ((d + 112#64) ↦₆₄ w_last)) =
          ((d + 48#64) ↦ₛ kpBytes) ∗ (((d + 112#64) ↦₆₄ w_last) ∗
          emptyHashMapAt (img.base + emptyCtrlOff) d k0 k1) by ac_rfl,
        show ((d + 48#64) ↦ₛ kpBytes) ∗ ((d + 112#64) ↦₃₂ regId) ∗ memRegion (d + 116#64) 4 ∗
          emptyHashMapAt (img.base + emptyCtrlOff) d k0 k1 =
          ((d + 48#64) ↦ₛ kpBytes) ∗
          ((((d + 112#64) ↦₃₂ regId) ∗ memRegion (d + 112#64 + 4#64) 4) ∗
           emptyHashMapAt (img.base + emptyCtrlOff) d k0 k1) by
          rw [show d + 112#64 + 4#64 = d + 116#64 by bv_lin]; ac_rfl]
    exact sepConj_mono_right (sepConj_mono_left (hw_last (d + 112#64)))

theorem inMemSessionStoreEmptyAt_detach {A : RustAlloc} {img : Obj.Image} {mp : BitVec 64}
    {peer : Role} {m : Memory} {R : SepProp}
    (hm : m ⊨ inMemSessionStoreAt A img mp peer none ∗ R) :
    ∃ (bws : List (BitVec 64)) (H : SepProp),
      bws.length = 6 ∧
      (m ⊨ words64At mp bws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d bws ∗ H ⊢ inMemSessionStoreAt A img d peer none) := by
  dsimp only [inMemSessionStoreAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k0, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨k1, hm⟩ := hm
  refine ⟨[img.base + emptyCtrlOff, 0#64, 0#64, 0#64, k0, k1], emp, rfl, ?_, fun d => ?_⟩
  · rw [emptyHashMapAt_eq_words64At (img.base + emptyCtrlOff) mp k0 k1] at hm
    exact Satisfies.of_eq hm (by ac_rfl)
  · dsimp only [inMemSessionStoreAt]
    refine Entails.sepExists_right k0 (Entails.sepExists_right k1 ?_)
    rw [sepConj_emp, emptyHashMapAt_eq_words64At (img.base + emptyCtrlOff) d k0 k1]
    exact Entails.refl _

theorem callEmptyAtP_detach {A : RustAlloc} {img : Obj.Image} {ptr : BitVec 64}
    {role : Role} {kpBytes : List (BitVec 8)} {regId : BitVec 32}
    {m : Memory} {R : SepProp}
    (hm : m ⊨ callEmptyAtP A img ptr role kpBytes regId ∗ R) :
    ∃ (bws : List (BitVec 64)) (H : SepProp),
      bws.length = 29 ∧
      (m ⊨ words64At ptr bws ∗ H ∗ R) ∧
      (∀ d : BitVec 64, words64At d bws ∗ H ⊢ callEmptyAtP A img d role kpBytes regId) := by
  dsimp only [callEmptyAtP] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gMe, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gPeer, hm⟩ := hm
  have hm1 : m ⊨ protocolAddressAt A gMe ptr ∗
      (protocolAddressAt A gPeer (ptr + 0x20#64) ∗
       inMemSessionStoreAt A img (ptr + 0x40#64) role.peer none ∗
       inMemIdentityStoreAtP A img (ptr + 0x70#64) role kpBytes regId none ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  obtain ⟨ws0, H0, hlen0, hm2, h0⟩ := protocolAddressAt_detach hm1
  have hm3 : m ⊨ protocolAddressAt A gPeer (ptr + 0x20#64) ∗
      (inMemSessionStoreAt A img (ptr + 0x40#64) role.peer none ∗
       inMemIdentityStoreAtP A img (ptr + 0x70#64) role kpBytes regId none ∗
       words64At ptr ws0 ∗ H0 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R) :=
    Satisfies.of_eq hm2 (by ac_rfl)
  obtain ⟨ws1, H1, hlen1, hm4, h1⟩ := protocolAddressAt_detach hm3
  have hm5 : m ⊨ inMemSessionStoreAt A img (ptr + 0x40#64) role.peer none ∗
      (inMemIdentityStoreAtP A img (ptr + 0x70#64) role kpBytes regId none ∗
       words64At ptr ws0 ∗ words64At (ptr + 0x20#64) ws1 ∗ H0 ∗ H1 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R) :=
    Satisfies.of_eq hm4 (by ac_rfl)
  obtain ⟨ws2, H2, hlen2, hm6, h2⟩ := inMemSessionStoreEmptyAt_detach hm5
  have hm7 : m ⊨ inMemIdentityStoreAtP A img (ptr + 0x70#64) role kpBytes regId none ∗
      (words64At ptr ws0 ∗ words64At (ptr + 0x20#64) ws1 ∗
       words64At (ptr + 0x40#64) ws2 ∗ H0 ∗ H1 ∗ H2 ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R) :=
    Satisfies.of_eq hm6 (by ac_rfl)
  obtain ⟨ws3, H3, hlen3, hm8, h3⟩ := inMemIdentityStoreEmptyAtP_detach hm7
  have hcomb : ∀ d : BitVec 64,
      words64At d (ws0 ++ (ws1 ++ (ws2 ++ ws3))) =
        words64At d ws0 ∗ words64At (d + 0x20#64) ws1 ∗
        words64At (d + 0x40#64) ws2 ∗ words64At (d + 0x70#64) ws3 := by
    intro d
    rw [words64At_append ws0 (ws1 ++ (ws2 ++ ws3)) d,
        words64At_append ws1 (ws2 ++ ws3) (d + BitVec.ofNat 64 (8 * ws0.length)),
        words64At_append ws2 ws3 (d + BitVec.ofNat 64 (8 * ws0.length) + BitVec.ofNat 64 (8 *
          ws1.length)),
        hlen0, hlen1, hlen2,
        show d + BitVec.ofNat 64 (8 * 4) = d + 0x20#64 by bv_lin,
        show d + 0x20#64 + BitVec.ofNat 64 (8 * 4) = d + 0x40#64 by bv_lin,
        show d + 0x40#64 + BitVec.ofNat 64 (8 * 6) = d + 0x70#64 by bv_lin]
  let H_all : SepProp :=
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
    H0 ∗ H1 ∗ H2 ∗ H3
  refine ⟨ws0 ++ (ws1 ++ (ws2 ++ ws3)), H_all, by simp [hlen0, hlen1, hlen2, hlen3], ?_,
    fun d => ?_⟩
  · rw [hcomb ptr]
    exact Satisfies.of_eq hm8 (by dsimp only [H_all]; ac_rfl)
  · dsimp only [callEmptyAtP]
    refine Entails.sepExists_right gMe (Entails.sepExists_right gPeer ?_)
    rw [hcomb d,
        show (words64At d ws0 ∗ words64At (d + 0x20#64) ws1 ∗
          words64At (d + 0x40#64) ws2 ∗ words64At (d + 0x70#64) ws3) ∗ H_all =
          ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
            gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
          (words64At d ws0 ∗ H0) ∗ (words64At (d + 0x20#64) ws1 ∗ H1) ∗
          (words64At (d + 0x40#64) ws2 ∗ H2) ∗ (words64At (d + 0x70#64) ws3 ∗ H3) by
            dsimp only [H_all]; ac_rfl]
    exact sepConj_mono_right (sepConj_mono (h0 d)
      (sepConj_mono (h1 (d + 0x20#64))
        (sepConj_mono (h2 (d + 0x40#64)) (h3 (d + 0x70#64)))))

theorem callEmptyAtP_head_word {A : RustAlloc} {img : Obj.Image} {callPtr : BitVec 64}
    {role : Role} {kpBytes : List (BitVec 8)} {regId : BitVec 32}
    {m : Memory} {F : SepProp}
    (hm : m ⊨ callEmptyAtP A img callPtr role kpBytes regId ∗ F) :
    ∃ (w : BitVec 64) (R_call : SepProp),
      (w + 1#64 == 0#64) = false ∧ m ⊨ (callPtr ↦₆₄ w) ∗ (R_call ∗ F) ∧
      ((callPtr ↦₆₄ w) ∗ R_call ⊢ callEmptyAtP A img callPtr role kpBytes regId) := by
  dsimp only [callEmptyAtP] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gMe, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; obtain ⟨gPeer, hm⟩ := hm
  let R_me : SepProp :=
    ((callPtr + 8#64) ↦₆₄ gMe.name.ptr) ∗ ((callPtr + 16#64) ↦₆₄ BitVec.ofNat 64
    gMe.name.bytes.length) ∗
    ⌜gMe.name.bytes.length ≤ gMe.name.cap.toNat ∧ gMe.name.cap.toNat < 2 ^ 63 ∧
      gMe.name.ptr ≠ 0#64⌝ ∗
    (if gMe.name.cap = 0#64 then emp
     else A.live gMe.name.ptr gMe.name.cap.toNat 1 ∗ (gMe.name.ptr ↦ₛ gMe.name.bytes) ∗
       memRegion (gMe.name.ptr + BitVec.ofNat 64 gMe.name.bytes.length) (gMe.name.cap.toNat -
         gMe.name.bytes.length)) ∗
    ((callPtr + asm64% addrDeviceOff) ↦₈ gMe.device) ∗
    memRegion (callPtr + asm64% (addrDeviceOff + 1)) (asm% (protocolAddressSize - (addrDeviceOff +
      1)))
  have hvec : protocolAddressAt A gMe callPtr = (callPtr ↦₆₄ gMe.name.cap) ∗ R_me := by
    dsimp only [protocolAddressAt, vecGhostAt, vecU8At, vecHeader, R_me]; ac_rfl
  let R_call : SepProp :=
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗ R_me ∗
    protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
    inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer none ∗
    inMemIdentityStoreAtP A img (callPtr + 0x70#64) role kpBytes regId none
  have hm1 : m ⊨ (callPtr ↦₆₄ gMe.name.cap) ∗ (R_call ∗ F) := by
    rw [hvec] at hm; exact Satisfies.of_eq hm (by dsimp only [R_call]; ac_rfl)
  have hcap : gMe.name.cap.toNat < 2 ^ 63 := by
    have hm2 : m ⊨ ⌜gMe.name.bytes.length ≤ gMe.name.cap.toNat ∧ gMe.name.cap.toNat < 2 ^ 63 ∧
      gMe.name.ptr ≠ 0#64⌝ ∗
      ((callPtr ↦₆₄ gMe.name.cap) ∗ ((callPtr + 8#64) ↦₆₄ gMe.name.ptr) ∗
       ((callPtr + 16#64) ↦₆₄ BitVec.ofNat 64 gMe.name.bytes.length) ∗
       (if gMe.name.cap = 0#64 then emp
        else A.live gMe.name.ptr gMe.name.cap.toNat 1 ∗ (gMe.name.ptr ↦ₛ gMe.name.bytes) ∗
          memRegion (gMe.name.ptr + BitVec.ofNat 64 gMe.name.bytes.length) (gMe.name.cap.toNat -
            gMe.name.bytes.length)) ∗
       ((callPtr + asm64% addrDeviceOff) ↦₈ gMe.device) ∗
       memRegion (callPtr + asm64% (addrDeviceOff + 1)) (asm% (protocolAddressSize - (addrDeviceOff
         + 1))) ∗
       ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
         gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
       protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
       inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer none ∗
       inMemIdentityStoreAtP A img (callPtr + 0x70#64) role kpBytes regId none ∗ F) :=
      Satisfies.of_eq hm1 (by dsimp only [R_call, R_me]; ac_rfl)
    rw [satisfies_pure_sepConj] at hm2; exact hm2.1.2.1
  refine ⟨gMe.name.cap, R_call, cap_add_one_beq_zero_false hcap, hm1, ?_⟩
  dsimp only [callEmptyAtP]
  refine Entails.sepExists_right gMe (Entails.sepExists_right gPeer ?_)
  have h1 : (callPtr ↦₆₄ gMe.name.cap) ∗ R_call =
      ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
        gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
      protocolAddressAt A gMe callPtr ∗ protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
      inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer none ∗
      inMemIdentityStoreAtP A img (callPtr + 0x70#64) role kpBytes regId none := by
    rw [hvec]; dsimp only [R_call]; ac_rfl
  rw [h1]; exact Entails.refl _

/-! ## Saved Registers and Seam Predicate for `libsignal_pqxdh_e2e::open` (`0x75f48`) -/

/-- Callee-saved registers `x19..x26, x28..x29` and link register `x30` spilled at the top of
`libsignal_pqxdh_e2e::open`'s `0x4b0`-byte stack frame (`s0.sp - 0x60#64 .. s0.sp`,
with unused 8-byte slot at `s0.sp - 0x48#64` since `x27` is untouched). -/
def openPqxdhSavedRegsAt (s0 : State) : SepProp :=
  ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x28) ∗ (∃∗ d27 : BitVec 64, (s0.sp - 0x48#64) ↦₆₄ d27) ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

theorem openPqxdhSavedRegsAt_entails_cells (s0 : State) :
    Entails (openPqxdhSavedRegsAt s0) (cells (s0.sp - 0x60#64) 12) := by
  dsimp only [openPqxdhSavedRegsAt]
  apply cells_sub_succ_entails 96 12
  apply cells_sub_succ_entails 88 11
  apply cells_sub_succ_entails 80 10
  rw [ProofLib.cells_sub_succ s0.sp 72 9 (by decide) (by decide), ← sepExists_sepConj_left]
  refine sepConj_mono_right ?_
  apply cells_sub_succ_entails 64 8
  apply cells_sub_succ_entails 56 7
  apply cells_sub_succ_entails 48 6
  apply cells_sub_succ_entails 40 5
  apply cells_sub_succ_entails 32 4
  apply cells_sub_succ_entails 24 3
  apply cells_sub_succ_entails 16 2
  rw [ProofLib.cells_sub_succ s0.sp 8 1 (by decide) (by decide), ProofLib.cells_zero]
  exact Entails.sepExists_right _ (by rw [sepConj_emp]; exact Entails.refl _)

/-- Per-seam live register and stack-slot layout (`s.sp .. s.sp + 0x450#64`) for
`libsignal_pqxdh_e2e::open` (`0x75f48`). -/
def openSeamSlotsP (C : Crypto) (A : RustAlloc) (img : Obj.Image) (off : BitVec 64)
    (g : OpenGhostP) (role : Role) (s : State) : SepProp :=
  if off = 0x0bc#64 then
    ⌜(s.readReg64 .x20).toNat = g.stateBytes.length ∧
      s.readReg64 .x21 = g.statePtr ∧
      s.readReg64 .x22 = g.mePtr⌝ ∗
      (∃∗ meBuf : BitVec 64, ∃∗ peerBuf : BitVec 64,
        ⌜s.readReg64 .x23 = meBuf ∧ s.readReg64 .x0 = peerBuf ∧
          meBuf ≠ 0#64 ∧ peerBuf ≠ 0#64⌝ ∗
          (meBuf ↦ₛ role.nameBytes) ∗ A.live meBuf 36 1 ∗
          (peerBuf ↦ₛ role.peer.nameBytes) ∗ A.live peerBuf 36 1) ∗
      memRegion s.sp 0x450
  else if off = 0x1bc#64 then
    ⌜(s.readReg64 .x20).toNat = g.stateBytes.length ∧
      s.readReg64 .x21 = g.statePtr ∧
      s.readReg64 .x24 = s.sp + 0x008#64 ∧
      s.readReg64 .x25 = s.sp + 0x260#64⌝ ∗
      memRegion s.sp 8 ∗
      (∃∗ gMe : AddrGhost, ∃∗ gPeer : AddrGhost,
        ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal⌝ ∗
          protocolAddressAt A gMe (s.sp + 0x008#64) ∗
          protocolAddressAt A gPeer (s.sp + 0x028#64)) ∗
      inMemSessionStoreAt A img (s.sp + 0x048#64) role.peer none ∗
      inMemIdentityStoreAtP A img (s.sp + 0x078#64) role
        (meKeyPairBytes C.pubKey g.meBytes) (meRegId g.meBytes) none ∗
      memRegion (s.sp + 0x0f0#64) 0x360
  else
    ⌜s.readReg64 .x24 = s.sp + 0x008#64 ∧
      s.readReg64 .x25 = s.sp + 0x260#64 ∧
      s.readReg64 .x0 = s.sp + 0x078#64 ∧
      s.readReg64 .x1 = s.sp + 0x028#64 ∧
      s.readReg64 .x2 = s.sp + 0x3d0#64⌝ ∗
      memRegion s.sp 8 ∗
      (∃∗ gMe : AddrGhost, ∃∗ gPeer : AddrGhost,
        ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal⌝ ∗
          protocolAddressAt A gMe (s.sp + 0x008#64) ∗
          protocolAddressAt A gPeer (s.sp + 0x028#64)) ∗
      inMemSessionStoreAt A img (s.sp + 0x048#64) role.peer none ∗
      inMemIdentityStoreAtP A img (s.sp + 0x078#64) role
        (meKeyPairBytes C.pubKey g.meBytes) (meRegId g.meBytes) none ∗
      (∃∗ G, ⌜BinCanonSession G g.sess⌝ ∗
        sessionRecordAt A (s.sp + 0x0f0#64) ⟨0#64, 8#64, some G⟩ ⟨some g.sess⟩) ∗
      memRegion (s.sp + 0x260#64) 0x170 ∗
      (∃∗ peerKey : IdentityKey, ⌜g.sess.state.remoteIdentity = some peerKey⌝ ∗
        ((s.sp + 0x3d0#64) ↦ₛ peerKey.publicKey.bytes.toList)) ∗
      memRegion (s.sp + 0x3f0#64) 0x60

def OpenSeamP (C : Crypto) (A : RustAlloc) (img : Obj.Image) (off : BitVec 64)
    (g : OpenGhostP) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = img.base + openPqxdhOff + off ∧ s.status = .Running ∧ s.spAligned = true ∧
    s0.spAligned = true ∧ openPqxdhStack ≤ s0.sp.toNat ∧
    s.sp = s0.sp - 0x4b0#64 ∧
    (off.toNat ≤ 0x1bc → s.tpidrEl0 = s0.tpidrEl0 ∧ ExecOnlyIn (Program.ofImage img) s.mem) ∧
    s.trace = s0.trace ∧
    s.readReg64 .x29 = s0.sp - 0x60#64 ∧ s.readReg64 .x19 = g.outPtr ∧
    s.readReg64 .x27 = s0.readReg64 .x27 ∧
    g.meBytes.length = 36 ∧ g.stateBytes.length < 2 ^ 63 ∧
    RecordCanonical g.stateBytes g.sess ∧ g.sess.state.remoteIdentity.isSome ∧
    img.FrozenLoaded s ∧
    ∃ role, Role.ofWho g.who = some role ∧
      (s.mem ⊨ (g.mePtr ↦ₛ g.meBytes) ∗ (g.statePtr ↦ₛ g.stateBytes) ∗
        (∃∗ tlsCur, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsCur) ∗
        A.pool ∗ memRegion (s0.sp - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗
        openSeamSlotsP C A img off g role s ∗ openPqxdhSavedRegsAt s0 ∗
        memRegion g.outPtr 232 ∗ R ∗ anyHeap)

end CryptoVerification.E2E.Pqxdh.WireEntries
