/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackDefs

/-!
# Segment 7 Helpers for `try_decrypt_with_state::<HookRng>`

Separation-logic framing and MAC-verification helpers for `S7Spec` (`+0x63c → +0x678 / +0x30c`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-! ## Segment 7 (`+0x63c → +0x678 / +0x30c`) -/

def trRestAt (A : RustAlloc) (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
    ratchetAt A t G.ratchet tr.ratchet ∗
    vecU8At A (t + 0xb0#64) G.pq.cap G.pq.ptr tr.pqrState

theorem trAt_eq_rest (A : RustAlloc) (sp : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp - 1504#64 + 0x38#64) G tr =
      (trRestAt A (sp - 1448#64) G tr ∗
       ((sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) := by
  unfold trAt trRestAt
  rw [show sp - 1504#64 + 0x38#64 = sp - 1448#64 by bv_omega,
      show sp - 1448#64 + 0xc8#64 = sp - 1248#64 by bv_omega,
      show sp - 1448#64 + 0xe8#64 = sp - 1216#64 by bv_omega]
  ac_rfl

theorem s7_scr_split (sp : BitVec 64) :
    memRegion (sp + 0x140#64) 0x3c0 =
      (memRegion (sp + 0x140#64) 40 ∗
       memRegion (sp + 0x168#64) 8 ∗
       memRegion (sp + 0x170#64) 8 ∗
       memRegion (sp + 0x178#64) 8 ∗
       memRegion (sp + 0x180#64) 1 ∗
       memRegion (sp + 0x181#64) 15 ∗
       memRegion (sp + 0x190#64) 9 ∗
       memRegion (sp + 0x199#64) 871) := by
  rw [show (0x3c0 : Nat) = 40 + (8 + (8 + (8 + (1 + (15 + (9 + 871)))))) by decide,
      memRegion_split (sp + 0x140#64) 40 _ (by decide),
      show sp + 0x140#64 + BitVec.ofNat 64 40 = sp + 0x168#64 by bv_omega,
      memRegion_split (sp + 0x168#64) 8 _ (by decide),
      show sp + 0x168#64 + BitVec.ofNat 64 8 = sp + 0x170#64 by bv_omega,
      memRegion_split (sp + 0x170#64) 8 _ (by decide),
      show sp + 0x170#64 + BitVec.ofNat 64 8 = sp + 0x178#64 by bv_omega,
      memRegion_split (sp + 0x178#64) 8 _ (by decide),
      show sp + 0x178#64 + BitVec.ofNat 64 8 = sp + 0x180#64 by bv_omega,
      memRegion_split (sp + 0x180#64) 1 _ (by decide),
      show sp + 0x180#64 + BitVec.ofNat 64 1 = sp + 0x181#64 by bv_omega,
      memRegion_split (sp + 0x181#64) 15 _ (by decide),
      show sp + 0x181#64 + BitVec.ofNat 64 15 = sp + 0x190#64 by bv_omega,
      memRegion_split (sp + 0x190#64) 9 871 (by decide),
      show sp + 0x190#64 + BitVec.ofNat 64 9 = sp + 0x199#64 by bv_omega]

theorem verifyMacResultAt_entails_memRegion (r : BitVec 64) (ok : Bool) :
    verifyMacResultAt r ok ⊢ memRegion r 9 := by
  unfold verifyMacResultAt
  rw [show (9 : Nat) = 8 + 1 by decide, memRegion_split r 8 1 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)

theorem verifyMacResultAt_parts_entails_memRegion (r : BitVec 64) (v0 : BitVec 64) (v8 : BitVec 8) :
    (r ↦₆₄ v0) ∗ ((r + 8#64) ↦₈ v8) ⊢ memRegion r 9 := by
  rw [show (9 : Nat) = 8 + 1 by decide, memRegion_split r 8 1 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)

theorem stackAt_vmac_split_alloc (sp : BitVec 64) :
    stackAt sp verifyMacWithAddressesStack =
      memRegion (sp - 4912#64) 816 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp 4096 816 (by decide)

theorem errTail_reg190_s7_split (sp : BitVec 64) :
    memRegion (sp - 1504#64 + 0x190#64) 0x3f0 =
      (memRegion (sp - 1104#64) 9 ∗ memRegion (sp - 1095#64) 871 ∗
       memRegion (sp - 1504#64 + 0x500#64) 0x54 ∗
       memRegion (sp - 1504#64 + 0x554#64) 0x2c) := by
  rw [show sp - 1504#64 + 0x190#64 = sp - 1104#64 by bv_omega,
      show (0x3f0 : Nat) = 9 + (871 + (0x54 + 0x2c)) by decide,
      memRegion_split (sp - 1104#64) 9 _ (by decide),
      show sp - 1104#64 + BitVec.ofNat 64 9 = sp - 1095#64 by bv_omega,
      memRegion_split (sp - 1095#64) 871 _ (by decide),
      show sp - 1095#64 + BitVec.ofNat 64 871 = sp - 1504#64 + 0x500#64 by bv_omega,
      memRegion_split (sp - 1504#64 + 0x500#64) 0x54 0x2c (by decide),
      show sp - 1504#64 + 0x500#64 + BitVec.ofNat 64 0x54 = sp - 1504#64 + 0x554#64 by bv_omega]

theorem errTail_sp_s7_entails_memRegion (sp : BitVec 64)
    (newPqrCap locA newPqrPtr remA : BitVec 64) (msgW : BitVec 32) :
    ((sp - 1496#64) ↦₆₄ newPqrCap) ∗
    ((sp - 1476#64) ↦₃₂ msgW) ∗
    ((sp - 1472#64) ↦₆₄ locA) ∗
    ((sp - 1464#64) ↦₆₄ newPqrPtr) ∗
    ((sp - 1456#64) ↦₆₄ remA) ⊢
    memRegion (sp - 1496#64) 8 ∗
    memRegion (sp - 1476#64) 4 ∗
    memRegion (sp - 1472#64) 8 ∗
    memRegion (sp - 1464#64) 8 ∗
    memRegion (sp - 1456#64) 8 :=
  sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _))))

abbrev macFailedBytes : List (BitVec 8) :=
  [0x4d#8, 0x41#8, 0x43#8, 0x20#8, 0x76#8, 0x65#8, 0x72#8, 0x69#8,
   0x66#8, 0x69#8, 0x63#8, 0x61#8, 0x74#8, 0x69#8, 0x6f#8, 0x6e#8,
   0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8, 0x64#8]

theorem macFailedStr_eq_bytes : macFailedStr = macFailedBytes := by
  decide +kernel

theorem rodata_macFailed_split1 (a : BitVec 64) :
    (a ↦ᵣ macFailedBytes) =
      ((a ↦₆₄ᵣ 0x697265762043414d#64) ∗
       ((a + 8#64) ↦₆₄ᵣ 0x6e6f697461636966#64) ∗
       ((a + 16#64) ↦ᵣ (macFailedBytes.drop 16))) := by
  rw [show macFailedBytes =
        unpack64 0x697265762043414d#64 ++
        (unpack64 0x6e6f697461636966#64 ++ macFailedBytes.drop 16) by decide,
      pointsToBytesRO_append, ← pointsTo64RO_eq_pointsToBytesRO,
      unpack64_length,
      pointsToBytesRO_append, ← pointsTo64RO_eq_pointsToBytesRO,
      unpack64_length,
      show a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 by bv_omega]
  rfl

theorem rodata_macFailed_split2 (a : BitVec 64) :
    (a ↦ᵣ macFailedBytes) =
      ((a ↦₆₄ᵣ 0x697265762043414d#64) ∗
       ((a + 8#64) ↦ᵣ (unpack64 0x6e6f697461636966#64).take 7) ∗
       ((a + 15#64) ↦₆₄ᵣ 0x64656c696166206e#64)) := by
  rw [show macFailedBytes =
        unpack64 0x697265762043414d#64 ++
        ((unpack64 0x6e6f697461636966#64).take 7 ++ unpack64 0x64656c696166206e#64) by decide,
      pointsToBytesRO_append, ← pointsTo64RO_eq_pointsToBytesRO,
      unpack64_length,
      pointsToBytesRO_append, ← pointsTo64RO_eq_pointsToBytesRO,
      show a + BitVec.ofNat 64 8 + BitVec.ofNat 64 ((unpack64 0x6e6f697461636966#64).take 7).length
        = a + 15#64 by
        rw [show ((unpack64 0x6e6f697461636966#64).take 7).length = 7 by decide]; bv_omega]

theorem rodata_macFailed_1_to_2 (a : BitVec 64) (R : SepProp) :
    (a ↦₆₄ᵣ 0x697265762043414d#64) ∗
    (((a + 8#64) ↦₆₄ᵣ 0x6e6f697461636966#64) ∗
     (((a + 16#64) ↦ᵣ (macFailedBytes.drop 16)) ∗ R)) =
    ((a ↦₆₄ᵣ 0x697265762043414d#64) ∗
     (((a + 8#64) ↦ᵣ (unpack64 0x6e6f697461636966#64).take 7) ∗
      (((a + 15#64) ↦₆₄ᵣ 0x64656c696166206e#64) ∗ R))) := by
  rw [← sepConj_assoc, ← sepConj_assoc, sepConj_assoc (a ↦₆₄ᵣ 0x697265762043414d#64),
      ← rodata_macFailed_split1, rodata_macFailed_split2, sepConj_assoc, sepConj_assoc]

theorem rodata_macFailed_2_back (a : BitVec 64) (R : SepProp) :
    (a ↦₆₄ᵣ 0x697265762043414d#64) ∗
    (((a + 8#64) ↦ᵣ (unpack64 0x6e6f697461636966#64).take 7) ∗
     (((a + 15#64) ↦₆₄ᵣ 0x64656c696166206e#64) ∗ R)) =
    (a ↦ᵣ macFailedBytes) ∗ R := by
  rw [← sepConj_assoc, ← sepConj_assoc, sepConj_assoc (a ↦₆₄ᵣ 0x697265762043414d#64),
      ← rodata_macFailed_split2]

theorem macFailed_alloc_split (p : BitVec 64) :
    memRegion p 23 = (memRegion p 8 ∗ memRegion (p + 8#64) 8 ∗ memRegion (p + 16#64) 7) := by
  rw [show (23 : Nat) = 8 + (8 + 7) by decide,
      memRegion_split p 8 (8 + 7) (by decide),
      show p + BitVec.ofNat 64 8 = p + 8#64 by bv_omega,
      memRegion_split (p + 8#64) 8 7 (by decide),
      show p + 8#64 + BitVec.ofNat 64 8 = p + 16#64 by bv_omega]

theorem macFailed_overlap_prep (p : BitVec 64) :
    ((p + 8#64) ↦₆₄ 0x6e6f697461636966#64) ∗ memRegion (p + 16#64) 7 ⊢
      ((p + 8#64) ↦ₛ (unpack64 0x6e6f697461636966#64).take 7) ∗ memRegion (p + 15#64) 8 := by
  rw [pointsTo64_eq_pointsToBytes,
      show unpack64 0x6e6f697461636966#64 =
        (unpack64 0x6e6f697461636966#64).take 7 ++
        (unpack64 0x6e6f697461636966#64).drop 7 by exact (List.take_append_drop 7 _).symm,
      pointsToBytes_append,
      show p + 8#64 + BitVec.ofNat 64 ((unpack64 0x6e6f697461636966#64).take 7).length
        = p + 15#64 by
        rw [show ((unpack64 0x6e6f697461636966#64).take 7).length = 7 by decide]; bv_omega,
      sepConj_assoc]
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion _ _)) ?_
  rw [show ((unpack64 0x6e6f697461636966#64).drop 7).length = 1 by decide,
      show (8 : Nat) = 1 + 7 by decide,
      memRegion_split (p + 15#64) 1 7 (by decide),
      show p + 15#64 + BitVec.ofNat 64 1 = p + 16#64 by bv_omega]
  exact Entails.refl _

theorem macFailed_bytes_assemble (p : BitVec 64) :
    (p ↦₆₄ 0x697265762043414d#64) ∗
    ((p + 8#64) ↦ₛ (unpack64 0x6e6f697461636966#64).take 7) ∗
    ((p + 15#64) ↦₆₄ 0x64656c696166206e#64) =
      (p ↦ₛ macFailedStr) := by
  rw [macFailedStr_eq_bytes,
      show macFailedBytes =
        unpack64 0x697265762043414d#64 ++
        ((unpack64 0x6e6f697461636966#64).take 7 ++ unpack64 0x64656c696166206e#64) by decide,
      pointsToBytes_append, ← pointsTo64_eq_pointsToBytes,
      unpack64_length,
      pointsToBytes_append, ← pointsTo64_eq_pointsToBytes,
      show p + BitVec.ofNat 64 8 + BitVec.ofNat 64 ((unpack64 0x6e6f697461636966#64).take 7).length
        = p + 15#64 by
        rw [show ((unpack64 0x6e6f697461636966#64).take 7).length = 7 by decide]; bv_omega]

theorem macFailed_assemble (A : RustAlloc) (sp p : BitVec 64) (hp : p ≠ 0) :
    ((sp - 1144#64) ↦₆₄ 23#64) ∗
    ((sp - 1136#64) ↦₆₄ p) ∗
    ((sp - 1128#64) ↦₆₄ 23#64) ∗
    A.live p 23 1 ∗
    (p ↦₆₄ 0x697265762043414d#64) ∗
    ((p + 8#64) ↦ₛ (unpack64 0x6e6f697461636966#64).take 7) ∗
    ((p + 15#64) ↦₆₄ 0x64656c696166206e#64) ⊢
    invalidMessageStrAt A (sp - 1504#64 + 0x168#64) .macFailed := by
  dsimp only [invalidMessageStrAt]
  rw [show sp - 1504#64 + 0x168#64 = sp - 1144#64 by bv_omega,
      macFailed_bytes_assemble p]
  have hlen : macFailedStr.length = 23 := macFailedStr_length.1
  have hcap_le : macFailedStr.length ≤ (23#64 : BitVec 64).toNat := by rw [hlen]; decide
  have hcap_lt : (23#64 : BitVec 64).toNat < 2 ^ 63 := by decide
  have hv := vecU8At_parts_entails_vecU8 A (sp - 1144#64) 23#64 p macFailedStr
    hcap_le hcap_lt hp
  simp only [show (23#64 : BitVec 64) = 0 ↔ False by decide, ↓reduceIte,
    show (23#64 : BitVec 64).toNat = 23 by decide, hlen,
    show sp - 1144#64 + 8#64 = sp - 1136#64 by bv_omega,
    show sp - 1144#64 + 16#64 = sp - 1128#64 by bv_omega] at hv
  rw [Nat.sub_self, memRegion_zero, sepConj_emp] at hv
  exact hv

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD
