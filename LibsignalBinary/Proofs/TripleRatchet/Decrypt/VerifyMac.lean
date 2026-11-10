/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-!
# Segment 7 (`verify_mac_with_addresses`) Proofs for `try_decrypt_with_state`

Verifies Segment 7 (`+0x63c → +0x678 / +0x30c`) across fixed-image and relocatable
`[LibsignalPlacement]` configurations (blocks `130` and `433` / `549`), calling
`SignalMessage::verify_mac_with_addresses` and either advancing to `AesDecryptState` or allocating
`"bad authentication code"`, freeing `newPqrState`, and entering `ErrTailState`.
-/

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

theorem verifyMac_scr_split (sp : BitVec 64) :
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

theorem rodata_0x44fe8_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2344) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2348)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 23 = macFailedBytes := by
  decide +kernel

theorem rodata_macFailed_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2344) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2348))) ↦ᵣ macFailedBytes) ∗ P := by
  have h := Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2344) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2348))) (secLen := 23) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by decide +kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by decide +kernel)) (by decide +kernel) hro hP
  rwa [rodata_0x44fe8_eq] at h

theorem adrp_macFailedStr_ext {img : Obj.Image} (halign : img.base &&& 0xfff#64 = 0#64)
    (ext : String → Option (State → State)) :
    (((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 2344#64) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2344) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2348) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 500)) =
      img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2344) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2348)) := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")]
  revert halign; bv_kernel

theorem adrp_macFailedStr {img : Obj.Image} (halign : img.base &&& 0xfff#64 = 0#64)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    (((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + 2344#64) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2344) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2348) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 500)) =
      img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2344) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 2348)) :=
  adrp_macFailedStr_ext halign (tripleRatchetExterns C ctl abs)

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
      show a + BitVec.ofNat 64 8 + BitVec.ofNat 64 ((unpack64 0x6e6f697461636966#64).take 7).length = a + 15#64 by
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
      show p + 8#64 + BitVec.ofNat 64 ((unpack64 0x6e6f697461636966#64).take 7).length = p + 15#64 by
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
      show p + BitVec.ofNat 64 8 + BitVec.ofNat 64 ((unpack64 0x6e6f697461636966#64).take 7).length = p + 15#64 by
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

theorem verifyMac_true_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hVMac : VerifyMacWithAddressesOkExt img C A uuidTryParse ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := hfn_tryDecrypt
  decrypt_fetches_ext img.base ext hfn 0x63c 60
  have hS7_pc := segS7PC_eq_ext himg ext
  have hS8_pc := segS8PC_eq_ext himg ext
  have hbl_vmac := bl_verifyMac_target_ext img ext
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [hS7_pc] at hpc
  dsimp only [tripleRatchetProgAtExt, VerifyMacWithAddressesOkExt] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr verifyMacWithAddressesName = vmac_entry at hbl_vmac hVMac
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  simp only [wp_norm, ← sepConj_assoc] at hpc hx20 hx22 hx23 hx25 hx27 hx28 hmem
  refine sepWPp_to_steps_or_panic (entry + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := vmac_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hfl1 hsym1
  refine SepWPp.call_inImage_frame (img := img) (spec := verifyMacWithAddressesSpec img C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff img ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := entry + bv% (1632))
    hfl1 hsym1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpec]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpec] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 (entry + bv% (1632))
        |>.setPC vmac_entry).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl1 hsym1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpec]
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (1656))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨?_, ⟨hrun1, hsp1, hsp0, hsp_al1, ?_, htr1, hfl2, hsym2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · rw [hS8_pc]; rfl
  · simp only [wp_norm, hx29_1]
  · unfold tryDecryptCommonHeap
    rw [trAt_eq_rest A s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)]
    have hmf1 := Satisfies.mono_focus (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

theorem verifyMac_true_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hVMac : VerifyMacWithAddressesOk img C A ctl uuidTryParse abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
      (AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) :=
  verifyMac_true_ok_ext img C A ctl S (tripleRatchetExterns C ctl abs) himg hVMac
    x trG tr st1 mks newPqrState draws R s0 s hok h7 hL

theorem verifyMac_false_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hVMac : VerifyMacWithAddressesOkExt img C A uuidTryParse ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := hfn_tryDecrypt
  decrypt_fetches_ext img.base ext hfn 0x63c 60
  decrypt_fetches_ext img.base ext hfn 0x914 88
  decrypt_fetches_ext img.base ext hfn 0x9d0 12
  decrypt_fetches_ext img.base ext hfn 0xcbc 12
  have hS7_pc := segS7PC_eq_ext himg ext
  have hErr_pc := errTailPC_eq_ext himg ext
  have hshim := shim_ok_at_ext img hC
  have halloc := alloc_ok_at_ext img C A ctl S ext hC
  have hdealloc := dealloc_ok_at_ext img C A ctl S ext hC
  have hpan_ext := externAt_handle_error_ext img ext
  have halign := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadrp := adrp_macFailedStr_ext halign ext
  have hbl_vmac := bl_verifyMac_target_ext img ext
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [hS7_pc] at hpc
  dsimp only [tripleRatchetProgAtExt, VerifyMacWithAddressesOkExt] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr verifyMacWithAddressesName = vmac_entry at hbl_vmac hVMac
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  simp only [wp_norm, ← sepConj_assoc] at hpc hx20 hx22 hx23 hx25 hx27 hx28 hmem
  refine sepWPp_to_steps_or_panic (entry + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := vmac_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hfl1 hsym1
  refine SepWPp.call_inImage_frame (img := img) (spec := verifyMacWithAddressesSpec img C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff img ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := entry + bv% (1632))
    hfl1 hsym1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpec]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpec] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 (entry + bv% (1632))
        |>.setPC vmac_entry).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl1 hsym1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpec]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  rw [stackAt_vmac_split_alloc (s0.sp - 1504#64)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  refine SepWPp.call_frame_frozen (img := img) (spec := sessionShimSpec) (x := ())
    (T := emp) (ret_pc := entry + bv% (2328))
    hfl2 hsym2 hshim (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [sessionShimSpec]; rw [pure_sepConj]; simp)
    trivial
    (by rw [emp_sepConj])
    (fun _ _ _ _ h => by dsimp only [sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl2 hsym2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [sessionShimSpec]
  apply SepWPp.elim_pure; intro htr2
  simp only [writeReg64_trace, setPC_trace, setPState_trace, htr1] at htr2
  apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hfl3 hsym3
  refine SepWPp.call_frame_frozen (img := img) (spec := rustAllocSpec A) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
    (ret_pc := entry + bv% (2340))
    hfl3 hsym3 halloc (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl3 hsym3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · -- OOM panic path: 0x34cc0 -> 0x35058 -> 0x35060 -> handle_error (entry + 80848#64)
    simp only [hp, ↓reduceIte]
    refine SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    wp_steps
    apply SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact SepWPp.panic_direct_ext C A ctl S img ext x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · -- Alloc succeeded: p ≠ 0#64
    simp only [hp, ↓reduceIte, sepConj_assoc]
    refine SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := rodata_macFailed_intro himg hfl3.roData hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := entry + bv% (2360))
    wp_steps
    apply SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hfl3b hsym3b
    simp only [sepConj_assoc]
    rw [rodata_macFailed_1_to_2]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl3b hsym3b (mid := entry + bv% (2380))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hfl4 hsym4
    simp only [sepConj_assoc]
    rw [rodata_macFailed_2_back]
    intro R' hm4
    rw [sepConj_assoc] at hm4
    have hm4' := Satisfies.drop_left hm4
    clear hm4
    revert R' hm4'
    change SepWPp _ _ _ _ _ _
    refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · -- newPqrCap = 0#64: cbz x8 at 0x34cf8 jumps directly to errTailPC (entry + 780#64)
      simp only [sepConj_assoc]
      refine SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
          simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
      simp only [emp_sepConj, ← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl5 hsym5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨?_, ⟨hrun3, hsp3, hsp0, hsp_al3, ?_, htr3, hfl5, hsym5, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · -- newPqrCap ≠ 0#64: dealloc newPqrPtr at 0x34d70
      simp only [sepConj_assoc]
      refine SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl5 hsym5
      refine SepWPp.call_frame_frozen (img := img) (spec := rustDeallocSpec A)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := entry + bv% (2520))
        hfl5 hsym5 hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hfl5 hsym5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl5 hsym5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC (entry + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC (entry + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC (entry + bv% (780))).spAligned = true :=
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
      have htr4' : (s4.setPC (entry + bv% (780))).trace = s0.trace := by simp only [setPC_trace, htr4]
      apply SepWPp.of_sepWP_frozen hfl5 hsym5 (mid := entry + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) hrun4'
      intro hfl6 hsym6
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) hrun4'
      intro _ _ hmf
      refine ⟨?_, ⟨hrun4', hsp4', hsp0, hsp_al4', ?_, htr4', hfl6, hsym6, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem verifyMac_false_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hS : TripleRatchetHooks C A S abs)
    (hVMac : VerifyMacWithAddressesOk img C A ctl uuidTryParse abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
      (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) :=
  verifyMac_false_ok_ext img C A ctl S (tripleRatchetExterns C ctl abs) himg (Stage2Contracts.of_tripleRatchetProgAt' hS) hVMac
    x trG tr st1 mks newPqrState draws R s0 s hok h7 hL

theorem verifyMac_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    S7SpecExt img C A ctl uuidTryParse S ext := by
  intro himg hC hVMac x trG tr st1 mks newPqrState draws R s0 s h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_ok_ext img C A ctl S ext himg hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_ok_ext img C A ctl S ext himg hC hVMac x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

theorem verifyMac_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    VerifyMacSpec img C A ctl uuidTryParse S abs :=
  fun himg hS => verifyMac_ok_ext img C A ctl S (tripleRatchetExterns C ctl abs) himg (Stage2Contracts.of_tripleRatchetProgAt' hS)

theorem stackAt_vmac_to_ext (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - verifyMacWithAddressesStackX) ∗
    stackAt sp verifyMacWithAddressesStackX ⊢
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
    stackAt sp extHookStack := by
  rw [← stackAt_sub_split sp verifyMacWithAddressesStackX (by decide),
      ← stackAt_sub_split sp extHookStack (by decide)]
  exact Entails.refl _

theorem verifyMac_true_ok_x (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hVMac : VerifyMacWithAddressesOkX img C A uuidTryParse ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := hfn_tryDecrypt
  decrypt_fetches_ext img.base ext hfn 0x63c 60
  have hS7_pc := segS7PC_eq_ext himg ext
  have hS8_pc := segS8PC_eq_ext himg ext
  have hbl_vmac := bl_verifyMac_target_ext img ext
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [hS7_pc] at hpc
  dsimp only [tripleRatchetProgAtExt, VerifyMacWithAddressesOkX, VerifyMacWithAddressesOkExt] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr verifyMacWithAddressesName = vmac_entry at hbl_vmac hVMac
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)] at hmem
  simp only [wp_norm, ← sepConj_assoc] at hpc hx20 hx22 hx23 hx25 hx27 hx28 hmem
  refine sepWPp_to_steps_or_panic (entry + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := vmac_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hfl1 hsym1
  refine SepWPp.call_inImage_frame (img := img) (spec := verifyMacWithAddressesSpecX img C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff img ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStackX)
    (ret_pc := entry + bv% (1632))
    hfl1 hsym1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpecX]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpecX] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 (entry + bv% (1632))
        |>.setPC vmac_entry).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecryptFn_onPanic_of_callee C decFn A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl1 hsym1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpecX]
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (1656))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨?_, ⟨hrun1, hsp1, hsp0, hsp_al1, ?_, htr1, hfl2, hsym2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · rw [hS8_pc]; rfl
  · simp only [wp_norm, hx29_1]
  · unfold tryDecryptCommonHeap
    rw [trAt_eq_rest A s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)]
    have hmf1 := Satisfies.mono_focus (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

theorem verifyMac_false_ok_x (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hVMac : VerifyMacWithAddressesOkX img C A uuidTryParse ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  have hfn := hfn_tryDecrypt
  decrypt_fetches_ext img.base ext hfn 0x63c 60
  decrypt_fetches_ext img.base ext hfn 0x914 88
  decrypt_fetches_ext img.base ext hfn 0x9d0 12
  decrypt_fetches_ext img.base ext hfn 0xcbc 12
  have hS7_pc := segS7PC_eq_ext himg ext
  have hErr_pc := errTailPC_eq_ext himg ext
  have hshim := shim_ok_at_x img hC
  have halloc := alloc_ok_at_x img C A encFn decFn ext hC
  have hdealloc := dealloc_ok_at_x img C A encFn decFn ext hC
  have hpan_ext := externAt_handle_error_ext img ext
  have halign := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadrp := adrp_macFailedStr_ext halign ext
  have hbl_vmac := bl_verifyMac_target_ext img ext
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  rw [hS7_pc] at hpc
  dsimp only [tripleRatchetProgAtExt, VerifyMacWithAddressesOkX, VerifyMacWithAddressesOkExt] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr verifyMacWithAddressesName = vmac_entry at hbl_vmac hVMac
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)] at hmem
  simp only [wp_norm, ← sepConj_assoc] at hpc hx20 hx22 hx23 hx25 hx27 hx28 hmem
  refine sepWPp_to_steps_or_panic (entry + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_frozen hfl hsym (mid := vmac_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hfl1 hsym1
  refine SepWPp.call_inImage_frame (img := img) (spec := verifyMacWithAddressesSpecX img C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff img ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStackX)
    (ret_pc := entry + bv% (1632))
    hfl1 hsym1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpecX]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpecX] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 (entry + bv% (1632))
        |>.setPC vmac_entry).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecryptFn_onPanic_of_callee C decFn A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl1 hsym1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpecX]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  refine SepWPp.mono_focus (stackAt_vmac_to_ext (s0.sp - 1504#64)) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  refine SepWPp.call_inImage_frame (img := img) (spec := withStack sessionShimSpec extHookStack) (x := ())
    (T := stackAt (s0.sp - 1504#64) extHookStack) (ret_pc := entry + bv% (2328))
    hfl2 hsym2 hshim (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, sessionShimSpec]; simp only [wp_norm, hsp1, pure_sepConj, true_and, emp_sepConj])
    trivial
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [withStack, sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl2 hsym2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [withStack, sessionShimSpec]
  simp only [wp_norm, hsp1, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr2
  simp only [htr1] at htr2
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hfl3 hsym3
  refine SepWPp.call_inImage_frame (img := img) (spec := rustAllocSpecWithStack A extHookStack) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (2340))
    hfl3 hsym3 halloc (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl3 hsym3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpecWithStack]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · -- OOM panic path: 0x34cc0 -> 0x35058 -> 0x35060 -> handle_error (entry + 80848#64)
    simp only [hp, ↓reduceIte]
    refine SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    wp_steps
    apply SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact SepWPp.panic_direct_fn_ext C decFn A ctl S img ext x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · -- Alloc succeeded: p ≠ 0#64
    simp only [hp, ↓reduceIte, sepConj_assoc]
    refine SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := rodata_macFailed_intro himg hfl3.roData hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := entry + bv% (2360))
    wp_steps
    apply SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hfl3b hsym3b
    simp only [sepConj_assoc]
    rw [rodata_macFailed_1_to_2]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl3b hsym3b (mid := entry + bv% (2380))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hfl4 hsym4
    simp only [sepConj_assoc]
    rw [rodata_macFailed_2_back]
    intro R' hm4
    rw [sepConj_assoc] at hm4
    have hm4' := Satisfies.drop_left hm4
    clear hm4
    revert R' hm4'
    change SepWPp _ _ _ _ _ _
    refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · -- newPqrCap = 0#64: cbz x8 at 0x34cf8 jumps directly to errTailPC (entry + 780#64)
      simp only [sepConj_assoc]
      refine SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
          simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
      simp only [emp_sepConj, ← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl5 hsym5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨?_, ⟨hrun3, hsp3, hsp0, hsp_al3, ?_, htr3, hfl5, hsym5, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · -- newPqrCap ≠ 0#64: dealloc newPqrPtr at 0x34d70
      simp only [sepConj_assoc]
      refine SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_frozen hfl4 hsym4 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hfl5 hsym5
      refine SepWPp.call_inImage_frame (img := img) (spec := rustDeallocExternSpecWithStack A extHookStack)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := entry + bv% (2520))
        hfl5 hsym5 hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                    layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hfl5 hsym5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl5 hsym5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpecWithStack]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC (entry + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC (entry + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC (entry + bv% (780))).spAligned = true :=
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
      have htr4' : (s4.setPC (entry + bv% (780))).trace = s0.trace := by simp only [setPC_trace, htr4]
      apply SepWPp.of_sepWP_frozen hfl5 hsym5 (mid := entry + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) hrun4'
      intro hfl6 hsym6
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) hrun4'
      intro _ _ hmf
      refine ⟨?_, ⟨hrun4', hsp4', hsp0, hsp_al4', ?_, htr4', hfl6, hsym6, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · rw [hErr_pc]; rfl
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem verifyMac_ok_x (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    S7SpecX img C encFn decFn A ctl uuidTryParse S ext := by
  intro himg hC hVMac x trG tr st1 mks newPqrState draws R s0 s h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_ok_x img C decFn A ctl S ext himg hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_ok_x img C encFn decFn A ctl S ext himg hC hVMac x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

/-! ## Relocatable `[LibsignalPlacement]` Segment 7 Proofs (Blocks `130` and `549`) -/

abbrev lsMacFailedRoSym : String := "libsignal_session:.rodata..Lanon.22"
abbrev lsMacFailedCoinsRoSym : String := "libsignal_cli_ratchet:.rodata..Lanon.22"
abbrev lsHandleErrorSym : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

theorem lsroCheck_macFailedRoSym :
    lsroCheck lsMacFailedRoSym macFailedBytes = true := by
  decide +kernel

theorem lsroCheck_macFailedCoinsRoSym :
    lsroCheck lsMacFailedCoinsRoSym macFailedBytes = true := by
  decide +kernel

theorem rodata_macFailed_159_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsρ lsMacFailedRoSym ↦ᵣ macFailedBytes) ∗ P :=
  lsro_intro_chk hro lsroCheck_macFailedRoSym hP

theorem rodata_macFailed_549_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsρ lsMacFailedCoinsRoSym ↦ᵣ macFailedBytes) ∗ P :=
  lsro_intro_chk hro lsroCheck_macFailedCoinsRoSym hP

theorem verifyMac_true_159_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      (AesDecryptStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  change s.pc = (blkPl_131).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_131).base + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff tryDecryptPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := (blkPl_131).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpec]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpec] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_131).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpec]
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_131).base + bv% (1656))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨by rfl, ⟨hrun1, hsp1, hsp0, hsp_al1, ?_, htr1, hcl2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · simp only [wp_norm, hx29_1]
  · unfold tryDecryptCommonHeap
    rw [trAt_eq_rest A s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)]
    have hmf1 := Satisfies.mono_focus (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

theorem verifyMac_false_159_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpan_ext : (((blkPC_131).rebase (blkPl_131).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  change s.pc = (blkPl_131).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_131).base + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff tryDecryptPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := (blkPl_131).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpec]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpec] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_131).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpec]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  rw [stackAt_vmac_split_alloc (s0.sp - 1504#64)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.call_frame_placed (spec := sessionShimSpec) (x := ())
    (T := emp) (ret_pc := (blkPl_131).base + bv% (2328))
    hcl2 hshim (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [sessionShimSpec]; rw [pure_sepConj]; simp)
    trivial
    (by rw [emp_sepConj])
    (fun _ _ _ _ h => by dsimp only [sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [sessionShimSpec]
  apply SepWPp.elim_pure; intro htr2
  simp only [writeReg64_trace, setPC_trace, setPState_trace, htr1] at htr2
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustAllocSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_frame_placed (spec := rustAllocSpec A) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
    (ret_pc := (blkPl_131).base + bv% (2340))
    hcl3 halloc (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    refine SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact SepWPp.panic_direct_placed C A ctl S x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · simp only [hp, ↓reduceIte, sepConj_assoc]
    refine SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := rodata_macFailed_159_intro hcl3.2 hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_131).base + bv% (2360))
    wp_steps
    apply SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl3b
    simp only [sepConj_assoc]
    rw [rodata_macFailed_1_to_2]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3b (mid := (blkPl_131).base + bv% (2380))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl4
    simp only [sepConj_assoc]
    rw [rodata_macFailed_2_back]
    intro R' hm4
    rw [sepConj_assoc] at hm4
    have hm4' := Satisfies.drop_left hm4
    clear hm4
    revert R' hm4'
    change SepWPp _ _ _ _ _ _
    refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
          simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
      simp only [emp_sepConj, ← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_131).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun3, hsp3, hsp0, hsp_al3, ?_, htr3, hcl5, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm]; rfl, ?_⟩
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      refine SepWPp.call_frame_placed (spec := rustDeallocSpec A)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := (blkPl_131).base + bv% (2520))
        hcl5 hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC ((blkPl_131).base + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC ((blkPl_131).base + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC ((blkPl_131).base + bv% (780))).spAligned = true :=
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
      have htr4' : (s4.setPC ((blkPl_131).base + bv% (780))).trace = s0.trace := by simp only [setPC_trace, htr4]
      apply SepWPp.of_sepWP_placed hcl5 (mid := (blkPl_131).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) hrun4'
      intro hcl6
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) hrun4'
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun4', hsp4', hsp0, hsp_al4', ?_, htr4', hcl6, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem verifyMac_159_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpan_ext : (((blkPC_131).rebase (blkPl_131).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked) :
    S7SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_159_placed_ok C A ctl S H hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_159_placed_ok C A ctl S H hVMac hshim halloc hdealloc hpan_ext x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

theorem verifyMac_true_159_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      (AesDecryptStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)] at hmem
  change s.pc = (blkPl_131).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_131).base + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff tryDecryptPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStackX)
    (ret_pc := (blkPl_131).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpecX]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpecX] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_131).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpecX]
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_131).base + bv% (1656))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨by rfl, ⟨hrun1, hsp1, hsp0, hsp_al1, ?_, htr1, hcl2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · simp only [wp_norm, hx29_1]
  · unfold tryDecryptCommonHeap
    rw [trAt_eq_rest A s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)]
    have hmf1 := Satisfies.mono_focus (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

theorem verifyMac_false_159_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustNoAllocShimSym) (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustAllocSym) (rustAllocSpecWithStack A extHookStack))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack))
    (hpan_ext : (((blkPC_131).rebase (blkPl_131).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacStatePlaced (blkPl_131).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)] at hmem
  change s.pc = (blkPl_131).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_131).base + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff tryDecryptPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStackX)
    (ret_pc := (blkPl_131).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpecX]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpecX] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_131).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpecX]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  refine SepWPp.mono_focus (stackAt_vmac_to_ext (s0.sp - 1504#64)) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.call_frame_placed (spec := withStack sessionShimSpec extHookStack) (x := ())
    (T := stackAt (s0.sp - 1504#64) extHookStack) (ret_pc := (blkPl_131).base + bv% (2328))
    hcl2 hshim (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, sessionShimSpec]; simp only [wp_norm, hsp1, pure_sepConj, true_and, emp_sepConj])
    trivial
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [withStack, sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [withStack, sessionShimSpec]
  simp only [wp_norm, hsp1, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr2
  simp only [htr1] at htr2
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustAllocSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_frame_placed (spec := rustAllocSpecWithStack A extHookStack) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_131).base + bv% (2340))
    hcl3 halloc (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpecWithStack]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    refine SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact SepWPp.panic_direct_fn_placed C decFn A ctl S x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · simp only [hp, ↓reduceIte, sepConj_assoc]
    refine SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := rodata_macFailed_159_intro hcl3.2 hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_131).base + bv% (2360))
    wp_steps
    apply SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl3b
    simp only [sepConj_assoc]
    rw [rodata_macFailed_1_to_2]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3b (mid := (blkPl_131).base + bv% (2380))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl4
    simp only [sepConj_assoc]
    rw [rodata_macFailed_2_back]
    intro R' hm4
    rw [sepConj_assoc] at hm4
    have hm4' := Satisfies.drop_left hm4
    clear hm4
    revert R' hm4'
    change SepWPp _ _ _ _ _ _
    refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
          simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
      simp only [emp_sepConj, ← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_131).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun3, hsp3, hsp0, hsp_al3, ?_, htr3, hcl5, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm]; rfl, ?_⟩
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack A extHookStack)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := (blkPl_131).base + bv% (2520))
        hcl5 hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                    layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpecWithStack]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC ((blkPl_131).base + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC ((blkPl_131).base + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC ((blkPl_131).base + bv% (780))).spAligned = true :=
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
      have htr4' : (s4.setPC ((blkPl_131).base + bv% (780))).trace = s0.trace := by simp only [setPC_trace, htr4]
      apply SepWPp.of_sepWP_placed hcl5 (mid := (blkPl_131).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) hrun4'
      intro hcl6
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) hrun4'
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun4', hsp4', hsp0, hsp_al4', ?_, htr4', hcl6, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem verifyMac_159_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustNoAllocShimSym) (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustAllocSym) (rustAllocSpecWithStack A extHookStack))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack))
    (hpan_ext : (((blkPC_131).rebase (blkPl_131).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked) :
    S7SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C decFn A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_159_placed_ok_x C decFn A ctl S H hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_159_placed_ok_x C decFn A ctl S H hVMac hshim halloc hdealloc hpan_ext x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

theorem verifyMac_true_549_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (AesDecryptStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff tryDecryptPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpec]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpec] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_434).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpec]
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1656))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨by rfl, ⟨hrun1, hsp1, hsp0, hsp_al1, ?_, htr1, hcl2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · simp only [wp_norm, hx29_1]
  · unfold tryDecryptCommonHeap
    rw [trAt_eq_rest A s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)]
    have hmf1 := Satisfies.mono_focus (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

theorem verifyMac_false_549_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpan_ext : (((blkPC_434).rebase (blkPl_434).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff tryDecryptPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStack)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpec]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpec] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_434).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpec]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  rw [stackAt_vmac_split_alloc (s0.sp - 1504#64)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.call_frame_placed (spec := sessionShimSpec) (x := ())
    (T := emp) (ret_pc := (blkPl_434).base + bv% (2328))
    hcl2 hshim (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [sessionShimSpec]; rw [pure_sepConj]; simp)
    trivial
    (by rw [emp_sepConj])
    (fun _ _ _ _ h => by dsimp only [sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [sessionShimSpec]
  apply SepWPp.elim_pure; intro htr2
  simp only [writeReg64_trace, setPC_trace, setPState_trace, htr1] at htr2
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustAllocSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_frame_placed (spec := rustAllocSpec A) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
    (ret_pc := (blkPl_434).base + bv% (2340))
    hcl3 halloc (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    refine SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact SepWPp.panic_direct_placed C A ctl S x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · simp only [hp, ↓reduceIte, sepConj_assoc]
    refine SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := rodata_macFailed_549_intro hcl3.2 hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + bv% (2360))
    wp_steps
    apply SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl3b
    simp only [sepConj_assoc]
    rw [rodata_macFailed_1_to_2]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3b (mid := (blkPl_434).base + bv% (2380))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl4
    simp only [sepConj_assoc]
    rw [rodata_macFailed_2_back]
    intro R' hm4
    rw [sepConj_assoc] at hm4
    have hm4' := Satisfies.drop_left hm4
    clear hm4
    revert R' hm4'
    change SepWPp _ _ _ _ _ _
    refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
          simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
      simp only [emp_sepConj, ← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun3, hsp3, hsp0, hsp_al3, ?_, htr3, hcl5, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm]; rfl, ?_⟩
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      refine SepWPp.call_frame_placed (spec := rustDeallocSpec A)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := (blkPl_434).base + bv% (2520))
        hcl5 hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC ((blkPl_434).base + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC ((blkPl_434).base + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC ((blkPl_434).base + bv% (780))).spAligned = true :=
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
      have htr4' : (s4.setPC ((blkPl_434).base + bv% (780))).trace = s0.trace := by simp only [setPC_trace, htr4]
      apply SepWPp.of_sepWP_placed hcl5 (mid := (blkPl_434).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) hrun4'
      intro hcl6
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) hrun4'
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun4', hsp4', hsp0, hsp_al4', ?_, htr4', hcl6, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStack (by decide),
            stackAt_vmac_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem verifyMac_549_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpec tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpan_ext : (((blkPC_434).rebase (blkPl_434).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked) :
    S7SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_549_placed_ok C A ctl S H hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_549_placed_ok C A ctl S H hVMac hshim halloc hdealloc hpan_ext x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

theorem verifyMac_true_549_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (AesDecryptStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (1656)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff tryDecryptPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStackX)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpecX]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpecX] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_434).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpecX]
  rw [hok]
  unfold verifyMacResultAt
  simp only [↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1656))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rfl) (by exact hrun1)
  intro _ _ hmf
  refine ⟨by rfl, ⟨hrun1, hsp1, hsp0, hsp_al1, ?_, htr1, hcl2, by simp only [wp_norm, hvregs_1]⟩,
    by simp only [wp_norm, hx19_1],
    by simp only [wp_norm, hx20_1],
    by simp only [wp_norm, hx21_1],
    by simp only [wp_norm, hx22_1],
    by simp only [wp_norm],
    by simp only [wp_norm, hx24_1],
    by simp only [wp_norm, hx25_1],
    by simp only [wp_norm, hx27_1],
    by simp only [wp_norm, hx28_1],
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
  · simp only [wp_norm, hx29_1]
  · unfold tryDecryptCommonHeap
    rw [trAt_eq_rest A s0.sp trG tr,
        messageKeysAt_eq (s0.sp - 1504#64) mks,
        verifyMac_scr_split (s0.sp - 1504#64),
        stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)]
    have hmf1 := Satisfies.mono_focus (verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 1#8) (by sep_focus) hmf
    clear hmf
    simp only [wp_norm, sepConj_assoc] at hmf1 ⊢
    sep_close

theorem verifyMac_false_549_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustNoAllocShimSym) (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustAllocSym) (rustAllocSpecWithStack A extHookStack))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack))
    (hpan_ext : (((blkPC_434).rebase (blkPl_434).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false)
    (h7 : VerifyMacStatePlaced (blkPl_434).base A ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s' : State, Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  rcases h7 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_rest A s0.sp trG tr,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      verifyMac_scr_split (s0.sp - 1504#64),
      stackAt_sub_split (s0.sp - 1504#64) verifyMacWithAddressesStackX (by decide)] at hmem
  change s.pc = (blkPl_434).base + 1596#64 at hpc
  simp only [wp_norm] at hx20 hx22 hx23 hx25 hx27 hx28
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + bv% (780)) hmem hL ?_
  apply SepWPp.of_sepWP_placed hcl (mid := lsmpl.base 62)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  intro hcl1
  refine SepWPp.call_cro_frame_placed (spec := verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)
    (x := ⟨x.msgA, x.msgG, x.msg, x.remA, x.rem, x.locA, x.loc,
           s0.sp - 1216#64, tr.remoteIdentityKey, s0.sp - 1248#64, tr.localIdentityKey,
           s0.sp - 192#64, mks.macKey, s0.sp - 1104#64⟩)
    (T := signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          ((s0.sp - 1216#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 1248#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((s0.sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
          memRegion (s0.sp - 1104#64) 9 ∗
          logOff tryDecryptPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) verifyMacWithAddressesStackX)
    (ret_pc := (blkPl_434).base + bv% (1632))
    hcl1 hVMac (by rfl) (by exact hrun)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [verifyMacWithAddressesSpecX]; simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm],
                by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [verifyMacWithAddressesSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by
      dsimp only [verifyMacWithAddressesSpecX] at hm_pan
      have h0m : s0.trace <+: (s.writeReg64 .x1 x.remA |>.writeReg64 .x2 x.locA
        |>.writeReg64 .x8 (s0.sp - 1104#64) |>.writeReg64 .x3 (s0.sp - 1216#64)
        |>.writeReg64 .x4 (s0.sp - 1248#64) |>.writeReg64 .x5 (s0.sp - 192#64)
        |>.writeReg64 .x0 x.msgA |>.writeReg32 .x6 32#32
        |>.writeReg64 .x30 ((blkPl_434).base + bv% (1632))
        |>.setPC (lsmpl.base 62)).trace := by
        simp only [writeReg64_trace, writeReg32_trace, setPC_trace, htr]
        exact List.prefix_refl _
      exact tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl1
  intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
  simp only [wp_norm, hsp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs_1
  dsimp only [verifyMacWithAddressesSpecX]
  rw [hok]
  unfold verifyMacResultAt
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr1
  simp only [htr] at htr1
  refine SepWPp.mono_focus (stackAt_vmac_to_ext (s0.sp - 1504#64)) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.call_frame_placed (spec := withStack sessionShimSpec extHookStack) (x := ())
    (T := stackAt (s0.sp - 1504#64) extHookStack) (ret_pc := (blkPl_434).base + bv% (2328))
    hcl2 hshim (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, sessionShimSpec]; simp only [wp_norm, hsp1, pure_sepConj, true_and, emp_sepConj])
    trivial
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, sessionShimSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [withStack, sessionShimSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
  dsimp only [withStack, sessionShimSpec]
  simp only [wp_norm, hsp1, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr2
  simp only [htr1] at htr2
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustAllocSym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_frame_placed (spec := rustAllocSpecWithStack A extHookStack) (x := (23, 1))
    (T := A.pool ∗ stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + bv% (2340))
    hcl3 halloc (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [rustAllocSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by decide, ⟨0, rfl⟩, by decide⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [rustAllocSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ _ hm_pan => by dsimp only [rustAllocSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
  dsimp only [rustAllocSpecWithStack]
  simp only [wp_norm, hsp2, sepConj_assoc]
  set p := s3.readReg64 .x0
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    refine SepWPp.elim_pure_focus (by sep_focus) fun htr3 => ?_
    simp only [htr2] at htr3
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.setPC_ite_true (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    exact SepWPp.panic_direct_fn_placed C decFn A ctl S x s0 _ _ _ _ R
      (by rfl) (by exact hrun3) hpan_ext
      (by simp only [writeReg64_trace, setPC_trace, htr3])
  · simp only [hp, ↓reduceIte, sepConj_assoc]
    refine SepWPp.elim_pure_focus (by sep_focus) fun h => ?_
    have htr3 := h.2
    simp only [htr2] at htr3
    have hmf_ent := verifyMacResultAt_parts_entails_memRegion (s0.sp - 1104#64) okTagVec 0#8
    refine SepWPp.mono_focus hmf_ent (by sep_focus) ?_
    rw [macFailed_alloc_split p]
    refine SepWPp.elim_memRegion8_focus (a := p) (by sep_focus) fun pw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 8#64) (by sep_focus) fun pw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun sw0 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun sw1 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun sw2 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun sb0 => ?_
    intro R' hm3
    have hm3_ro := rodata_macFailed_549_intro hcl3.2 hm3
    clear hm3
    rw [rodata_macFailed_split1, ← sepConj_assoc] at hm3_ro
    revert R' hm3_ro
    change SepWPp _ _ _ _ _ _
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + bv% (2360))
    wp_steps
    apply SepWP.setPC_ite_false (by simp only [beq_iff_eq]; exact hp)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl3b
    simp only [sepConj_assoc]
    rw [rodata_macFailed_1_to_2]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl3b (mid := (blkPl_434).base + bv% (2380))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun3)
    intro hcl4
    simp only [sepConj_assoc]
    rw [rodata_macFailed_2_back]
    intro R' hm4
    rw [sepConj_assoc] at hm4
    have hm4' := Satisfies.drop_left hm4
    clear hm4
    revert R' hm4'
    change SepWPp _ _ _ _ _ _
    refine SepWPp.mono_focus (macFailed_overlap_prep p) (by sep_focus) ?_
    refine SepWPp.elim_memRegion8_focus (a := p + 15#64) (by sep_focus) fun pw2 => ?_
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus
        (show (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
          (newPqrPtr ↦ₛ newPqrState) ∗
          memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢ emp by
          simp only [hpqr_cap]; exact Entails.refl _) (by sep_focus) ?_
      simp only [emp_sepConj, ← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun3, hsp3, hsp0, hsp_al3, ?_, htr3, hcl5, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm]; rfl, ?_⟩
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close
    · simp only [sepConj_assoc]
      refine SepWPp.mono_focus (newPqr_dealloc_prep A newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl5
      refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack A extHookStack)
        (x := (newPqrPtr, newPqrCap.toNat, 1))
        (T := A.pool ∗ A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := (blkPl_434).base + bv% (2520))
        hcl5 hdealloc (by rfl) (by exact hrun3)
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                    layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun sf _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl5
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl5
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpecWithStack]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; intro htr4
      simp only [htr3] at htr4
      simp only [← sepConj_assoc]
      have hrun4' : (s4.setPC ((blkPl_434).base + bv% (780))).status = .Running := by simp only [wp_norm, hrun4]
      have hsp4' : (s4.setPC ((blkPl_434).base + bv% (780))).sp = s0.sp - 1504#64 := by simp only [wp_norm, hsp4]
      have hsp_al4' : (s4.setPC ((blkPl_434).base + bv% (780))).spAligned = true :=
        AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4
      have htr4' : (s4.setPC ((blkPl_434).base + bv% (780))).trace = s0.trace := by simp only [setPC_trace, htr4]
      apply SepWPp.of_sepWP_placed hcl5 (mid := (blkPl_434).base + bv% (780))
      wp_steps
      apply SepWP.done (by rfl) hrun4'
      intro hcl6
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) hrun4'
      intro _ _ hmf
      refine ⟨by rfl, ⟨hrun4', hsp4', hsp0, hsp_al4', ?_, htr4', hcl6, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap speBodyAt
        rw [trAt_eq_rest A s0.sp trG tr,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_s7_split s0.sp]
        have hmf1 := Satisfies.mono_focus (macFailed_assemble A s0.sp p hp) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
        have hmf3 := Satisfies.mono_focus (errTail_sp_s7_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA msgW) (by sep_focus) hmf2
        clear hmf hmf1 hmf2
        simp only [wp_norm, sepConj_assoc] at hmf3 ⊢
        sep_close

theorem verifyMac_549_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hVMac : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesSpecX tryDecryptPlacedImg C.F A uuidTryParse)))
    (hshim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustNoAllocShimSym) (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustAllocSym) (rustAllocSpecWithStack A extHookStack))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack))
    (hpan_ext : (((blkPC_434).rebase (blkPl_434).base H)).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked) :
    S7SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C decFn A ctl uuidTryParse S := by
  intro x trG tr st1 mks newPqrState draws R s0 s h7 hL
  by_cases hok : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey = true
  · simp only [hok, ↓reduceIte]
    exact verifyMac_true_549_placed_ok_x C decFn A ctl S H hVMac x trG tr st1 mks newPqrState draws R s0 s hok h7 hL
  · have hok_false : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey = false :=
      Bool.eq_false_iff.mpr hok
    simp only [hok_false, Bool.false_eq_true, ↓reduceIte]
    exact verifyMac_false_549_placed_ok_x C decFn A ctl S H hVMac hshim halloc hdealloc hpan_ext x trG tr st1 mks newPqrState draws R s0 s hok_false h7 hL

end CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
