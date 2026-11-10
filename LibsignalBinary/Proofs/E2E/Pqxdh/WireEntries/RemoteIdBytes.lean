/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Specs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Fetch
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue

/-!
# `<SessionRecord>::remote_identity_key_bytes` (`0x17c94`)

Proves `remoteIdentityKeyBytes_sp2_ok` and `remoteIdentityKeyBytes_ok` on `tripleRatchetProgAt` and
`tripleRatchetProg`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x17c94
  libsignalSessionCode_fnOff_0x11b04
  libsignalSessionCode_fnOff_0x3e2c4
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## Callee and Stub Helpers -/

private theorem fnAddr_remoteIdBytes_add_eq {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff remoteIdentityKeyBytesName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target) := by
      fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).fnAddr remoteIdentityKeyBytesName + off =
      (tripleRatchetProgAt b C ctl abs).fnAddr target := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, BitVec.add_assoc, h]

private theorem remoteIdentityKey_ok_at_remoteIdBytes
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr remoteIdentityKeyBytesName +
      18446744073709526640#64)
      (remoteIdentityKeySpec A img) := by
  rw [fnAddr_remoteIdBytes_add_eq (target := remoteIdentityKeyName)]
  exact Glue.remoteIdentityKeyOk img C A ctl abs himg

private theorem publicKeySerialize_ok_at_remoteIdBytes
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr remoteIdentityKeyBytesName + 157232#64)
      (publicKeySerializeSpec A) := by
  rw [fnAddr_remoteIdBytes_add_eq (target := publicKeySerializeName)]
  exact Glue.publicKeySerializeOk hA

/-! ## Stack and Memory Decomposition Helpers -/

private theorem stackAt_remoteIdBytes (sp : BitVec 64) :
    stackAt sp (128 + publicKeySerializeStack) =
      stackAt (sp - 128#64) publicKeySerializeStack ∗
      memRegion (sp - 128#64) 8 ∗
      (∃∗ s8 : BitVec 64, (sp - 120#64) ↦₆₄ s8) ∗
      (∃∗ s16 : BitVec 16, (sp - 112#64) ↦₁₆ s16) ∗
      memRegion (sp - 110#64) 6 ∗
      memRegion (sp - 104#64) 34 ∗
      memRegion (sp - 70#64) 6 ∗
      (∃∗ c0 : BitVec 64, (sp - 64#64) ↦₆₄ c0) ∗
      (∃∗ c1 : BitVec 64, (sp - 56#64) ↦₆₄ c1) ∗
      (∃∗ c2 : BitVec 64, (sp - 48#64) ↦₆₄ c2) ∗
      (∃∗ s58 : BitVec 32, (sp - 40#64) ↦₃₂ s58) ∗
      (∃∗ s5c : BitVec 16, (sp - 36#64) ↦₁₆ s5c) ∗
      memRegion (sp - 34#64) 2 ∗
      (∃∗ c3 : BitVec 64, (sp - 32#64) ↦₆₄ c3) ∗
      (∃∗ c4 : BitVec 64, (sp - 24#64) ↦₆₄ c4) ∗
      (∃∗ c5 : BitVec 64, (sp - 16#64) ↦₆₄ c5) ∗
      (∃∗ c6 : BitVec 64, (sp - 8#64) ↦₆₄ c6) := by
  unfold stackAt publicKeySerializeStack allocHookStack
  rw [show (128 + (4096 + 32) : Nat) = 4128 + 128 from rfl,
      ProofLib.memRegion_split' (b := sp - 4256#64) (n := 4128) (k := 128)
        (b' := sp - 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 120)
        (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 112)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 2) (k := 110)
        (b' := sp - 110#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 110#64) (n := 6) (k := 104)
        (b' := sp - 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 34) (k := 70)
        (b' := sp - 70#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 70#64) (n := 6) (k := 64)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56)
        (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 4) (k := 36)
        (b' := sp - 36#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 36#64) (n := 2) (k := 34)
        (b' := sp - 34#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 34#64) (n := 2) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 120#64),
      memRegion_two (sp - 112#64),
      ProofLib.memRegion_eight (sp - 64#64),
      ProofLib.memRegion_eight (sp - 56#64),
      ProofLib.memRegion_eight (sp - 48#64),
      memRegion_four (sp - 40#64),
      memRegion_two (sp - 36#64),
      ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64),
      ProofLib.memRegion_eight (sp - 8#64)]
  have hsub : sp - 4256#64 = sp - 128#64 - BitVec.ofNat 64 publicKeySerializeStack := by
    change sp - 4256#64 = sp - 128#64 - 4128#64
    bv_omega
  rw [hsub]

private theorem stackAt_publicKeySerialize_to_allocHook (sp : BitVec 64) :
    stackAt sp publicKeySerializeStack =
      memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack := by
  unfold stackAt publicKeySerializeStack allocHookStack
  exact ProofLib.memRegion_split' (b := sp - 4128#64) (n := 32) (k := 4096)
    (b' := sp - 4096#64) rfl (by bv_omega) (by decide)

private theorem stackAt_publicKeySerialize_to_remoteIdentityKey (sp : BitVec 64) :
    stackAt sp publicKeySerializeStack =
      memRegion (sp - 4128#64) 3984 ∗ stackAt sp remoteIdentityKeyStack := by
  unfold stackAt publicKeySerializeStack allocHookStack remoteIdentityKeyStack
  exact ProofLib.memRegion_split' (b := sp - 4128#64) (n := 3984) (k := 144)
    (b' := sp - 144#64) rfl (by bv_omega) (by decide)

/-- The 6 disjoint chunks (`4 + 2 + 8 + 8 + 8 + 2 = 32` bytes) used by `0x17d28..0x17d7c`
to shift `peerKey.publicKey.bytes` from `sp + 0x1a` down to `sp + 0x18`. -/
def pkShiftChunks (a : BitVec 64) (v0 : BitVec 32) (v4 : BitVec 16)
    (v6 v14 v22 : BitVec 64) (v30 : BitVec 16) : SepProp :=
  (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₁₆ v4) ∗ ((a + 6#64) ↦₆₄ v6) ∗
  ((a + 14#64) ↦₆₄ v14) ∗ ((a + 22#64) ↦₆₄ v22) ∗ ((a + 30#64) ↦₁₆ v30)

private theorem pkShiftChunks_sp_102 (sp : BitVec 64)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16) :
    pkShiftChunks (sp - 102#64) v0 v4 v6 v14 v22 v30 =
      ((sp - 102#64) ↦₃₂ v0) ∗ ((sp - 98#64) ↦₁₆ v4) ∗ ((sp - 96#64) ↦₆₄ v6) ∗
      ((sp - 88#64) ↦₆₄ v14) ∗ ((sp - 80#64) ↦₆₄ v22) ∗ ((sp - 72#64) ↦₁₆ v30) := by
  dsimp only [pkShiftChunks]
  have h4  : sp - 102#64 + 4#64  = sp - 98#64 := by bv_omega
  have h6  : sp - 102#64 + 6#64  = sp - 96#64 := by bv_omega
  have h14 : sp - 102#64 + 14#64 = sp - 88#64 := by bv_omega
  have h22 : sp - 102#64 + 22#64 = sp - 80#64 := by bv_omega
  have h30 : sp - 102#64 + 30#64 = sp - 72#64 := by bv_omega
  rw [h4, h6, h14, h22, h30]

private theorem pkShiftChunks_sp_104 (sp : BitVec 64)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16) :
    pkShiftChunks (sp - 104#64) v0 v4 v6 v14 v22 v30 =
      ((sp - 104#64) ↦₃₂ v0) ∗ ((sp - 100#64) ↦₁₆ v4) ∗ ((sp - 98#64) ↦₆₄ v6) ∗
      ((sp - 90#64) ↦₆₄ v14) ∗ ((sp - 82#64) ↦₆₄ v22) ∗ ((sp - 74#64) ↦₁₆ v30) := by
  dsimp only [pkShiftChunks]
  have h4  : sp - 104#64 + 4#64  = sp - 100#64 := by bv_omega
  have h6  : sp - 104#64 + 6#64  = sp - 98#64  := by bv_omega
  have h14 : sp - 104#64 + 14#64 = sp - 90#64  := by bv_omega
  have h22 : sp - 104#64 + 22#64 = sp - 82#64  := by bv_omega
  have h30 : sp - 104#64 + 30#64 = sp - 74#64  := by bv_omega
  rw [h4, h6, h14, h22, h30]

private theorem exists_pkShiftChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16),
      ∀ a : BitVec 64, (a ↦ₛ bs) = pkShiftChunks a v0 v4 v6 v14 v22 v30 := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5,
    _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13,
    _ | ⟨b14, _ | ⟨b15, _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21,
    _ | ⟨b22, _ | ⟨b23, _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29,
    _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length_cons, List.length_nil] at h; omega)
  refine ⟨b3 ++ b2 ++ b1 ++ b0, b5 ++ b4,
    b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6,
    b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15 ++ b14,
    b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24 ++ b23 ++ b22,
    b31 ++ b30, fun a => ?_⟩
  dsimp only [pkShiftChunks]
  rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes2_eq_pointsTo16,
      ← pointsToBytes8_eq_pointsTo64, ← pointsToBytes8_eq_pointsTo64,
      ← pointsToBytes8_eq_pointsTo64, ← pointsToBytes2_eq_pointsTo16]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion_34_split_dest (sp : BitVec 64) :
    memRegion (sp - 104#64) 34 =
      (∃∗ d0 : BitVec 32, (sp - 104#64) ↦₃₂ d0) ∗
      (∃∗ d4 : BitVec 16, (sp - 100#64) ↦₁₆ d4) ∗
      (∃∗ d6 : BitVec 64, (sp - 98#64) ↦₆₄ d6) ∗
      (∃∗ d14 : BitVec 64, (sp - 90#64) ↦₆₄ d14) ∗
      (∃∗ d22 : BitVec 64, (sp - 82#64) ↦₆₄ d22) ∗
      (∃∗ d30 : BitVec 16, (sp - 74#64) ↦₁₆ d30) ∗
      (∃∗ d32 : BitVec 16, (sp - 72#64) ↦₁₆ d32) := by
  rw [ProofLib.memRegion_split' (b := sp - 104#64) (n := 4) (k := 30)
        (b' := sp - 100#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 100#64) (n := 2) (k := 28)
        (b' := sp - 98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 98#64) (n := 8) (k := 20)
        (b' := sp - 90#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 90#64) (n := 8) (k := 12)
        (b' := sp - 82#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 8) (k := 4)
        (b' := sp - 74#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 2)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      memRegion_four (sp - 104#64), memRegion_two (sp - 100#64),
      ProofLib.memRegion_eight (sp - 98#64), ProofLib.memRegion_eight (sp - 90#64),
      ProofLib.memRegion_eight (sp - 82#64), memRegion_two (sp - 74#64),
      memRegion_two (sp - 72#64)]

private theorem shift_source_to_memRegion34 (sp : BitVec 64)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16) :
    (((sp - 104#64) ↦₈ 0#8) ∗ ((sp - 103#64) ↦₈ 1#8) ∗
     ((sp - 102#64) ↦₃₂ v0) ∗ ((sp - 98#64) ↦₁₆ v4) ∗ ((sp - 96#64) ↦₆₄ v6) ∗
     ((sp - 88#64) ↦₆₄ v14) ∗ ((sp - 80#64) ↦₆₄ v22) ∗ ((sp - 72#64) ↦₁₆ v30)) ⊢
      memRegion (sp - 104#64) 34 := by
  rw [ProofLib.memRegion_split' (b := sp - 104#64) (n := 1) (k := 33)
        (b' := sp - 103#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 103#64) (n := 1) (k := 32)
        (b' := sp - 102#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 102#64) (n := 4) (k := 28)
        (b' := sp - 98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 98#64) (n := 2) (k := 26)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 18)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 10)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 2)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo16_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo16_entails_memRegion _ _)))))))

private theorem shift_dest_to_memRegion34 (sp : BitVec 64)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 v32 : BitVec 16) :
    (((sp - 104#64) ↦₃₂ v0) ∗ ((sp - 100#64) ↦₁₆ v4) ∗ ((sp - 98#64) ↦₆₄ v6) ∗
     ((sp - 90#64) ↦₆₄ v14) ∗ ((sp - 82#64) ↦₆₄ v22) ∗ ((sp - 74#64) ↦₁₆ v30) ∗
     ((sp - 72#64) ↦₁₆ v32)) ⊢
      memRegion (sp - 104#64) 34 := by
  rw [ProofLib.memRegion_split' (b := sp - 104#64) (n := 4) (k := 30)
        (b' := sp - 100#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 100#64) (n := 2) (k := 28)
        (b' := sp - 98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 98#64) (n := 8) (k := 20)
        (b' := sp - 90#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 90#64) (n := 8) (k := 12)
        (b' := sp - 82#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 8) (k := 4)
        (b' := sp - 74#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 2)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo16_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo16_entails_memRegion _ _)
              (pointsTo16_entails_memRegion _ _))))))

private theorem truncate16_zeroExtend32_idem (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 v) = v :=
  (BitVec.setWidth_setWidth_of_le v (by decide)).trans (BitVec.setWidth_eq v)

private theorem memRegion_out32_split (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ o0 : BitVec 64, out ↦₆₄ o0) ∗
      (∃∗ o1 : BitVec 64, (out + 8#64) ↦₆₄ o1) ∗
      (∃∗ o2 : BitVec 64, (out + 16#64) ↦₆₄ o2) ∗
      (∃∗ o3 : BitVec 64, (out + 24#64) ↦₆₄ o3) := by
  rw [memRegion_split out 8 24 (by decide),
      memRegion_split (out + 8#64) 8 16 (by decide),
      memRegion_split (out + 8#64 + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## `sessionRecordAt` Exposure -/

/-- Rest of `sessionRecordAt` not touched by `remote_identity_key_bytes`. -/
def sessionRecordRestAt (A : RustAlloc) (recPtr : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) recPtr 0#64 8#64 [] ∗
  ⌜PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat⌝ ∗
  ⌜PublicKey.deserialize G.localIk.bytes = .ok s.state.localIdentity.publicKey ∧
    (match s.state.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = s.state.receiverChains.length ∧
    G.pending.isSome = s.state.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  ((recPtr + 0x18#64 + 8#64) ↦₆₄ G.localIk.ptr) ∗
  ((recPtr + 0x18#64 + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
  vecU8Buf A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
  vecU8At A (recPtr + 0x18#64 + asm64% ssRootKeyOff) G.root.cap G.root.ptr (HMAC.keyToBytes32
    s.state.rootKey) ∗
  vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (recPtr + 0x18#64 + asm64%
    ssReceiverChainsOff)
    G.chainsCap G.chainsPtr (G.chains.zip s.state.receiverChains) ∗
  vecGhostAt A G.alice (recPtr + 0x18#64 + asm64% ssAliceBaseKeyOff) ∗
  vecU8At A (recPtr + 0x18#64 + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr s.state.pqRatchetState
    ∗
  optSenderChainAt A (recPtr + 0x18#64 + asm64% ssSenderChainOff) G.sender s.state.senderChain ∗
  optTailVecAt A (asm% pendingPreKeySize) (recPtr + 0x18#64 + asm64% ssPendingPreKeyOff) G.pending ∗
  optTailVecAt A (asm% pendingKyberPreKeySize) (recPtr + 0x18#64 + asm64% ssPendingKyberPreKeyOff)
    G.kyber ∗
  ((recPtr + 0x18#64 + asm64% ssSessionVersionOff) ↦₃₂ s.state.sessionVersion) ∗
  ((recPtr + 0x18#64 + asm64% ssPreviousCounterOff) ↦₃₂ s.state.previousCounter) ∗
  ((recPtr + 0x18#64 + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)

private theorem sessionRecordAt_expose_remoteId (A : RustAlloc) (recPtr : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionRecordAt A recPtr ⟨0#64, 8#64, some G⟩ ⟨some s⟩ =
      ((recPtr + 0x18#64) ↦₆₄ G.localIk.cap) ∗
      vecGhostAt A G.remoteIk (recPtr + 0x18#64 + 0x18#64) ∗
      sessionRecordRestAt A recPtr G s := by
  unfold sessionRecordAt sessionStateReprAt sessionStateAt sessionRecordRestAt
  dsimp only
  have hloc : vecGhostAt A G.localIk (recPtr + 0x18#64) =
      (((recPtr + 0x18#64) ↦₆₄ G.localIk.cap) ∗
       ((recPtr + 0x18#64 + 8#64) ↦₆₄ G.localIk.ptr) ∗
       ((recPtr + 0x18#64 + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length)) ∗
      vecU8Buf A G.localIk.cap G.localIk.ptr G.localIk.bytes := by
    unfold vecGhostAt
    exact vecU8At_eq_header_sep_buf A (recPtr + 0x18#64) G.localIk.cap G.localIk.ptr G.localIk.bytes
  rw [hloc]
  ac_rfl

private theorem sessionRecordAt_localIk_and_remoteId {A : RustAlloc} {recPtr : BitVec 64}
    {G : SessionGhost} {s : Session (List (BitVec 8))} {m : Memory} {R : SepProp}
    (h : m ⊨ sessionRecordAt A recPtr ⟨0#64, 8#64, some G⟩ ⟨some s⟩ ∗ R) :
    G.localIk.cap.toNat < 2 ^ 63 ∧
    (match s.state.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) := by
  have hrec := Satisfies.of_sep_left h
  unfold sessionRecordAt sessionStateReprAt at hrec
  dsimp only at hrec
  have hss := Satisfies.of_sep_right (Satisfies.of_sep_right hrec)
  unfold sessionStateAt at hss
  have hpure := Satisfies.of_sep_left hss
  rw [satisfies_pure] at hpure
  have hloc := Satisfies.of_sep_left (Satisfies.of_sep_right hss)
  unfold vecGhostAt vecU8At at hloc
  have hcap := Satisfies.of_sep_left (Satisfies.of_sep_right hloc)
  rw [satisfies_pure] at hcap
  exact ⟨hcap.2.1, hpure.2.1⟩

private theorem cond_eq_adds_false_of_ult {cap : BitVec 64}
    (h : cap.ult 0x8000000000000000#64 = true) :
    ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  simp only [BitVec.ult, decide_eq_true_eq] at h
  bv_omega

private theorem cond_eq_adds_false_of_lt63 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
  apply cond_eq_adds_false_of_ult
  rw [BitVec.ult_eq_decide, decide_eq_true_iff]
  exact h

private theorem vecU8_intro_33 (A : RustAlloc) (out ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 33) (hptr : ptr ≠ 0#64) :
    (((out + 8#64) ↦₆₄ 33#64) ∗
     ((out + 16#64) ↦₆₄ ptr) ∗
     ((out + 24#64) ↦₆₄ 33#64) ∗
     A.live ptr 33 1 ∗
     (ptr ↦ₛ bs)) ⊢
    vecU8 A (out + 8#64) bs := by
  refine Entails.trans ?_ (vecU8At_entails_vecU8 A (out + 8#64) 33#64 ptr bs)
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf
  have h1 : (out + 8#64) + 8#64 = out + 16#64 := by bv_omega
  have h2 : (out + 8#64) + 16#64 = out + 24#64 := by bv_omega
  have h3 : (33#64 : BitVec 64) ≠ 0 := by decide
  rw [h1, h2, hlen, ite_eq_right_iff.mpr fun h => absurd h h3]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_self,
    memRegion_zero, sepConj_emp, BitVec.ofNat_eq_ofNat]
  rw [show (((out + 8#64) ↦₆₄ 33#64) ∗ ((out + 16#64) ↦₆₄ ptr) ∗ ((out + 24#64) ↦₆₄ 33#64)) ∗
        (⌜33 ≤ 33 ∧ 33 < 9223372036854775808 ∧ ptr ≠ 0#64⌝ ∗
          (A.live ptr 33 1 ∗ (ptr ↦ₛ bs))) =
      ⌜33 ≤ 33 ∧ 33 < 9223372036854775808 ∧ ptr ≠ 0#64⌝ ∗
        (((out + 8#64) ↦₆₄ 33#64) ∗ ((out + 16#64) ↦₆₄ ptr) ∗ ((out + 24#64) ↦₆₄ 33#64) ∗
         A.live ptr 33 1 ∗ (ptr ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide, hptr⟩ (Entails.refl _)

private theorem allocFailedIn_trans {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr] using h

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

/-! ## Main Subroutine Proof (`0x17c94`) -/

theorem remoteIdentityKeyBytes_sp2_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr remoteIdentityKeyBytesName)
      (remoteIdentityKeyBytesSpec A img) := by
  simp only [remoteIdentityKeyBytesSpec, stackAt_remoteIdBytes, memRegion_out32_split,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hrem := remoteIdentityKey_ok_at_remoteIdBytes (img := img) (C := C) (A := A)
    (ctl := ctl) (abs := abs) himg
  have hpk := publicKeySerialize_ok_at_remoteIdBytes (b := img.base) (C := C) (A := A)
    (ctl := ctl) (abs := abs) hA
  have hshim := noAllocShim_ok_at (b := img.base) (C := C) (ctl := ctl) (abs := abs)
    (name := remoteIdentityKeyBytesName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x17c94))
  have halloc :=
    alloc_ok_at_norm (b :=
      img.base) (C := C) (ctl := ctl) (name := remoteIdentityKeyBytesName) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x17c94)) hA
  have hmemcpy := framelessMemcpy_ok_at (b := img.base) (C := C) (ctl := ctl) (abs := abs)
    (name := remoteIdentityKeyBytesName) (k := num% (ls_off% "memcpy" - 0x17c94))
  have hdealloc :=
    dealloc_ok_at_norm (b :=
      img.base) (C := C) (ctl := ctl) (name := remoteIdentityKeyBytesName) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x17c94)) hA
  have hpanic :=
    panic_at_handle_error_norm (b :=
      img.base) (C :=
        C) (ctl := ctl) (abs := abs) (name := remoteIdentityKeyBytesName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x17c94))
  dsimp only [remoteIdentityKeySpec] at hrem
  dsimp only [noAllocShimSpec] at hshim
  dsimp only [framelessMemcpySpec] at hmemcpy
  wpp_init x s0
  remoteIdBytes_fetches_range (img.base) (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0 0x178
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr remoteIdentityKeyBytesName := by
    rw [hpc, Program.fnAddr_rebase, remoteIdentityKeyBytes_fnOff]
  dsimp only [tripleRatchetProgAt] at hrem hpk hshim halloc hmemcpy hdealloc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr remoteIdentityKeyBytesName = entry
  examples_hide_fetches
  rcases x with ⟨recPtr, out, G, sess, peerKey⟩
  dsimp only at *
  obtain ⟨hcap_lt63, hrem_raw⟩ := sessionRecordAt_localIk_and_remoteId hpre
  have hrem_deser : PublicKey.deserialize G.remoteIk.bytes = .ok peerKey.publicKey := by
    simpa [h] using hrem_raw
  have hcond_ne : ConditionHolds .EQ (addsPState64 G.localIk.cap 1#64) = false :=
    cond_eq_adds_false_of_lt63 hcap_lt63
  have hbs32 : peerKey.publicKey.bytes.toList.length = 32 := by simp
  obtain ⟨v0, v4, v6, v14, v22, v30, hchunks⟩ := exists_pkShiftChunks_of_length_32 hbs32
  rw [sessionRecordAt_expose_remoteId A recPtr G sess,
      stackAt_publicKeySerialize_to_remoteIdentityKey (s0.sp - 128#64)]
  subst h_1 h_2
  apply SepWPp.of_sepWP (mid := entry + 157232#64)
  wp_steps
  wp_call hrem ⟨s0.readReg64 (Reg.gpr 0#5) + 0x18#64, G.remoteIk, some peerKey, s0.sp - 104#64⟩
  dsimp only [remoteIdentityOkAt]
  have hsp103 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
  have hsp102 : s0.sp - 104#64 + 2#64 = s0.sp - 102#64 := by bv_omega
  rw [hsp103, hsp102, hchunks (s0.sp - 102#64), pkShiftChunks_sp_102 s0.sp]
  wp_steps
  refine SepWP.focus_weaken
    (shift_source_to_memRegion34 s0.sp v0 v4 v6 v14 v22 v30) (by sep_focus) ?_
  rw [memRegion_34_split_dest s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d32
  apply SepWP.exists_elim; intro d30
  apply SepWP.exists_elim; intro d22
  apply SepWP.exists_elim; intro d14
  apply SepWP.exists_elim; intro d6
  apply SepWP.exists_elim; intro d4
  apply SepWP.exists_elim; intro d0
  wp_steps
  have hdest_join :
      (((s0.sp - 104#64) ↦₃₂ v0) ∗ ((s0.sp - 100#64) ↦₁₆ v4) ∗ ((s0.sp - 98#64) ↦₆₄ v6) ∗
       ((s0.sp - 90#64) ↦₆₄ v14) ∗ ((s0.sp - 82#64) ↦₆₄ v22) ∗ ((s0.sp - 74#64) ↦₁₆ v30)) =
      ((s0.sp - 104#64) ↦ₛ peerKey.publicKey.bytes.toList) := by
    rw [← pkShiftChunks_sp_104, ← hchunks (s0.sp - 104#64)]
  refine SepWP.focus_rw hdest_join (by sep_focus) ?_
  have h3984 : s0.sp - 4256#64 = s0.sp - 128#64 - 4128#64 := by bv_omega
  rw [h3984]
  refine SepWP.focus_rw
    (stackAt_publicKeySerialize_to_remoteIdentityKey (s0.sp - 128#64)).symm (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame
    (x := ⟨s0.sp - 104#64, peerKey.publicKey⟩)
    (ret_pc := entry + 240#64) hpk
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
    (by simp only [State.spAligned, arm64_norm, hsp_sf]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hsp_sf]; rfl)
    (rfl : s0.sp - 104#64 = s0.sp - 104#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun _ _ hpan => by
      simpa only [sepConj_assoc] using
        allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm, hpost])) hpan) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm,
    *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  dsimp only [publicKeySerializeSpec]
  simp only [State.sp_setMem, State.sp_setPC, State.sp_writeReg64,
    State.trace_setMem, State.trace_setPC, State.trace_writeReg64,
    reduceCtorEq, ↓reduceIte, hsp_sf, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_1, htr1⟩ => ?_
  have htr1_s0 : sf1.trace = s0.trace := htr1.trans hpost
  have hser_ne : peerKey.publicKey.serialize ≠ [] := by simp [PublicKey.serialize]
  have hser_len : peerKey.publicKey.serialize.length = 33 := by simp [PublicKey.serialize, hbs32]
  dsimp only [boxU8Buf]
  rw [ite_eq_right_iff.mpr fun h => absurd h hser_ne]
  simp only [hser_len, sepConj_assoc]
  have hpure_focus : ∀ {prog ret s P F Q Qp} (φ : Prop),
      (φ → SepWPp prog ret s F Q Qp) → P = ⌜φ⌝ ∗ F → SepWPp prog ret s P Q Qp :=
    fun _ h hf => hf ▸ SepWPp.pure_elim h
  refine hpure_focus
    (sf1.readReg64 .x0 ≠ 0#64 ∧ 33 < 2 ^ 63)
    (fun ⟨hbox_ne, _⟩ => ?_) (by sep_focus)
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 300#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  rw [stackAt_publicKeySerialize_to_allocHook (s0.sp - 128#64)]
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_2.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_2.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x17c94))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf_1.trace =
        sf1.trace›, htr1_s0])) hm
  · have hoom64 : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    have hmem_dst : memRegion (sf_2.readReg64 (Reg.gpr 0#5)) 33 =
        memRegion (sf_2.readReg64 (Reg.gpr 0#5)) peerKey.publicKey.serialize.length := by
      rw [hser_len]
    refine SepWP.focus_rw hmem_dst (by sep_focus) ?_
    wp_call hmemcpy (sf_2.readReg64 .x0, sf1.readReg64 .x0, peerKey.publicKey.serialize)
    wp_steps
    have hmem33 : ((sf1.readReg64 .x0) ↦ₛ peerKey.publicKey.serialize) ⊢
        memRegion (sf1.readReg64 .x0) 33 := by
      simpa [hser_len] using
        pointsToBytes_entails_memRegion (sf1.readReg64 .x0) peerKey.publicKey.serialize
    refine SepWP.focus_weaken hmem33 (by sep_focus) ?_
    wp_call hdealloc (sf1.readReg64 .x0, 33, 1)
    wp_steps
    rw [show sf_3.sp = s0.sp - 128#64 by simp only [*]]
    refine SepWP.focus_rw
      (stackAt_publicKeySerialize_to_allocHook (s0.sp - 128#64)).symm (by sep_focus) ?_
    refine SepWP.focus_weaken
      (vecU8_intro_33 A (s0.readReg64 (Reg.gpr 8#5)) (sf_2.readReg64 (Reg.gpr 0#5))
        peerKey.publicKey.serialize hser_len hoom64)
      (by sep_focus) ?_
    rw [hchunks (s0.sp - 104#64), pkShiftChunks_sp_104 s0.sp,
        stackAt_publicKeySerialize_to_remoteIdentityKey (s0.sp - 128#64)]
    dsimp only [PublicKey.serialize, djbType]
    wp_done

theorem remoteIdentityKeyBytes_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (img.base + remoteIdentityKeyBytesOff)
      (remoteIdentityKeyBytesSpec A img) := by
  have hfn : (tripleRatchetProgAt img.base C ctl abs).fnAddr remoteIdentityKeyBytesName =
      img.base + remoteIdentityKeyBytesOff := by
    rw [tripleRatchetProgAt, Program.fnAddr_rebase, remoteIdentityKeyBytes_fnOff]
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg, ← hfn]
  exact remoteIdentityKeyBytes_sp2_ok img C A ctl abs himg hA

end CryptoVerification.E2E.Pqxdh.WireEntries
