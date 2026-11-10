/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `VmPreserved` Contract for `PrivateKey::derive_public_key_bytes` (Block `200`)

Verifies `<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes` against its
`VmPreserved`-strengthened specification on `tripleRatchetProgAt` and under `[LibsignalPlacement]`
(Block `200`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto PubKeyFn)
open CryptoVerification (
  LibsignalPlacement blkPC_200 blkPl_200 libsignalSessionCode lsPubFromSecretSym
  ls_hook_ok_of_mem lsρ
)
open CryptoVerification.LibsignalTripleRatchet (
  derivePublicKeyBytesName pubFromSecretName
  subroutine_ok_kit_of_trTrap trTrapProgAt trapsOnly_trTrap_kit tripleRatchetProgAt
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  derivePublicKeyBytesSpec derivePublicKeyBytesStackSpec derivePublicKeyBytesStack_of_spec
  pubFromSecret_ok_at_of_contract pubFromSecret_ok_at_trap
)

attribute [local irreducible] Program.fetch Program.externAt?

theorem derive_public_key_bytes_ok_of_contract_stack {b : BitVec 64} {pubKey : PubKeyFn}
    {H : String → Option (State → State)} (hookStack : Nat := 0)
    (hpub : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr pubFromSecretName)
      (derivePublicKeyBytesStackSpec pubKey hookStack)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr derivePublicKeyBytesName)
      (derivePublicKeyBytesStackSpec pubKey hookStack) := by
  have hfetch : (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr derivePublicKeyBytesName) =
      some (.b (bv% (ls_off% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from" - ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"))) := by
    rw [show (libsignalSessionCode.rebase b H).fnAddr derivePublicKeyBytesName = b + bv% (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes") by
      simp only [Program.fnAddr, arm64_norm]]
    exact (ls_rebase_fetch% CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes")) b H
  have hstub := pubFromSecret_ok_at_of_contract hpub
    (name := derivePublicKeyBytesName)
    (k := libsignalSessionCode.fnOff pubFromSecretName -
      libsignalSessionCode.fnOff derivePublicKeyBytesName)
  exact subroutine_ok_of_b hfetch (by simp only [arm64_norm]) rfl
    (by intros; rfl) hstub

theorem derive_public_key_bytes_ok_of_contract {b : BitVec 64} {pubKey : PubKeyFn}
    {H : String → Option (State → State)}
    (hpub : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr pubFromSecretName)
      (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr derivePublicKeyBytesName)
      (derivePublicKeyBytesSpec pubKey) := by
  have hfetch : (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr derivePublicKeyBytesName) =
      some (.b (bv% (ls_off% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from" - ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"))) := by
    rw [show (libsignalSessionCode.rebase b H).fnAddr derivePublicKeyBytesName = b + bv% (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes") by
      simp only [Program.fnAddr, arm64_norm]]
    exact (ls_rebase_fetch% CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes")) b H
  have hstub := pubFromSecret_ok_at_of_contract hpub
    (name := derivePublicKeyBytesName)
    (k := libsignalSessionCode.fnOff pubFromSecretName -
      libsignalSessionCode.fnOff derivePublicKeyBytesName)
  exact subroutine_ok_of_b hfetch (by simp only [arm64_norm]) rfl
    (by intros; rfl) hstub

theorem derive_public_key_bytes_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr derivePublicKeyBytesName)
      (derivePublicKeyBytesSpec C.pubKey) := by
  apply derive_public_key_bytes_ok_of_contract
  have h0 := pubFromSecret_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := pubFromSecretName) (k := 0)
  rw [BitVec.add_zero] at h0
  exact h0

/-- `<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes` meets
`derivePublicKeyBytesSpec C.pubKey` on `tripleRatchetProgAt`. -/
theorem derive_public_key_bytes_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr derivePublicKeyBytesName)
      (derivePublicKeyBytesSpec C.pubKey) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr derivePublicKeyBytesName]
  exact subroutine_ok_kit_of_trTrap (derive_public_key_bytes_ok_trap (b := b) (C := C) (abs := abs))

theorem derive_public_key_bytes_ok_of_contract_stack_inImage {img : Obj.Image} {pubKey : PubKeyFn}
    {H : String → Option (State → State)} (hookStack : Nat := 0)
    (hpub : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr pubFromSecretName)
      ((derivePublicKeyBytesStackSpec pubKey hookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr derivePublicKeyBytesName)
      ((derivePublicKeyBytesStackSpec pubKey hookStack).inImage img) := by
  have hfetch : (libsignalSessionCode.rebase img.base H).fetch
      ((libsignalSessionCode.rebase img.base H).fnAddr derivePublicKeyBytesName) =
      some (.b (bv% (ls_off% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from" - ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"))) := by
    rw [show (libsignalSessionCode.rebase img.base H).fnAddr derivePublicKeyBytesName = img.base + bv% (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes") by
      simp only [Program.fnAddr, arm64_norm]]
    exact (ls_rebase_fetch% CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes")) img.base H
  have hstub := pubFromSecret_ok_at_of_contract hpub
    (name := derivePublicKeyBytesName)
    (k := libsignalSessionCode.fnOff pubFromSecretName -
      libsignalSessionCode.fnOff derivePublicKeyBytesName)
  exact subroutine_ok_of_b hfetch (by simp only [arm64_norm]) rfl
    (by intros; simp only [Spec.inImage, Obj.Image.frozenLoaded_iff]; rfl) hstub

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `200`) -/

theorem derive_public_key_bytes_placed_ok_of_contract_stack [LibsignalPlacement]
    {pubKey : PubKeyFn} {H : String → Option (State → State)} (hookStack : Nat := 0)
    (hpub : subroutine_ok ((blkPC_200).rebase (blkPl_200).base H)
      (lsρ lsPubFromSecretSym)
      (derivePublicKeyBytesStackSpec pubKey hookStack)) :
    subroutine_ok ((blkPC_200).rebase (blkPl_200).base H) (blkPl_200).base
      (derivePublicKeyBytesStackSpec pubKey hookStack) := by
  have hfetch : ((blkPC_200).rebase (blkPl_200).base H).fetch
      ((blkPl_200).base + BitVec.ofNat 64 0) =
      some (.b ((blkPl_200).ρ lsPubFromSecretSym - (blkPl_200).base - BitVec.ofNat 64 0)) := by
    simp only [arm64_norm]
  rw [BitVec.add_zero] at hfetch
  exact subroutine_ok_of_b hfetch (by simp only [arm64_norm, wp_norm]) rfl
    (by intros; rfl) hpub

theorem derive_public_key_bytes_placed_ok_of_contract [LibsignalPlacement]
    {pubKey : PubKeyFn} {H : String → Option (State → State)}
    (hpub : subroutine_ok ((blkPC_200).rebase (blkPl_200).base H)
      (lsρ lsPubFromSecretSym)
      (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok ((blkPC_200).rebase (blkPl_200).base H) (blkPl_200).base
      (derivePublicKeyBytesSpec pubKey) := by
  have hfetch : ((blkPC_200).rebase (blkPl_200).base H).fetch
      ((blkPl_200).base + BitVec.ofNat 64 0) =
      some (.b ((blkPl_200).ρ lsPubFromSecretSym - (blkPl_200).base - BitVec.ofNat 64 0)) := by
    simp only [arm64_norm]
  rw [BitVec.add_zero] at hfetch
  exact subroutine_ok_of_b hfetch (by simp only [arm64_norm, wp_norm]) rfl
    (by intros; rfl) hpub

/-- Relocatable `<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes`
(Block `200`) meets `derivePublicKeyBytesSpec pubKey` when `H` satisfies `HookSat` at
`lsPubFromSecretSym`. -/
theorem derive_public_key_bytes_placed_ok [LibsignalPlacement]
    {pubKey : PubKeyFn} {H : String → Option (State → State)}
    (hpub : HookSat H lsPubFromSecretSym (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok ((blkPC_200).rebase (blkPl_200).base H) (blkPl_200).base
      (derivePublicKeyBytesSpec pubKey) :=
  derive_public_key_bytes_placed_ok_of_contract (ls_hook_ok_of_mem hpub)

theorem derive_public_key_bytes_stack_placed_ok [LibsignalPlacement]
    {pubKey : PubKeyFn} {H : String → Option (State → State)} (hookStack : Nat := 0)
    (hpub : HookSat H lsPubFromSecretSym (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok ((blkPC_200).rebase (blkPl_200).base H) (blkPl_200).base
      (derivePublicKeyBytesStackSpec pubKey hookStack) :=
  derivePublicKeyBytesStack_of_spec hookStack (derive_public_key_bytes_placed_ok hpub)

end LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget
