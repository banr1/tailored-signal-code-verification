/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem

/-!
# Error-Result to Owned `SignalProtocolError` Bridges

Separation-logic entailments converting the `Err` arms of `run`'s callee result layouts
(`apiEncResultAt`, `decResAt`, `initResAt`, `pksmResAt`, `signalMessageResultAt`, and
`kemDeserResAt`) into `RunDrop.speOwnedAt`, enabling `dropSpeOwnedSpec` to release the error value
and rejoin the caller's stack slot.

Note that `e ≠ .store ()` suffices on `ApiError AddrVal Unit` because `apiErrAt A _ .panic =
⌜False⌝`, and `recordResultAt_err_owned` witnesses `.invalidMessage t .badCiphertext` on the
`.decryptionFailed` arm since both share the `speWord 24` tag, message-type byte at `+32`, and
owned `Vec<u8>` at `+8`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose

/-! ## Underlying `SignalProtocolError`, `recordResultAt`, and `apiErrAt` bridges -/

theorem speAt_owned (A : RustAlloc) (fn : List (BitVec 8)) (a : BitVec 64)
    (e : SignalProtocolError) :
    speAt A fn a e ⊢ ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A a k :=
  Entails.sepExists_right (.proto fn e) (Entails.refl _)

/-- Converts `recordResultAt A r (.error e)` into an owned 48-byte `SignalProtocolError` at `r`,
witnessing `.invalidMessage t .badCiphertext` on `.decryptionFailed`. -/
theorem recordResultAt_err_owned (A : RustAlloc) (r : BitVec 64) (e : SignalProtocolError) :
    LibsignalTripleRatchet.recordResultAt A r (.error e) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k := by
  cases e with
  | invalidMessage t rsn =>
    cases rsn with
    | decryptionFailed =>
      exact Entails.sepExists_right (.proto (utf8 "decrypt") (.invalidMessage t .badCiphertext))
        (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro decryptionFailedStr)))
    | tooFarInFuture => exact speAt_owned A (utf8 "decrypt") r (.invalidMessage t .tooFarInFuture)
    | macFailed => exact speAt_owned A (utf8 "decrypt") r (.invalidMessage t .macFailed)
    | pqRatchet => exact speAt_owned A (utf8 "decrypt") r (.invalidMessage t .pqRatchet)
    | badCiphertext => exact speAt_owned A (utf8 "decrypt") r (.invalidMessage t .badCiphertext)
  | invalidState => exact speAt_owned A (utf8 "decrypt") r .invalidState
  | ciphertextMessageTooShort n =>
    exact speAt_owned A (utf8 "decrypt") r (.ciphertextMessageTooShort n)
  | legacyCiphertextVersion v =>
    exact speAt_owned A (utf8 "decrypt") r (.legacyCiphertextVersion v)
  | unrecognizedCiphertextVersion v =>
    exact speAt_owned A (utf8 "decrypt") r (.unrecognizedCiphertextVersion v)
  | invalidProtobufEncoding => exact speAt_owned A (utf8 "decrypt") r .invalidProtobufEncoding
  | noKeyTypeIdentifier => exact speAt_owned A (utf8 "decrypt") r .noKeyTypeIdentifier
  | badKeyType t => exact speAt_owned A (utf8 "decrypt") r (.badKeyType t)
  | badKeyLength n => exact speAt_owned A (utf8 "decrypt") r (.badKeyLength n)
  | invalidKeyAgreement => exact speAt_owned A (utf8 "decrypt") r .invalidKeyAgreement
  | invalidSessionStructure rsn =>
    exact speAt_owned A (utf8 "decrypt") r (.invalidSessionStructure rsn)
  | duplicatedMessage i c => exact speAt_owned A (utf8 "decrypt") r (.duplicatedMessage i c)
  | panic => exact speAt_owned A (utf8 "decrypt") r .panic

/-- Converts any non-`store` `apiErrAt A a e` into an owned 48-byte `SignalProtocolError` at `a`. -/
theorem apiErrAt_owned (A : RustAlloc) (a : BitVec 64)
    (e : ApiError AddrVal Unit) (he : e ≠ .store ()) :
    apiErrAt A a e ⊢ ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A a k := by
  cases e with
  | sessionNotFound addr op =>
    exact Entails.sepExists_right (.sessionNotFound addr op) (Entails.refl _)
  | untrustedIdentity addr =>
    exact Entails.sepExists_right (.untrustedIdentity addr) (Entails.refl _)
  | store u => cases u; exact absurd rfl he
  | protocol _ => exact Entails.sepExists_right (.proto [] .panic) (Entails.refl _)
  | panic => exact Entails.sepExists_right (.proto [] .panic) (Entails.refl _)

/-! ## Wrapper and `PreKeySignalMessage` error bridges -/

theorem slotOut_err_ne_store {α : Type} {ans : SlotAns α} {g' : StoresGhost}
    {e : ApiError AddrVal Unit} {s0 sf : State}
    (h : slotOut ans g' (.error e) s0 sf) : e ≠ .store () :=
  fun he => h.2.1 (congrArg Except.error he)

/-- Decomposes `apiEncResultAt A r (.error e)` (`e ≠ .store ()`) into `errTag` at `r`, an owned
48-byte `SignalProtocolError` at `r + 8`, and the 192-byte tail at `r + 56`. -/
theorem apiEncResultAt_err_owned (A : RustAlloc) (r : BitVec 64)
    (e : ApiError AddrVal Unit) (he : e ≠ .store ()) :
    apiEncResultAt A r (.error e) ⊢
      (r ↦₆₄ errTag) ∗ (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (r + 8#64) k) ∗
        memRegion (r + 56#64) 192 := by
  cases e with
  | protocol e' =>
    exact sepConj_mono_right (sepConj_mono_left (speAt_owned A (utf8 "encrypt") (r + 8#64) e'))
  | sessionNotFound addr op =>
    exact sepConj_mono_right (sepConj_mono_left
      (apiErrAt_owned A (r + 8#64) (.sessionNotFound addr op) he))
  | untrustedIdentity addr =>
    exact sepConj_mono_right (sepConj_mono_left
      (apiErrAt_owned A (r + 8#64) (.untrustedIdentity addr) he))
  | store u => cases u; exact absurd rfl he
  | panic =>
    exact sepConj_mono_right (sepConj_mono_left (apiErrAt_owned A (r + 8#64) .panic he))

theorem apiDecResultAt_err_owned (A : RustAlloc) (r : BitVec 64)
    (e : ApiError AddrVal Unit) (he : e ≠ .store ()) :
    apiDecResultAt A r (.error e) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k := by
  cases e with
  | protocol e' => exact recordResultAt_err_owned A r e'
  | sessionNotFound addr op => exact apiErrAt_owned A r (.sessionNotFound addr op) he
  | untrustedIdentity addr => exact apiErrAt_owned A r (.untrustedIdentity addr) he
  | store u => cases u; exact absurd rfl he
  | panic => exact apiErrAt_owned A r .panic he

set_option linter.unusedVariables false in
theorem decResAt_err_owned (A : RustAlloc) (r : BitVec 64)
    (e : ApiError AddrVal Unit) (he : e ≠ .store ()) :
    decResAt A r (.error e) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k :=
  Entails.refl _

set_option linter.unusedVariables false in
theorem initResAt_err_owned (A : RustAlloc) (r : BitVec 64)
    (e : ApiError AddrVal Unit) (he : e ≠ .store ()) :
    initResAt A r (.error e) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k :=
  Entails.refl _

/-- Decomposes `pksmResAt A r none` into `errTag` at `r`, an owned 48-byte `SignalProtocolError` at
`r + 8`, the 192-byte tail at `r + 56`, and `anyHeap`. -/
theorem pksmResAt_err_owned (A : RustAlloc) (r : BitVec 64) :
    pksmResAt A r none ⊢
      (r ↦₆₄ errTag) ∗ (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (r + 8#64) k) ∗
        memRegion (r + 56#64) 192 ∗ anyHeap :=
  sepConj_mono_right (sepConj_mono_left
    (Entails.sepExists_elim fun fn => Entails.sepExists_elim fun e =>
      speAt_owned A fn (r + 8#64) e))

/-! ## Wire-decoder, KEM-deserializer, and sret-slot rejoin bridges -/

/-- Decomposes `signalMessageResultAt A fn r (.error e)` into `errTag` at `r`, an owned 48-byte
`SignalProtocolError` at `r + 8`, and the 64-byte tail at `r + 56`. -/
theorem msgResultAt_err_owned (A : RustAlloc) (fn : List (BitVec 8)) (r : BitVec 64)
    (e : SignalProtocolError) :
    signalMessageResultAt A fn r (.error e) ⊢
      (r ↦₆₄ errTag) ∗ (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (r + 8#64) k) ∗
        memRegion (r + 56#64) 64 :=
  sepConj_mono_right (sepConj_mono_left (speAt_owned A fn (r + 8#64) e))

/-- Pairs an error `kemDeserResAt A r d` (24 bytes) with `memRegion (r + 24) 24` to form an owned
48-byte `SignalProtocolError` at `r`. -/
theorem kemDeserResAt_err_owned (A : RustAlloc) (r : BitVec 64) (d : KemDeserResult)
    (hd : ∀ key, d ≠ .ok key) :
    (kemDeserResAt A r d ∗ memRegion (r + 24#64) 24) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k := by
  cases d with
  | ok key => exact absurd rfl (hd key)
  | noKeyType =>
    have hmerge : memRegion (r + 8#64) 16 ∗ memRegion (r + 24#64) 24 = memRegion (r + 8#64) 40 := by
      rw [show r + 24#64 = (r + 8#64) + 16#64 from by rw [BitVec.add_assoc]; rfl]
      exact (ProofLib.memRegion_split (r + 8#64) 16 24 (by omega)).symm
    rw [kemDeserResAt, sepConj_assoc, hmerge]
    exact Entails.sepExists_right (.proto [] .noKeyTypeIdentifier) (Entails.refl _)
  | badType t =>
    have hmerge1 : memRegion (r + 9#64) 15 ∗ memRegion (r + 24#64) 24 = memRegion (r + 9#64) 39 := by
      rw [show r + 24#64 = (r + 9#64) + 15#64 from by rw [BitVec.add_assoc]; rfl]
      exact (ProofLib.memRegion_split (r + 9#64) 15 24 (by omega)).symm
    have hcell : ((r + 8#64) ↦₈ t) ∗ memRegion (r + 9#64) 39 ⊢ memRegion (r + 8#64) 40 := by
      rw [show r + 9#64 = (r + 8#64) + 1#64 from by rw [BitVec.add_assoc]; rfl,
          show (40 : Nat) = 1 + 39 from rfl,
          ProofLib.memRegion_split (r + 8#64) 1 39 (by omega)]
      exact sepConj_mono_left (pointsTo8_entails_memRegion (r + 8#64) t)
    rw [kemDeserResAt, sepConj_assoc, sepConj_assoc, hmerge1]
    exact Entails.sepExists_right .badKemKeyType (sepConj_mono_right hcell)
  | badLength n =>
    have hmerge1 : memRegion (r + 16#64) 8 ∗ memRegion (r + 24#64) 24 = memRegion (r + 16#64) 32 := by
      rw [show r + 24#64 = (r + 16#64) + 8#64 from by rw [BitVec.add_assoc]; rfl]
      exact (ProofLib.memRegion_split (r + 16#64) 8 24 (by omega)).symm
    have hcell :
        ((r + 8#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (r + 16#64) 32 ⊢ memRegion (r + 8#64) 40 := by
      rw [show r + 16#64 = (r + 8#64) + 8#64 from by rw [BitVec.add_assoc]; rfl]
      exact ProofLib.memRegion_cons (r + 8#64) (BitVec.ofNat 64 n) (n := 40) (by omega) (by omega)
    rw [kemDeserResAt, sepConj_assoc, sepConj_assoc, hmerge1]
    exact Entails.sepExists_right .badKemKeyLength (sepConj_mono_right hcell)

theorem sret248_rejoin (r tag : BitVec 64) :
    ((r ↦₆₄ tag) ∗ memRegion (r + 8#64) 48 ∗ memRegion (r + 56#64) 192) ⊢ memRegion r 248 := by
  have hmerge : memRegion (r + 8#64) 48 ∗ memRegion (r + 56#64) 192 = memRegion (r + 8#64) 240 := by
    rw [show r + 56#64 = (r + 8#64) + 48#64 from by rw [BitVec.add_assoc]; rfl]
    exact (ProofLib.memRegion_split (r + 8#64) 48 192 (by omega)).symm
  rw [hmerge]
  exact ProofLib.memRegion_cons r tag (n := 248) (by omega) (by omega)

theorem sret120_rejoin (r tag : BitVec 64) :
    ((r ↦₆₄ tag) ∗ memRegion (r + 8#64) 48 ∗ memRegion (r + 56#64) 64) ⊢ memRegion r 120 := by
  have hmerge : memRegion (r + 8#64) 48 ∗ memRegion (r + 56#64) 64 = memRegion (r + 8#64) 112 := by
    rw [show r + 56#64 = (r + 8#64) + 48#64 from by rw [BitVec.add_assoc]; rfl]
    exact (ProofLib.memRegion_split (r + 8#64) 48 64 (by omega)).symm
  rw [hmerge]
  exact ProofLib.memRegion_cons r tag (n := 120) (by omega) (by omega)

end CryptoVerification.SignalSession.Cli.RunProofs
