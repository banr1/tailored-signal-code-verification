/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec

/-!
# Entry and Exit Separation-Logic Bridges for `decrypt_signal`

Unpacks `storesAt` into the session and identity store kits alongside the five untouched `Dir`
fields, and relates `apiDecResultAt` to `decResAt` when no store error occurs.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes

/-- The five `Stores` directory fields (`signed`, `kyber.oneTime`, `kyber.lastResort`, `oneTime`,
`pub`) untouched by `decrypt_signal`. -/
def storesOther5At (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) : SepProp :=
  dirAt A (a + 0x50#64) g.signed ∗ dirAt A (a + 0x78#64) g.kyber.oneTime ∗
    dirAt A (a + 0xa0#64) g.kyber.lastResort ∗ dirAt A (a + 0xc8#64) g.oneTime ∗
    dirAt A (a + 0x118#64) g.pub

private theorem perm_unpack_8 {d0 d1 d2 d3 d4 d5 d6 d7 : SepProp} :
    d0 ∗ d1 ∗ d2 ∗ d3 ∗ d4 ∗ d5 ∗ d6 ∗ d7 =
      d6 ∗ (d0 ∗ d1) ∗ (d2 ∗ d3 ∗ d4 ∗ d5 ∗ d7) := by
  ac_rfl

private theorem perm_repack_8 {p1 p2 : Prop} {d0 d1 d2 d3 d4 d5 d6 d7 : SepProp} :
    (⌜p1⌝ ∗ d6) ∗ (⌜p2⌝ ∗ d0 ∗ d1) ∗ (d2 ∗ d3 ∗ d4 ∗ d5 ∗ d7) =
      ⌜p1⌝ ∗ (⌜p2⌝ ∗ (d0 ∗ d1 ∗ d2 ∗ d3 ∗ d4 ∗ d5 ∗ d6 ∗ d7)) := by
  ac_rfl

theorem storesAt_unpack_dec (A : RustAlloc) (a : BitVec 64) (g : StoresGhost)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (hsess : CliSessInv cliIo.rd F0 cliWrOk Scope peer g.sessions)
    (hid : CliIdInv cliIo.rd F0 cliWrOk peer g.identity) :
    storesAt A a g ⊢
      cliSessStoreAt A cliIo.rd F0 cliWrOk Scope peer (a + 0xf0#64) g.sessions ∗
        cliIdStoreAt A cliIo.rd F0 cliWrOk peer a g.identity ∗
        storesOther5At A a g := by
  unfold storesAt cliSessStoreAt cliIdStoreAt storesOther5At
  rw [perm_unpack_8]
  exact sepConj_mono
    (Entails.pure_right hsess (Entails.refl _))
    (sepConj_mono_left (Entails.pure_right hid (Entails.refl _)))

theorem storesAt_repack_dec (A : RustAlloc) (a : BitVec 64) (g0 g' : StoresGhost)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (hsigned : g'.signed = g0.signed)
    (hkot : g'.kyber.oneTime = g0.kyber.oneTime)
    (hklr : g'.kyber.lastResort = g0.kyber.lastResort)
    (hot : g'.oneTime = g0.oneTime)
    (hpub : g'.pub = g0.pub) :
    cliSessStoreAt A cliIo.rd F0 cliWrOk Scope peer (a + 0xf0#64) g'.sessions ∗
      cliIdStoreAt A cliIo.rd F0 cliWrOk peer a g'.identity ∗
      storesOther5At A a g0 ⊢
      storesAt A a g' := by
  unfold storesAt cliSessStoreAt cliIdStoreAt storesOther5At
  rw [← hsigned, ← hkot, ← hklr, ← hot, ← hpub, perm_repack_8]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  exact Entails.refl _

private theorem speAt_owned_dec (A : RustAlloc) (fn : List (BitVec 8)) (a : BitVec 64)
    (e : SignalProtocolError) :
    speAt A fn a e ⊢ ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A a k :=
  Entails.sepExists_right (.proto fn e) (Entails.refl _)

private theorem recordResultAt_err_owned_dec (A : RustAlloc) (r : BitVec 64)
    (e : SignalProtocolError) :
    LibsignalTripleRatchet.recordResultAt A r (.error e) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k := by
  cases e with
  | invalidMessage t rsn =>
    cases rsn with
    | decryptionFailed =>
      exact Entails.sepExists_right (.proto (utf8 "decrypt") (.invalidMessage t .badCiphertext))
        (sepConj_mono_right (sepConj_mono_left
          (Entails.sepExists_intro LibsignalTripleRatchet.decryptionFailedStr)))
    | tooFarInFuture => exact speAt_owned_dec A (utf8 "decrypt") r (.invalidMessage t .tooFarInFuture)
    | macFailed => exact speAt_owned_dec A (utf8 "decrypt") r (.invalidMessage t .macFailed)
    | pqRatchet => exact speAt_owned_dec A (utf8 "decrypt") r (.invalidMessage t .pqRatchet)
    | badCiphertext => exact speAt_owned_dec A (utf8 "decrypt") r (.invalidMessage t .badCiphertext)
  | invalidState => exact speAt_owned_dec A (utf8 "decrypt") r .invalidState
  | ciphertextMessageTooShort n =>
    exact speAt_owned_dec A (utf8 "decrypt") r (.ciphertextMessageTooShort n)
  | legacyCiphertextVersion v =>
    exact speAt_owned_dec A (utf8 "decrypt") r (.legacyCiphertextVersion v)
  | unrecognizedCiphertextVersion v =>
    exact speAt_owned_dec A (utf8 "decrypt") r (.unrecognizedCiphertextVersion v)
  | invalidProtobufEncoding => exact speAt_owned_dec A (utf8 "decrypt") r .invalidProtobufEncoding
  | noKeyTypeIdentifier => exact speAt_owned_dec A (utf8 "decrypt") r .noKeyTypeIdentifier
  | badKeyType t => exact speAt_owned_dec A (utf8 "decrypt") r (.badKeyType t)
  | badKeyLength n => exact speAt_owned_dec A (utf8 "decrypt") r (.badKeyLength n)
  | invalidKeyAgreement => exact speAt_owned_dec A (utf8 "decrypt") r .invalidKeyAgreement
  | invalidSessionStructure rsn =>
    exact speAt_owned_dec A (utf8 "decrypt") r (.invalidSessionStructure rsn)
  | duplicatedMessage i c => exact speAt_owned_dec A (utf8 "decrypt") r (.duplicatedMessage i c)
  | panic => exact speAt_owned_dec A (utf8 "decrypt") r .panic

theorem apiDecResultAt_entails_decResAt (A : RustAlloc) (r : BitVec 64)
    (res : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (hnst : res ≠ .error (.store ())) :
    apiDecResultAt A r res ⊢ decResAt A r res := by
  cases res with
  | ok pt => exact Entails.refl _
  | error e =>
    cases e with
    | protocol e' => exact recordResultAt_err_owned_dec A r e'
    | sessionNotFound addr op =>
      exact Entails.sepExists_right (.sessionNotFound addr op) (Entails.refl _)
    | untrustedIdentity addr =>
      exact Entails.sepExists_right (.untrustedIdentity addr) (Entails.refl _)
    | store u => cases u; exact absurd rfl hnst
    | panic => exact Entails.sepExists_right (.proto [] .panic) (Entails.refl _)

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
