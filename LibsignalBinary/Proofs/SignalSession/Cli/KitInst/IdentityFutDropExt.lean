/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base

/-!
# External-Hook-Generic `cliIdFutDrop` Contract

`drop_glue::<<IdentityFiles as IdentityKeyStore>::get_identity::{closure#0}>` compiles to a
single `ret` instruction in `.text`, so it satisfies `futDropSpec` on
`tripleRatchetProgAtExt b ext` with no external-hook assumptions on `ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")

set_option maxHeartbeats 1600000 in
/-- `drop_glue::<…get_identity::{closure#0}>` (a single `ret`) satisfies `futDropSpec` at its
`fnAddr` for arbitrary `ext`. -/
theorem cliIdFutDrop_fnAddr_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr cliIdFutDropName) futDropSpec := by
  simp only [futDropSpec]
  have hfn : libsignalSessionCode.fnOff cliIdFutDropName = num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
    cliIdFutDrop_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdFutDropBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) 4
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `cliIdFutDropOff` satisfies `futDropSpec` on `tripleRatchetProgAtExt b ext` for arbitrary
`ext`. -/
theorem cliIdFutDrop_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext) (b + cliIdFutDropOff) futDropSpec := by
  have h := cliIdFutDrop_fnAddr_ok_ext (b := b) (ext := ext)
  have hfn : libsignalSessionCode.fnOff cliIdFutDropName = num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
    cliIdFutDrop_fnOff
  rwa [show (tripleRatchetProgAtExt b ext).fnAddr cliIdFutDropName = b + cliIdFutDropOff by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, cliIdFutDropOff]] at h

theorem cliIdentityStoreSpec_trustFutDrop_ext {A : RustAlloc} {b : BitVec 64} {rd : ReadRule}
    {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).trustFutDropOff)
      futDropSpec :=
  cliIdFutDrop_ok_ext

theorem cliIdentityStoreSpec_saveFutDrop_ext {A : RustAlloc} {b : BitVec 64} {rd : ReadRule}
    {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (b + (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).saveFutDropOff)
      futDropSpec :=
  cliIdFutDrop_ok_ext

/-! ## Specialization to `tripleRatchetProgAt` -/

section
variable {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
  {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}

example :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr cliIdFutDropName) futDropSpec :=
  cliIdFutDrop_fnAddr_ok_ext

example :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + cliIdFutDropOff) futDropSpec :=
  cliIdFutDrop_ok_ext

example :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).trustFutDropOff)
      futDropSpec :=
  cliIdentityStoreSpec_trustFutDrop_ext

example :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).saveFutDropOff)
      futDropSpec :=
  cliIdentityStoreSpec_saveFutDrop_ext

end

end CryptoVerification.SignalSession.Cli.KitInst
