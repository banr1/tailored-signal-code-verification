/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.Chain
import LibsignalBinary.Proofs.FnOffEq

/-!
# Cross-Directory Callee Discharges for the CLI Triple Ratchet

Connects `drop_glue<Chain>` and `ChainKey::message_keys` proofs to `Stage2Contracts`,
`TripleRatchetHooks`, and `AllocContractsX` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Glue

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalTripleRatchet

/-! ## Callee Discharges -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Glue.drop_chain_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName)
      (Getters.dropChainSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_ok_ext hH.toAllocContracts

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Glue.drop_chain_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName)
      (Getters.dropChainSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_ok_trap hH.alloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Glue.drop_chain_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName)
      (Getters.dropChainSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Glue.drop_chain_ok_of_tripleRatchetHooks_trap hH)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Glue.drop_chain_ok_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName)
      ((Getters.dropChainSpecX A).inImage img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_ok_x hA

/-- `ChainKey::message_keys` meets `MessageKeysOkX img F A ext` (`messageKeysStackX = 20480` B)
from `AllocContractsX` and `Stage1X.hmacSpecX` (`2048 + extHookStack = 18432` B). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Glue.messageKeys_ok_of_hmacX
    {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hhmac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "libsignal_protocol::crypto::hmac_sha256")
      ((hmacSpecWithStack F (2048 + extHookStack)).inImage img)) :
    MessageKeysOkX img F A ext := by
  have hhmac_at : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName +
        bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys"))
      ((hmacSpecWithStack F (2048 + extHookStack)).inImage img) := by
    have haddr :
        (tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName +
          bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys") =
        (tripleRatchetProgAtExt img.base ext).fnAddr "libsignal_protocol::crypto::hmac_sha256" := by
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys"),
        (ls_lemma% fnOff "libsignal_protocol::crypto::hmac_sha256"), BitVec.add_assoc]
      rfl
    rw [haddr]
    exact hhmac
  exact messageKeys_ok_of_hooks_gen
    (totalStack := messageKeysStackX) (midStack := 2048 + extHookStack) (padTop := 1968)
    (hmacStack := 2048 + extHookStack) (hmacPad := 0)
    (allocStack := extHookStack) (allocPad := 2048)
    (by decide) (by decide) (by decide) (by decide)
    hhmac_at
    (shim_opt_of_x hA (by fnoff_eq))
    (alloc_opt_of_x hA (by fnoff_eq))
    (panic_at_handle_error_ext img.base ext messageKeysName _ (by fnoff_eq))

end CryptoVerification.LibsignalTripleRatchet.Glue
