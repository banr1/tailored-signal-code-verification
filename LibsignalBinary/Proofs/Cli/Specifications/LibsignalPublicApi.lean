/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs

/-!
# CLI Public API Entry Symbol and `decrypt_signal` Specification

Defines `encryptWithStoresName` and the machine-level specification `decryptSignalSpec` for
`signal_session_ratchet::decrypt_signal` on `Coins` in the CLI session image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol names -/

/-- `message_encrypt::<HookRng>` on `dyn` stores (`(ls_off% "signal_session_ratchet::encrypt")`, 1009 instructions; `src/lib.rs`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName : String := "libsignal_cli_ratchet::encrypt"

set_option linter.unusedVariables false in
/-- **The binding spec of `session_message_decrypt_signal`** (`message_decrypt_signal`,
`session_management.rs:297–354`, on the hook stores). Normal return: for some store answers (those
in the trace), `x.model` does not panic, the trace grew by `x.model`'s calls with their answers,
the sret holds `x.model`'s result (`apiDecResultAt`), the borrowed message and addresses are
unchanged, and the tape advanced by `draws`. Panic only on a failed allocation, or (with the loaded
record in the trace) when `x.model` panics or `spqr::recv` panics on the loaded session's inputs.

On a panic, the guarantee is only that the trace extends `s0 ++ [load]`. "Nothing stored on
panic" is **not** guaranteed, because the underlying panic contracts
(`CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec`, the spqr hooks, `format_inner`,
the allocation-panic hooks) allow arbitrary trace growth. The message and the two addresses are
separate blocks (`∗`): aliased borrowed inputs are out of scope. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.decryptSignalSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) : Spec DecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x8 = x.ret ∧ entryStack ≤ s.sp.toNat⌝ ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
        logOff img ∗ stackAt s.sp entryStack ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            sf.trace = s0.trace ++ (x.model C S uuidParse answers).2.map (storeEvent encRecord answers)⌝ ∗
          apiDecResultAt A x.ret (x.model C S uuidParse answers).1 ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C answers) ∗
          logOff img ∗ stackAt s0.sp entryStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              s0.trace ++ [loadEvent encRecord x.rem.val answers.loadSession] <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.recvPanics S answers))⌝ ∗
          anyHeap }
    img

end CryptoVerification.LibsignalPublicApi
