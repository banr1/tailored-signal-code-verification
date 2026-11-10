/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrap

/-!
# `try_decrypt_with_state::<Coins>` Fixed Callee Discharge

Proves `cliTryDecryptPqV1_ok` on `tripleRatchetProgAtExt img.base (cliExterns W)` at
`E2E.HooksE.A0` and `spqrV1 W.C.F W.Q.K`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession

/-- `try_decrypt_with_state::<Coins>` meets `tryDecryptSpecTPTight` on
`tripleRatchetProgAtExt img.base (cliExterns W)` at `E2E.HooksE.A0` and `spqrV1 W.C.F W.Q.K`. -/
theorem cliTryDecryptPqV1_ok (W : CliHooks) (ctl : BitVec 64) {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight W.C E2E.HooksE.A0 ctl
        uuidTryParse (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_cli W ctl img himg

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
