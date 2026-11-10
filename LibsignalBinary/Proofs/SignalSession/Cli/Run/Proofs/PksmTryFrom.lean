/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem

/-!
# `PreKeySignalMessage::try_from` Subroutine Proof

Proves `cliPksmTryFrom_ok`: `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` meets
`pksmSlotSpec A img S` on every input byte slice whenever `S.pksmParse = Pksm.pksmParse`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli.RunCompose

/-- `PreKeySignalMessage::try_from` meets the all-inputs slot contract
`pksmSlotSpec` at any `S` whose parse answer is `Pksm.pksmParse`. -/
theorem cliPksmTryFrom_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext)
    (hS : ∀ b, S.pksmParse b = Pksm.pksmParse b) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S) := by
  exact PksmWire.pksmSlotSpec_of_preKeyTryFromOk hS (PksmWire.preKeyTryFrom_ok himg hA)

end CryptoVerification.SignalSession.Cli.RunProofs
