/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPack
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PackPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` Packing Helpers and Full `PreKeySignalMessage::try_from` Exports

Re-exports packing/regrouping helpers from `W8bPack` and the `[LibsignalPlacement]`
subroutine theorems (`preKeyTryFrom_placed_ok`, `preKeyTryFrom_cro_placed_ok`, and
caller-program variants) from `PreKeyTryFromOkPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev post_f90_to_034_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.post_f90_to_034_placed_wp

abbrev epilogue_034_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.epilogue_034_placed_wp

abbrev preKeyTryFrom_inv_ok :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFrom_inv_ok

abbrev preKeyTryFrom_placed_ok_of_callees :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFrom_placed_ok_of_callees

abbrev preKeyTryFrom_placed_ok :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFrom_placed_ok

abbrev preKeyTryFrom_placed_ok_at :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFrom_placed_ok_at

abbrev preKeyTryFrom_cro_placed_ok :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFrom_cro_placed_ok

abbrev preKeyTryFrom_cro_placed_ok_at :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFrom_cro_placed_ok_at

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
