/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepX
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` Decode-Loop Field Steps

Re-exports pure `mergeProtoField` / `decodeProtoLoop` lemmas alongside placed per-field merge
step theorems on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev step_field1_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.step_field1_placed_wp

abbrev step_field2_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.step_field2_placed_wp

abbrev step_field3_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.step_field3_placed_wp

abbrev step_field4_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.step_field4_placed_wp

abbrev step_field5_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.step_field5_placed_wp

abbrev step_field6_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.step_field6_placed_wp

abbrev step_field7_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.step_field7_placed_wp

abbrev step_field8_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.step_field8_placed_wp

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
