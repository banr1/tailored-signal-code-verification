/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPackWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWPresencePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWBaseKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWKyberPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWIdentPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSigMsgPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepWPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `PreKeySignalMessage::try_from` Contract

Establishes the relocatable `[LibsignalPlacement]` contract for `PreKeySignalMessage::try_from`
(Block `111`) from `CodecHooksPlaced A H`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Relocatable `PreKeySignalMessage::try_from` contract (Block `111`) from `CodecHooksPlaced A H`. -/
theorem pksmTryFromPlaced_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hH : RecordCodecsBinary.CodecHooksPlaced A H) :
    subroutine_ok ((CryptoVerification.blkPC_111).rebase (CryptoVerification.blkPl_111).base H)
      (CryptoVerification.blkPl_111).base (pksmTryFromSpecPlaced A) := by
  have hC : PksmCalleesPlaced A H := pksmCalleesPlaced_of_codecHooks hH
  exact pksmTryFromPlaced_ok_of_postLoop hC.deallocX hC.dropDecodeError
    (preKeyDecodeLoopF4W_of_callees_placed_ok hC)
    (preKeyPostLoopOkW_placed_of_5b4 hC (preKeyPresenceErrW_placed_proof hC)
      (preKey5b4OkW_placed_of_684 hC (preKeyBaseKeyErrW_placed_proof hC)
        (preKey684OkW_placed_of_830 hC (preKeyKyberErrW_placed_proof hH hC)
          (preKey830OkW_placed_of_864 hC (preKeyIdentErrW_placed_proof hC)
            (preKey864OkW_placed_of_8c0 hC (preKeySigMsgErrW_placed_proof hC)
              (preKey8c0OkW_placed_proof hC))))))

theorem subsetA4PksmTryFromPlaced_of_codecHooks [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hH : RecordCodecsBinary.CodecHooksPlaced A H) :
    SubsetA4PksmTryFromPlaced A H :=
  ⟨pksmTryFromPlaced_ok hH⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
