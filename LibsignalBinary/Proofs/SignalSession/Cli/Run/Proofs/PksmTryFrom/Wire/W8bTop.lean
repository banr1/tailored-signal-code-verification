/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssembly
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepX
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWBaseKey
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWIdent
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWKyber
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWPresence
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSigMsg
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPack

/-!
# Top-Level `PreKeySignalMessage::try_from` Contract

Assembles the protobuf field-decode loop, post-loop validation layers, and error exits to establish
`PreKeyTryFromOk` from `Obj.Loads libsignalSessionImage img` and `AllocContractsX img A ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- Establishes `PreKeyTryFromOk img A ext` for a loaded `libsignalSessionImage`. -/
theorem preKeyTryFrom_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext) :
    PreKeyTryFromOk img A ext := by
  have hC : PksmCallees img A ext := pksmCallees_of_loads himg hA
  have hb : (img.base &&& 0xfff#64) = 0#64 := hC.baseAligned
  have hLoopF4 : PreKeyDecodeLoopF4OkW img A ext :=
    fun _ _ _ _ _ _ fuel _ _ _ _ _ hpc hrun hregs hx28 hx26 hx2 hsp hF hsym htr hfuel hlen =>
      preKeyStep_wp hC.decodeErrorFrom hC.decodeErrorPush hC.decodeVarintSlow
        hC.varintSlice hC.int32Merge hC.skipField hC.bytesMerge
        (preKeyDecodeLoop_e4 hC.decodeErrorFrom hC.decodeErrorPush hC.decodeVarintSlow
          hC.varintSlice hC.int32Merge hC.skipField hC.bytesMerge fuel)
        hpc hrun hregs hx28 hx26 hx2 hsp hF hsym htr hfuel hlen
  exact preKeyTryFrom_ok_of_postLoop hC.alloc hC.dropDecodeError hLoopF4
    (preKeyPostLoopOkW_of_5b4 hC.dropSpe (preKeyPresenceErrW_proof hC)
      (preKey5b4OkW_of_684 hb (preKeyBaseKeyErrW_proof hb hC)
        (preKey684OkW_of_830 hC.intoBoxed (preKeyKyberErrW_proof himg hA hC)
          (preKey830OkW_of_864 hC.identityKeyOk (preKeyIdentErrW_proof hC)
            (preKey864OkW_of_8c0 hC.sigTryFrom hC.tryClone (preKeySigMsgErrW_proof hC)
              (preKey8c0OkW_proof hC))))))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
