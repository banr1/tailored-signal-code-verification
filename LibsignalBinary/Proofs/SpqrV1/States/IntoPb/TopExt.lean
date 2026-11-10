/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3b
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aExt
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bExt
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cExt
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dExt
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aExt
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cExt
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eExt
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.PolyIntoPbExt

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::into_pb`: Top-Level 4-KiB Allocator Proof

Combines all 11 arms of `<spqr::v1::chunked::states::States>::into_pb` (615 instructions,
2,460 bytes) under `SpqrV1.Alloc.AllocContracts4K` to prove `states_into_pb_variant_4k`,
`states_into_pb_ok_ext_4k`, and `states_into_pb_ok_x_4k`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopExt

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet
  (tripleRatchetProgAtExt subroutine_ok_inImage_of_subroutine_ok)
open CryptoVerification.LibsignalSpqrV1 (States spqrPolyApi spqrAuthApi)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
  (EncoderIntoPbOkExt encoder_into_pb_ok_ext_4k)
open CryptoVerification.SpqrV1.Poly.DecoderPb
  (DecoderIntoPbOkExt decoder_into_pb_ok_ext_4k)
open CryptoVerification.SpqrV1.States.IntoPb
  (statesIntoPbName statesIntoPbVariantSpec
   StatesIntoPbOkExt StatesIntoPbOkX statesIntoPbSpecX_of_statesIntoPbSpec
   states_into_pb_keysUnsampled states_into_pb_keysSampled
   states_into_pb_ct1Received states_into_pb_ct2Sampled
   states_into_pb_headerSent_4k states_into_pb_ekSentCt1Received_4k
   states_into_pb_noHeaderReceived_4k states_into_pb_headerReceived_4k
   states_into_pb_ct1Sampled_4k states_into_pb_ekReceivedCt1Sampled_4k
   states_into_pb_ct1Acknowledged_4k)

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Per-variant correctness of `<spqr::v1::chunked::states::States>::into_pb`
    across all 11 `States` constructors under `AllocContracts4K`. -/
theorem states_into_pb_variant_4k {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b st) := by
  have henc : EncoderIntoPbOkExt b A ext := encoder_into_pb_ok_ext_4k hA
  have hdec : DecoderIntoPbOkExt b A ext := decoder_into_pb_ok_ext_4k hA
  cases st with
  | keysUnsampled s => exact states_into_pb_keysUnsampled s
  | keysSampled s => exact states_into_pb_keysSampled henc s
  | headerSent s => exact states_into_pb_headerSent_4k henc hdec hA s
  | ct1Received s => exact states_into_pb_ct1Received henc s
  | ekSentCt1Received s => exact states_into_pb_ekSentCt1Received_4k hdec hA s
  | noHeaderReceived s => exact states_into_pb_noHeaderReceived_4k hdec hA s
  | headerReceived s => exact states_into_pb_headerReceived_4k hdec hA s
  | ct1Sampled s => exact states_into_pb_ct1Sampled_4k hA henc hdec s
  | ekReceivedCt1Sampled s => exact states_into_pb_ekReceivedCt1Sampled_4k hA henc s
  | ct1Acknowledged s => exact states_into_pb_ct1Acknowledged_4k hA hdec s
  | ct2Sampled s => exact states_into_pb_ct2Sampled henc s

/-- `<spqr::v1::chunked::states::States>::into_pb` (615 instructions)
    satisfies `statesIntoPbSpec A F b` on `tripleRatchetProgAtExt b ext`
    under `AllocContracts4K`. -/
theorem states_into_pb_ok_ext_4k {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    StatesIntoPbOkExt b A F ext := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal =>
    (states_into_pb_variant_4k hA x.st).mono_outcome ⟨x.out, x.stA⟩ R s0 hpc hrun hpre hal
      fun _ hout => hout

/-- `<spqr::v1::chunked::states::States>::into_pb` (615 instructions)
    satisfies `(statesIntoPbSpecX A F img.base).inImage img` on
    `tripleRatchetProgAtExt img.base ext` under `AllocContracts4K`. -/
theorem states_into_pb_ok_x_4k {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext) :
    StatesIntoPbOkX img A F ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (statesIntoPbSpecX_of_statesIntoPbSpec (states_into_pb_ok_ext_4k hA))

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.States.IntoPb
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopExt
  (states_into_pb_variant_4k states_into_pb_ok_ext_4k states_into_pb_ok_x_4k)
end CryptoVerification.SpqrV1.States.IntoPb
-- AUTO-BRIDGE END
