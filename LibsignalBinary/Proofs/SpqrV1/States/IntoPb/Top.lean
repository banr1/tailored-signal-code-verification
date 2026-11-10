/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbProof
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Proof
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3b
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4a
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4b
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4c
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4d
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5a
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5c
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5e

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`): Top-Level Proof

**Checked by Lean.**

Combines all 11 arms of `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`,
615 instructions, 2,460 bytes) to prove `states_into_pb_variant`, `states_into_pb_ok_ext`,
and `states_into_pb_ok_x`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Per-variant correctness of `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`)
    across all 11 `States` constructors. -/
theorem states_into_pb_variant {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (st : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b st) := by
  have henc : EncoderIntoPbOkExt b A ext := encoder_into_pb_ok_ext hA
  have hdec : DecoderIntoPbOkExt b A ext := decoder_into_pb_ok_ext hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec := by
    have h0 := hA.session_memcpy_region_ok_at memcpyName 0 (Nat.add_zero _)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
  cases st with
  | keysUnsampled s => exact states_into_pb_keysUnsampled s
  | keysSampled s => exact states_into_pb_keysSampled henc s
  | headerSent s => exact states_into_pb_headerSent henc hdec hmemcpy s
  | ct1Received s => exact states_into_pb_ct1Received henc s
  | ekSentCt1Received s => exact states_into_pb_ekSentCt1Received hdec hmemcpy s
  | noHeaderReceived s => exact states_into_pb_noHeaderReceived hdec hmemcpy s
  | headerReceived s => exact states_into_pb_headerReceived hdec hmemcpy s
  | ct1Sampled s => exact states_into_pb_ct1Sampled hA henc hdec s
  | ekReceivedCt1Sampled s => exact states_into_pb_ekReceivedCt1Sampled hA henc s
  | ct1Acknowledged s => exact states_into_pb_ct1Acknowledged hA hdec hmemcpy s
  | ct2Sampled s => exact states_into_pb_ct2Sampled henc s

/-- `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`, 615 instructions)
    satisfies `statesIntoPbSpec A F b` on `tripleRatchetProgAtExt b ext`. -/
theorem states_into_pb_ok_ext {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    StatesIntoPbOkExt b A F ext := by
  unfold StatesIntoPbOkExt
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  exact ((states_into_pb_variant hA x.st).to_outcome ⟨x.out, x.stA⟩ R s0 hpc hrun hpre hal).mono_outcome
    fun _ hout => hout

/-- `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20`, 615 instructions)
    satisfies `(statesIntoPbSpecX A F img.base).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
theorem states_into_pb_ok_x {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    StatesIntoPbOkX img A F ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (statesIntoPbSpecX_of_statesIntoPbSpec (states_into_pb_ok_ext hA))

end CryptoVerification.SpqrV1.States.IntoPb
