/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Final
import ProofLib.SepLogic.WPp

/-!
# CLI `PqRatchetState::encode_to_vec` Top-Level Contract

Proves `pqRatchetStateEncodeToVec_okX` on the CLI image under `AllocContracts img.base A ext`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec


open CryptoVerification.CodeLayout

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

section UnconditionalTopLevel

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Prost

open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Prost.MessageEncode

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_okX
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqRatchetStateEncodeToVecOkX img A ext :=
  pqRatchetStateEncodeToVec_ok_ext_x hA himg

end UnconditionalTopLevel

end CryptoVerification.SpqrV1.Prost.EncodeToVec
