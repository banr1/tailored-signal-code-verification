/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2
public import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.Defs
import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.DropDecodeError
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorFrom
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.VarintSlow

/-!
# X-Form Crate-10 `decode_varint [local#6]` and `drop_glue<DecodeError> [local#3]`

Proves `decodeVarint6_ok_of_alloc_x` and `dropDecodeError3_ok_of_alloc_x` on
`tripleRatchetProgAtExt img.base ext` under `AllocContractsX img A ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7

open Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (AllocContractsX tripleRatchetProgAtExt)
open CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
  (decodeErrorFrom_ok_ext_x decodeVarintSlow_ok_ext_x)

/-- `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]` satisfies
`(SpqrV1.Varint.decodeVarint2SpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext`
under `AllocContractsX img A ext`. -/
theorem decodeVarint6_ok_of_alloc_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2Name)
      ((CryptoVerification.SpqrV1.Varint.decodeVarint2SpecX A).inImage img) := by
  have hFrom := decodeErrorFrom_ok_ext_x hA
  have hSlow := CryptoVerification.LibsignalTripleRatchet.Prost.decodeVarintSlowX_ok_of_session2
    (decodeVarintSlow_ok_ext_x hA)
  refine CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_ok_of_contracts_x ?_ ?_
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_from_eq_fnAddr]
    exact CryptoVerification.LibsignalTripleRatchet.Prost.decodeErrorFromSpecWithStack_inImage_mono
      (s2 := CryptoVerification.LibsignalTripleRatchet.Prost.decodeErrorHookStackX) hFrom
  · rw [CryptoVerification.CliC.SpqrV1.Varint.decodeVarint2_add_slow_eq_fnAddr, BitVec.add_zero]
    exact hSlow

/-- `core::ptr::drop_glue::<prost::error::DecodeError> [local#3]` satisfies
`(Prost.dropDecodeErrorSpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext`
under `AllocContractsX img A ext`. -/
theorem dropDecodeError3_ok_of_alloc_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName)
      ((CryptoVerification.LibsignalTripleRatchet.Prost.dropDecodeErrorSpecX A).inImage img) :=
  CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_ok_ext_x hA

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SignedPort7.VarintDrop7
