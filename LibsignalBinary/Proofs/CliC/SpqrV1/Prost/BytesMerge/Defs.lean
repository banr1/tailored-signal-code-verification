/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Symbol Names and Offsets for `CliC` `prost::encoding::bytes::merge`

Defines the CLI symbol names and `fnOff` equations for `prost::encoding::bytes::merge`,
`decode_varint`, and `RawVecInner::do_reserve_and_handle` in `CliC`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.BytesMerge

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

abbrev _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.bytesMerge3Name : String :=
  "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]"

abbrev _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.decodeVarint2Name : String :=
  "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]"

abbrev _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.doReserve7Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.bytesMerge3_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.bytesMerge3Name = (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]") :=
  (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]")

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.decodeVarint2_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.decodeVarint2Name = (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") :=
  (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")

theorem _root_.CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.doReserve7_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.CliC.SpqrV1.Prost.BytesMerge.doReserve7Name = (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
  (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")

gen_decodes libsignalSessionCode_tree bytesMerge3BinCliC [(ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]" + 0) → (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]" + 784)]

end CryptoVerification.SpqrV1.Prost.BytesMerge
