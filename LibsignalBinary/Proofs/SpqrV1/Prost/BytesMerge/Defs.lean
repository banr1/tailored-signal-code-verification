/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.GenDecodes

/-!
# `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#3]`: Decodes and Offsets

Instruction decode table and symbol offset lemmas for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` (`0x4d13c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.BytesMerge

open Arm64 ProofLib ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

abbrev bytesMerge3Name : String :=
  "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"

abbrev decodeVarint2Name : String :=
  "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]"

abbrev doReserve7Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]"

theorem bytesMerge3_fnOff :
    libsignalSessionCode.fnOff bytesMerge3Name = 0x47d44 :=
  libsignalSessionCode_fnOff_0x47d44

theorem decodeVarint2_fnOff :
    libsignalSessionCode.fnOff decodeVarint2Name = 0x480d4 :=
  libsignalSessionCode_fnOff_0x480d4

theorem doReserve7_fnOff :
    libsignalSessionCode.fnOff doReserve7Name = 0x4dca8 :=
  libsignalSessionCode_fnOff_0x4dca8

gen_decodes libsignalSessionCode_tree bytesMerge3Bin [0x47d44 → 0x48054]

end CryptoVerification.SpqrV1.Prost.BytesMerge
