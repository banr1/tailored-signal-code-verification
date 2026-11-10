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
# Handshake Prost and `RawVecInner` Helper Decodes

Generates instruction decode tables on `libsignalSessionCode_tree` for the handshake copies of
`prost::encoding::bytes::merge [local#5]` (`bytesMerge6`), `decode_varint [local#4]`
(`decodeVarint5`), `skip_field [local#5]` (`skipField6`), `RawVecInner::finish_grow [local#9]`
(`finishGrow11`), and `RawVecInner::do_reserve_and_handle [local#8]` (`doReserve10`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib.ProgramReflection

set_option maxHeartbeats 1200000 in
gen_decodes libsignalSessionCode_tree bytesMerge6
  [(ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]" + 0) →
   (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]" + 884)]

set_option maxHeartbeats 1200000 in
gen_decodes libsignalSessionCode_tree decodeVarint5
  [(ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]" + 0) →
   (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]" + 576)]

set_option maxHeartbeats 1200000 in
gen_decodes libsignalSessionCode_tree skipField6
  [(ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]" + 0) →
   (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]" + 416)]

set_option maxHeartbeats 1200000 in
gen_decodes libsignalSessionCode_tree finishGrow11
  [(ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]" + 0) →
   (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]" + 164)]

set_option maxHeartbeats 1200000 in
gen_decodes libsignalSessionCode_tree doReserve10
  [(ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]" + 0) →
   (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]" + 116)]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
