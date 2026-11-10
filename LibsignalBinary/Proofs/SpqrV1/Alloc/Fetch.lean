/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib.ProgramReflection CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! # Instruction Decode Tables for SPQR V1 Allocator Subroutines -/

-- `finish_grow [local#2, 4, 7, 8]`, `grow_amortized`, and `RawVec<(&str, &str)>::grow_one`
gen_decodes libsignalSessionCode_tree spqrAllocBin [
  (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]") →
    (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]" + 164),
  (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]") →
    (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]" + 164),
  (ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one") →
    (ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one" + 32),
  (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]") →
    (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]" + 160),
  (ls_off% "<alloc::raw_vec::RawVecInner>::grow_amortized") →
    (ls_off% "<alloc::raw_vec::RawVecInner>::grow_amortized" + 120),
  (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]") →
    (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" + 176)]

-- `do_reserve_and_handle [local#2, 4, 7]`
gen_decodes libsignalSessionCode_tree spqrAllocBin [
  (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]") →
    (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]" + 116),
  (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#4]") →
    (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#4]" + 116),
  (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") →
    (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]" + 136)]

-- `RawVec<{ChainEpoch, Pt, Poly, GF16, &[Pt]}>::grow_one` and `VecDeque<ChainEpoch>::grow`
gen_decodes libsignalSessionCode_tree spqrAllocBin [
  (ls_off% "<alloc::collections::vec_deque::VecDeque<spqr::chain::ChainEpoch>>::grow") →
    (ls_off% "<alloc::collections::vec_deque::VecDeque<spqr::chain::ChainEpoch>>::grow" + 148),
  (ls_off% "<alloc::raw_vec::RawVec<spqr::chain::ChainEpoch>>::grow_one") →
    (ls_off% "<alloc::raw_vec::RawVec<spqr::chain::ChainEpoch>>::grow_one" + 100),
  (ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one") →
    (ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one" + 100),
  (ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Poly>>::grow_one") →
    (ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Poly>>::grow_one" + 100),
  (ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one") →
    (ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one" + 100),
  (ls_off% "<alloc::raw_vec::RawVec<&[spqr::encoding::polynomial::Pt]>>::grow_one") →
    (ls_off% "<alloc::raw_vec::RawVec<&[spqr::encoding::polynomial::Pt]>>::grow_one" + 100)]

-- `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]`
gen_decodes libsignalSessionCode_tree spqrAllocBin [
  (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]") →
    (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" + 492)]

-- `<bytes::bytes_mut::BytesMut>::reserve_inner`
gen_decodes libsignalSessionCode_tree spqrAllocBin [
  (ls_off% "<bytes::bytes_mut::BytesMut>::reserve_inner") →
    (ls_off% "<bytes::bytes_mut::BytesMut>::reserve_inner" + 972)]

end CryptoVerification.SpqrV1.Alloc
