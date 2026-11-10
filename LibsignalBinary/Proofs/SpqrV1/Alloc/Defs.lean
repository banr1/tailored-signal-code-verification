/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortized
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Bytes
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat

/-!
# SPQR V1 Allocator Glue

Re-exports the verified `RawVecInner::{finish_grow, grow_amortized, do_reserve_and_handle}`,
`RawVec::grow_one`, `VecDeque<ChainEpoch>::grow`, `BytesMut::reserve_inner`,
`Bytes::from(Vec<u8>)`, and `slice::Concat::concat` contracts.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

end CryptoVerification.SpqrV1.Alloc
