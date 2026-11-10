/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ConstsMerge

@[expose] public section

set_option autoImplicit false

/-!
# Handshake `bytes::merge` Constants Kit Re-export

Re-exports `PrevDec.ConstsMerge` for `VerNe.Chain3`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  bytesMerge6Name
  chainMerge5Name
  rawVecGrowOneMkName
  bytesMerge6Off
  decodeVarint5Off
  doReserve10Off
  chainMerge5Off
  rawVecGrowOneMkOff
  bytesMerge6_fnOff
  doReserve10_fnOff
  bm6DecodeErrorFromRelOff
  bm6MemcpyRelOff
  bm6MemcpyRelNat
  bm6ShimRelOff
  bm6ShimRelNat
  bm6AllocRelOff
  bm6AllocRelNat
  bm6HandleErrorRelOff
  bm6HandleErrorRelNat
  bm6BytesFromVecRelOff
  bm6DoReserve10RelOff
  bm6DecodeVarint5RelOff
  bm6_add_decodeErrorFrom_eq_fnAddr
  bm6_add_bytesFromVec_eq_fnAddr
  bm6_add_doReserve10_eq_fnAddr
  bm6_add_decodeVarint5_eq_fnAddr
  bm6Off050
  bm6Off074
  bm6Off07c
  bm6Off094
  bm6Off0e4
  bm6Off1b8
  bm6Off210
  bm6Off220
  bm6Off230
  bm6Off254
  bm6Off29c
  bm6Off2c0
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit
