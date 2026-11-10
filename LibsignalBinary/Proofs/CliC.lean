/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.Fetch
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.Defs
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrow
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Phase23
public import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.DropDecodeError
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Proof
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrowPlaced
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlaced
public import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.DropDecodeErrorPlaced
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2Placed
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3Placed
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Phase23Placed
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ProofPlaced
public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps

/-!
# CLI Crate-12 (`CliC`) Proofs and `SignedPortDepsPlaced` Discharge

Aggregates the CLI crate-12 (`signal_session`) monomorph proofs under `CryptoVerification.CliC` and
discharges `SignedPortDepsPlaced` from `CodecHooksPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.CliC

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecsBinary

/-- Discharge all `SignedPortDepsPlaced` callee contracts (`559`, `546`, `558`, `555`)
directly from external allocator / `memcpy` hooks. -/
theorem signedPortDepsPlaced_of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H Prost.lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    SignedPortDepsPlaced A H :=
  SignedPortDepsPlaced.of_prost hdealloc
    (SpqrV1.Varint.decodeVarint2_placed_ok hshim halloc hpanic_alloc)
    (SpqrV1.Varint.skipField3_placed_ok hshim halloc hpanic_alloc)
    (SpqrV1.Prost.BytesMerge.bytes_merge_3_placed_ok
      hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)

/-- Bundle `SignedPortDepsPlaced A H` from `CodecHooksPlaced A H` so
`RecordCodecsBinary.SignedAssembly.decodeKyberPreKey_placed_ok` /
`decodeSignedPreKey_placed_ok` can be discharged directly. -/
theorem signedPortDepsPlaced_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : CodecHooksPlaced A H) :
    SignedPortDepsPlaced A H :=
  signedPortDepsPlaced_of_hooks
    hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy hH.panic_alloc hH.panic_raw

end CryptoVerification.CliC
