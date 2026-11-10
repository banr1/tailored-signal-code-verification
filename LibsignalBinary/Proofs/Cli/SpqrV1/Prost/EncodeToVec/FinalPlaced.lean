/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.TopPlaced

/-!
# Relocatable `[LibsignalPlacement]` Top-Level Closure for `Cli/SpqrV1/Prost/EncodeToVec` (`Block 426`)

Re-exports the unconditional `[LibsignalPlacement]` contracts for the shared `spqr` CGU
`PqRatchetState::encode_to_vec` (`Block 426`) under `CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec`,
mirroring fixed-ELF `LibsignalBinary/Proofs/Cli/SpqrV1/Prost/EncodeToVec/Final.lean` while rooting
all `Cli/SpqrV1` `MessageEncode` and `ProtoRepr` placed contracts.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Prost.EncodeToVec

theorem pqRatchetStateEncodeToVec_ro_pinned_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A)) :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_ro_pinned_placed_ok_ext
    h_panic hshim halloc hrealloc hmc

theorem pqRatchetStateEncodeToVec_ro_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf doReserveStack A)) :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_ro_placed_ok_ext
    h_panic hshim halloc hrealloc hmc

theorem pqRatchetStateEncodeToVec_pinned_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A ext :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_pinned_placed_ok_ext
    h_panic hshim halloc hrealloc hmc

theorem pqRatchetStateEncodeToVec_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    PqRatchetStateEncodeToVecPlacedOkExt A ext :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_placed_ok_ext
    h_panic hshim halloc hrealloc hmc

theorem pqRatchetStateEncodeToVec_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A ext :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_pinned_placed_ok
    h_panic hshim halloc hrealloc hmc

theorem pqRatchetStateEncodeToVec_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    PqRatchetStateEncodeToVecPlacedOkExt A ext :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_placed_ok
    h_panic hshim halloc hrealloc hmc

end CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec
