/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Core

/-!
# Refinement of `RawVec<MessageKey>::grow_one`

Proves that `alloc::raw_vec::RawVec<T>::grow_one` (`0x15cac`, 104-byte 8-aligned `T`) and
`RawVecInner::finish_grow` (`0x15de4`) satisfy `growOneSpec A`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- `RawVec<MessageKey>::grow_one` satisfies `GrowOneOk`. -/
theorem grow_one_ok (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img)
    (A : RustAlloc) (hA : AllocHooks A alloc) :
    GrowOneOk img F alloc A := by
  exact RawVecGrowOne.grow_one_ok' img F alloc A himg hA

theorem finish_grow_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (RawVecGrowOne.finishGrowZeroSpec A) :=
  RawVecGrowOne.finish_grow_zero_placed_ok h_shim h_alloc

theorem finish_grow_ne_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (RawVecGrowOne.finishGrowNeSpec A) :=
  RawVecGrowOne.finish_grow_ne_placed_ok h_realloc

theorem finish_grow_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (RawVecGrowOne.finishGrowSpec A) :=
  RawVecGrowOne.finish_grow_placed_ok h_shim h_alloc h_realloc

theorem grow_one_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneSpec A)) :=
  RawVecGrowOne.grow_one_placed_ok h_shim h_alloc h_realloc h_panic

end CryptoVerification.LibsignalSession
