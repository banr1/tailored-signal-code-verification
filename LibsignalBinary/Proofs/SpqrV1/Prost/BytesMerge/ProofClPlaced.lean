/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From

/-!
# `prost::encoding::bytes::merge [local#3]` (Block `290`): Code-Loaded Placed Verification

Discharges the `withLsCodeLoaded` callee contracts of `bytes_merge_3_placed_ok_of_contracts` and
`bytes_merge_3_proto_placed_ok_of_contracts` using `decodeVarint2_cl_placed_ok` (Block `291`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlaced

open Arm64 ProofLib
open CryptoVerification
open CryptoVerification.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Prost.BytesMerge
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlaced

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem bytes_merge_3_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)) :=
  bytes_merge_3_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (decode_error_from_placed_ok hshim halloc hpanic_alloc))
    (ls_hook_ok_of_mem hmc)
    (ls_hook_ok_of_mem hshim)
    (subroutine_ok_withLsCl_of_plain (ls_hook_ok_of_mem halloc))
    ((ls_externAt?_of_mem (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H) (j := 291)
      (decodeVarint2_cl_placed_ok hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (do_reserve_7_placed_ok hpanic_raw hshim halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok hdealloc (by decide) tmpPtr v v.length))

theorem bytes_merge_3_proto_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_290).rebase (blkPl_290).base H)
      (blkPl_290).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A)) :=
  bytes_merge_3_proto_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (decode_error_from_placed_ok hshim halloc hpanic_alloc))
    (ls_hook_ok_of_mem hmc)
    (ls_hook_ok_of_mem hshim)
    (subroutine_ok_withLsCl_of_plain (ls_hook_ok_of_mem halloc))
    ((ls_externAt?_of_mem (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H) (j := 291)
      (decodeVarint2_cl_placed_ok hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_290).rebase (blkPl_290).base H)
      (do_reserve_7_placed_ok hpanic_raw hshim halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok hdealloc (by decide) tmpPtr v v.length))

end LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlaced
