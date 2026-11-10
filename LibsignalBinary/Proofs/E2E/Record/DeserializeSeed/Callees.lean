/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeedTop
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Core
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import LibsignalBinary.Proofs.TripleRatchet.RunAssembly.TryFromAssembly

/-!
# Callee Bundle Discharge for Seed `SessionRecord::deserialize`

Discharges `DeserializeCallees` (`deserializeCallees_ok_of_hooks`) and its relocatable counterpart
`DeserializeCalleesPlaced` (`deserializeCallees_placed_ok_of_hooks`) from `decode_varint_slice`,
`int32::merge`, `bytes::merge`, and `RawVec<Chain>::grow_one`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSession.NonVacuityWitness

/-- Discharges `DeserializeCallees` on `tripleRatchetProgAt` for any hook table satisfying
`AllocHooks A0 abs`. -/
theorem deserializeCallees_ok_of_hooks (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hA : AllocHooks A0 abs) :
    DeserializeCallees C ctl abs := by
  have himg := E2E.Record.loads_sessionImg0
  refine ⟨Prost.decodeVarintSlice_ok hA, Prost.int32Merge_ok hA, ?_,
    ConsumeMessageKeyTransfer.growOneChain_ok himg hA⟩
  exact Prost.bytes_merge_ok himg hA hA (TryFromAssembly.varintSlow_ok hA)
    (Prost.decodeVarintSlice_ok hA) (Glue.bytes_from_vec_inImage_ok himg) (do_reserve_ok hA)
    bytesVtableSlotLoaded (fun p v => Glue.bytes_vtable_drop_inImage_ok hA p v v.length)

/-! ## Relocatable `[LibsignalPlacement]` Callee Bundle -/

section Placed

set_option maxRecDepth 200000

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

private theorem hookSat_sessionShim_of_noop {H : String → Option (State → State)}
    (h : H lsRustNoAllocShimSym = some hookNoop) :
    HookSat H lsRustNoAllocShimSym sessionShimSpec :=
  ⟨hookNoop, h, hookNoop_ok fun _ _ _ hm => by simpa [sessionShimSpec, hookNoop, retHook] using hm⟩

private theorem hookSat_noAllocShim_of_noop {H : String → Option (State → State)}
    (h : H lsRustNoAllocShimSym = some hookNoop) :
    HookSat H lsRustNoAllocShimSym noAllocShimSpec :=
  ⟨hookNoop, h, hookNoop_ok fun _ _ _ hm => by simpa [noAllocShimSpec, hookNoop, retHook] using hm⟩

private theorem bytes_merge_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H Prost.lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpec A)) :=
  Prost.bytes_merge_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (Prost.decode_error_from_placed_ok hshim halloc hpanic_alloc))
    (Prost.bmMemcpy_placed_of_frameless (ls_hook_ok_of_mem hmc))
    (Prost.bmShim_placed_of_noAllocShim (ls_hook_ok_of_mem hshim))
    (Prost.subroutine_ok_withLsCl_of_plain (ls_hook_ok_of_mem halloc))
    ((ls_externAt?_of_mem (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (Prost.decode_varint_slow_placed_ok_with_stack_of_hooks hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (Prost.decode_varint_slice_placed_ok hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (do_reserve_placed_ok hshim halloc hrealloc hpanic_raw))
    (fun tmpPtr v =>
      Prost.subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok hdealloc (by decide) tmpPtr v v.length))

/-- Discharges `DeserializeCalleesPlaced H` under `[LibsignalPlacement]` from explicit hook
hypotheses. -/
theorem deserializeCallees_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hshim : H lsRustNoAllocShimSym = some hookNoop)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A0))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A0))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A0))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsDeserHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    DeserializeCalleesPlaced H :=
  ⟨Prost.decode_varint_slice_placed_ok (hookSat_sessionShim_of_noop hshim) halloc hpanic_alloc,
    Prost.int32_merge_placed_ok (hookSat_sessionShim_of_noop hshim) halloc hpanic_alloc,
    bytes_merge_placed_ok (hookSat_noAllocShim_of_noop hshim) halloc hrealloc hdealloc hmc
      hpanic_alloc hpanic_raw,
    CryptoVerification.LibsignalSession.RawVecGrowOne.grow_one_placed_ok hshim halloc hrealloc
      hpanic_raw⟩

/-- Discharges `DeserializeCalleesPlaced H` under `[LibsignalPlacement]` from
`PlacedDeserializeHooks A0 H`. -/
theorem deserializeCallees_placed_ok_of_hooks [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hH : PlacedDeserializeHooks A0 H) :
    DeserializeCalleesPlaced H :=
  deserializeCallees_placed_ok hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy
    hH.panic_alloc hH.panic_raw

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
