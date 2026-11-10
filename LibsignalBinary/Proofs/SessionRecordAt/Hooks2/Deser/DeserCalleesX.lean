/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.BytesMergeXPhase1
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.Int32MergeX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.VarintSliceX

@[expose] public section

set_option autoImplicit false

/-!
# `DeserializeCallees` Assembly

Discharges `DeserializeCalleesAtW`, `DeserializeCalleesAtWA`, and `DeserializeCalleesPlacedW`
(`decode_varint_slice`, `int32::merge`, `bytes::merge`, and `RawVec<Chain>::grow_one`) from
`Stage2Contracts` external hook bundles.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.WireX
open CryptoVerification.E2E.Record
open Proofs.libsignal.Stage1X

/-- Assemble `DeserializeCalleesAtW img ext` from `Stage2ContractsA0 img ext` and an explicit
`Prost.X.BytesMergeOkW img A0 ext`. -/
theorem deserializeCalleesAtW_of_stage2_bytes {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsA0 img ext)
    (hbytes : Prost.X.BytesMergeOkW img A0 ext) :
    DeserializeCalleesAtW img ext := by
  have hA : Stage1X.AllocContractsX img A0 ext := allocContractsX_of_stage2ContractsA0 hC
  have hFrom : DecodeErrorFromOkW img A0 ext := decodeErrorFrom_okW hA
  have hSlow : DecodeVarintSlowOkW img A0 ext := decodeVarintSlow_okW hFrom
  have hSlice : DecodeVarintSliceOkW img A0 ext := decodeVarintSlice_okW hFrom
  exact ⟨hSlice, int32Merge_okW hFrom hSlow hSlice, hbytes, grow_one_72_ok_ext_x hA⟩

/-- Assemble `DeserializeCalleesAtW img ext` from `Stage2ContractsA0 img ext`. -/
theorem deserializeCalleesAtW_of_stage2 {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsA0 img ext) :
    DeserializeCalleesAtW img ext :=
  deserializeCalleesAtW_of_stage2_bytes hC
    (bytes_merge_okW hC.loads (allocContractsX_of_stage2ContractsA0 hC) hC.memcpy)

/-! ## Arbitrary-Allocator `DeserializeCalleesAtWA` Assembly -/

/-- Bridge `Stage2ContractsA img A ext` (`Hooks2.Adapters`) to `Stage1X.AllocContractsX img A ext`. -/
theorem allocContractsX_of_stage2ContractsA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsA img A ext) :
    Stage1X.AllocContractsX img A ext :=
  allocContractsX_of_stage2Stubs hC.alloc hC.deallocLayout hC.realloc hC.shim hC.memmove

/-- Assemble `DeserializeCalleesAtWA img A ext` from `AllocContractsX` and `memcpy`. -/
theorem deserializeCalleesAtWA_of_alloc_memcpy {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hA : Stage1X.AllocContractsX img A ext)
    (hmemcpy : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memcpyName)
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)) :
    DeserializeCalleesAtWA img A ext := by
  have hFrom : DecodeErrorFromOkW img A ext := decodeErrorFrom_okW hA
  have hSlow : DecodeVarintSlowOkW img A ext := decodeVarintSlow_okW hFrom
  have hSlice : DecodeVarintSliceOkW img A ext := decodeVarintSlice_okW hFrom
  exact ⟨hSlice, int32Merge_okW hFrom hSlow hSlice, bytes_merge_okW hLoads hA hmemcpy,
    grow_one_72_ok_ext_x hA⟩

/-- Assemble `DeserializeCalleesAtWA img A ext` from `Stage2ContractsA img A ext` and explicit `BytesMergeOkW`. -/
theorem deserializeCalleesAtWA_of_stage2_bytes {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsA img A ext)
    (hbytes : Prost.X.BytesMergeOkW img A ext) :
    DeserializeCalleesAtWA img A ext := by
  have hA : Stage1X.AllocContractsX img A ext := allocContractsX_of_stage2ContractsA hC
  have hFrom : DecodeErrorFromOkW img A ext := decodeErrorFrom_okW hA
  have hSlow : DecodeVarintSlowOkW img A ext := decodeVarintSlow_okW hFrom
  have hSlice : DecodeVarintSliceOkW img A ext := decodeVarintSlice_okW hFrom
  exact ⟨hSlice, int32Merge_okW hFrom hSlow hSlice, hbytes, grow_one_72_ok_ext_x hA⟩

/-- Assemble `DeserializeCalleesAtWA img A ext` from `Stage2ContractsA img A ext`. -/
theorem deserializeCalleesAtWA_of_stage2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsA img A ext) :
    DeserializeCalleesAtWA img A ext :=
  deserializeCalleesAtWA_of_alloc_memcpy hC.loads (allocContractsX_of_stage2ContractsA hC) hC.memcpy

/-! ## Relocatable `[LibsignalPlacement]` `DeserializeCalleesPlacedW` Assembly -/

section Placed

open Arm64.Obj

theorem L1_DeserCalleesX_Placed : True := trivial

/-- Assemble `DeserializeCalleesPlacedW H` from `Stage1X.AllocContractsPlaced A0 H` and an explicit
`Prost.X.BytesMergePlacedOkW A0 H`. -/
theorem deserializeCalleesPlacedW_of_alloc_bytes [LibsignalPlacement]
    {H : LibsignalHooks}
    (hA : Stage1X.AllocContractsPlaced A0 H)
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H) :
    DeserializeCalleesPlacedW H := by
  have hFrom : DecodeErrorFromPlacedOkW A0 H := decodeErrorFrom_placed_okW hA
  have hSlow : DecodeVarintSlowPlacedOkW A0 H := decodeVarintSlow_placed_okW hFrom
  have hSlice : DecodeVarintSlicePlacedOkW A0 H := decodeVarintSlice_placed_okW hFrom
  exact ⟨hSlice, int32Merge_placed_okW hFrom hSlow hSlice, hbytes, growOneChain_placed_ok_x hA⟩

/-- Assemble `DeserializeCalleesPlacedW H` directly from `Stage1X.AllocContractsPlaced A0 H` and
`memcpy` at `extHookStack` (without needing the unused fields of `Stage2ContractsA0Placed`). -/
theorem deserializeCalleesPlacedW_of_alloc [LibsignalPlacement]
    {H : LibsignalHooks}
    (hA : Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec extHookStack))) :
    DeserializeCalleesPlacedW H :=
  deserializeCalleesPlacedW_of_alloc_bytes hA (bytes_merge_placed_okW hA hMemcpy)

/-- Assemble `DeserializeCalleesPlacedW H` from `Stage2ContractsA0Placed H`. -/
theorem deserializeCalleesPlacedW_of_stage2 [LibsignalPlacement]
    {H : LibsignalHooks}
    (hC : Stage2ContractsA0Placed H) :
    DeserializeCalleesPlacedW H :=
  deserializeCalleesPlacedW_of_alloc (allocContractsPlaced_of_stage2ContractsA0Placed hC) hC.memcpy

end Placed

end Proofs.libsignal.Hooks2
