/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChainX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRawX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerializeLenExt
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::serialize` Assembly (`HSerX`)

Composes the verified leaf contracts (`encode_varint`, `do_reserve_and_handle`, `encoded_len`,
`encode::<Chain>`, `SessionStructure::encode_raw`, and `drop_glue::<SessionStructure>`) with
`SessionCloneOkX` to prove `SessionRecord::serialize` (`0x284e8`, Block `52`) from `SerContractsX`
on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Bin

/-- `encodeRaw` contract from the stub contracts alone. -/
theorem encodeRaw_ok_of_serContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : SerContractsX img A ext) :
    EncodeRawOkX img A ext := by
  have hEV : EncodeVarintOkX img A ext :=
    Prost.encodeVarint_ok_ext_x img A ext (do_reserve_ok_ext_x hC.alloc)
  have hDR : DoReserveOkX img A ext := do_reserve_ok_ext_x hC.alloc
  have hmk := msgKeyLen_ok_ext img.base ext A
  have hchain := chainLen_ok_ext img.base ext A hmk
  have hEC : EncodeChainOkX img A ext := encodeChain_ok_ext A ext hC hEV hDR hchain hmk
  exact encodeRaw_ok_ext A ext hC hEV hDR hEC

/-- `SessionRecord::serialize` contract on `SP2Ext` from `SerContractsX` and `SessionCloneOkX`. -/
theorem hSer_ext_of_clone {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : SerContractsX img A ext)
    (hClone : SessionCloneOkX img A ext) :
    subroutine_ok (CryptoVerification.LibsignalTripleRatchet.contractProg img.base ext)
      (img.base + CryptoVerification.E2E.Bin.serializeOff)
      ((CryptoVerification.E2E.Bin.recordSerializeSpec A).inImage img) := by
  have hEV : EncodeVarintOkX img A ext :=
    Prost.encodeVarint_ok_ext_x img A ext (do_reserve_ok_ext_x hC.alloc)
  have hRaw := encodeRaw_ok_of_serContractsX hC
  have hDrop : DropSessionStructureLocal1OkX img A ext :=
    drop_session_structure_local1_ok_ext hC.alloc
  exact recordSerialize_ok_ext_of_serializeX
    (SerializeBodyAuxX.serialize_ok_of_leaves_ext hC hClone hEV hRaw hDrop)

/-! ## Relocatable `[LibsignalPlacement]` assembly (Block `52`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_HSerX_Placed : True := trivial

/-- Relocatable `encodeRaw` contract (Block `14`) from `SerContractsXPlaced` alone. -/
theorem encodeRaw_placed_ok_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : SerContractsXPlaced A H) :
    EncodeRawPlacedOkX A H := by
  have hDR : DoReservePlacedOkX A H := do_reserve_placed_ok_ext_x hC.alloc
  have hEV : EncodeVarintPlacedOkX A H :=
    Prost.encode_varint_placed_ok_of_doReserve_x A H hDR
  have hmk := msgKeyLen_placed_ok_ext A H
  have hchain := chainLen_placed_ok_ext A H
  have hEC : EncodeChainPlacedOkX A H := encodeChain_placed_ok_ext A H hC hEV hDR hchain hmk
  exact encodeRaw_placed_ok_ext A H hC hEV hDR hEC

theorem encodeRaw_placed_cl_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsmpl.base 14) (withLsCl lsmpl (encodeRawSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeRaw_placed_ok_of_serContractsX hC)

/-- Relocatable `SessionRecord::serialize` (Block `52`) from `SerContractsXPlaced` and
`SessionClonePlacedOkX`. -/
theorem hSer_placed_ext_of_clone [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : SerContractsXPlaced A H)
    (hClone : SessionClonePlacedOkX A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (CryptoVerification.E2E.Bin.recordSerializeSpec A)) := by
  have hDR : DoReservePlacedOkX A H := do_reserve_placed_ok_ext_x hC.alloc
  have hEV : EncodeVarintPlacedOkX A H :=
    Prost.encode_varint_placed_ok_of_doReserve_x A H hDR
  have hRaw := encodeRaw_placed_ok_of_serContractsX hC
  have hDrop : DropSessionStructureLocal1PlacedOkX A H :=
    drop_session_structure_local1_placed_ok_ext hC.alloc
  exact recordSerialize_placed_ok_ext_of_serializeX
    (SerializeBodyAuxX.serialize_placed_ok_of_leaves_ext hC hClone hEV hRaw hDrop)

theorem hSer_placed_cl_of_clone [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hClone : SessionClonePlacedOkX A H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (CryptoVerification.E2E.Bin.recordSerializeSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (hSer_placed_ext_of_clone hC hClone)

end Placed

end Proofs.libsignal.Hooks2
