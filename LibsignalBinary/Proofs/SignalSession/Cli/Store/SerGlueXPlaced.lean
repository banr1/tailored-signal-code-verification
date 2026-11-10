/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneX
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyX
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint

/-!
# Relocatable `SessionRecord::serialize` Glue

Proves `serializeCanonSpecX` on Block `52` from `SerContractsXPlaced` under `[LibsignalPlacement]`,
together with its `StoreKit.withLsCodeRoLoaded` transfer.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.SerGlueX

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

/-- Relocatable `[LibsignalPlacement]` `serializeCanonSpecX A` on Block `52` from
`Proofs.libsignal.Hooks2.SerContractsXPlaced A H`. -/
theorem serializeCanonX_placed_ok_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : Proofs.libsignal.Hooks2.SerContractsXPlaced A H) :
    subroutine_ok (CryptoVerification.E2E.Record.Placed.lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX A)) := by
  have hClone := CryptoVerification.E2E.Record.Serialization.sessionClone_placed_ok_ext hC
  have hDR : Proofs.libsignal.Hooks2.DoReservePlacedOkX A H :=
    Proofs.libsignal.Hooks2.do_reserve_placed_ok_ext_x hC.alloc
  have hEV : Proofs.libsignal.Hooks2.EncodeVarintPlacedOkX A H :=
    CryptoVerification.LibsignalTripleRatchet.Prost.encode_varint_placed_ok_of_doReserve_x A H hDR
  have hRaw := Proofs.libsignal.Hooks2.encodeRaw_placed_ok_of_serContractsX hC
  have hDrop : Proofs.libsignal.Hooks2.DropSessionStructureLocal1PlacedOkX A H :=
    Proofs.libsignal.Hooks2.drop_session_structure_local1_placed_ok_ext hC.alloc
  exact Proofs.libsignal.Hooks2.serializeCanonX_of_serialize_placedX
    (CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX.serialize_placed_ok_of_leaves_ext
      hC hClone hEV hRaw hDrop)

/-- Caller-block-polymorphic `StoreKit.withLsCodeRoLoaded` form of
`serializeCanonX_placed_ok_of_serContractsX`. -/
theorem serializeCanonX_placed_lscro_of_serContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : Proofs.libsignal.Hooks2.SerContractsXPlaced A H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX A)) :=
  ls_transfer_cl_to_lscro (callerProg := callerProg) (j := 52)
    (serializeCanonX_placed_ok_of_serContractsX hC) hblk

end Placed

end CryptoVerification.SignalSession.Cli.Store.SerGlueX
