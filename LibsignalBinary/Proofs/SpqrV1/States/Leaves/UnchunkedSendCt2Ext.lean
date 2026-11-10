/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Proof

/-!
# `<unchunked::send_ct::Ct1SentEkReceived>::send_ct2`: `.inImage img` & `StatesRecvContractsAx`

Lifts `unchunked_ct1_sent_ek_received_send_ct2_ok` to `Spec.inImage img` and discharges the
`unchunkedCt1SentEkReceivedSendCt2_ok` field of `StatesRecvContractsAx`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedSendCt2Ext

open Arm64 ProofLib ProofLib.ObjectLoad
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap (RustAlloc rustAllocSpec allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (tripleRatchetProgAtExt shimName allocName memcpyName noAllocShimSpec)
open CryptoVerification.LibsignalSpqrV1
  (MlKem mlkemEncaps2Name mlkemEncaps2Spec libcruxHmacName libcruxHmacSpec)
open CryptoVerification.SpqrV1.Alloc
  (AllocContracts4K sliceConcat3Spec session2MemcpySpecWithStack sessionMemcpyRegionROSpecWithStack)
open CryptoVerification.SpqrV1.ChainProofs (sliceConcatName)
open CryptoVerification.SpqrV1.States.Leaves
  (unchunkedSendCt2Stack unchunkedCt1SentEkReceivedSendCt2Name
   unchunkedCt1SentEkReceivedSendCt2Spec)
open CryptoVerification.SpqrV1.Unchunked
  (unchunked_ct1_sent_ek_received_send_ct2_ok_4k
   unchunked_ct1_sent_ek_received_send_ct2_ok_4k_of_hooks)
open CryptoVerification.SpqrV1.States.Recv
  (sub_ok_inImage_of_sub_ok_ax growToCalleeExt sub_ok_inImage_growToCalleeExt_ax)

set_option maxRecDepth 200000

/-- Native-stack (`unchunkedSendCt2Stack = 16720` B) `.inImage img` contract for
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` under `AllocContracts4K`
    and `sliceConcat3Spec A`. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sliceConcatName) (sliceConcat3Spec A))
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img) :=
  sub_ok_inImage_of_sub_ok_ax img
    (unchunked_ct1_sent_ek_received_send_ct2_ok_4k hA hconcat3 hencaps2 hhmac)

/-- Native-stack (`unchunkedSendCt2Stack = 16720` B) `.inImage img` contract for
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` directly from
    `AllocContracts4K` and 4-KiB `HookSat` contracts. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_ok_inImage_of_hooks
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext)
    (hshim : HookSat ext shimName noAllocShimSpec)
    (halloc : HookSat ext allocName (rustAllocSpec A))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack))
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img) :=
  sub_ok_inImage_of_sub_ok_ax img
    (unchunked_ct1_sent_ek_received_send_ct2_ok_4k_of_hooks hA hshim halloc hmc hRO hencaps2 hhmac)

/-- `StatesRecvContractsAx.unchunkedCt1SentEkReceivedSendCt2_ok` (Field 9, `35936` B grown stack)
    under `AllocContracts4K` and `sliceConcat3Spec A`. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sliceConcatName) (sliceConcat3Spec A))
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((growToCalleeExt unchunkedSendCt2Stack
        (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax unchunkedSendCt2Stack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked_ct1_sent_ek_received_send_ct2_ok_inImage hA hconcat3 hencaps2 hhmac)

/-- `StatesRecvContractsAx.unchunkedCt1SentEkReceivedSendCt2_ok` (Field 9, `35936` B grown stack)
    under `AllocContracts4K` and 4-KiB `HookSat` contracts (`shim`, `alloc`, `memcpy`, `memcpyRO`,
    `encapsulate2`, `hmac`). -/
theorem unchunked_ct1_sent_ek_received_send_ct2_ok_ax_of_hooks
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext)
    (hshim : HookSat ext shimName noAllocShimSpec)
    (halloc : HookSat ext allocName (rustAllocSpec A))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack))
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((growToCalleeExt unchunkedSendCt2Stack
        (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax unchunkedSendCt2Stack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked_ct1_sent_ek_received_send_ct2_ok_inImage_of_hooks hA hshim halloc hmc hRO hencaps2 hhmac)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedSendCt2Ext
