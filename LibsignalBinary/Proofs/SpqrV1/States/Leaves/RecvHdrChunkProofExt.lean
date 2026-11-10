/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProof

/-!
# `<NoHeaderReceived>::recv_hdr_chunk`: `.inImage img` & `StatesRecvContractsAx`

Lifts `noHeaderReceived_recv_hdr_chunk_okX` to `Spec.inImage img` and discharges the
`noHeaderReceivedRecvHdrChunk_ok` field of `StatesRecvContractsAx`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofExt

open Arm64 ProofLib ProofLib.ObjectLoad
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (AllocContractsX tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (libcruxHmacName libcruxHmacSpec)
open CryptoVerification.SpqrV1.Poly.AddChunk (AddChunkOkX)
open CryptoVerification.SpqrV1.Alloc (SliceConcat3OkX)
open CryptoVerification.SpqrV1.Drop (DeallocOkExt)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (PolyDecodedMessageOkX)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
  (NoHeaderReceivedRecvHdrChunkOkX noHeaderReceivedRecvHdrChunkName
   noHeaderReceivedRecvHdrChunkStackX noHeaderReceivedRecvHdrChunkSpec
   noHeaderReceived_recv_hdr_chunk_okX)
open CryptoVerification.SpqrV1.States.Recv
  (growToCalleeExt sub_ok_inImage_growToCalleeExt_ax)

set_option maxRecDepth 200000

/-- Native-stack (`noHeaderReceivedRecvHdrChunkStackX`) `.inImage img` contract for
    `<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk` under `AllocContractsX`. -/
theorem noHeaderReceived_recv_hdr_chunk_ok_inImage
    {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hadd_ok : AddChunkOkX img A ext)
    (hdec_ok : PolyDecodedMessageOkX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    NoHeaderReceivedRecvHdrChunkOkX img F A ext :=
  noHeaderReceived_recv_hdr_chunk_okX himg hAx hdealloc hadd_ok hdec_ok hconcat3 hhmac

/-- `StatesRecvContractsAx.noHeaderReceivedRecvHdrChunk_ok` (Field 5, `35936` B grown stack)
    under `AllocContractsX`. -/
theorem noHeaderReceived_recv_hdr_chunk_ok_ax
    {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hadd_ok : AddChunkOkX img A ext)
    (hdec_ok : PolyDecodedMessageOkX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName)
      ((growToCalleeExt noHeaderReceivedRecvHdrChunkStackX
        (noHeaderReceivedRecvHdrChunkSpec F A img.base)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax noHeaderReceivedRecvHdrChunkStackX
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (noHeaderReceived_recv_hdr_chunk_okX himg hAx hdealloc hadd_ok hdec_ok hconcat3 hhmac)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofExt
