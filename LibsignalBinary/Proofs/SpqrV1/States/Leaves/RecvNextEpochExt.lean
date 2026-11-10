/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch

/-!
# `<Ct2Sampled>::recv_next_epoch`: `.inImage img` & `StatesRecvContractsAx`

Lifts `ct2_sampled_recv_next_epoch_ok_ext` to `Spec.inImage img` and discharges the
`ct2SampledRecvNextEpoch_ok` field of `StatesRecvContractsAx`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochExt

open Arm64 ProofLib ProofLib.ObjectLoad
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Drop (DeallocOkExt dropGluePoly16Stack drop_glue_poly16_ok_ext)
open CryptoVerification.SpqrV1.States.Leaves
  (ct2SampledRecvNextEpochName ct2SampledRecvNextEpochSpec ct2_sampled_recv_next_epoch_ok_ext)
open CryptoVerification.SpqrV1.States.Recv
  (sub_ok_inImage_of_sub_ok_ax growToCalleeExt sub_ok_inImage_growToCalleeExt_ax)

/-- Native-stack (`dropGluePoly16Stack`) `.inImage img` contract for `<Ct2Sampled>::recv_next_epoch`
    under `DeallocOkExt`. -/
theorem ct2_sampled_recv_next_epoch_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct2SampledRecvNextEpochName)
      ((ct2SampledRecvNextEpochSpec A F).inImage img) :=
  sub_ok_inImage_of_sub_ok_ax img
    (ct2_sampled_recv_next_epoch_ok_ext (drop_glue_poly16_ok_ext hdealloc))

/-- `StatesRecvContractsAx.ct2SampledRecvNextEpoch_ok` (Field 13, `35936` B grown stack)
    under `DeallocOkExt`. -/
theorem ct2_sampled_recv_next_epoch_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct2SampledRecvNextEpochName)
      ((growToCalleeExt dropGluePoly16Stack
        (ct2SampledRecvNextEpochSpec A F)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax dropGluePoly16Stack
    (fun _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (ct2_sampled_recv_next_epoch_ok_inImage hdealloc)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochExt
