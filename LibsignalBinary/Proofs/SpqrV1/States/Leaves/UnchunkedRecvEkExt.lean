/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEk

/-!
# `<unchunked::send_ct::Ct1Sent>::recv_ek`: `.inImage img` & `StatesRecvContractsAx`

Lifts `unchunked_ct1_sent_recv_ek_ok_ext` to `Spec.inImage img` and discharges the
`unchunkedCt1SentRecvEk_ok` field of `StatesRecvContractsAx`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkExt

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (MlKem mlkemValidatePkName mlkemValidatePkSpec)
open CryptoVerification.SpqrV1.Drop (DeallocOkExt)
open CryptoVerification.SpqrV1.States.Leaves
  (mlkemValidatePk_fnOff unchunkedRecvEkStack
   unchunkedCt1SentRecvEkName unchunkedCt1SentRecvEkSpec
   unchunked_ct1_sent_recv_ek_ok_ext)
open CryptoVerification.SpqrV1.States.Recv
  (sub_ok_inImage_of_sub_ok_ax growToCalleeExt sub_ok_inImage_growToCalleeExt_ax)

private theorem mlkemValidatePk_ok_of_hookSat {b : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (h : HookSat ext mlkemValidatePkName (mlkemValidatePkSpec K)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr mlkemValidatePkName)
      (mlkemValidatePkSpec K) := by
  have h0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr mlkemValidatePkName + BitVec.ofNat 64 0)
      (mlkemValidatePkSpec K) :=
    hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext)
      (name := mlkemValidatePkName) (hname := mlkemValidatePkName)
      (stub := libsignalSessionCode.fnOff mlkemValidatePkName) (k := 0)
      rfl (Nat.add_zero _) (by simp only [arm64_norm])
      (fun H => by
        rw [mlkemValidatePk_fnOff]
        exact ls_hook% "libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes" H)
      (by simp [Rust.isPanicSymbol, mlkemValidatePkName]) h
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0

/-- Native-stack (`unchunkedRecvEkStack = 16592` B) `.inImage img` contract for
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` under `DeallocOkExt` and `validate_pk_bytes`. -/
theorem unchunked_ct1_sent_recv_ek_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext)
    (hval_pk : HookSat ext mlkemValidatePkName (mlkemValidatePkSpec K)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((unchunkedCt1SentRecvEkSpec A F K).inImage img) :=
  sub_ok_inImage_of_sub_ok_ax img
    (unchunked_ct1_sent_recv_ek_ok_ext hdealloc (mlkemValidatePk_ok_of_hookSat hval_pk))

/-- `StatesRecvContractsAx.unchunkedCt1SentRecvEk_ok` (Field 8, `35936` B grown stack)
    under `DeallocOkExt` and `validate_pk_bytes`. -/
theorem unchunked_ct1_sent_recv_ek_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext)
    (hval_pk : HookSat ext mlkemValidatePkName (mlkemValidatePkSpec K)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax unchunkedRecvEkStack
    (fun _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked_ct1_sent_recv_ek_ok_inImage hdealloc hval_pk)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkExt
