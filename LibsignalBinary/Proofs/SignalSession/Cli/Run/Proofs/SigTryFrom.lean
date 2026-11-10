/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorFrom
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.VarintSlow
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorPush
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSlice
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.X
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRoot

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire

theorem cliTryFromHooksW_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (C : Crypto) (S : SpqrModel)
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    TripleRatchetHooksW img C A S ext := by
  let _ := himg
  exact
    { alloc := AllocHooksW.of_contracts_x hA
      decodeErrorFrom := SigTryFromHelpers.decodeErrorFrom_ok_ext_x hA
      decodeErrorPush := SigTryFromHelpers.decodeErrorPush_ok_ext_x hA
      decodeVarintSlow := SigTryFromHelpers.decodeVarintSlow_ok_ext_x hA }

theorem cliTryFromDeps_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (C : Crypto) (ctl : BitVec 64)
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    TryFromDeps img C A ctl ext := by
  let _ := C
  let _ := ctl
  have hFrom := SigTryFromHelpers.decodeErrorFrom_ok_ext_x hA
  have hSlow := SigTryFromHelpers.decodeVarintSlow_ok_ext_x hA
  have hVS : Prost.DecodeVarintSliceOkExtX img A ext :=
    Prost.decodeVarintSlice_ok_of_contract_x
      (sub_ok_at_of_fnAddr hFrom Prost.decodeVarintSliceName
        (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
          ls_off% "prost::encoding::varint::decode_varint_slice"))
        (by rw [(ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]; simp only [arm64_norm]))
  have hIM : Prost.Int32MergeOkExtX img A ext :=
    Prost.int32Merge_ok_of_contracts_x
      (sub_ok_at_of_fnAddr hFrom Prost.int32MergeName
        (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
          ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
        (by rw [(ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]; simp only [arm64_norm]))
      (sub_ok_at_of_fnAddr (Prost.decodeVarintSlowX_ok_of_session2 hSlow) Prost.int32MergeName
        (num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
          ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
        (by rw [(ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]; simp only [arm64_norm]))
      hVS
  have hSF : Prost.SkipFieldOkExtX img A ext :=
    Prost.skipField_ok_of_contracts_x
      (Prost.decodeErrorFromSpecWithStack_inImage_mono (s2 := Prost.decodeErrorHookStackX)
        (sub_ok_at_of_fnAddr hFrom Prost.skipFieldName
          (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
            ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
          (by rw [(ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")]; simp only [arm64_norm])))
      (sub_ok_at_of_fnAddr (Prost.decodeVarintSlowX_ok_of_session2 hSlow) Prost.skipFieldName
        (num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
          ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
        (by rw [(ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")]; simp only [arm64_norm]))
      hVS
  exact
    { intoBoxed := into_boxed_slice_ok_ext_x hA
      tryClone := try_clone_from_ref_ok_ext_x hA
      varintSlice := hVS
      int32Merge := hIM
      skipField := hSF
      dropDecodeError := Prost.dropDecodeError_ok_ext_x hA
      bytesMerge := Prost.bytes_merge_ok_ext_x himg hA hFrom hSlow hVS
        (bytesFromVecOk_ext himg rfl)
        (do_reserve_ok_ext_x hA)
        bytesVtableSlotLoaded
        (fun p v => bytesVtableDropOk_ext_x p v v.length hA himg rfl)
      dropSpe := Getters.drop_spe_ok_x himg hA }

/-- Establishes the `SignalMessage::try_from` contract for a loaded `libsignalSessionImage` (`C` is a phantom parameter of `TripleRatchetHooksW`). -/
theorem cliSigTryFrom_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (C : Crypto)
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryFromName) (tryFromSpec A img) :=
  tryFrom_subroutine_ok (C := C) (S := ⟨fun _ _ => none, fun _ _ => 0,
      fun _ _ => .error false, fun _ _ => False, fun _ _ => False⟩) 0#64
    (cliTryFromHooksW_ok C _ himg hA)
    (cliTryFromDeps_ok C _ himg hA).varintSlice (cliTryFromDeps_ok C _ himg hA).int32Merge
    (cliTryFromDeps_ok C _ himg hA).skipField (cliTryFromDeps_ok C _ himg hA).bytesMerge
    (cliTryFromDeps_ok C _ himg hA).dropDecodeError (cliTryFromDeps_ok C _ himg hA).dropSpe
    (cliTryFromDeps_ok C _ himg hA).intoBoxed (cliTryFromDeps_ok C _ himg hA).tryClone
    (ProofLib.ObjectLoad.base_aligned_of_loads himg)

end CryptoVerification.SignalSession.Cli.RunProofs
