/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSlice
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.X
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRoot

/-!
# Assembly of `<SignalMessage as TryFrom<&[u8]>>::try_from`

Discharges the 8 callee contracts (`Wire.TryFromDeps`) of `<SignalMessage as TryFrom<&[u8]>>::try_from`
from proved Prost, `Bytes`, `Box`, and error-drop lemmas to establish `tryFrom_run_closed`.
-/

@[expose] public section

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

namespace CryptoVerification.LibsignalTripleRatchet.TryFromAssembly

/-- The in-image `decode_varint_slow` satisfies `decodeVarintSlowSpec` at its own entry address. -/
theorem varintSlow_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr varintSlowName)
      (decodeVarintSlowSpec A) :=
  decodeVarintSlow_ok b C A ctl abs hA

theorem tryFromCallees_ext {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} {img : Obj.Image}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    Wire.TryFromDeps img C A ctl ext := by
  have hAX : AllocContractsX img A ext := AllocContractsX.of_AllocContracts hC.toAllocContracts
  have hFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img) :=
    subroutine_ok_inImage_of_subroutine_ok img
      (decodeErrorFromWithStack_of_decodeErrorFrom hC.decode_error_from)
  have hSlow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img) :=
    subroutine_ok_inImage_of_subroutine_ok img
      (decodeVarintSlowWithStack_of_decodeVarintSlow hC.decode_varint_slow)
  have hVS : Prost.DecodeVarintSliceOkExtX img A ext :=
    Prost.decodeVarintSlice_ok_of_contract_x
      (sub_ok_at_of_fnAddr hFrom Prost.decodeVarintSliceName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice"))
        (by fnoff_eq))
  have hIM : Prost.Int32MergeOkExtX img A ext :=
    Prost.int32Merge_ok_of_contracts_x
      (sub_ok_at_of_fnAddr hFrom Prost.int32MergeName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
        (by fnoff_eq))
      (sub_ok_at_of_fnAddr (Prost.decodeVarintSlowX_ok_of_session2 hSlow) Prost.int32MergeName (num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::int32::merge::<&mut &[u8]>"))
        (by fnoff_eq))
      hVS
  have hSF : Prost.SkipFieldOkExtX img A ext :=
    Prost.skipField_ok_of_contracts_x
      (Prost.decodeErrorFromSpecWithStack_inImage_mono (s2 := Prost.decodeErrorHookStackX)
        (sub_ok_at_of_fnAddr hFrom Prost.skipFieldName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
          (by fnoff_eq)))
      (sub_ok_at_of_fnAddr (Prost.decodeVarintSlowX_ok_of_session2 hSlow) Prost.skipFieldName (num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]"))
        (by fnoff_eq))
      hVS
  exact
    { intoBoxed := into_boxed_slice_ok_ext_x hAX
      tryClone := try_clone_from_ref_ok_ext_x hAX
      varintSlice := hVS
      int32Merge := hIM
      skipField := hSF
      dropDecodeError := Prost.dropDecodeError_ok_ext_x hAX
      bytesMerge := Prost.bytes_merge_ok_ext_x himg hAX hFrom hSlow hVS
        (bytesFromVecOk_ext himg rfl)
        (do_reserve_ok_ext_x hAX)
        bytesVtableSlotLoaded
        (fun p v => bytesVtableDropOk_ext_x p v v.length hAX himg rfl)
      dropSpe := Getters.drop_spe_ok_x himg hAX }

theorem tryFrom_subroutine_ok_ext {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {img : Obj.Image}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryFromName)
      (tryFromSpec A img) :=
  Wire.tryFrom_subroutine_ok_of_deps hC (tryFromCallees_ext hC himg) (Wire.base_aligned himg)

theorem tryFrom_run_ext {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {img : Obj.Image}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img tryFromName) (tryFromSpec A img) :=
  root_of_tripleRatchetProgAtExt himg (tryFrom_subroutine_ok_ext hC himg)

theorem tryFromCallees (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    Wire.TryFromDeps img C A ctl (tripleRatchetExterns C ctl abs) :=
  tryFromCallees_ext (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hH) himg

theorem tryFrom_run_closed (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) :
    TryFromRunStmt C A ctl S abs img := fun hH himg =>
  tryFrom_run_ext (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hH) himg

end CryptoVerification.LibsignalTripleRatchet.TryFromAssembly
