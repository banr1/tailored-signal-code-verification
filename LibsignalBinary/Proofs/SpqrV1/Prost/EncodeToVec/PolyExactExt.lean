/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExact
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLen
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp

/-!
# Stack-Bounded Exact-Capacity `PolynomialEncoder::encode` and `PolynomialDecoder::encode` (`AllocContractsX`)

Lifts `encode_polyEncoder_2_exact_pinned_ok_ext_x` and `encode_polyDecoder_2_exact_pinned_ok_ext_x`
to `AllocContractsX img A ext` using `do_reserve_7_ok_ext_xa` and `encode_repeated_2_59_ok_ext_xa`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Prost.MessageEncode

theorem encode_repeated_2_59_ok_ext_xa {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated2Name)
      ((encodeRepeated59SpecOf doReserveStackX A).inImage img) := by
  have hdoReserve := do_reserve_7_ok_ext_xa (img := img) hAx
  have henc0 := encodeVarint4_fit_ok_ext_x img A ext hdoReserve
  unfold EncodeVarint4FitOkExtX at henc0
  rw [← EncodeRepeated2.encodeVarint4_fnAddr_eq] at henc0
  have hdoReserve0 := hdoReserve
  rw [← EncodeRepeated2.doReserve7_fnAddr_eq] at hdoReserve0
  have hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated2Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" "memcpy"))
      ((withStack sessionMemcpyRegionSpec (48 + doReserveStackX)).inImage img) :=
    hAx.session_memcpy_region_ok_at encodeRepeated2Name
      (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" "memcpy")
      (48 + doReserveStackX) (by decide) (by decide)
      (by rw [(ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"), (ls_stub% "memcpy")])
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ EncodeRepeated2.encodeRepeated59PreOf doReserveStackX A x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := EncodeRepeated2.encode_repeated_2_59_gen_ok_ext_cs (resStack := doReserveStackX)
    (by decide)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 henc0)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 hdoReserve0)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 hmemcpy0)
    hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyEncoder_2_exact_pinned_ok_ext_xa {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name)
      ((encodePolyEncoderExactSpecOf doReserveStackX A).inImage img) := by
  have hdoReserve := do_reserve_7_ok_ext_xa (img := img) hAx
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have hencL0 := subroutine_ok_polyEncLenElemsOut_of_pinned
    (polynomialEncoderEncodedLen_local2_pinned_ok_ext img.base A ext)
  rw [← encodePolyEncoder2_encodedLen2_fnAddr_eq] at hencL0
  have hencV0 := encodeVarint4_fit_ok_ext_x img A ext hdoReserve
  unfold EncodeVarint4FitOkExtX at hencV0
  rw [← encodePolyEncoder2_encodeVarint4_fnAddr_eq] at hencV0
  have hencR0 := encode_repeated_2_59_ok_ext_xa (img := img) (A := A) (ext := ext) hAx
  rw [← encodePolyEncoder2_encodeRepeated2_fnAddr_eq] at hencR0
  obtain ⟨P, hP, hwp⟩ := polyEncoder2_exact_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CS_ext s0 hencL0)
    (subroutine_ok_withMsgEnc48CS_x img s0 hinv0 hencV0)
    (subroutine_ok_withMsgEnc48CS_x img s0 hinv0 hencR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyDecoder_2_exact_pinned_ok_ext_xa {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name)
      ((encodePolyDecoderExactSpecOf doReserveStackX A).inImage img) := by
  have hdoReserve := do_reserve_7_ok_ext_xa (img := img) hAx
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have hencL0 := subroutine_ok_polyDecLenElemsOut_of_pinned
    (polynomialDecoderEncodedLen_local2_pinned_ok_ext img.base A ext)
  rw [← encodePolyDecoder2_encodedLen2_fnAddr_eq] at hencL0
  have hencV0 := encodeVarint4_fit_ok_ext_x img A ext hdoReserve
  unfold EncodeVarint4FitOkExtX at hencV0
  rw [← encodePolyDecoder2_encodeVarint4_fnAddr_eq] at hencV0
  have hencR0 := encode_repeated_2_59_ok_ext_xa (img := img) (A := A) (ext := ext) hAx
  rw [← encodePolyDecoder2_encodeRepeated2_fnAddr_eq] at hencR0
  obtain ⟨P, hP, hwp⟩ := polyDecoder2_exact_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CS_ext s0 hencL0)
    (subroutine_ok_withMsgEnc48CS_x img s0 hinv0 hencV0)
    (subroutine_ok_withMsgEnc48CS_x img s0 hinv0 hencR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

end CryptoVerification.SpqrV1.Prost.EncodeToVec
