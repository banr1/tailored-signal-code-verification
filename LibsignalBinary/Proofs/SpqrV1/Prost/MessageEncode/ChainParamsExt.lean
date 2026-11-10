/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp

/-!
# Stack-Bounded `ChainParams::encode [local#2]` Contract (`AllocContractsX`)

Lifts `encode_chainParams_2_ok_ext_x` to `AllocContractsX img A ext` using `do_reserve_7_ok_ext_xa`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint

theorem encode_chainParams_2_ok_ext_xa {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext) :
    EncodeChainParams2OkX img A ext := by
  have hdoReserve := do_reserve_7_ok_ext_xa (img := img) hAx
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have henc0 := encodeVarint4_fit_ok_ext_x img A ext hdoReserve
  unfold EncodeVarint4FitOkExtX at henc0
  rw [← encodeChainParams2_encodeVarint4_fnAddr_eq] at henc0
  have hdoR0 := hdoReserve
  rw [← encodeChainParams2_doReserve7_fnAddr_eq] at hdoR0
  obtain ⟨P, hP, hwp⟩ := chainParams2_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_x img s0 hinv0 henc0)
    (subroutine_ok_withMsgEnc48CSPlaced_x img s0 hinv0 hdoR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

end CryptoVerification.SpqrV1.Prost.MessageEncode
