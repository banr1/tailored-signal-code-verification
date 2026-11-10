/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.CompRBobInit

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRWSBobChain
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompRBobInit
theorem gamma_kemEncap_snd_compI0 (S : Sem) (g : Ghost) (pk e : DY.Bytes) : gamma compI0 S g (DY.PQKem.kemEncap pk e).2 = if (gamma compI0 S g e).length = 32 then ((compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e]).getD []).drop 1568 else S.kemDecap (gamma compI0 S g pk) (gamma compI0 S g e) := by
  unfold gamma gamma'
  show ((({pk, entropy := e} : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes = _
  rw [DY.Bytes.rec_eq (gKemSS compI0 S) (gAll compI0 S g)]; dsimp only [gKemSS, concretizeKemSS]
  split <;> rfl
theorem gamma_setupSecret_0 {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) (hc : Compat compI0 r S g) : gamma compI0 S g (setupSecret r 0) = secretBytes r 0 := CompRX0Bytes.gamma_setupSecret_0 hNe hc
theorem gamma_litByte0 {S : Sem} {g : Ghost} (b : UInt8) : gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte b) = [b.toBitVec] := by unfold DY.Libsignal.TripleRatchet.litByte; rw [CompRBobInit.gamma_lit0]; rfl
theorem gamma_pqxdhLabel0 {S : Sem} {g : Ghost} : gamma compI0 S g DY.Libsignal.PQXDH.pqxdhLabel = ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8 := by unfold DY.Libsignal.PQXDH.pqxdhLabel DY.Libsignal.TripleRatchet.lit; rw [CompRBobInit.gamma_lit0]
theorem gamma_whisperRatchet0 {S : Sem} {g : Ghost} : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") = ofByteArray "WhisperRatchet".toUTF8 := by unfold DY.Libsignal.TripleRatchet.lit; rw [CompRBobInit.gamma_lit0]
theorem gamma_whisperMessageKeys0 {S : Sem} {g : Ghost} : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") = ofByteArray "WhisperMessageKeys".toUTF8 := by unfold DY.Libsignal.TripleRatchet.lit; rw [CompRBobInit.gamma_lit0]
theorem gamma_hkdfBlock10 {S : Sem} {g : Ghost} (prk info : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) = hmacWith F0 (gamma compI0 S g prk) (gamma compI0 S g info ++ [0x01#8]) := by unfold DY.Libsignal.TripleRatchet.hkdfBlock1; rw [CompRBobInit.gamma_hmac0, CompRBobInit.gamma_concat0, gamma_litByte0]; rfl
end Symbolic.BugInjection.Proofs.Common443.CompRWSBobChain
