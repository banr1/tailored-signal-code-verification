/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.Headline
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# Assembly and projection lemmas for the δ-correct PQXDH headline

**Checked by Lean.** Correctness-from-`WellFormedPrimitivesδ`, assembly, and conjunct-projection
lemmas accompanying `Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean`.
-/

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.ReductionDsl (Ty CostedReduction TwoStageCostedReduction Mid)
open SignalPqxdh.Costed

theorem WellFormedPrimitivesδ.x25519_base_ne_zero_any (P : Primitives)
    (hWF : WellFormedPrimitivesδ P) (a b : Bytes) :
    P.x25519 a (P.x25519Base b) ≠ List.replicate 32 0 := by
  rw [← hWF.x25519_clamp, ← hWF.x25519Base_clamp]
  exact hWF.x25519_base_ne_zero (clampScalar25519 a) (clampScalar25519 b)
    (clampScalar25519_length a) (clampScalar25519_length b)

/-- PQXDH handshake roundtrip correctness under `WellFormedPrimitivesδ`. -/
theorem wellFormedδ_pqxdhCorrect (P : Primitives) (hWF : WellFormedPrimitivesδ P) :
    PqxdhCorrect P := by
  intro initInp accKeysInp ss kemCt hTrustA hTrustB hReplay hSigSpk hSigKem hIkA hIkB hSpkB hOpkB
    hEncaps hDecaps hSpqrOk
  exact pqxdh_handshake_roundtrip P hWF.x25519_comm hWF.canon_base hWF.x25519Base_len
    (WellFormedPrimitivesδ.x25519_base_ne_zero_any P hWF) hWF.aead_corr
    initInp accKeysInp hTrustA hTrustB hReplay hSigSpk hSigKem hIkA hIkB hSpkB hOpkB
    ss kemCt hEncaps hDecaps (hWF.kemEncaps_len _ _ _ _ hEncaps).2
    (fun pqrKey stA salt? pqMsg hS => hWF.spqr_corr pqrKey initInp.spqrCoins stA salt? pqMsg hS)
    hSpqrOk

theorem headlineδ_of_securityδ (hKI : ∀ (S : Setup), PqxdhKeyIndSecureδ S)
    (hAuth : ∀ (S : Setup), PqxdhAuth1KeySecureδ S) :
    PqxdhCorrectAndSecureδ :=
  fun P S => ⟨wellFormedδ_pqxdhCorrect P, hKI S, hAuth S⟩

/-- Inhabited `Primitives` witness used to project `PqxdhSecureδ S` out of `PqxdhCorrectAndSecureδ`. -/
def dummyPqxdhPrimitives : Primitives where
  x25519 := fun _ _ => []
  x25519Base := fun _ => []
  isCanonical := fun _ => false
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  sigVerify := fun _ _ _ => false
  sha512 := fun _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  scalarFromBytesModOrder := fun _ => []
  scalarFromWide := fun _ => []
  montToEd := fun _ _ => none
  isTorsionFree := fun _ => false
  edNeg := fun _ => []
  doubleScalarMulBasepoint := fun _ _ _ => []
  compress := fun _ => []
  kemKeyGen := fun _ => ([], [])
  kemEncaps := fun _ _ => none
  kemDecaps := fun _ _ => none
  hkdfDerive96 := fun _ => default
  rootCreateChain := fun _ _ => ([], [])
  chainKdfSeed := fun _ => []
  chainKdfNext := fun _ => []
  spqrInitSend := fun _ _ => none
  spqrInitRecv := fun _ _ => none
  deriveMsgKeys := fun _ _ => default
  aeadEnc := fun _ _ _ => []
  aeadDec := fun _ _ _ => none
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false
  sha256Compress := fun _ _ => []
  sha512Compress := fun _ _ => []
  aesEncBlock := fun _ _ => []
  aesDecBlock := fun _ _ => []

theorem PqxdhCorrectAndSecureδ.secure (h : PqxdhCorrectAndSecureδ) (S : Setup) :
    PqxdhSecureδ S :=
  (h dummyPqxdhPrimitives S).2

theorem PqxdhCorrectAndSecureδ.keyInd (h : PqxdhCorrectAndSecureδ) (S : Setup) :
    PqxdhKeyIndSecureδ S :=
  (h.secure S).1

theorem PqxdhCorrectAndSecureδ.auth (h : PqxdhCorrectAndSecureδ) (S : Setup) :
    PqxdhAuth1KeySecureδ S :=
  (h.secure S).2

theorem headline2Keyδ_of_securityδ (hSec : ∀ (S : Setup), Pqxdh2KeySecureδ S) :
    Pqxdh2KeyCorrectAndSecureδ :=
  ⟨wellFormedδ_pqxdhCorrect, hSec⟩

end SignalPqxdh.Security
