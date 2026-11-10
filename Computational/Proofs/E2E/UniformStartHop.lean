/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.UniformStart
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
import ProofLib.Lemmas
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs

/-!
# Session Model from Uniform Keys and the PRG Hop

**Checked by Lean.**

Defines `libSessionU`, the session model initialized directly from uniform `(rk, ck)`, and bounds
its game bias against `libsignalSessionScheme` via the `rootKdfAsPrg` advantage of
`uniformStartDistinguisher`.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.HeadlineU

open CryptoGames Ratchet LibsignalInst
  LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E

/-- Variant of `libsignalSessionScheme` using the key's `(rk, ck)` directly as epoch-0 keys without `rootKdf`. -/
def libSessionU {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ) :
    SMSchemeR KeyU (GhostState PQ) (Plain ℓ) PQC (BitVec 256) (List (BitVec 8)) where
  initA k := P.initA ⟨k.1.1, k.1.2, k.2.1, k.2.2.1, k.2.2.2⟩
  initB k := P.initB ⟨k.1.1, k.1.2, k.2.1, k.2.2.1, k.2.2.2⟩
  send g m r := P.send g m.toList r
  receive g c rc := (P.receive g c rc).map fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)

theorem sample_prod_bindU {α β γ : Type} [SampleableType α] [SampleableType β]
    (f : α × β → ProbComp γ) :
    (($ᵗ (α × β) : ProbComp (α × β)) >>= f) =
      (($ᵗ α : ProbComp α) >>= fun a => ($ᵗ β : ProbComp β) >>= fun b => f (a, b)) := by
  have hsel : ($ᵗ (α × β) : ProbComp (α × β)) =
      (Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β)) := rfl
  rw [hsel]
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

section Hop

variable {PQ PQC Pt : Type} [Inhabited PQ] [SampleableType PQC]

theorem evalDist_gameR_libSessionR_eq_prgReal (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    𝒟[SM.gameR (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg A] =
      𝒟[(LibsignalSim.rootKdfAsPrg P.C.F (encPt lam)).prgRealExperiment
        (uniformStartDistinguisher P ℓ cfg qep A)] := by
  have horacle : ∀ rk0 ck0,
      oracleImplR (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep cfg =
        oracleImplR (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg := by
    intro rk0 ck0
    unfold oracleImplR transmitR challR deliverR injectR corrR
      SM.transmitImpl SM.challImpl SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libsignalSessionScheme
    rfl
  have hinit : ∀ (rk rk' : Ratchet.RootKey) (rest : BitVec 256 × BitVec 256 × BitVec 256) (b :
    Bool),
      SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ (rootKdf P.C.F rk (encPt lam)).1
        (rootKdf P.C.F rk (encPt lam)).2).sendPart (rk', rest) b =
        SM.initState (libsignalSessionScheme P ℓ encPt lam).sendPart (rk, rest) b := by
    intro rk rk' rest b
    unfold SM.initState SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libsignalSessionScheme
    rfl
  unfold SM.gameR PRGScheme.prgRealExperiment LibsignalSim.rootKdfAsPrg uniformStartDistinguisher SM.runR
  simp only [bind_assoc, horacle]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Ratchet.RootKey) ($ᵗ Bool)]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bindU]
  refine evalDist_bind_congr ($ᵗ Ratchet.RootKey) _ _ fun rk => ?_
  symm
  rw [sample_prod_bindU]
  simp only [hinit rk]
  exact OracleComp.evalDist_bind_const ($ᵗ Ratchet.RootKey) _

theorem evalDist_gameR_libSessionU_eq_prgIdeal (P : Params PQ PQC) (ℓ : ℕ)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    𝒟[SM.gameR (libSessionU P ℓ) 3 qep cfg A] =
      𝒟[PRGScheme.prgIdealExperiment (uniformStartDistinguisher P ℓ cfg qep A)] := by
  have horacle : ∀ rk0 ck0,
      oracleImplR (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep cfg =
        oracleImplR (libSessionU P ℓ) 3 qep cfg := by
    intro rk0 ck0
    unfold oracleImplR transmitR challR deliverR injectR corrR
      SM.transmitImpl SM.challImpl SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libSessionU
    rfl
  have hinit : ∀ (rc : Ratchet.RootKey × BitVec 256) (rk' : Ratchet.RootKey)
      (rest : BitVec 256 × BitVec 256 × BitVec 256) (b : Bool),
      SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2).sendPart (rk', rest) b =
        SM.initState (libSessionU P ℓ).sendPart (rc, rest) b := by
    intro rc rk' rest b
    unfold SM.initState SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libSessionU
    rfl
  unfold SM.gameR PRGScheme.prgIdealExperiment uniformStartDistinguisher SM.runR
  simp only [bind_assoc, horacle]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ (Ratchet.RootKey × BitVec 256)) ($ᵗ Bool)]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bindU]
  refine evalDist_bind_congr ($ᵗ (Ratchet.RootKey × BitVec 256)) _ _ fun rc => ?_
  symm
  rw [sample_prod_bindU]
  simp only [hinit rc]
  exact OracleComp.evalDist_bind_const ($ᵗ Ratchet.RootKey) _

end Hop

end CryptoVerification.E2E.HeadlineU
