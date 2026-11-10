/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Defs
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs

/-!
# Spurious-step and epoch-0 bad-event bounds

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Bounds single and union spurious DH-ratchet step probabilities (`spuriousStepTerm`,
`forgedEpochStartSpuriousStepTerm`) and reduces `eps0Event` to `epoch0Distinguisher` under
`rootKdfAsPrg`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

theorem prgReal_true_le {Seed Out : Type} [SampleableType Seed] [SampleableType Out]
    (G : PRGScheme Seed Out) (B : PRGScheme.PRGAdversary Out) :
    𝒟[G.prgRealExperiment B] {true} ≤
      G.prgAdvantage B + 𝒟[PRGScheme.prgIdealExperiment B] {true} := by
  unfold PRGScheme.prgAdvantage Measure.boolDist ENNReal.absDiff
  calc 𝒟[G.prgRealExperiment B] {true}
      ≤ (𝒟[G.prgRealExperiment B] {true} - 𝒟[PRGScheme.prgIdealExperiment B] {true}) +
          𝒟[PRGScheme.prgIdealExperiment B] {true} := le_tsub_add
    _ ≤ ((𝒟[G.prgRealExperiment B] {true} - 𝒟[PRGScheme.prgIdealExperiment B] {true}) +
          (𝒟[PRGScheme.prgIdealExperiment B] {true} - 𝒟[G.prgRealExperiment B] {true})) +
          𝒟[PRGScheme.prgIdealExperiment B] {true} := by
        gcongr
        exact le_self_add

noncomputable def spurUnit (F : ShaState → List (BitVec 8) → ShaState) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) : ℝ≥0∞ :=
  ⨆ (rk : Ratchet.RootKey) (curCkaMsg : Pt) (y : BitVec 256) (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt)
    (ids : SerializedIdentityKeys) (ser : List (BitVec 8)) (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
    ((evictedKeySpuriousStepPrg F encPt Dh rk curCkaMsg y).prgAdvantage (wireMacVerifiesTest F c salt ids ser tag) +
      𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true})

theorem spurUnit_eq_rootKdfSpuriousStepUnit (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) :
    spurUnit F encPt Dh = rootKdfSpuriousStepUnit F encPt Dh :=
  rfl

theorem spurSingle_le_spurUnit (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt)
    (rk : Ratchet.RootKey) (curCkaMsg : Pt) (y : BitVec 256) (c : ℕ) (hc : c < 2 ^ 32) (salt : Salt)
    (ids : SerializedIdentityKeys) (ser : List (BitVec 8)) (hser : ser.length < 2 ^ 32)
    (tag : BitVec 64) :
    𝒟[(evictedKeySpuriousStepPrg F encPt Dh rk curCkaMsg y).prgRealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true} ≤
      spurUnit F encPt Dh := by
  refine (prgReal_true_le (evictedKeySpuriousStepPrg F encPt Dh rk curCkaMsg y) (wireMacVerifiesTest F c salt ids ser tag)).trans ?_
  unfold spurUnit
  exact le_iSup_of_le rk (le_iSup_of_le curCkaMsg (le_iSup_of_le y (le_iSup₂_of_le c hc
    (le_iSup_of_le salt (le_iSup_of_le ids (le_iSup₂_of_le ser hser (le_iSup_of_le tag le_rfl)))))))

theorem spurBound_eq_mul_spurUnit (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) :
    spuriousStepTerm F encPt Dh q qep = (q * qep : ℕ) * spurUnit F encPt Dh :=
  rfl

theorem spuriousStepTerm_le_old (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) :
    spuriousStepTerm F encPt Dh q qep ≤
      (q * (qep + 1) : ℕ) * spurUnit F encPt Dh := by
  rw [spurBound_eq_mul_spurUnit]
  gcongr
  exact Nat.le_succ qep

noncomputable def spurUnitPt (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) : ℝ≥0∞ :=
  ⨆ (rk : Ratchet.RootKey) (curCkaMsg : {P : Pt // P ≠ 0}) (T : {P : Pt // P ≠ 0})
    (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
    (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
    ((pointSpuriousStepPrg F encPt Dh rk curCkaMsg.1 T.1).prgAdvantage (wireMacVerifiesTest F c salt ids ser tag) +
      𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true})

theorem spurUnitPt_eq_rootKdfForgedEpochStartUnit (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) :
    spurUnitPt F encPt Dh = rootKdfForgedEpochStartUnit F encPt Dh :=
  rfl

theorem spurBoundPt_eq_mul_spurUnitPt (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q : ℕ) :
    forgedEpochStartSpuriousStepTerm F encPt Dh q = (q : ℝ≥0∞) * spurUnitPt F encPt Dh :=
  rfl

theorem forgedEpochStartSpuriousStepTerm_le_old (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) :
    forgedEpochStartSpuriousStepTerm F encPt Dh q ≤
      (q * (qep + 1) : ℕ) * spurUnitPt F encPt Dh := by
  rw [spurBoundPt_eq_mul_spurUnitPt]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast Nat.le_mul_of_pos_right q (Nat.succ_pos qep)

theorem spurSinglePt_le_spurUnitPt (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt)
    (rk : Ratchet.RootKey) (curCkaMsg : Pt) (hTcur : curCkaMsg ≠ 0) (T : Pt) (hT : T ≠ 0)
    (c : ℕ) (hc : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
    (hser : ser.length < 2 ^ 32) (tag : BitVec 64) :
    𝒟[(pointSpuriousStepPrg F encPt Dh rk curCkaMsg T).prgRealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true} ≤
      spurUnitPt F encPt Dh := by
  refine (prgReal_true_le (pointSpuriousStepPrg F encPt Dh rk curCkaMsg T) (wireMacVerifiesTest F c salt ids ser tag)).trans ?_
  unfold spurUnitPt
  exact le_iSup_of_le rk (le_iSup_of_le ⟨curCkaMsg, hTcur⟩ (le_iSup_of_le ⟨T, hT⟩ (le_iSup₂_of_le c hc
    (le_iSup_of_le salt (le_iSup_of_le ids (le_iSup₂_of_le ser hser (le_iSup_of_le tag le_rfl)))))))

noncomputable def eps0IdealUnit (F : ShaState → List (BitVec 8) → ShaState) : ℝ≥0∞ :=
  ⨆ (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
    (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
    𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true}

theorem spurDist_ideal_le_unit (F : ShaState → List (BitVec 8) → ShaState)
    (c : ℕ) (hc : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
    (hser : ser.length < 2 ^ 32) (tag : BitVec 64) :
    𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true} ≤
      eps0IdealUnit F := by
  unfold eps0IdealUnit
  exact le_iSup₂_of_le c hc (le_iSup_of_le salt (le_iSup_of_le ids
    (le_iSup₂_of_le ser hser (le_iSup_of_le tag le_rfl))))

/-- Bad event in `libsignalSessionScheme` where Alice accepts or forges in epoch 0 without Bob
being corrupted in epoch 0. -/
def eps0Event (P : Params PQ PQC) (ℓ : ℕ) (encPt : Pt → List (BitVec 8)) (lam : Pt)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ) (A : LibAdv PQ PQC ℓ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (_, s) ← SM.runR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

theorem sample_prod_bind {α β γ : Type} [SampleableType α] [SampleableType β]
    (f : α × β → ProbComp γ) :
    (($ᵗ (α × β) : ProbComp (α × β)) >>= f) =
      (($ᵗ α : ProbComp α) >>= fun a => ($ᵗ β : ProbComp β) >>= fun b => f (a, b)) := by
  have hsel : ($ᵗ (α × β) : ProbComp (α × β)) =
      (Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β)) := rfl
  rw [hsel]
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

theorem evalDist_eps0Event_eq_prgReal (P : Params PQ PQC) (ℓ : ℕ) (encPt : Pt → List (BitVec 8))
    (lam : Pt) (onImage : List (BitVec 8) → Bool) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    𝒟[eps0Event P ℓ encPt lam onImage qep A] =
      𝒟[(rootKdfAsPrg P.C.F (encPt lam)).prgRealExperiment (epoch0Distinguisher P ℓ onImage qep A)] := by
  have horacle : ∀ rk0 ck0,
      oracleImplR (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep (configEpoch0Distinguisher onImage) =
        oracleImplR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher onImage) := by
    intro rk0 ck0
    unfold oracleImplR transmitR challR deliverR injectR corrR
      SM.transmitImpl SM.challImpl SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libsignalSessionScheme
    rfl
  have hinit : ∀ (rk rk' : Ratchet.RootKey) (rest : BitVec 256 × BitVec 256 × BitVec 256) (b : Bool),
      SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ (rootKdf P.C.F rk (encPt lam)).1
        (rootKdf P.C.F rk (encPt lam)).2).sendPart (rk', rest) b =
        SM.initState (libsignalSessionScheme P ℓ encPt lam).sendPart (rk, rest) b := by
    intro rk rk' rest b
    unfold SM.initState SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libsignalSessionScheme
    rfl
  unfold eps0Event PRGScheme.prgRealExperiment rootKdfAsPrg epoch0Distinguisher SM.runR
  simp only [bind_assoc, pure_bind, horacle]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Ratchet.RootKey) ($ᵗ Bool)]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ Ratchet.RootKey) _ _ fun rk => ?_
  symm
  rw [sample_prod_bind]
  simp only [hinit rk]
  exact OracleComp.evalDist_bind_const ($ᵗ Ratchet.RootKey) _

theorem eps0Event_le_prgAdv_add_ideal (P : Params PQ PQC) (ℓ : ℕ) (encPt : Pt → List (BitVec 8))
    (lam : Pt) (onImage : List (BitVec 8) → Bool) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    𝒟[eps0Event P ℓ encPt lam onImage qep A] {true} ≤
      (rootKdfAsPrg P.C.F (encPt lam)).prgAdvantage (epoch0Distinguisher P ℓ onImage qep A) +
        𝒟[PRGScheme.prgIdealExperiment (epoch0Distinguisher P ℓ onImage qep A)] {true} := by
  rw [evalDist_eps0Event_eq_prgReal]
  exact prgReal_true_le (rootKdfAsPrg P.C.F (encPt lam)) (epoch0Distinguisher P ℓ onImage qep A)

end CryptoGames.LibsignalSM.Proofs.Refinement
