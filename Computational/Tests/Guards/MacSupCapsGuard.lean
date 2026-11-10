/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Specifications.Session.StatementSpkModel
public import Computational.Specifications.Session.SpkHop2Red

/-!
# MAC Supremum Caps and Spurious-Step Unit Guards

**Checked by Lean.** Checks by `rfl` that the fixed-test session bound terms (`eps0IdealUnit`,
`epoch0ChainForgeryTerm`, `spkSwapSpuriousStepTerm`, `rootKdfSpuriousStepUnit`, and
`rootKdfForgedEpochStartUnit`) restrict their suprema to chain counters `c < 2 ^ 32` and serialized
lengths `ser.length < 2 ^ 32`, matching `macForgeryProb` (`DEV-LS23`). Also checks that
`spuriousStepTerm` and `forgedEpochStartSpuriousStepTerm` factor definitionally through the
standalone HMAC-SHA256 extractor units `rootKdfSpuriousStepUnit` and `rootKdfForgedEpochStartUnit`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Guards.MacSupCaps

open CryptoVerification.E2E CryptoGames CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalSim
  CryptoGames.LibsignalSM OracleComp ENNReal
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA LibsignalSession LibsignalInst

theorem eps0IdealUnit_capped (F : ShaState → List (BitVec 8) → ShaState) :
    eps0IdealUnit F =
      ⨆ (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys)
        (ser : List (BitVec 8)) (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
        𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true} := rfl

theorem epoch0ChainForgeryTerm_eq (F : ShaState → List (BitVec 8) → ShaState) (q : ℕ) :
    epoch0ChainForgeryTerm F q = q * eps0IdealUnit F := rfl

theorem spkSwapSpuriousStepTerm_capped (F : ShaState → List (BitVec 8) → ShaState) (q : ℕ) :
    spkSwapSpuriousStepTerm F q =
      q * ⨆ (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys)
        (ser : List (BitVec 8)) (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
        ((Ratchet.expandPRG F).prgAdvantage (wireMacVerifiesTest F c salt ids ser tag) +
          𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true}) := rfl

theorem rootKdfSpuriousStepUnit_capped {Pt : Type} (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) :
    rootKdfSpuriousStepUnit F encPt Dh =
      ⨆ (rk : Ratchet.RootKey) (curCkaMsg : Pt) (y : BitVec 256) (c : ℕ) (_ : c < 2 ^ 32)
        (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
        (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
        ((evictedKeySpuriousStepPrg F encPt Dh rk curCkaMsg y).prgAdvantage
            (wireMacVerifiesTest F c salt ids ser tag) +
          𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true}) := rfl

theorem rootKdfForgedEpochStartUnit_capped {Pt : Type} [Zero Pt] (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) :
    rootKdfForgedEpochStartUnit F encPt Dh =
      ⨆ (rk : Ratchet.RootKey) (curCkaMsg : {P : Pt // P ≠ 0}) (T : {P : Pt // P ≠ 0}) (c : ℕ)
        (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
        (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
        ((pointSpuriousStepPrg F encPt Dh rk curCkaMsg.1 T.1).prgAdvantage
            (wireMacVerifiesTest F c salt ids ser tag) +
          𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true}) := rfl

theorem spuriousStepTerm_eq_unit {Pt : Type} (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ) :
    spuriousStepTerm F encPt Dh q qep = (q * qep : ℕ) * rootKdfSpuriousStepUnit F encPt Dh := rfl

theorem forgedEpochStartSpuriousStepTerm_eq_unit {Pt : Type} [Zero Pt] (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q : ℕ) :
    forgedEpochStartSpuriousStepTerm F encPt Dh q = q * rootKdfForgedEpochStartUnit F encPt Dh :=
  rfl

end CryptoVerification.E2E.Guards.MacSupCaps
