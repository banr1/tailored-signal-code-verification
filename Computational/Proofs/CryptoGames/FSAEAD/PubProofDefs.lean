/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.SM.Game

/-!
# Public-Part and Single-AD-Class Adversary Predicates

Query predicates restricting OT-CCA, FS-AEAD, and SM adversaries to equal public challenge parts
(`EqualPubChallenges`, `EqualPubChalls`) and a single associated-data class
(`OTAllQueriesInOneADClass`, `AllQueriesInOneADClass`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace AEADScheme
variable {K AD Pub M C : Type}

/-- The OT-CCA query `t` has an AD of class other than `k₀`. -/
def otQueryADOutsideClass {κ : Type} [DecidableEq κ] (cls : AD → κ) (k₀ : κ) :
    (unifSpec + otccaSpec AD M C).Domain → Bool
  | .inr (.inl ⟨a, _⟩) => decide (cls a ≠ k₀)
  | .inr (.inr ⟨a, _⟩) => decide (cls a ≠ k₀)
  | _ => false

/-- An OT-CCA adversary all of whose encryption and decryption ADs have the class `k₀`. -/
def OTAllQueriesInOneADClass {κ : Type} [DecidableEq κ] (cls : AD → κ) (B : OTCCAAdversary AD M C) : Prop :=
  ∃ k₀, B.IsQueryBoundP (fun t => otQueryADOutsideClass (M := M) (C := C) cls k₀ t = true) 0

end AEADScheme
namespace FSAEAD
variable {SS RS AD Pub M C : Type}

/-- The FS-AEAD query `t` is a challenge with different public parts. -/
def unequalPubChall [DecidableEq Pub] :
    (unifSpec + spec SS RS AD (Pub × M) C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl (.inr ⟨_, m₀, m₁⟩))))) => decide (m₀.1 ≠ m₁.1)
  | _ => false

/-- Every challenge `(a, (p₀, m₀), (p₁, m₁))` of `A` has equal public parts `p₀ = p₁`. -/
def EqualPubChallenges [DecidableEq Pub] (A : Adversary SS RS AD (Pub × M) C) : Prop :=
  A.IsQueryBoundP (fun t => unequalPubChall (SS := SS) (RS := RS) (AD := AD) (C := C) t = true) 0

/-- The FS-AEAD query `t` carries an AD of class other than `k₀`. -/
def queryADOutsideClass {Msg κ : Type} [DecidableEq κ] (cls : AD → κ) (k₀ : κ) :
    (unifSpec + spec SS RS AD Msg C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl (.inl ⟨a, _⟩))))) => decide (cls a ≠ k₀)
  | .inr (.inl (.inl (.inl (.inl (.inr ⟨a, _⟩))))) => decide (cls a ≠ k₀)
  | .inr (.inl (.inr ⟨a, _⟩)) => decide (cls a ≠ k₀)
  | .inr (.inr ⟨a, _⟩) => decide (cls a ≠ k₀)
  | _ => false

/-- **DEV-FS20 (libsignal): one AD class per adversary.** Restricts `A`'s `transmit`, `challenge`,
`deliver`, and `inject` queries to a single AD class `k₀` (one epoch in libsignal, whose MAC binds
the epoch only through its parity). -/
def AllQueriesInOneADClass {Msg κ : Type} [DecidableEq κ] (cls : AD → κ) (A : Adversary SS RS AD Msg C) :
    Prop :=
  ∃ k₀, A.IsQueryBoundP
    (fun t => queryADOutsideClass (SS := SS) (RS := RS) (Msg := Msg) (C := C) cls k₀ t = true) 0

end FSAEAD
namespace SM
variable {St Msg Coins C Pub : Type}

/-- The SM query `t` is a challenge `chall-P(m₀, m₁, r)` with `pubOf m₀ ≠ pubOf m₁`. -/
def unequalPubChall [DecidableEq Pub] (pubOf : Msg → Pub) :
    (unifSpec + spec St Msg Coins C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inr ⟨_, m₀, m₁, _⟩)))) => decide (pubOf m₀ ≠ pubOf m₁)
  | _ => false

/-- Every SM challenge `chall-P(m₀, m₁, r)` of `A` has `pubOf m₀ = pubOf m₁`. -/
def EqualPubChalls [DecidableEq Pub] (pubOf : Msg → Pub) (A : Adversary St Msg Coins C) : Prop :=
  A.IsQueryBoundP (fun t => unequalPubChall (St := St) (Coins := Coins) (C := C) pubOf t = true) 0

end SM
end CryptoGames
