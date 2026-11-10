/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim

@[expose] public section

set_option autoImplicit false

/-!
# Simulator Ghost Chains and Epoch-0 Bound Terms

**Checked by Lean.**

Ghost receiver-chain tracking (`GhostChain`) and the signed-pre-key epoch-0 PRG distinguisher and
error term (`epoch0Distinguisher`, `epoch0Term`) for the libsignal-to-Fig. 8 simulator.
-/

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet
namespace LibsignalSim

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA LibsignalSession LibsignalInst

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}

/-- Public part of a libsignal receiver chain tracked by the simulator. -/
structure GhostChain where
  key : Option PublicKey
  epoch : ℕ
  last : ℕ
  skipped : List ℕ

/-- Update a ghost chain on accepting 1-based index `i`, keeping at most 2000 skipped indices. -/
def GhostChain.accept (g : GhostChain) (i : ℕ) : GhostChain :=
  if g.last < i then
    { g with last := i,
             skipped :=
               ((List.range (i - 1 - g.last)).map (fun d => i - 1 - d) ++ g.skipped).take 2000 }
  else { g with skipped := g.skipped.erase i }

/-- Structural rejection check at index `i`: duplicate or evicted key, jump past 25000, or `u32` counter overflow. -/
def GhostChain.rejects (g : GhostChain) (i : ℕ) : Bool :=
  if i ≤ g.last then !(g.skipped.contains i)
  else decide (25000 < i - 1 - g.last) || decide (2 ^ 32 ≤ i)

/-- Restricted libsignal game configuration for `epoch0Distinguisher`, refusing `corr-A` while `A` retains epoch 0. -/
def configEpoch0Distinguisher (onImage : List (BitVec 8) → Bool) :
    SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)) :=
  { configR1OnCurve onImage with
    base := { SM.Config.h1 with injectFull := (· == 0) }
    corrOK := fun s P =>
      noAliceCorrWhileAliceBelowEpoch10 s P && !(P == Party.A && (s.st Party.A).chainEpochs.contains 0) }

/-- PRG distinguisher running the libsignal game from epoch-0 keys `(rc.1, rc.2)` and testing for an
uncorrupted epoch-0 injection at `A`. -/
def epoch0Distinguisher (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    PRGScheme.PRGAdversary (Ratchet.RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let (_, s) ← SM.runR (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

/-- Epoch-0 error term combining the `rootKdfAsPrg` advantage of `epoch0Distinguisher` with `q`
uniform-key MAC forgery attempts. -/
noncomputable def epoch0Term (P : Params PQ PQC) (ℓ : ℕ) (encPt : Pt → List (BitVec 8)) (lam : Pt)
    (onImage : List (BitVec 8) → Bool) (qep q : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : ℝ≥0∞ :=
  (rootKdfAsPrg P.C.F (encPt lam)).prgAdvantage (epoch0Distinguisher P ℓ onImage qep A) +
    q * ⨆ (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
      (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
      𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest P.C.F c salt ids ser tag)] {true}

end LibsignalSim
end Ratchet
end CryptoGames
