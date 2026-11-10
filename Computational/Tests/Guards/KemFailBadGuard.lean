/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Game.StatementPqOomGame
public import LibsignalBinary.Proofs.SpqrV1.MlKemCorrectFacts

/-!
# Guards for the ML-KEM Failure Event `MlKem.KemFailBad`

**Checked by Lean.** Checks the bad event `MlKem.KemFailBad` and the failure-probability terms
`sessionKemFailProb` and `CliKemFailProb`. On 64-byte send coin tapes, `MlKem.tapePairFails` reduces
to `K.honestExchangeFails` (whereas 32-byte receive coin tapes never trigger it), any failing pair
in the coin log sets `KemFailBad = true`, and for the ideal KEM `MlKem.ideal` both failure
probabilities vanish.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Guards.KemFailBad

open OracleComp OracleSpec MeasureTheory ENNReal
open CryptoVerification.E2E CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession
  CryptoGames CryptoGames.LibsignalSession

theorem kemFailBad_nil (K : MlKem) : K.KemFailBad [] = false := rfl

theorem tapePairFails_of_length_ne_left (K : MlKem) (t₁ t₂ : List (BitVec 8))
    (h : t₁.length ≠ 64) : K.tapePairFails t₁ t₂ = false := by
  unfold MlKem.tapePairFails
  split
  · contradiction
  · rfl

theorem tapePairFails_of_length_ne_right (K : MlKem) (t₁ t₂ : List (BitVec 8))
    (h : t₂.length ≠ 64) : K.tapePairFails t₁ t₂ = false := by
  unfold MlKem.tapePairFails
  simp [h]

theorem tapePairFails_of_length (K : MlKem) (t₁ t₂ : List (BitVec 8)) (h₁ : t₁.length = 64)
    (h₂ : t₂.length = 64) :
    K.tapePairFails t₁ t₂ =
      K.honestExchangeFails ⟨t₁, h₁⟩ ⟨t₂.take 32, by simp [h₂]⟩ := by
  unfold MlKem.tapePairFails
  simp [h₁, h₂]

theorem tapePairFails_coinBytes (K : MlKem) (r₁ r₂ : BitVec 512) :
    K.tapePairFails (coinBytes r₁) (coinBytes r₂) =
      K.honestExchangeFails ⟨coinBytes r₁, coinBytes_length r₁⟩
        ⟨(coinBytes r₂).take 32, by simp [coinBytes_length r₂]⟩ :=
  tapePairFails_of_length K _ _ (coinBytes_length r₁) (coinBytes_length r₂)

theorem cliCoinsTape?_send (s : CliPartyState) (m : List (BitVec 8)) (rs : BitVec 512) :
    cliCoinsTape? (cliPqSendInp s m rs) = some (coinBytes rs) := by
  simp [cliCoinsTape?, cliPqSendInp, cliPqDirInputs]

/-- Receive inputs carry a 32-byte coin tape `HMAC.keyToBytes32 rc`, so they never match the
64-byte guard in `tapePairFails`. -/
theorem cliCoinsTape?_recv (s : CliPartyState) (c : List (BitVec 8)) (rc : BitVec 256) :
    cliCoinsTape? (cliPqRecvInp s c rc) = some (HMAC.keyToBytes32 rc) := by
  simp [cliCoinsTape?, cliPqRecvInp, cliPqDirInputs]

theorem kemFailBad_of_mem (K : MlKem) (log : List (List (BitVec 8))) (t₁ t₂ : List (BitVec 8))
    (h₁ : t₁ ∈ log) (h₂ : t₂ ∈ log) (h : K.tapePairFails t₁ t₂ = true) :
    K.KemFailBad log = true := by
  unfold MlKem.KemFailBad
  rw [List.any_eq_true]
  exact ⟨t₁, h₁, List.any_eq_true.mpr ⟨t₂, h₂, h⟩⟩

theorem kemFailBad_of_coinBytes (K : MlKem) (log : List (BitVec 512)) (r₁ r₂ : BitVec 512)
    (h₁ : r₁ ∈ log) (h₂ : r₂ ∈ log)
    (h : K.honestExchangeFails ⟨coinBytes r₁, coinBytes_length r₁⟩
        ⟨(coinBytes r₂).take 32, by simp [coinBytes_length r₂]⟩ = true) :
    K.KemFailBad (log.map coinBytes) = true :=
  kemFailBad_of_mem K _ _ _ (List.mem_map_of_mem h₁) (List.mem_map_of_mem h₂)
    (by rw [tapePairFails_coinBytes]; exact h)

theorem tapePairFails_ideal (t₁ t₂ : List (BitVec 8)) : MlKem.ideal.tapePairFails t₁ t₂ = false := by
  unfold MlKem.tapePairFails
  split
  · split
    · exact MlKem.ideal_honestFail _ _
    · rfl
  · rfl

theorem kemFailBad_ideal (log : List (List (BitVec 8))) : MlKem.ideal.KemFailBad log = false := by
  unfold MlKem.KemFailBad
  simp [tapePairFails_ideal]

theorem sessionKemFailProb_ideal {α : Type} (C : Crypto) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    sessionKemFailProb C MlKem.ideal ℓ decT encT qep oa ida idb s A = 0 := by
  unfold sessionKemFailProb
  exact prEvent_eq_zero_of_forall_not _ _ fun z => by simp [kemFailBad_ideal]

theorem cliKemFailProb_ideal (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512)) (hK : W.Q.K = MlKem.ideal) :
    CliKemFailProb S run X W l qep decT encT A = 0 := by
  unfold CliKemFailProb
  exact prEvent_eq_zero_of_forall_not _ _ fun z => by simp [hK, kemFailBad_ideal]

end CryptoVerification.E2E.Guards.KemFailBad
