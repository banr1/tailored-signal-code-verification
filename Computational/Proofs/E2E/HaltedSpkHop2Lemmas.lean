/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.E2E.HaltedSpkHop2Init
public import Computational.Proofs.E2E.HaltedSpkHop2Phase2Last
import Computational.Proofs.E2E.HaltedSpkHop2Phase0
import Computational.Proofs.E2E.HaltedSpkHop2Phase1

/-!
# Tracker-Halted Hop-2 Hybrid Lemmas

Re-exports the tracker-halted Hop-2 initial bridge and terminal hybrid bound, and composes Phases 2,
1, and 0 to prove `evalDist_hop2PrfRedKTrackHalted_true_le_hop2PrgRedKTrackHalted_succ`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkHop2Lemmas

export Computational.Proofs.E2E.HaltedSpkHop2Init (
  evalDist_spkLeakRedTrackHalted_apply_le_hop2PrgRedKTrackHalted_zero)
export Computational.Proofs.E2E.HaltedSpkHop2Phase2Last (
  evalDist_hop2PrfRedKTrackHalted_last_le)

open scoped ENNReal
open OracleComp
open Computational.Proofs.E2E.HaltedSpkDefs (hop2PrfRedKTrackHalted hop2PrgRedKTrackHalted)
open Computational.Proofs.E2E.HaltedSpkHop2Phase0 (
  evalDist_hop2PrfRedKTrackHalted_true_le_hop2PrgRedKTrackHalted_succ_of_phase1)
open Computational.Proofs.E2E.HaltedSpkHop2Phase1 (Hop2TrackPhase2Bound
  evalDist_runHop2Track_phase1_le)
open Computational.Proofs.E2E.HaltedSpkHop2Phase2Last (evalDist_runHop2Track_phase2_le_createColl)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (GhostState LengthsOk Params PublicKey)
open CryptoGames.Ratchet (expandPRG extractPRF)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh)
open CryptoGames.SM (Adversary MakesAtMostQueries)
open CryptoVerification.E2E (Bytes)
open CryptoVerification.E2E.SpkHop1 (hop2CreateCollUnit)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)

section Hop2Step

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Tracker-halted Hop-2 hybrid step `k → k + 1` bound connecting Phases 2, 1, and 0. -/
theorem evalDist_hop2PrfRedKTrackHalted_true_le_hop2PrgRedKTrackHalted_succ {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep q : ℕ) (s : BitVec 256) (k : ℕ)
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) :
    𝒟[(extractPRF P.C.F encPt).branch true
        (hop2PrfRedKTrackHalted P K ℓ Dh encT decT qep s k A)] {true} ≤
      𝒟[(expandPRG P.C.F).prgRealExperiment
        (hop2PrgRedKTrackHalted P K ℓ Dh encPt encT decT qep s (k + 1) A)] {true} +
        ((6 * q : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh := by
  refine evalDist_hop2PrfRedKTrackHalted_true_le_hop2PrgRedKTrackHalted_succ_of_phase1
    P K hcodec hL Dh encPt encT decT hX hdec qep q s k
    (fun rc_L oa rem hq_oa st tr hrel1 => ?_) A hq
  have hph2 : Hop2TrackPhase2Bound P K Dh encPt decT encT ℓ qep s k rc_L :=
    fun u_chall Q_create oa' rem' hq' sL tr' tL sR hrel2 hwin_inv =>
      evalDist_runHop2Track_phase2_le_createColl K hcodec hL hX hdec hz qep s k rc_L
        u_chall Q_create oa' rem' hq' sL tr' tL sR hrel2 hwin_inv
  simpa only [List.length_nil, add_zero] using
    evalDist_runHop2Track_phase1_le hcodec hL hX hdec qep s k rc_L hph2 oa rem hq_oa st tr [] st hrel1

end Hop2Step

end Computational.Proofs.E2E.HaltedSpkHop2Lemmas
