/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalRefinesDefs
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed
public import Computational.Proofs.CryptoGames.SM.ReductionsQueries
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.QueryBounds
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RestrictedReds
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltHop

/-!
# Intermediate statements of the libsignal session theorem

**Checked by Lean.**

Intermediate reductions, query bounds, and the H1 session refinement (`Refine.libsignal_refines`)
from the restricted libsignal SM game (DEV-LS1–DEV-LS7) to ACD19's H1 game (DEV-LS6). Assumes short
version-4 header round-tripping (`SignalRoundTripShort`, DEV-LS21), single-epoch AD classes
(DEV-LS8), public message parts (DEV-LS13), and the salt hop (DEV-LS25).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

namespace PubRed

variable {MK CK AD Pub M C : Type}

end PubRed

namespace Inst

variable {Pt : Type}

end Inst

namespace Pres

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- If `A` has equal-pub challenges, `redFSAuth` on `challSim A` has equal-pub challenges and a
single AD epoch. -/
theorem auth_restricted (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (qep : ℕ) (A : Fig8Adv Pt ℓ)
    (heq : SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) A) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    FSAEAD.EqualPubChallenges (redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep j tL t (Thm1.challSim (2 + 1) qep A)) ∧
      FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) (redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep j tL t (Thm1.challSim (2 + 1) qep A)) := by
  exact LibsignalSM.Proofs.RestrictedReds.auth_restricted_proof Dh encPt C codec ℓ encT idOf maxSkip lam qep A heq j tL t

/-- If `A` has equal-pub challenges, `redFSPriv` and `redFSPrivCoin` on `privRedB` have equal-pub
challenges and a single AD epoch. -/
theorem priv_restricted (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (qep : ℕ) (A : Fig8Adv Pt ℓ)
    (heq : SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) A) (tL : Option ℕ) (i : ℕ) :
    let fs := lFS C codec ℓ encT idOf maxSkip
    let B := ThmB.privRedB (2 + 1) qep i (lBlank ℓ) A
    (FSAEAD.EqualPubChallenges (redFSPriv (dhScheme Dh) (rootPRNG C.F encPt) fs lam 1 qep tL i B) ∧
      FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1)
        (redFSPriv (dhScheme Dh) (rootPRNG C.F encPt) fs lam 1 qep tL i B)) ∧
    (FSAEAD.EqualPubChallenges (redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt) fs lam 1 qep tL i B) ∧
      FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1)
        (redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt) fs lam 1 qep tL i B)) := by
  exact LibsignalSM.Proofs.RestrictedReds.priv_restricted_proof Dh encPt C codec ℓ encT idOf maxSkip lam qep A heq tL i (lBlank ℓ) (fun _ => rfl)

end Pres

namespace Refine

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-- `sim A` makes at most `q` Fig. 8 queries if `A` makes at most `q`. -/
theorem sim_queries (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) :
    SM.MakesAtMostQueries (sim P ℓ Dh encT decT qep A) q := by
  let _ := ‹SampleableType Pt›
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.sim_queries_proof P Dh encT decT qep q A hq

/-- Under X25519 realization of `Dh`, short version-4 wire round-tripping, `LengthsOk`,
`SpqrOffCorrect`, and per-pair ratchet-key collision bound `δ`, `LibSim` holds with
`εcoll = (qep + 2) * (q + qep + 2) * δ`. -/
theorem libsignal_refines (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ) (hfit : SignalEncodeFits32 P.codec)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : Corr.SpqrOffCorrect P.spqr) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) :
    LibSim P ℓ Dh encPt encT decT idOf lam qep q ((qep + 2) * (q + qep + 2) * δ) := by
  exact CryptoGames.LibsignalSM.Proofs.Refinement.libsignal_refines_proof P ℓ Dh encPt encT decT hX hdec hrt hL hfit hinj
    hdum hz hS idOf hid lam qep q hq32 δ hδ

end Refine

namespace Corr

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC]

end Corr

section Fig8Bound

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-- Unbounded-FS-AEAD form of the ACD19 Theorem 6 H1 bound for `lFS` and Fig. 8 adversary `B`. -/
noncomputable def fig8H1Bound (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (B : Fig8Adv Pt ℓ) : ℝ≥0∞ :=
  let cka := dhScheme Dh
  let prng := rootPRNG C.F encPt
  let fs := lFS C codec ℓ encT idOf 25000
  2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
      (CKA.advantage cka 1 (healEpoch tL)
          (redCKAAuth cka prng fs lam 1 qep tL t (Thm1.challSim (2 + 1) qep B))
        + PRFPRNG.advantage prng
          (redPRNGAuth cka prng fs lam 1 qep tL t (Thm1.challSim (2 + 1) qep B))
        + ∑ j ∈ Finset.range q, FSAEAD.advantage fs
            (redFSAuth cka prng fs lam 1 qep j tL t (Thm1.challSim (2 + 1) qep B)))
    + 2 * ∑ i ∈ Finset.range (qep + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
      (2 * CKA.advantage cka 1 (healEpoch tL)
          (redCKAPriv cka prng fs lam 1 qep tL i (ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B))
        + 2 * PRFPRNG.advantage prng
          (redPRNGPriv cka prng fs lam 1 qep tL i (ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B))
        + FSAEAD.advantage fs
          (redFSPriv cka prng fs lam 1 qep tL i (ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B))
        + 2 * FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam 1 qep tL i
          (ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B)))

end Fig8Bound

end CryptoGames.LibsignalSM
