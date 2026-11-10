/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed
public import Computational.Proofs.CryptoGames.SM.Reductions
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.CostedTables
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# Libsignal Session Reduction Programs and Concrete Advantage Bounds

First-order `ReductionDsl` simulator programs (`Refine.SimProg`, `Refine.evalSim`) and concrete and
costed ACD19 Theorem 5 and Theorem 6 advantage bounds (`fsShortBound`, `fsShortBoundWith`,
`fig8ShortBoundWith`) for the libsignal Double Ratchet instance.
-/

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

namespace Refine

/-- First-order `ReductionDsl.CostedReduction` simulator program from the libsignal R1 session game
to the ACD19 Fig. 8 SM instance. -/
abbrev SimProg (PQ PQC Pt : Type) [SampleableType PQC] [DecidableEq Pt] [Zero Pt]
    (ℓ : ℕ) (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) :=
  ReductionDsl.CostedReduction
    (LibsignalSim.simOps (ℓ := ℓ) P Dh encT decT)
    (LibsignalSim.simIface PQ PQC Pt ℓ)
    (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (LibsignalSim.simCodec PQ PQC Pt ℓ)
    .unit .unit .bool .bool

/-- Evaluate a `SimProg` reduction program on a libsignal R1 adversary `A`. -/
def evalSim {PQ PQC Pt : Type} [SampleableType PQC] [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} {P : Params PQ PQC}
    {Dh : DHFun (BitVec 256) Pt} {encT : Pt → PublicKey}
    {decT : PublicKey → Option Pt}
    (R : SimProg PQ PQC Pt ℓ P Dh encT decT) (A : LibAdv PQ PQC ℓ) : Fig8Adv Pt ℓ :=
  R.eval (fun _ => A) ()

end Refine

end CryptoGames.LibsignalSM

namespace CryptoVerification.LibsignalSession

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD

section Bounds

variable {Pt : Type} [DecidableEq Pt]

/-- Slot `j` chain-PRG advantage term of ACD19 Theorem 5 against `lChainPRG`. -/
noncomputable def chainPRGTerm (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (R : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  (lChainPRG C.F (j / 2)).prgAdvantage
    (FSAEAD.Thm5.cumulativeChainPrgReduction (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) (lChainPRG C.F)
      maxForwardJumps j (pubToAD codec R))

/-- Computational slot sum of `fsShortBound` over the `fsSlotCount qR` active hybrid slots. -/
noncomputable def fsCompBound (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (qR qd : ℕ) (R : FsAdv Pt ℓ) : ℝ≥0∞ :=
  2 * ∑ j ∈ Finset.range (fsSlotCount qR),
    (chainPRGTerm C codec ℓ encT idOf R (FSAEAD.Thm5.slotToHybridHopIndex qR j) +
      (2 * saltPRFTerm C codec ℓ encT idOf qR R (FSAEAD.Thm5.slotToHybridHopIndex qR j) +
        wireOtccaTerm C codec ℓ encT idOf qR qd R (FSAEAD.Thm5.slotToHybridHopIndex qR j)))

/-- ACD19 Theorem 5 bound for an FS-AEAD adversary `R` with at most `qR` queries and `qd`
decryption queries (`DEV-LS10`, `DEV-LS13`, `DEV-LS14`, `DEV-LS23`, `DEV-LS25`). -/
noncomputable def fsShortBound (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (qR qd : ℕ) (R : FsAdv Pt ℓ) : ℝ≥0∞ :=
  fsCompBound C codec ℓ encT idOf qR qd R + 4 * macForgeryTerm C qd

variable [Zero Pt] [SampleableType Pt]

/-!
**DEV-LS30 (formalization): terms left open.** ACD19 composes Thm 6 with Thm 3 (CKA from DDH),
Thm 5, and the PRF-PRNG of §4.3; here the X25519 CKA, root-KDF PRF-PRNG, chain PRG, salt PRF, and
wire OT-CCA terms remain named advantages, and the MAC-forgery and spurious-step terms remain sups
over fixed tests.

**DEV-LS32 (formalization): `Δ_SM = 3`.** ACD19 Thm 6 sets `Δ_SM = 2 + Δ_CKA` with `Δ_CKA = 1`
from Thm 3, written `(2 + 1)` here with CKA parameter `1`.
-/

/-- Step-cost, query-count, and size-honesty bounds for a `Refine.SimProg` reduction program `R`
at query bound `q` and epoch cap `qep`. -/
def simCostedBounds {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    {ℓ : ℕ} {P : Params PQ PQC} {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt}
    (q qep : ℕ) (R : Refine.SimProg PQ PQC Pt ℓ P Dh encT decT) : Prop :=
  GRedBounded R (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep)

omit [Zero Pt] [SampleableType Pt] in
/-- `fsCompBound` evaluated on a costed FS-AEAD reduction bundle `R`. -/
noncomputable def fsCompBoundWith (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) : ℝ≥0∞ :=
  2 * ∑ j ∈ Finset.range (fsSlotCount qR),
    (chainPRGTermCosted C qR R A (FSAEAD.Thm5.slotToHybridHopIndex qR j) +
      (2 * saltPRFTermCosted C qR R A (FSAEAD.Thm5.slotToHybridHopIndex qR j) +
        wireOtccaTermCosted C codec ℓ qR R A (FSAEAD.Thm5.slotToHybridHopIndex qR j)))

omit [Zero Pt] [SampleableType Pt] in
/-- `fsShortBound` evaluated on a costed FS-AEAD reduction bundle `R`. -/
noncomputable def fsShortBoundWith (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (qR qd : ℕ) (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) : ℝ≥0∞ :=
  fsCompBoundWith C codec ℓ qR R A + 4 * macForgeryTerm C qd

/-- Concrete ACD19 Theorem 6 bound evaluated on costed Fig. 8 and FS-AEAD reduction bundles `R` and `Rfs`. -/
noncomputable def fig8ShortBoundWith (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam)
    (Rfs : FsCostedReds C codec ℓ encT idOf) (B : Fig8Adv Pt ℓ) : ℝ≥0∞ :=
  let cka := dhScheme Dh
  let prng := rootPRNG C.F encPt
  let authB := R.challSim.eval (fun _ => B) ()
  let privB := fun i => (R.privRedB i).eval (fun _ => B) ()
  2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
      (CKA.advantage cka 1 (healEpoch tL) ((R.redCKAAuth tL t).eval (fun _ => authB) ())
        + PRFPRNG.advantage prng ((R.redPRNGAuth tL t).eval (fun _ => authB) ())
        + ∑ j ∈ Finset.range q,
            fsShortBoundWith C codec ℓ (min (2 * q) (q + 2)) q Rfs
              ((R.redFSAuth j tL t).eval (fun _ => authB) ()))
    + 2 * ∑ i ∈ Finset.range (qep + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
      (2 * CKA.advantage cka 1 (healEpoch tL) ((R.redCKAPriv tL i).eval (fun _ => privB i) ())
        + 2 * PRFPRNG.advantage prng ((R.redPRNGPriv tL i).eval (fun _ => privB i) ())
        + fsShortBoundWith C codec ℓ (min (2 * q) (q + 2)) q Rfs
            ((R.redFSPriv tL i).eval (fun _ => privB i) ())
        + 2 * fsShortBoundWith C codec ℓ (min (2 * q) (q + 2)) q Rfs
            ((R.redFSPrivCoin tL i).eval (fun _ => privB i) ()))

end Bounds

end CryptoVerification.LibsignalSession
