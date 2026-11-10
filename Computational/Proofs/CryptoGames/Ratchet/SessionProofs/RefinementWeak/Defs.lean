/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrHyp
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation

/-!
# Definitions for the refinement under the weak SPQR hypothesis

Defines `SpqrWLocal`, `HonestEntryInvW`, and `SimInvW`, weakening the SPQR assumptions of `SimInv` to hold relative to an inductive SPQR state invariant `Inv`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-- `Corr.SpqrWeakCorrect S` specialized to a fixed invariant `Inv`. -/
def SpqrWLocal (S : Spqr PQ PQC) (Inv : PQ → Prop) : Prop :=
  Corr.SpqrInvClosed S Inv ∧ Corr.SpqrSendTotalOn S Inv ∧ Corr.SpqrSaltBindingOn S Inv

/-- Variant of `HonestEntryInv` weakening SPQR salt agreement to states satisfying `Inv`. -/
def HonestEntryInvW (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (epExp : ℕ → BitVec 256)
    (wc : List (BitVec 8) × Fig8C Pt) : Prop :=
  let w := wc.1
  let c := wc.2
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  w = LibsignalSim.toWire c ∧
  ¬ w.length < 9 ∧
  1 ≤ c.1.1 ∧
  c.2.2.1 = (ser, tag) ∧
  1 ≤ c.2.1 ∧ c.2.1 < 2 ^ 32 ∧
  c.1.2 = some (Dh.dh (epExp c.1.1) Dh.base) ∧
  ∃ h body,
    (signalWireCodec P.codec).parse ser = some (h, body) ∧
    h.messageVersion = currentVersion ∧
    h.senderRatchetKey = encT (Dh.dh (epExp c.1.1) Dh.base) ∧
    h.counter.toNat + 1 = c.2.1 ∧
    addressCheckPasses h.addresses (P.expectedAddrs (Party.senderOf c.1.1).other) = true ∧
    (∀ pq_st pq' salt, Inv pq_st → P.spqr.recv pq_st h.pqRatchet = .ok (pq', salt) →
      effectiveHkdfSalt32 salt = c.2.2.2) ∧
    w.length < 2 ^ 32

/-- Variant of `SimInv` using `HonestEntryInvW` and tracking `Inv` on both simulated SPQR states. -/
structure SimInvW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool)
    (epExp : ℕ → BitVec 256) : Prop where
  hmeta : SameMeta s_R s s_fig8
  hcomp : ∀ p ∈ s.mir.comp, SM.healedBy s.mir.tL 3 p.epoch = false
  hec : ValidEagerCoins s.mir ec
  hwinBefore : ∀ j < s.amb, winBefore j = false
  hamb : s.amb + r ≤ q
  hamb_strict : (0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B) → s.amb + r < q
  hidx_le : ∀ Q, s.mir.idx Q + r ≤ q
  hhon_len : s.honest.length + r ≤ q
  hep_le : ∀ Q, s.mir.epoch Q ≤ qep
  hep_adj : ∀ Q, (inReceiveOnlyEpoch s.mir Q = true → s.mir.epoch Q ≤ s.mir.epoch Q.other) ∧
    s.mir.epoch Q ≤ s.mir.epoch Q.other + 1
  hst_R : ∀ Q, s_R.st Q = expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s Q (s_fig8.st Q) (ec Q)
  hst_id : ∀ Q, (s_fig8.st Q).id = Q
  htcur : ∀ Q, (s_fig8.st Q).tcur = s.mir.epoch Q
  hepExp0 : epExp 0 = x₀
  hspur : ∀ Q, ∃ rk_base T_base,
    (inReceiveOnlyEpoch s.mir Q = true →
      (s_fig8.st Q).root = rk_base ∧
      (s_fig8.st Q).γ = .pub T_base ∧
      T_base ≠ 0 ∧
      epExp (s.mir.epoch Q + 1) = ec Q) ∧
    (inReceiveOnlyEpoch s.mir Q = false →
      (s_fig8.st Q).γ = .exp (epExp (s.mir.epoch Q)) ∧
      (0 < s.mir.epoch Q →
        (s_fig8.st Q).root = (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 ∧
        (s_fig8.st Q).curCkaMsg = some (Dh.dh (epExp (s.mir.epoch Q)) Dh.base)) ∧
      ∃ vS, (s_fig8.st Q).vS = some vS ∧ vS.lastIndex = s.mir.idx Q) ∧
    (∀ wc ∈ s.honest, Party.senderOf wc.2.1.1 = Q.other →
      wc.2.1.1 ≤ s.mir.epoch Q → wc.2.1.1 ∉ (s.chains Q).map (·.epoch) →
      0 < s.mir.epoch Q ∧
      spurBadSingle P encPt Dh Q rk_base T_base wc.1 wc.2.2.2.2 (epExp wc.2.1.1)
        (epExp (maxActiveEp s.mir Q)) = false)
  hchainsA : ChainsEpochInvA (s.mir.epoch .A) (s.chains .A)
  hchainsA_ep : (s.chains .A).map (·.epoch) = epListA (s.mir.epoch .A / 2)
  hchainsB_ep : (s.chains .B).map (·.epoch) = epListB ((s.mir.epoch .B + 1) / 2)
  hchainsB_none : ∀ g ∈ s.chains .B, g.key.isNone = false
  hcorrB0 : (.B, 0) ∈ s.mir.corrs → ∀ g ∈ s.chains .A, g.key.isNone = false
  hchains_sync : ∀ Q g, g ∈ s.chains Q →
    g.epoch ≤ s.mir.epoch Q ∧
    Q.sendsIn g.epoch = false ∧
    (if g.key.isNone then some (encT (Dh.dh x₀ Dh.base)) else g.key) =
      some (encT (Dh.dh (epExp g.epoch) Dh.base)) ∧
    ∃ v, (s_fig8.st Q).vR g.epoch = some v ∧ ChainSync g v
  hhon : ∀ wc ∈ s.honest,
    HonestEntryInvW P Inv Dh encT epExp wc ∧
    wc.2.1.1 ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) ∧
    (Party.senderOf wc.2.1.1).sendsIn wc.2.1.1 = true ∧
    wc.2.1.1 ≤ s.mir.epoch (Party.senderOf wc.2.1.1)
  htrans_hon : ∀ rec_f ∈ s_fig8.trans,
    (LibsignalSim.toWire rec_f.ct, rec_f.ct) ∈ s.honest ∧
    rec_f.pos.sender = Party.senderOf rec_f.ct.1.1 ∧
    rec_f.pos.epoch = rec_f.ct.1.1 ∧
    rec_f.pos.idx = rec_f.ct.2.1
  hcoll : ∀ t₁ t₂,
    t₁ ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) →
    t₂ ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) →
    Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂
  /-- Both simulated SPQR states satisfy `Inv`. -/
  hpqInv : ∀ Q, Inv (s.pq Q)

theorem simInvW_init (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (b : Bool) (k_root x₀ eA₀ pqrKey : BitVec 256)
    (hcoll0 : Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base)
    (hcl : Corr.SpqrInvClosed P.spqr Inv) :
    let sm_R := libsignalSessionScheme P ℓ encPt lam
    let sm_fig8 := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let s_R := SM.initState sm_R.sendPart (k_root, x₀, eA₀, pqrKey) b
    let s := initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let s_fig8 := SM.initState sm_fig8 (k_root, x₀) b
    let ec : Party → BitVec 256 := fun Q => match Q with | .A => eA₀ | .B => 0
    let epExp : ℕ → BitVec 256 := fun t => if t = 0 then x₀ else if t = 1 then eA₀ else 0
    SimInvW P Inv ℓ Dh encPt encT qep q q x₀ s_R s s_fig8 ec (fun _ => false) epExp := by
  intro sm_R sm_fig8 s_R s s_fig8 ec epExp
  have h := simInv_init P ℓ Dh encPt encT idOf lam qep q hX b k_root x₀ eA₀ pqrKey hcoll0
  exact { h with
    hhon := fun wc hwc => absurd hwc (by simp [s, initSim])
    hpqInv := fun Q => by cases Q <;> simp [s, initSim, hcl.init] }

end CryptoGames.LibsignalSM.Proofs.Refinement
