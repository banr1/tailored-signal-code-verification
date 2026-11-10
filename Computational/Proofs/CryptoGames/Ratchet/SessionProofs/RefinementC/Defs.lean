/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Defs
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalRefinesCDefs

/-!
# Definitions for the refinement without salt binding

Invariants, joint-state step functions, eager-coin runs, and coupling relations (`CloseByRefinesH`,
`CloseByStateC`) for the refinement with `libsignalToModularSchemeSim` under `Corr.SpqrSendCorrectQ`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## SPQR hypothesis and invariants -/

/-- `Corr.SpqrSendCorrectQ S q` at a fixed graded invariant `Inv`. -/
def SpqrCLocal (S : Spqr PQ PQC) (q : ℕ) (Inv : ℕ → PQ → Prop) : Prop :=
  Corr.SpqrInvClosedQ S Inv ∧ (∀ n st r, n < q → Inv n st → (S.send st r).isSome) ∧
    ∀ n st r, n < q → Inv n st → S.sendPanics st r = false

theorem spqrSendCorrectQ_iff_exists_spqrCLocal (S : Spqr PQ PQC) (q : ℕ) :
    Corr.SpqrSendCorrectQ S q ↔ ∃ Inv, SpqrCLocal S q Inv := Iff.rfl

/-- SPQR invariant with `r` send queries remaining out of `q`. -/
def InvB (Inv : ℕ → PQ → Prop) (q r : ℕ) (st : PQ) : Prop :=
  ∃ n, n + r ≤ q ∧ Inv n st

theorem InvB.init {S : Spqr PQ PQC} {q : ℕ} {Inv : ℕ → PQ → Prop} (hS : SpqrCLocal S q Inv)
    (dir : SpqrDirection) (k : BitVec 256) : InvB Inv q q (S.init dir k) :=
  ⟨0, by omega, hS.1.init dir k⟩

theorem InvB.recv {S : Spqr PQ PQC} {q r : ℕ} {Inv : ℕ → PQ → Prop} (hS : SpqrCLocal S q Inv)
    {st : PQ} {msg} {st' : PQ} {salt} (h : InvB Inv q r st) (hr : S.recv st msg = .ok (st', salt)) :
    InvB Inv q r st' := by
  obtain ⟨n, hn, hI⟩ := h
  exact ⟨n, hn, hS.1.recv n st msg st' salt hI hr⟩

theorem InvB.send {S : Spqr PQ PQC} {q r : ℕ} {Inv : ℕ → PQ → Prop} (hS : SpqrCLocal S q Inv)
    (hr0 : 0 < r) {st : PQ} {rq : PQC} {st' : PQ} {salt msg} (h : InvB Inv q r st)
    (hs : S.send st rq = some (st', salt, msg)) : InvB Inv q (r - 1) st' := by
  obtain ⟨n, hn, hI⟩ := h
  exact ⟨n + 1, by omega, hS.1.send n st rq st' salt msg hI hs⟩

theorem InvB.mono {Inv : ℕ → PQ → Prop} {q r r' : ℕ} (hle : r' ≤ r) {st : PQ}
    (h : InvB Inv q r st) : InvB Inv q r' st := by
  obtain ⟨n, hn, hI⟩ := h
  exact ⟨n, by omega, hI⟩

theorem spqrCLocal_total {S : Spqr PQ PQC} {q r : ℕ} {Inv : ℕ → PQ → Prop}
    (hS : SpqrCLocal S q Inv) (hr0 : 0 < r) : Corr.SpqrSendTotalOn S (InvB Inv q r) := by
  rintro st rq ⟨n, hn, hI⟩
  exact hS.2.1 n st rq (by omega) hI

theorem spqrCLocal_noSendPanic {S : Spqr PQ PQC} {q r : ℕ} {Inv : ℕ → PQ → Prop}
    (hS : SpqrCLocal S q Inv) (hr0 : 0 < r) :
    ∀ st rq, InvB Inv q r st → S.sendPanics st rq = false := by
  rintro st rq ⟨n, hn, hI⟩
  exact hS.2.2 n st rq (by omega) hI

theorem spqrCLocal_closedRecv {S : Spqr PQ PQC} {q r : ℕ} {Inv : ℕ → PQ → Prop}
    (hS : SpqrCLocal S q Inv) :
    ∀ st msg st' salt, InvB Inv q r st → S.recv st msg = .ok (st', salt) → InvB Inv q r st' :=
  fun _ _ _ _ h hr => InvB.recv hS h hr

/-- `HonestEntryInvW` without its salt-binding conjunct. -/
def HonestEntryInvC (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
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
    w.length < 2 ^ 32

theorem honestEntryInvC_len_lt {P : Params PQ PQC} {Inv : PQ → Prop} {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {epExp : ℕ → BitVec 256} {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInvC P Inv Dh encT epExp wc) : wc.1.length < 2 ^ 32 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩
  exact h

theorem HonestEntryInvW.toC {P : Params PQ PQC} {Inv : PQ → Prop} {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {epExp : ℕ → BitVec 256} {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInvW P Inv Dh encT epExp wc) : HonestEntryInvC P Inv Dh encT epExp wc := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, hd, body, h8, h9, h10, h11, h12, _, h13⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, hd, body, h8, h9, h10, h11, h12, h13⟩

/-- `SimInvW` instantiated with `HonestEntryInvC` in place of `HonestEntryInvW`. -/
structure SimInvC (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
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
    HonestEntryInvC P Inv Dh encT epExp wc ∧
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
  hpqInv : ∀ Q, Inv (s.pq Q)

theorem SimInvW.toC {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))} {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)} {ec : Party → BitVec 256}
    {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp) :
    SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp :=
  { h with hhon := fun wc hwc => ⟨(h.hhon wc hwc).1.toC, (h.hhon wc hwc).2⟩ }

theorem SimInvC.mono {P : Params PQ PQC} {Inv Inv' : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))} {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)} {ec : Party → BitVec 256}
    {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hpq : ∀ Q, Inv' (s.pq Q)) :
    SimInvC P Inv' ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp :=
  { h with hhon := h.hhon, hpqInv := hpq }

/-- Uniqueness of honest records at any Fig. 8 `(epoch, idx)` position. -/
def PosUniq (s : SimState PQ Pt ℓ) : Prop :=
  ∀ wc₁ ∈ s.honest, ∀ wc₂ ∈ s.honest, wc₁.2.1.1 = wc₂.2.1.1 → wc₁.2.2.1 = wc₂.2.2.1 → wc₁ = wc₂

/-- Agreement between `libsignalToModularSchemeSim`'s `kept` state and Fig. 8's party states. -/
structure KeptInv (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop where
  hfull : ∀ Q st, (sC.kept Q).full = some st → st = s_fig8.st Q
  hrs : ∀ Q t v, (sC.kept Q).full = none → (sC.kept Q).rs t = some v → (s_fig8.st Q).vR t = some v
  hvR : ∀ Q t, ((s_fig8.st Q).vR t).isSome ↔ (t ≤ (s_fig8.st Q).tcur ∧ Q.sendsIn t = false)

/-- Honest indices in a party's current sending epoch are at most `mir.idx`. -/
def HonestIdxLe (s : SimState PQ Pt ℓ) : Prop :=
  ∀ wc ∈ s.honest, wc.2.1.1 = s.mir.epoch (Party.senderOf wc.2.1.1) →
    wc.2.2.1 ≤ s.mir.idx (Party.senderOf wc.2.1.1)

/-! ### Epoch chain keys (`EpochSync`) -/

/-- Chain key after `n` steps of `lChainPRG` from `k`. -/
def lChainAt (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256) : ℕ → BitVec 256
  | 0 => k
  | n + 1 => ((lChainPRG F n).gen (lChainAt F k n)).1

/-- Message-key seed at 1-based index `i` of a chain initialized with `k`. -/
def lSeedAt (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256) (i : ℕ) : BitVec 256 :=
  ((lChainPRG F (i - 1)).gen (lChainAt F k (i - 1))).2

/-- Agreement of a receiving FS-AEAD session with epoch chain key `k`. -/
def RecvAgrees (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256)
    (v : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) : Prop :=
  v.chainKey = lChainAt F k v.lastIndex ∧ ∀ p ∈ v.skippedKeys, p.2 = lSeedAt F k p.1

/-- Agreement of a sending FS-AEAD session with epoch chain key `k`. -/
def SendAgrees (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256)
    (v : FSAEAD.RatchetSenderState (BitVec 256)) : Prop :=
  v.chainKey = lChainAt F k v.lastIndex

/-- Synchronization of a corruption snapshot with epoch chain keys `K`, root keys `rk`, and exponents `epExp`. -/
def SnapSync (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (K rk epExp : ℕ → BitVec 256) (tFront : ℕ)
    (snap : Party × ℕ × GhostState PQ) : Prop :=
  snap.1.sendsIn snap.2.1 = true ∧
  snap.2.1 ≤ tFront ∧
  snap.2.2.session.rootKey = rk snap.2.1 ∧
  (∃ j < 2 ^ 32,
    snap.2.2.session.senderChain =
      some ⟨KeyPair.generate C (epExp snap.2.1),
            ⟨lChainAt C.F (K snap.2.1) j, BitVec.ofNat 32 j⟩⟩) ∧
  (∀ rc ∈ snap.2.2.session.receiverChains,
    ∃ ep ≤ snap.2.1,
      rc.senderRatchetKey = encT (Dh.dh (epExp ep) Dh.base) ∧
      (∃ j < 2 ^ 32, rc.chainKey = some ⟨lChainAt C.F (K ep) j, BitVec.ofNat 32 j⟩) ∧
      (∀ mk ∈ rc.messageKeys,
        mk.seed = keyToBytes32 (lSeedAt C.F (K ep) (mk.counter.toNat + 1)))) ∧
  (2 ≤ snap.2.1 →
    ∃ rc_last, snap.2.2.session.receiverChains.getLast? = some rc_last ∧
      rc_last.senderRatchetKey = encT (Dh.dh (epExp (snap.2.1 - 1)) Dh.base))

/-- Synchronization of honest records, recorded sender sessions, snapshots, and Fig. 8 states with
epoch chain keys `K` and root keys `rk`. -/
structure EpochSyncK (P : Params PQ PQC) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (honest : List (List (BitVec 8) × Fig8C Pt))
    (sent : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    (snaps : List (Party × ℕ × GhostState PQ))
    (st : Party → Fig8St Pt) (K rk epExp : ℕ → BitVec 256) : Prop where
  hhon : ∀ wc ∈ honest, ∃ res,
    (lFS P.C P.codec ℓ encT idOf 25000).receive
      ⟨lChainAt P.C.F (K wc.2.1.1) (wc.2.2.1 - 1), wc.2.2.1 - 1, []⟩ wc.2.1 wc.2.2 = some res
  hhdr : ∀ wc ∈ honest, (st (Party.senderOf wc.2.1.1)).tcur = wc.2.1.1 →
    (st (Party.senderOf wc.2.1.1)).curCkaMsg = wc.2.1.2
  hsent : ∀ e ∈ sent, e.2.lastIndex + 1 = e.1.2.1 ∧ SendAgrees P.C.F (K e.1.1.1) e.2
  hrecv : ∀ R t v, (st R).vR t = some v → RecvAgrees P.C.F (K t) v
  hsend : ∀ R v, (st R).vS = some v → R.sendsIn (st R).tcur = true →
    SendAgrees P.C.F (K (st R).tcur) v
  hahead : ∀ R, (st R).tcur = (st R.other).tcur + 1 → R.sendsIn (st R).tcur = true ∧ ∃ x,
    (st R).γ = .exp x ∧ (st R).curCkaMsg = some (Dh.dh x Dh.base) ∧
    (rootPRNG P.C.F encPt).up (st R.other).root ((dhScheme Dh).receive (st R.other).γ (Dh.dh x Dh.base)).2 =
      ((st R).root, K (st R).tcur)
  hequal : ∀ R, (st R).tcur = (st R.other).tcur → R.sendsIn (st R).tcur = true →
    (st R).root = (st R.other).root ∧
    ∃ x, (st R).γ = .exp x ∧ (st R.other).γ = .pub (Dh.dh x Dh.base)
  hgap : ∀ R, (st R).tcur ≤ (st R.other).tcur + 1
  hvS : ∀ R, R.sendsIn (st R).tcur = true → ((st R).vS).isSome
  hsent_ep : ∀ e ∈ sent, e.1.1.1 ≤ (st (Party.senderOf e.1.1.1)).tcur
  hroot : ∀ R, (st R).root = rk (st R).tcur
  hγ_exp : ∀ R, R.sendsIn (st R).tcur = true → (st R).γ = .exp (epExp (st R).tcur)
  hStep : ∀ e < max (st .A).tcur (st .B).tcur,
    rootKdf P.C.F (rk e) (encPt (Dh.dh (epExp (e + 1)) (Dh.dh (epExp e) Dh.base))) =
      (rk (e + 1), K (e + 1))
  hsnaps : ∀ snap ∈ snaps,
    SnapSync P.C Dh encT K rk epExp (max (st .A).tcur (st .B).tcur) snap

/-- Existence of synchronized epoch chain keys and root keys prior to a Fig. 8 win. -/
def EpochSync (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (honest : List (List (BitVec 8) × Fig8C Pt))
    (sent : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    (snaps : List (Party × ℕ × GhostState PQ))
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (epExp : ℕ → BitVec 256) : Prop :=
  s_fig8.win = false →
    ∃ K rk, EpochSyncK P ℓ encT idOf Dh encPt honest sent snaps s_fig8.st K rk epExp

/-- Combined C-side coupling invariant (`SimInvC`, `PosUniq`, `KeptInv`, `HonestIdxLe`, and `EpochSync`). -/
structure SimInvCX (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool)
    (epExp : ℕ → BitVec 256) : Prop where
  hsim : SimInvC P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp
  huniq : PosUniq sC.base
  hkept : KeptInv P Dh encPt encT idOf lam sC s_fig8
  hidx : HonestIdxLe sC.base
  hsync : EpochSync P Dh encPt encT idOf sC.base.honest sC.sent sC.snaps s_fig8 epExp

/-! ## Joint state and steps -/

/-- Joint state pairing `libsignalToModularSchemeSim`'s state, the Fig. 8 game state, and the probe flag. -/
abbrev JointC (PQ Pt : Type) (ℓ : ℕ) :=
  LibsignalToModularSchemeSimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool

def JointC.sim (x : JointC PQ Pt ℓ) :
    SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
  (x.1.base, x.2.1)

def JointC.withSim (x : JointC PQ Pt ℓ)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    JointC PQ Pt ℓ :=
  ({ x.1 with base := st.1 }, st.2, x.2.2)

/-- Updates `kept` and `sent` after `simSend` emits a message. -/
def cxSend (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (Q : Party)
    (x : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ) (res : Option (List (BitVec 8))) :
    LibsignalToModularSchemeSimState PQ Pt ℓ :=
  match res with
  | none => { x with base := s' }
  | some _ =>
    let sent := match (x.kept Q).full, s'.honest.head? with
      | some st, some (_, c) =>
        if st.id.sendsIn (st.tcur + 1) then x.sent
        else match st.vS with
          | some v => (c, v) :: x.sent
          | none => x.sent
      | _, _ => x.sent
    { x with
      base := s',
      kept := Function.update x.kept Q
        (Kept.send (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (x.kept Q)),
      sent }

/-- One non-stopping C-side oracle step (`simImplC` with `probeHook`). -/
def stepSimCNone (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) :
    ProbComp ((SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q × JointC PQ Pt ℓ) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  (((simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) (H := probeHook fig (qep + 1)) Dh (.inr q)).run
      x.1).run x.2) >>= fun r => pure (r.1.1, (r.1.2, r.2))

/-- Pure C-side forward of `c'` at `k = none`, handling case-3a resync and probe when `c3a = true`. -/
def fwdCPure (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC PQ Pt ℓ) : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let sC := x.1
  let plain : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ :=
    let z := fwdPure fig 3 (qep + 1) SM.Config.h1 sC.base Q c' x.2.1
    let kept' := match z.1 with
      | some (.accepted _ _ _) => Function.update sC.kept Q (Kept.recv (fig := fig) (fs := fs) c' (sC.kept Q))
      | _ => sC.kept
    let a := onAnswerPure qep Q w isDel ci? T pq' z.1 sC.base
    (a.1, ({ sC with base := a.2, kept := kept' }, z.2, x.2.2))
  match honestC with
  | some c =>
    if c3a && decide (c ≠ c') && isDel && !(sC.base.mir.safeInj 3) then
      match predictReceiveWithSnapshots (fig := fig) (fs := fs) P sC Q w c c' with
      | some none => (some .rejected, x)
      | some (some (t, i, pm)) =>
        let z := deliverPure fig SM.Config.h1 Q c x.2.1
        match z.1 with
        | some (.accepted _ _ _) =>
          let kept' := Function.update sC.kept Q (Kept.recv (fig := fig) (fs := fs) c (sC.kept Q))
          let a := onAcceptPure qep Q w true t i pm.2 ci? T pq' sC.base
          (a.1, ({ sC with base := a.2, kept := kept' }, z.2, x.2.2))
        | _ => (some .rejected, (sC, z.2, x.2.2))
      | none =>
        (some .rejected, (sC, x.2.1, x.2.2 || (fig.receive (x.2.1.st Q) c').isSome))
    else plain
  | none => plain

/-- Pure C-side forward of `c'` on an evicted salt mismatch. -/
def fwdEvictCPure (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (x : JointC PQ Pt ℓ) : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  if c3a && isDel && !(x.1.base.mir.safeInj 3) then
    (some .rejected, (x.1, x.2.1, x.2.2 || (fig.receive (x.2.1.st Q) c').isSome))
  else fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel none T pq' none c' x

/-- Pure C-side receive step at `k = none`, parameterized by whether case 3a (`c3a`) is enabled. -/
def simRecvStepCGen (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) :
    Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ :=
  let s := x.1.base
  if s.stopped then (none, x)
  else if s.mir.win then (none, x)
  else if isDel && (s.mir.inTransit Q.other w).isNone then (none, x)
  else if !isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) then (none, x)
  else if w.length < 9 then (some .rejected, x)
  else
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    match (signalWireCodec P.codec).parse ser with
    | none => (some .rejected, x)
    | some (h, _) =>
      if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) then (some .rejected, x)
      else if P.spqr.recvPanics (s.pq Q) h.pqRatchet then (some .rejected, x)
      else match P.spqr.recv (s.pq Q) h.pqRatchet with
      | .error _ => (some .rejected, x)
      | .ok (pq', salt) =>
        let i := h.counter.toNat + 1
        let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
        let mkC (t : ℕ) (T : Option Pt) : Fig8C Pt :=
          match honestC with
          | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((t, T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
          | none => ((t, T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
        let T? := decT h.senderRatchetKey
        let spkAmb := Q == Party.A && (s.chains Q).any (·.key.isNone)
        match (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
        | some ci =>
          let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
          if g.rejects i then (some .rejected, x)
          else fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel (some ci) h.senderRatchetKey pq'
            honestC (mkC g.epoch T?) x
        | none =>
          let evicted := (honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true
          if evicted && (honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true then
            (some .rejected, x)
          else if T? == some 0 then (some .rejected, x)
          else
            let amb := inReceiveOnlyEpoch s.mir Q || spkAmb
            let x₁ : JointC PQ Pt ℓ :=
              if amb then ({ x.1 with base := { s with amb := s.amb + 1 } }, x.2) else x
            if inReceiveOnlyEpoch s.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then (some .rejected, x₁)
            else match T? with
            | none => (some .rejected, x₁)
            | some T =>
              if evicted then
                fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel h.senderRatchetKey pq'
                  ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) x₁
              else
                fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel none h.senderRatchetKey pq'
                  honestC (mkC (s.mir.epoch Q + 1) (some T)) x₁

/-- Pure C-side receive step at `k = none` with case 3a enabled. -/
abbrev simRecvStepC (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) :
    Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ :=
  simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep true Q w isDel x

/-- Whether `w` parses with `Q`'s addresses and triggers `spqr.recvPanics`. -/
def recvPanicsW (P : Params PQ PQC) (Q : Party) (w : List (BitVec 8)) (s : SimState PQ Pt ℓ) :
    Bool :=
  if w.length < 9 then false
  else match (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
    | none => false
    | some (h, _) =>
      if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) then false
      else P.spqr.recvPanics (s.pq Q) h.pqRatchet

/-- Whether `sim`'s receive step for family `k` stops without an SPQR receive panic. -/
def simRecvStops (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Bool :=
  !recvPanicsW P Q w st.1 && !st.1.stopped &&
    (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel 0 st).2.1.stopped

theorem recvPanicsW_eq_false_of_simRecvStops (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w isDel st = true) :
    recvPanicsW P Q w st.1 = false := by
  unfold simRecvStops at h
  cases hp : recvPanicsW P Q w st.1
  · rfl
  · rw [hp] at h; simp at h

theorem simRecvStops_eq_of_not_recvPanicsW (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hp : recvPanicsW P Q w st.1 = false) (hs : st.1.stopped = false) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w isDel st =
      (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel 0 st).2.1.stopped := by
  unfold simRecvStops
  rw [hp, hs]
  rfl

/-- One C-side oracle step for family `k`, switching to `stepSim` on `simRecvStops`. -/
def stepSimC (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) :
    ProbComp ((SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q × JointC PQ Pt ℓ) :=
  match q with
  | .inl (.inl (.inr (Q, w))) =>
    if simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true x.sim then
      stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x.sim >>= fun r =>
        pure (r.1, x.withSim r.2)
    else stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x
  | .inl (.inr (Q, w)) =>
    if simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim then
      stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x.sim >>= fun r =>
        pure (r.1, x.withSim r.2)
    else stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x
  | q' => stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q' x

/-- Whether `(Q, w)` is an evicted honest wire with a mismatched salt arriving in a receive-only epoch. -/
def evictCaseC (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (s : SimState PQ Pt ℓ) : Bool :=
  if s.stopped then false
  else if s.mir.win then false
  else if isDel && (s.mir.inTransit Q.other w).isNone then false
  else if !isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w)) then false
  else if w.length < 9 then false
  else
    let ser := w.take (w.length - 8)
    match (signalWireCodec P.codec).parse ser with
    | none => false
    | some (h, _) =>
      if !(addressCheckPasses h.addresses (P.expectedAddrs Q)) then false
      else if P.spqr.recvPanics (s.pq Q) h.pqRatchet then false
      else match P.spqr.recv (s.pq Q) h.pqRatchet with
      | .error _ => false
      | .ok (_, salt) =>
        let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
        match (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
        | some _ => false
        | none =>
          let evicted := (honestC.map fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true
          if evicted && (honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true then false
          else if decT h.senderRatchetKey == some 0 then false
          else evicted && inReceiveOnlyEpoch s.mir Q

/-- Whether family `k` stops on `evictCaseC` at the `k`-th ambiguous receive. -/
def evictStopsC (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (k : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) : Bool :=
  evictCaseC P encT decT Q w isDel x.1.base && k == some x.1.base.amb

/-- Stopping transition for `evictStopsC`, recording libsignal's spurious-accept win bit under `c_cka`. -/
def evictStopStepC (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (decT : PublicKey → Option Pt)
    (Q : Party) (w : List (BitVec 8)) (c_cka : BitVec 256) (x : JointC PQ Pt ℓ) :
    Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ :=
  (none, ({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1, stopped := true } },
    { x.2.1 with win := spurPtStep P Dh encPt decT Q w false c_cka x.sim }, x.2.2))

def stepSimCEagerTransmit (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    ProbComp (Option (List (BitVec 8)) × (JointC PQ Pt ℓ × (Party → BitVec 256))) :=
  stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r x.sim ec >>= fun res =>
    pure (res.1, ((cxSend P Dh encPt encT idOf lam Q x.1 res.2.1.1 res.1, res.2.1.2, x.2.2), res.2.2))

def stepSimCEagerChall (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    ProbComp (Option (List (BitVec 8)) × (JointC PQ Pt ℓ × (Party → BitVec 256))) :=
  stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r x.sim ec >>= fun res =>
    pure (res.1, ((cxSend P Dh encPt encT idOf lam Q x.1 res.2.1.1 res.1, res.2.1.2, x.2.2), res.2.2))

/-- Eager-coin C-side `deliver` step, stopping on `simRecvUsesCoin` or `evictStopsC`. -/
def stepSimCEagerDeliver (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    ProbComp (Option (RecvResult (Plain ℓ)) × (JointC PQ Pt ℓ × (Party → BitVec 256))) :=
  if simRecvUsesCoin P encT decT k Q w true x.sim && !recvPanicsW P Q w x.1.base then
    let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true (ec Q) x.sim
    updateAllEagerCoins x.1.base.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
    pure (res.1, (x.withSim res.2, ec'))
  else if evictStopsC P encT decT k Q w true x then
    let res := evictStopStepC P Dh encPt decT Q w (ec Q) x
    updateAllEagerCoins x.1.base.mir res.2.1.base.mir (· == Q) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))
  else
    stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x >>= fun res =>
    updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))

def stepSimCEagerInject (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    ProbComp (Option (RecvResult (Plain ℓ)) × (JointC PQ Pt ℓ × (Party → BitVec 256))) :=
  if simRecvUsesCoin P encT decT k Q w false x.sim && !recvPanicsW P Q w x.1.base then
    let res := simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false (ec Q) x.sim
    updateAllEagerCoins x.1.base.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
    pure (res.1, (x.withSim res.2, ec'))
  else if evictStopsC P encT decT k Q w false x then
    let res := evictStopStepC P Dh encPt decT Q w (ec Q) x
    updateAllEagerCoins x.1.base.mir res.2.1.base.mir (· == Q) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))
  else
    stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x >>= fun res =>
    updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
    pure (res.1, (res.2, ec'))

def stepSimCEagerCorr (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    ProbComp (Option (GhostState PQ) × (JointC PQ Pt ℓ × (Party → BitVec 256))) :=
  stepSimC P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) x >>= fun res =>
  updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
  pure (res.1, (res.2, ec'))

/-- One eager-coin C-side oracle step. -/
def stepSimCEager (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    ProbComp ((SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q ×
      (JointC PQ Pt ℓ × (Party → BitVec 256))) :=
  match q with
  | .inl (.inl (.inl (.inl (Q, m₀, r)))) =>
    stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r x ec
  | .inl (.inl (.inl (.inr (Q, m₀, m₁, r)))) =>
    stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r x ec
  | .inl (.inl (.inr (Q, w))) =>
    stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec
  | .inl (.inr (Q, w)) =>
    stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec
  | .inr Q =>
    stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q x ec

def simEagerImplC (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ) :
    QueryImpl (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (JointC PQ Pt ℓ × (Party → BitVec 256)) ProbComp) :=
  fun q => StateT.mk fun ⟨x, ec⟩ => stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k q x ec

/-- Runs adversary computation `oa` against the eager-coin C-side oracles. -/
def runSimCEager {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) :
    ProbComp (α × (JointC PQ Pt ℓ × (Party → BitVec 256))) :=
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (JointC PQ Pt ℓ × (Party → BitVec 256)) ProbComp) +
    simEagerImplC P ℓ Dh encPt encT decT idOf lam qep k
  (simulateQ impl oa).run (x, ec)

/-- Indexed `cWin` experiment family for the eager C run. -/
def runWinAtC {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool) (idx : ℕ) : ProbComp Bool :=
  match idx with
  | 0 =>
    runSimCEager P ℓ Dh encPt encT decT idOf lam qep none oa x ec >>=
      fun r => pure r.2.1.2.1.win
  | j + 1 =>
    if j < x.1.base.amb then
      pure (winBefore j)
    else
      runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) oa x ec >>=
        fun r => pure (r.2.1.1.base.stopped && r.2.1.2.1.win)

/-- Hidden-salt `cHid` experiment returning the final probe flag of the eager C run. -/
def runHidC {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) : ProbComp Bool :=
  runSimCEager P ℓ Dh encPt encT decT idOf lam qep none oa x ec >>= fun r => pure r.2.1.2.2

/-! ## Coupling relations -/

/-- `CloseByRefines` extended with an additional hidden-salt error term `cHid`. -/
def CloseByRefinesH (n : ℕ) (d : ℝ≥0∞)
    (cR cS : ProbComp Bool) (cWin : ℕ → ProbComp Bool) (cEps0 cHid : ProbComp Bool) : Prop :=
  𝒟[cR] {true} ≤
      𝒟[cS] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} +
        𝒟[cHid] {true} ∧
    𝒟[cS] {true} ≤
      𝒟[cR] {true} + (∑ k ∈ Finset.range n, 𝒟[cWin k] {true}) + d + 𝒟[cEps0] {true} +
        𝒟[cHid] {true}

/-- State-indexed `CloseByRefinesH` coupling between the R game and the eager C run. -/
def CloseByStateC {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool)
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool) : Prop :=
  CloseByRefinesH (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir))
    (runRCont (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) oa s_R >>=
      fun z => pure (post z.1 || z.2.win))
    (runSimCEager P ℓ Dh encPt encT decT idOf lam qep none oa (sC, s_fig8, fl) ec >>=
      fun z => pure (post z.1 || z.2.1.2.1.win))
    (runWinAtC P ℓ Dh encPt encT decT idOf lam qep oa (sC, s_fig8, fl) ec winBefore)
    (runRCont (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) oa s_R >>=
      fun z => pure ((decide (0 < z.2.maxAcc .A 0) || z.2.win) && !(z.2.corrs.contains (.B, 0))))
    (runHidC P ℓ Dh encPt encT decT idOf lam qep oa (sC, s_fig8, fl) ec)

/-- Experiment returning Fig. 8 `win` in the H1 game against `libsignalToModularSchemeSim`. -/
def simCNoneWinEvent (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, s) ← SM.run sm 3 (qep + 1) SM.Config.h1 b (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)
  return s.win

end CryptoGames.LibsignalSM.Proofs.Refinement
