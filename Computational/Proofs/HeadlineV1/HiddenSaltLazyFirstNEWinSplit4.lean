/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit3
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.KnownSeedEval
import Computational.Proofs.CryptoGames.SM.Theorem7Proof
import ProofLib.SepLogic.WP.StepsCore

/-!
# Lazy Corruption-Window Extraction

Derives the deliver-time corruption window and `DeliverHcasesAtExt` from a set probe flag under
`SimInvCXLazy`, `SnapSync`, and `CorrsKeptRecvInv`, without `SnapsInv` or strict `SimInvCX`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoGames.LibsignalSM.Proofs.Correctness CryptoGames.LibsignalSM.Proofs.SaltMismatch
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem evalC_eq_none_imp_kept_none
    {Pt PQ : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (c c' : Fig8C Pt)
    (heval : predictReceive (fig := fig) (fs := fs) sC Q c c' = none) :
    (sC.kept Q).full = none ∧ (sC.kept Q).rs c'.1.1 = none := by
  unfold predictReceive Kept.eval at heval
  cases hfull : (sC.kept Q).full with
  | some st =>
    rw [hfull] at heval
    cases heval
  | none =>
    rw [hfull] at heval
    dsimp only at heval
    cases hrs : (sC.kept Q).rs c'.1.1 with
    | some v =>
      rw [hrs] at heval
      cases heval
    | none =>
      exact ⟨rfl, rfl⟩

theorem corrs_lt_of_evalC_none_and_corrsKeptRecvInv
    {Pt PQ : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (c c' : Fig8C Pt)
    (hkept_corr : CorrsKeptRecvInv sC g)
    (heval : predictReceive (fig := fig) (fs := fs) sC Q c c' = none)
    (hc'_ep : c'.1.1 = c.1.1)
    (hQ_ns : Q.sendsIn c.1.1 = false) :
    ∀ e, (Q, e) ∈ g.corrs → e < c.1.1 := by
  rcases evalC_eq_none_imp_kept_none fig fs sC Q c c' heval with ⟨hfull, hrs⟩
  rw [hc'_ep] at hrs
  intro e hce
  by_contra hge
  have hle : c.1.1 ≤ e := Nat.le_of_not_lt hge
  rcases hkept_corr Q e hce c.1.1 hle hQ_ns with h1 | h2
  · rw [hfull] at h1; cases h1
  · rw [hrs] at h2; cases h2

theorem knownSeedR_none_no_corr_window_snapSync
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt]
    (P : Params PQ PQC)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace P.C.F Dh encPt)
    {Q : Party} {snaps : List (Party × ℕ × GhostState PQ)}
    (hsnaps : ∀ snap ∈ snaps, SnapSync P.C Dh encT tr.ck tr.rk tr.x tr.tFront snap)
    {t : ℕ} (ht : t ≤ tr.tFront) (hsends : Q.other.sendsIn t = true)
    {msg : SignalMessage} {w : List (BitVec 8)}
    (hw : SignalMessage.tryFrom P.codec w = .ok msg)
    (hY : msg.senderRatchetKey = encT (tr.T t))
    (hnone : snapshotMessageKeySeed P snaps Q t w = none) :
    (∀ e g, (Q, e, g) ∈ snaps → e ≤ t → e + 3 ≤ t) ∧
    (∀ e g, (Q.other, e, g) ∈ snaps → t ≠ e + 1) ∧
    (∀ g sc, (Q.other, t, g) ∈ snaps → g.session.senderChain = some sc →
      msg.counter.toNat < sc.chainKey.index.toNat) ∧
    ¬ ((∃ e₁ g₁, (Q.other, e₁, g₁) ∈ snaps ∧ t = e₁ + 2) ∧
       (∃ g₂, (Q.other, t, g₂) ∈ snaps)) := by
  unfold snapshotMessageKeySeed at hnone
  rw [hw] at hnone
  dsimp only at hnone
  have hor_none {a b : Option (List (BitVec 8))} (h : (a <|> b) = none) :
      a = none ∧ b = none := by
    cases a <;> cases b <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  rcases hor_none hnone with ⟨_, hk324_none⟩
  rcases hor_none hk324_none with ⟨hk3_none, hk24_none⟩
  rcases hor_none hk24_none with ⟨hk2_none, hk4_none⟩
  have hQ_ns_t : Q.sendsIn t = false := by
    have h := sendsIn_other_eq_not Q t
    rw [hsends] at h
    simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e g hmem hle
    have hsnap := hsnaps (Q, e, g) hmem
    have hQe : Q.sendsIn e = true := hsnap.1
    have hne_t : e ≠ t := by
      rintro rfl; rw [hQ_ns_t] at hQe; cases hQe
    have hne_t1 : t ≠ e + 1 := by
      intro ht1
      have hnone_e := List.findSome?_eq_none_iff.mp hk2_none (Q, e, g) hmem
      rcases hsnap.2.2.2.1 with ⟨j, _, hsc_eq⟩
      rw [lChainAt_eq_chainKeyValAt] at hsc_eq
      have hk2_eq := k2Seed_eq_some_of_trace hX hDh tr (e := e) (by omega)
        (sc := ⟨KeyPair.generate P.C (tr.x e),
          ⟨chainKeyValAt P.C.F (tr.ck e) j, BitVec.ofNat 32 j⟩⟩) rfl msg.counter
      unfold k2Seed at hk2_eq
      have hrk_e : g.session.rootKey = tr.rk e := hsnap.2.2.1
      have hsc_e : g.session.senderChain =
          some ⟨KeyPair.generate P.C (tr.x e),
            ⟨chainKeyValAt P.C.F (tr.ck e) j, BitVec.ofNat 32 j⟩⟩ := hsc_eq
      simp only [hQe, hY, ht1, and_self, ↓reduceIte, hrk_e, hsc_e,
        Option.bind_some] at hnone_e hk2_eq
      exact nomatch hnone_e.symm.trans hk2_eq
    have hne_t2 : t ≠ e + 2 := by
      intro ht2
      rw [ht2, Party.sendsIn_succ, Party.sendsIn_succ, Bool.not_not] at hQ_ns_t
      rw [hQ_ns_t] at hQe
      cases hQe
    omega
  · intro e g hmem ht1
    have hsnap := hsnaps (Q.other, e, g) hmem
    have h1 : Q.other.sendsIn e = true := hsnap.1
    rw [ht1, Party.sendsIn_succ, h1] at hsends
    cases hsends
  · intro g sc hmem hsc
    have hsnap := hsnaps (Q.other, t, g) hmem
    rcases hsnap.2.2.2.1 with ⟨j, hj, hsc_eq⟩
    rw [lChainAt_eq_chainKeyValAt] at hsc_eq
    have hsc' : sc = ⟨KeyPair.generate P.C (tr.x t),
        ⟨chainKeyValAt P.C.F (tr.ck t) j, BitVec.ofNat 32 j⟩⟩ :=
      Option.some.inj (hsc.symm.trans hsc_eq)
    have hidx : sc.chainKey.index.toNat = j := by
      rw [hsc']
      exact Nat.mod_eq_of_lt hj
    rw [hidx]
    by_contra hge
    rw [Nat.not_lt] at hge
    have hk3_eq := k3Seed_eq_some_of_trace hX tr hj (sc := sc)
      (by rw [hsc']) (by rw [hsc']) hge
    unfold k3Seed at hk3_eq
    have hnone_t := List.findSome?_eq_none_iff.mp hk3_none (Q.other, t, g) hmem
    simp only [↓reduceIte, hsc, Option.bind_some, hY] at hnone_t
    rw [hnone_t] at hk3_eq
    cases hk3_eq
  · rintro ⟨⟨e₁, g₁, hmem₁, ht_e1⟩, ⟨g₂, hmem₂⟩⟩
    have hsnap₁ := hsnaps (Q.other, e₁, g₁) hmem₁
    have hsnap₂ := hsnaps (Q.other, t, g₂) hmem₂
    rcases hsnap₁.2.2.2.1 with ⟨j₁, _, hsc₁_eq⟩
    rcases hsnap₂.2.2.2.1 with ⟨j₂, _, hsc₂_eq⟩
    rw [lChainAt_eq_chainKeyValAt] at hsc₁_eq hsc₂_eq
    have ht2 : 2 ≤ t := by omega
    rcases hsnap₂.2.2.2.2.2 ht2 with ⟨rc_last, hlast, hrc_last_rk⟩
    have he₁_eq : e₁ = t - 2 := by omega
    have hpk_cur : (KeyPair.generate P.C (tr.x t)).publicKey = encT (tr.T t) := by
      rw [KeyPair_generate_publicKey hX, EpochTrace.T]
    have hsc₂_eq' : g₂.session.senderChain =
        some ⟨KeyPair.generate P.C (tr.x t),
          ⟨chainKeyValAt P.C.F (tr.ck t) j₂, BitVec.ofNat 32 j₂⟩⟩ := hsc₂_eq
    have hlast' : g₂.session.receiverChains.getLast? = some rc_last := hlast
    rcases hcur_opt : (snaps.findSome? fun e_cur =>
        if e_cur.1 = Q.other ∧ e_cur.2.1 = t then
          e_cur.2.2.session.senderChain.bind fun sc_cur =>
            if sc_cur.ratchetKey.publicKey = msg.senderRatchetKey then
              e_cur.2.2.session.receiverChains.getLast?.map fun rc_last =>
                (rc_last.senderRatchetKey, sc_cur.ratchetKey.privateKey)
            else none
        else none) with _ | p
    · have hnone_cur := List.findSome?_eq_none_iff.mp hcur_opt (Q.other, t, g₂) hmem₂
      simp only [and_self, ↓reduceIte, hsc₂_eq', Option.bind_some, hY, hpk_cur, hlast',
        Option.map_some, reduceCtorEq] at hnone_cur
    · rw [hcur_opt, Option.bind_some] at hk4_none
      rcases mem_of_findSome?_eq_some hcur_opt with ⟨e_cur, hmem_cur, hbody_cur⟩
      split at hbody_cur
      · rename_i hcur_cond
        rcases hcur_cond with ⟨_, ht_cur⟩
        rcases hsnaps e_cur hmem_cur with ⟨_, _, _, ⟨j_cur, _, hsc_cur_eq⟩, _, hlast_cur⟩
        rw [lChainAt_eq_chainKeyValAt] at hsc_cur_eq
        rw [hsc_cur_eq, Option.bind_some] at hbody_cur
        split at hbody_cur
        · rw [Option.map_eq_some_iff] at hbody_cur
          rcases hbody_cur with ⟨rc_last_cur, hlast_cur_opt, hp_eq⟩
          rcases hlast_cur (by omega) with ⟨rc_last_cur', hlast_cur', hrc_last_cur_rk⟩
          rw [hlast_cur_opt] at hlast_cur'
          injection hlast_cur' with hrc_cur_eq
          subst hrc_cur_eq
          rw [ht_cur] at hrc_last_cur_rk hp_eq
          subst hp_eq
          have hk4_eq := k4Seed_eq_some_of_trace hX hDh tr (t := t) ht2 ht
            (sc_cur := ⟨KeyPair.generate P.C (tr.x t),
              ⟨chainKeyValAt P.C.F (tr.ck t) j_cur, BitVec.ofNat 32 j_cur⟩⟩)
            (sc_prev := ⟨KeyPair.generate P.C (tr.x e₁),
              ⟨chainKeyValAt P.C.F (tr.ck e₁) j₁, BitVec.ofNat 32 j₁⟩⟩)
            (rc_last := rc_last_cur)
            rfl hrc_last_cur_rk (by simp [he₁_eq]) msg.counter
          unfold k4Seed at hk4_eq
          simp only [Option.bind_some, hpk_cur, ↓reduceIte, ← he₁_eq] at hk4_eq
          have hnone_prev := List.findSome?_eq_none_iff.mp hk4_none (Q.other, e₁, g₁) hmem₁
          have hsends₁ : Q.other.sendsIn e₁ = true := hsnap₁.1
          have hrk₁_eq : g₁.session.rootKey = tr.rk e₁ := hsnap₁.2.2.1
          have hsc₁_eq' : g₁.session.senderChain =
              some ⟨KeyPair.generate P.C (tr.x e₁),
                ⟨chainKeyValAt P.C.F (tr.ck e₁) j₁, BitVec.ofNat 32 j₁⟩⟩ := hsc₁_eq
          simp only [hsends₁, ← ht_e1, and_self, ↓reduceIte] at hnone_prev
          rw [hrk₁_eq, hsc₁_eq', Option.bind_some] at hnone_prev
          exact nomatch hnone_prev.symm.trans hk4_eq
        · cases hbody_cur
      · cases hbody_cur

theorem no_corr_window_of_evalCK_none_snapSync
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (P : Params PQ PQC) (hX : X25519RealizesDh P.C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace P.C.F Dh encPt)
    {s : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party}
    (hsnaps : ∀ snap ∈ s.snaps, SnapSync P.C Dh encT tr.ck tr.rk tr.x tr.tFront snap)
    (hkept_corr : CorrsKeptRecvInv s g)
    (hcorrs_snaps : ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ s.snaps)
    {w : List (BitVec 8)} {c c' : Fig8C Pt}
    (ht : c.1.1 ≤ tr.tFront) (hsends : Q.other.sendsIn c.1.1 = true)
    (hc'_ep : c'.1.1 = c.1.1)
    {msg : SignalMessage}
    (hw : SignalMessage.tryFrom P.codec w = .ok msg)
    (hY : msg.senderRatchetKey = encT (tr.T c.1.1))
    (heval : predictReceiveWithSnapshots fig fs P s Q w c c' = none) :
    predictReceive (fig := fig) (fs := fs) s Q c c' = none ∧
    snapshotMessageKeySeed P s.snaps Q c.1.1 w = none ∧
    (∀ e, (Q, e) ∈ g.corrs → e + 3 ≤ c.1.1) ∧
    (∀ e, (Q.other, e) ∈ g.corrs → c.1.1 ≠ e + 1) ∧
    (∀ g₀ sc, (Q.other, c.1.1, g₀) ∈ s.snaps → g₀.session.senderChain = some sc →
      msg.counter.toNat < sc.chainKey.index.toNat) ∧
    (2 ≤ c.1.1 → ¬ ((Q.other, c.1.1 - 2) ∈ g.corrs ∧ (Q.other, c.1.1) ∈ g.corrs)) := by
  rcases (evalCK_eq_none_iff fig fs P s Q w c c').mp heval with ⟨hevC, hknone⟩
  have hQ_ns : Q.sendsIn c.1.1 = false := by
    have h0 := sendsIn_other_eq_not Q c.1.1
    rw [hsends] at h0
    simpa using h0
  have he_lt := corrs_lt_of_evalC_none_and_corrsKeptRecvInv
    fig fs s g Q c c' hkept_corr hevC hc'_ep hQ_ns
  rcases knownSeedR_none_no_corr_window_snapSync P hX hDh tr hsnaps ht hsends hw hY hknone
    with ⟨hw1_s, hw2_s, hw3_s, hw4_s⟩
  refine ⟨hevC, hknone, ?_, ?_, hw3_s, ?_⟩
  · intro e hce
    rcases hcorrs_snaps Q e hce with ⟨g₀, hg₀⟩
    exact hw1_s e g₀ hg₀ (Nat.le_of_lt (he_lt e hce))
  · intro e hce
    rcases hcorrs_snaps Q.other e hce with ⟨g₀, hg₀⟩
    exact hw2_s e g₀ hg₀
  · intro ht2 ⟨hc_tm2, hc_t⟩
    rcases hcorrs_snaps Q.other (c.1.1 - 2) hc_tm2 with ⟨g₁, hg₁⟩
    rcases hcorrs_snaps Q.other c.1.1 hc_t with ⟨g₂, hg₂⟩
    exact hw4_s ⟨⟨c.1.1 - 2, g₁, hg₁, by omega⟩, ⟨g₂, hg₂⟩⟩

theorem honestEntryInvC_header_and_tryFrom
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt]
    (P : Params PQ PQC) (Inv' : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (epExp : ℕ → BitVec 256)
    {w : List (BitVec 8)} {c : Fig8C Pt}
    (hhon : HonestEntryInvC P Inv' Dh encT epExp (w, c))
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body)) :
    SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ ∧
    1 ≤ c.1.1 ∧
    h.messageVersion = currentVersion ∧
    h.senderRatchetKey = encT (Dh.dh (epExp c.1.1) Dh.base) ∧
    h.counter.toNat + 1 = c.2.1 ∧
    c = ((c.1.1, some (Dh.dh (epExp c.1.1) Dh.base)),
      (c.2.1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), c.2.2.2))) := by
  have htry := tryFrom_of_parse P.codec w h body hlen hparse
  rcases hhon with
    ⟨_, _, ht1, hraw, _, _, hT, h_hdr, body_hdr, hparse_hdr, hver_hdr, hsrk_hdr, hctr_hdr, _⟩
  have hhb : (h, body) = (h_hdr, body_hdr) := Option.some.inj (hparse.symm.trans hparse_hdr)
  rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
  refine ⟨htry, ht1, hver_hdr, hsrk_hdr, hctr_hdr, ?_⟩
  rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
  dsimp only at hraw hT ⊢
  rw [hT, hraw]

def epochTrace_of_epochSyncK
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    {honest : List (List (BitVec 8) × Fig8C Pt)}
    {sent : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256))}
    {snaps : List (Party × ℕ × GhostState PQ)}
    {st : Party → Fig8St Pt} {K rk epExp : ℕ → BitVec 256}
    (hK : EpochSyncK P ℓ encT idOf Dh encPt honest sent snaps st K rk epExp)
    (hFront_pos : 1 ≤ max (st .A).tcur (st .B).tcur)
    (hDistinct : ∀ e₁ ≤ max (st .A).tcur (st .B).tcur,
      ∀ e₂ ≤ max (st .A).tcur (st .B).tcur,
      Dh.dh (epExp e₁) Dh.base = Dh.dh (epExp e₂) Dh.base → e₁ = e₂) :
    EpochTrace P.C.F Dh encPt where
  tFront := max (st .A).tcur (st .B).tcur
  rk := rk
  ck := K
  x := epExp
  hFront_pos := hFront_pos
  hStep := hK.hStep
  hDistinct := hDistinct

theorem corrs_window_of_evalCK_none_lazy
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (lam : Pt) (qep q r : ℕ) (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp)
    (hkept_corr : CorrsKeptRecvInv sC g)
    (hcorrs_snaps : ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ sC.snaps)
    {c c' : Fig8C Pt}
    (hc_mem : (w, c) ∈ sC.base.honest)
    (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hc'_ep : c'.1.1 = c.1.1)
    (heval : predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = none) :
    (∀ e, (Party.receiverOf c.1.1, e) ∈ g.corrs → e + 3 ≤ c.1.1) ∧
    (∀ e, (Party.senderOf c.1.1, e) ∈ g.corrs → c.1.1 ≠ e + 1) ∧
    (2 ≤ c.1.1 →
      ¬((Party.senderOf c.1.1, c.1.1 - 2) ∈ g.corrs ∧
        (Party.senderOf c.1.1, c.1.1) ∈ g.corrs)) ∧
    (∀ g₀ sc, (Party.senderOf c.1.1, c.1.1, g₀) ∈ sC.snaps →
      g₀.session.senderChain = some sc → c.2.1 ≤ sc.chainKey.index.toNat) := by
  rcases hinv.hsim.hhon (w, c) hc_mem with ⟨hhon_c, _, hsends_c, hc_le_sender⟩
  rcases honestEntryInvC_header_and_tryFrom P (InvB Inv q r) Dh encT epExp hhon_c hlen hparse with
    ⟨htry, ht1, _, hsrk, hctr, _⟩
  rcases hinv.hsync rfl with ⟨K, rk, hK⟩
  have htcur_eq : ∀ R, (g.st R).tcur = sC.base.mir.epoch R := hinv.hsim.htcur
  have hc_le_front : c.1.1 ≤ max (g.st .A).tcur (g.st .B).tcur := by
    rw [htcur_eq .A, htcur_eq .B]
    cases hP : Party.senderOf c.1.1 with
    | A => rw [hP] at hc_le_sender; exact le_trans hc_le_sender (le_max_left _ _)
    | B => rw [hP] at hc_le_sender; exact le_trans hc_le_sender (le_max_right _ _)
  have hFront_pos : 1 ≤ max (g.st .A).tcur (g.st .B).tcur := le_trans ht1 hc_le_front
  have hDistinct : ∀ e₁ ≤ max (g.st .A).tcur (g.st .B).tcur,
      ∀ e₂ ≤ max (g.st .A).tcur (g.st .B).tcur,
      Dh.dh (epExp e₁) Dh.base = Dh.dh (epExp e₂) Dh.base → e₁ = e₂ := by
    rw [htcur_eq .A, htcur_eq .B]
    exact fun e₁ he₁ e₂ he₂ hdh => hinv.hsim.hcoll e₁ e₂ he₁ he₂ hdh
  let tr := epochTrace_of_epochSyncK P encT idOf Dh encPt hK hFront_pos hDistinct
  have hsends : Q.other.sendsIn c.1.1 = true := hc_sender ▸ hsends_c
  rcases no_corr_window_of_evalCK_none_snapSync
    (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
    (lFS P.C P.codec ℓ encT idOf 25000)
    P hX hDh tr hK.hsnaps hkept_corr hcorrs_snaps hc_le_front hsends hc'_ep htry hsrk heval with
    ⟨_, _, hw1, hw2, hw3_s, hw4⟩
  have hrcv : Party.receiverOf c.1.1 = Q := by
    unfold Party.receiverOf; rw [hc_sender]; cases Q <;> rfl
  rw [← hrcv] at hw1
  rw [← hc_sender] at hw2 hw4
  exact ⟨hw1, hw2, hw4, hw3_of_snaps_no_corr_window hc_sender hctr.symm hw3_s⟩

theorem knownChain_fwdCPure_flag_true_corrs_window_lazy
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT)
    (lam : Pt) (qep q r : ℕ) (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp)
    (hkept_corr : CorrsKeptRecvInv sC g)
    (hcorrs_snaps : ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ sC.snaps)
    (hlen : ¬ w.length < 9) {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    {pq' : PQ} {salt : Salt} {ci : ℕ}
    (hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = some ci)
    (hfl : (fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true (some ci) h.senderRatchetKey pq'
      ((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2))
      (match (sC.base.honest.find? fun wc =>
          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
      | some c₀ =>
        if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀
        else ((((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, decT h.senderRatchetKey),
          (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
            effectiveHkdfSalt32 salt)))
      | none =>
        ((((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch, decT h.senderRatchetKey),
          (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
            effectiveHkdfSalt32 salt))))
      (sC, (g, false))).2.2.2 = true) :
    ∃ c, (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
        (·.2) = some c ∧
      (∀ e, (Party.receiverOf c.1.1, e) ∈ g.corrs → e + 3 ≤ c.1.1) ∧
      (∀ e, (Party.senderOf c.1.1, e) ∈ g.corrs → c.1.1 ≠ e + 1) ∧
      (2 ≤ c.1.1 →
        ¬((Party.senderOf c.1.1, c.1.1 - 2) ∈ g.corrs ∧
          (Party.senderOf c.1.1, c.1.1) ∈ g.corrs)) ∧
      (∀ g₀ sc, (Party.senderOf c.1.1, c.1.1, g₀) ∈ sC.snaps →
        g₀.session.senderChain = some sc → c.2.1 ≤ sc.chainKey.index.toNat) := by
  rcases fwdCPure_flag_true_imp_evalCK_none P ℓ Dh encPt encT idOf lam qep true Q w true (some ci)
    h.senderRatchetKey pq' _ _ sC g hfl with ⟨c, hhonC, heval⟩
  rcases honest_mem_and_sender_of_find_map_some hhonC with ⟨hc_mem, hc_sender⟩
  rcases honestEntryInvC_header_and_tryFrom P (InvB Inv q r) Dh encT epExp
    (hinv.hsim.hhon (w, c) hc_mem).1 hlen hparse with ⟨_, _, _, hsrk, hctr, hc_raw⟩
  let ch := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
  rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
    ⟨ch', hch_elem', hch_key'⟩
  have hch_eq : ch = ch' := by simp [ch, hch_elem']
  have hch_elem : (sC.base.chains Q)[ci]? = some ch := by rw [hch_eq, hch_elem']
  have hch_key : ch.key = some h.senderRatchetKey := by rw [hch_eq, hch_key']
  rcases hinv.hsim.hchains_sync Q ch (List.mem_of_getElem? hch_elem) with
    ⟨hch_ep_le, _, hch_key_sync, _⟩
  have hch_none : ch.key.isNone = false := by rw [hch_key]; rfl
  rw [hch_none] at hch_key_sync
  simp only [Bool.false_eq_true, ↓reduceIte, hch_key] at hch_key_sync
  have hdh : Dh.dh (epExp ch.epoch) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
    hinj ((Option.some.inj hch_key_sync).symm.trans hsrk)
  have hle_ch : ch.epoch ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) := by
    cases Q <;>
      [exact le_trans hch_ep_le (le_max_left _ _);
       exact le_trans hch_ep_le (le_max_right _ _)]
  have hch_ep : ch.epoch = c.1.1 :=
    hinv.hsim.hcoll ch.epoch c.1.1 hle_ch (hinv.hsim.hhon (w, c) hc_mem).2.1 hdh
  rw [hhonC] at heval; dsimp only at heval
  have hc'_ep : (if c.2.2.2 = effectiveHkdfSalt32 salt then c
      else ((ch.epoch, decT h.senderRatchetKey),
        (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
          effectiveHkdfSalt32 salt)))).1.1 = c.1.1 := by
    split_ifs <;> [rfl; exact hch_ep]
  rcases corrs_window_of_evalCK_none_lazy P Inv ℓ Dh hDh encPt encT idOf hX lam qep q r Q w x₀
    s_R sC g ec winBefore epExp hinv hkept_corr hcorrs_snaps hc_mem hc_sender hlen hparse
    hc'_ep heval with ⟨hw1, hw2, hw4, hw3⟩
  exact ⟨c, hhonC, hw1, hw2, hw4, hw3⟩

theorem newChain_fwdCPure_flag_true_corrs_window_lazy
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (lam : Pt) (qep q r : ℕ) (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp)
    (hkept_corr : CorrsKeptRecvInv sC g)
    (hcorrs_snaps : ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ sC.snaps)
    (heval_eq : ∀ c c',
      predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) P sC₁ Q w c c' =
      predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c')
    (hlen : ¬ w.length < 9) {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    {pq' : PQ} {salt : Salt} {T : Pt}
    (hev_false : ¬((((sC.base.honest.find? fun wc =>
        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true)
    (hfl : (fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true none h.senderRatchetKey pq'
      ((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2))
      (match (sC.base.honest.find? fun wc =>
          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
      | some c₀ =>
        if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀
        else ((sC.base.mir.epoch Q + 1, some T),
          (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
            effectiveHkdfSalt32 salt)))
      | none =>
        ((sC.base.mir.epoch Q + 1, some T),
          (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
            effectiveHkdfSalt32 salt))))
      (sC₁, (g, false))).2.2.2 = true) :
    ∃ c, (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
        (·.2) = some c ∧
      (∀ e, (Party.receiverOf c.1.1, e) ∈ g.corrs → e + 3 ≤ c.1.1) ∧
      (∀ e, (Party.senderOf c.1.1, e) ∈ g.corrs → c.1.1 ≠ e + 1) ∧
      (2 ≤ c.1.1 →
        ¬((Party.senderOf c.1.1, c.1.1 - 2) ∈ g.corrs ∧
          (Party.senderOf c.1.1, c.1.1) ∈ g.corrs)) ∧
      (∀ g₀ sc, (Party.senderOf c.1.1, c.1.1, g₀) ∈ sC.snaps →
        g₀.session.senderChain = some sc → c.2.1 ≤ sc.chainKey.index.toNat) := by
  rcases fwdCPure_flag_true_imp_evalCK_none P ℓ Dh encPt encT idOf lam qep true Q w true none
    h.senderRatchetKey pq' _ _ sC₁ g hfl with ⟨c, hhonC, heval⟩
  rw [heval_eq] at heval
  rcases honest_mem_and_sender_of_find_map_some hhonC with ⟨hc_mem, hc_sender⟩
  have hepoch : c.1.1 = sC.base.mir.epoch Q + 1 := by
    rw [hhonC] at hev_false
    simp only [Option.map_some, beq_iff_eq, Option.some.injEq, decide_eq_true_eq, not_ne_iff]
      at hev_false
    exact hev_false
  rw [hhonC] at heval; dsimp only at heval
  have hc'_ep : (if c.2.2.2 = effectiveHkdfSalt32 salt then c
      else ((sC.base.mir.epoch Q + 1, some T),
        (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
          effectiveHkdfSalt32 salt)))).1.1 = c.1.1 := by
    split_ifs <;> [rfl; exact hepoch.symm]
  rcases corrs_window_of_evalCK_none_lazy P Inv ℓ Dh hDh encPt encT idOf hX lam qep q r Q w x₀
    s_R sC g ec winBefore epExp hinv hkept_corr hcorrs_snaps hc_mem hc_sender hlen hparse
    hc'_ep heval with ⟨hw1, hw2, hw4, hw3⟩
  exact ⟨c, hhonC, hw1, hw2, hw4, hw3⟩

theorem simRecvStepC_deliver_flag_true_corrs_window_lazy
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT)
    (lam : Pt) (qep q r : ℕ) (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp)
    (hkept_corr : CorrsKeptRecvInv sC g)
    (hcorrs_snaps : ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ sC.snaps)
    (hno_ev : EvictedOnlyNoForgeAt P decT (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      sC g Q)
    (hprobe : (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 =
      true) :
    ∃ c, (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
        (·.2) = some c ∧
      (∃ h body, (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body)) ∧
      (∀ e, (Party.receiverOf c.1.1, e) ∈ g.corrs → e + 3 ≤ c.1.1) ∧
      (∀ e, (Party.senderOf c.1.1, e) ∈ g.corrs → c.1.1 ≠ e + 1) ∧
      (2 ≤ c.1.1 →
        ¬((Party.senderOf c.1.1, c.1.1 - 2) ∈ g.corrs ∧
          (Party.senderOf c.1.1, c.1.1) ∈ g.corrs)) ∧
      (∀ g₀ sc, (Party.senderOf c.1.1, c.1.1, g₀) ∈ sC.snaps →
        g₀.session.senderChain = some sc → c.2.1 ≤ sc.chainKey.index.toNat) := by
  unfold simRecvStepC simRecvStepCGen at hprobe
  by_cases hst : sC.base.stopped = true
  · simp only [hst, ↓reduceIte] at hprobe; cases hprobe
  simp only [hst, Bool.false_eq_true, ↓reduceIte] at hprobe
  by_cases hwin : sC.base.mir.win = true
  · simp only [hwin, ↓reduceIte] at hprobe; cases hprobe
  simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hprobe
  by_cases hdel : (true && (sC.base.mir.inTransit Q.other w).isNone) = true
  · simp only [hdel, ↓reduceIte] at hprobe; cases hprobe
  simp only [hdel, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and] at hprobe
  by_cases hlen : w.length < 9
  · simp only [hlen, ↓reduceIte] at hprobe; cases hprobe
  simp only [hlen, ↓reduceIte] at hprobe
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => rw [hparse] at hprobe; cases hprobe
  | some hb =>
    rcases hb with ⟨h, body⟩
    rw [hparse] at hprobe; dsimp only at hprobe
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp only [haddr, ↓reduceIte] at hprobe; cases hprobe
    simp only [haddr, Bool.false_eq_true, ↓reduceIte] at hprobe
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · simp only [hpan, ↓reduceIte] at hprobe; cases hprobe
    simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hprobe
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => rw [hspqr] at hprobe; cases hprobe
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      rw [hspqr] at hprobe; dsimp only at hprobe
      cases hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) with
      | some ci =>
        rw [hfind] at hprobe; dsimp only at hprobe
        by_cases hrej :
            ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
        · simp only [hrej, ↓reduceIte] at hprobe; cases hprobe
        simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hprobe
        rcases knownChain_fwdCPure_flag_true_corrs_window_lazy P Inv ℓ Dh hDh encPt encT decT idOf
          hX hinj lam qep q r Q w x₀ s_R sC g ec winBefore epExp hinv hkept_corr hcorrs_snaps hlen
          hparse hfind hprobe with ⟨c, hhonC, hw1, hw2, hw4, hw3⟩
        exact ⟨c, hhonC, ⟨h, body, rfl⟩, hw1, hw2, hw4, hw3⟩
      | none =>
        rw [hfind] at hprobe; dsimp only at hprobe
        by_cases hev_eq :
            (((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
                (·.2)).map (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
              ((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
                (·.2)).map (fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) = true
        · simp only [hev_eq, ↓reduceIte] at hprobe; cases hprobe
        simp only [hev_eq, Bool.false_eq_true, ↓reduceIte] at hprobe
        by_cases hT0 : (decT h.senderRatchetKey == some 0) = true
        · simp only [hT0, ↓reduceIte] at hprobe; cases hprobe
        simp only [hT0, Bool.false_eq_true, ↓reduceIte] at hprobe
        let sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          if inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
            { sC with base := { sC.base with amb := sC.base.amb + 1, stopped := false } }
          else sC
        have hx₁ :
            (if inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
              ({ sC with base := { sC.base with amb := sC.base.amb + 1, stopped := false } }, g,
                false)
            else (sC, g, false)) = (sC₁, (g, false)) := by
          dsimp only [sC₁]; split <;> rfl
        have heval_eq : ∀ c c',
            predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
              (lFS P.C P.codec ℓ encT idOf 25000) P sC₁ Q w c c' =
            predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
              (lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' := by
          intro c c'; dsimp only [sC₁]; split <;> rfl
        rw [hx₁] at hprobe
        by_cases hskip :
            (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
              decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
        · simp only [hskip, ↓reduceIte] at hprobe; cases hprobe
        simp only [hskip, Bool.false_eq_true, ↓reduceIte] at hprobe
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hskip
        have hinw : inReceiveOnlyEpoch sC.base.mir Q = false := Bool.eq_false_iff.mpr hskip.1.1
        have hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1) :=
          not_or.mpr ⟨hskip.1.2, hskip.2⟩
        cases hT : decT h.senderRatchetKey with
        | none => rw [hT] at hprobe; cases hprobe
        | some T =>
          rw [hT] at hprobe; dsimp only at hprobe
          by_cases hev_true :
              (((sC.base.honest.find? fun wc =>
                  wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
          · simp only [hev_true, ↓reduceIte] at hprobe
            rw [beq_iff_eq, Option.map_eq_some_iff] at hev_true
            rcases hev_true with ⟨c, hhonC, hc_ne⟩
            have hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1 := of_decide_eq_true hc_ne
            rcases honest_mem_and_sender_of_find_map_some hhonC with ⟨hmem, hsender⟩
            rcases fwdEvictCPure_flag_true_of_false P ℓ Dh encPt encT idOf lam qep true Q w true
              h.senderRatchetKey pq' _ (sC₁, (g, false)) rfl hprobe with ⟨_, _, hsafe₁, _⟩
            have hsafe : sC.base.mir.safeInj 3 = false := by
              have hmir : sC₁.base.mir = sC.base.mir := by dsimp only [sC₁]; split <;> rfl
              exact hmir ▸ hsafe₁
            have hfalse := fwdEvictCPure_not_flag_true_of_evictedOnlyNoForgeAt P Dh encPt encT
              decT idOf lam qep true Q w true sC g (sC₁, (g, false)) rfl rfl hno_ev hmem hsender
              hparse hspqr hfind hepoch hinw hbound hsafe hT
            rw [hfalse] at hprobe; cases hprobe
          · simp only [hev_true, Bool.false_eq_true, ↓reduceIte] at hprobe
            rcases newChain_fwdCPure_flag_true_corrs_window_lazy P Inv ℓ Dh hDh encPt encT idOf hX
              lam qep q r Q w x₀ s_R sC sC₁ g ec winBefore epExp hinv hkept_corr hcorrs_snaps
              heval_eq hlen hparse hev_true hprobe with ⟨c, hhonC, hw1, hw2, hw4, hw3⟩
            exact ⟨c, hhonC, ⟨h, body, rfl⟩, hw1, hw2, hw4, hw3⟩

theorem simRecvStepC_deliver_flag_true_corrs_window_at_inTransit_lazy
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT)
    (lam : Pt) (qep q r : ℕ) (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (rec_f : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (t' i' : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp)
    (hkept_corr : CorrsKeptRecvInv sC g)
    (hcorrs_snaps : ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ sC.snaps)
    (hno_ev : EvictedOnlyNoForgeAt P decT (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      sC g Q)
    (hprobe : (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 =
      true)
    (hw : w = LibsignalSim.toWire c)
    (hin_g : g.inTransit Q.other c = some rec_f)
    (hr_pos : rec_f.pos = ⟨Q.other, t', i'⟩) :
    (∀ e, (Party.receiverOf t', e) ∈ g.corrs → e + 3 ≤ t') ∧
    (∀ e, (Party.senderOf t', e) ∈ g.corrs → t' ≠ e + 1) ∧
    (2 ≤ t' → ¬((Party.senderOf t', t' - 2) ∈ g.corrs ∧ (Party.senderOf t', t') ∈ g.corrs)) ∧
    (∀ g₀ sc, (Party.senderOf t', t', g₀) ∈ sC.snaps →
      g₀.session.senderChain = some sc → i' ≤ sc.chainKey.index.toNat) := by
  rcases simRecvStepC_deliver_flag_true_corrs_window_lazy P Inv ℓ Dh hDh encPt encT decT idOf hX
    hinj lam qep q r Q w x₀ s_R sC g ec winBefore epExp hinv hkept_corr hcorrs_snaps hno_ev hprobe
    with ⟨c₀, hhonC₀, ⟨h, body, hparse⟩, hw1, hw2, hw4, hw3⟩
  rcases honest_mem_and_sender_of_find_map_some hhonC₀ with ⟨hc₀_mem, _⟩
  have hr_mem : rec_f ∈ g.trans := List.mem_of_find?_eq_some hin_g
  have hr_pred := List.find?_some hin_g
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
  rcases hinv.hsim.htrans_hon rec_f hr_mem with ⟨hc_hon, _, hr_ep, hr_idx⟩
  rw [hr_pred.2, ← hw] at hc_hon
  rw [hr_pred.2, hr_pos] at hr_ep hr_idx
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hinv.hsim.hhon (w, c₀) hc₀_mem).1
    hparse with ⟨_, hsrk₀, hctr₀, _⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hinv.hsim.hhon (w, c) hc_hon).1
    hparse with ⟨_, hsrk, hctr, _⟩
  have hdh : Dh.dh (epExp c₀.1.1) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
    hinj (hsrk₀.symm.trans hsrk)
  have hc₀_ep : c₀.1.1 = t' := by
    have hcoll := hinv.hsim.hcoll c₀.1.1 c.1.1
      (hinv.hsim.hhon (w, c₀) hc₀_mem).2.1 (hinv.hsim.hhon (w, c) hc_hon).2.1 hdh
    exact hcoll.trans hr_ep.symm
  have hc₀_idx : c₀.2.1 = i' := by
    calc c₀.2.1 = h.counter.toNat + 1 := hctr₀.symm
      _ = c.2.1 := hctr
      _ = i' := hr_idx.symm
  rw [hc₀_ep] at hw1 hw2 hw4 hw3
  rw [hc₀_idx] at hw3
  exact ⟨hw1, hw2, hw4, hw3⟩

theorem firstNEOriginAt_of_probe_and_inTransOriginInv_lazy
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT)
    (lam : Pt) (qep q r : ℕ) (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (rec_f : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (t' i' : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp)
    (hkept_corr : CorrsKeptRecvInv sC g)
    (hcorrs_snaps : ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ sC.snaps)
    (hno_ev : EvictedOnlyNoForgeAt P decT (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      sC g Q)
    (hprobe : (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 =
      true)
    (hw : w = LibsignalSim.toWire c)
    (hcell : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (hreach : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hin_g : g.inTransit Q.other c = some rec_f)
    (hr_pos : rec_f.pos = ⟨Q.other, t', i'⟩) :
    FirstNEOriginAt Q t' rec_f g s_cell := by
  rcases simRecvStepC_deliver_flag_true_corrs_window_at_inTransit_lazy
    P Inv ℓ Dh hDh encPt encT decT idOf hX hinj lam qep q r Q w c rec_f t' i' x₀ s_R sC g
    ec winBefore epExp hinv hkept_corr hcorrs_snaps hno_ev hprobe hw hin_g hr_pos with
    ⟨hw1, hw2, hw4, hw3⟩
  have hw3' : ∀ g₀ sc, (Party.senderOf t', t', g₀) ∈ sC.snaps →
      g₀.session.senderChain = some sc → rec_f.pos.idx ≤ sc.chainKey.index.toNat := by
    rw [hr_pos]; exact hw3
  exact firstNEOriginAt_of_corrs_window_and_inTransOriginInv
    qep sC.snaps Q c rec_f t' i' hw1 hw2 hw3' hw4 hcell hreach ht'_le hin_g hr_pos

/-- Under `SimInvCXLazy` and `CorrsKeptRecvInv`, a set probe flag on an in-transit record yields
`DeliverHcasesAtExt Q t' rec_f g s_cell`. -/
theorem firstNEProbeAt_imp_deliverHcasesAtExt_of_inv_lazy
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT)
    (lam : Pt) (qep q r : ℕ) (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (rec_f : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (t' i' : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp)
    (hkept_corr : CorrsKeptRecvInv sC g)
    (hcorrs_snaps : ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ sC.snaps)
    (hno_ev : EvictedOnlyNoForgeAt P decT (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      sC g Q)
    (hprobe : (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 =
      true)
    (hw : w = LibsignalSim.toWire c)
    (hcell : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (hreach : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hin_g : g.inTransit Q.other c = some rec_f)
    (hr_pos : rec_f.pos = ⟨Q.other, t', i'⟩) :
    DeliverHcasesAtExt Q t' rec_f g s_cell := by
  have horigin := firstNEOriginAt_of_probe_and_inTransOriginInv_lazy
    P Inv ℓ Dh hDh encPt encT decT idOf hX hinj lam qep q r Q w c rec_f t' i' x₀ s_R sC g
    ec winBefore epExp hinv hkept_corr hcorrs_snaps hno_ev hprobe hw hcell hreach
    ht'_le hin_g hr_pos
  exact firstNEProbeAt_imp_deliverHcasesAtExt_of_origin
    P ℓ Dh encPt encT decT idOf lam qep Q w c rec_f t' i'
    hprobe hcell ht'_le hin_g hr_pos horigin

theorem corrsLeEpoch_of_corrs_nil {St Msg C : Type} {s : SM.GameState St Msg C}
    (hnil : s.corrs = []) : CorrsLeEpoch s := by
  intro R e hmem; rw [hnil] at hmem; cases hmem

theorem corrsLeEpoch_afterCorr {St Msg C : Type} {s : SM.GameState St Msg C} (P : Party)
    (h : CorrsLeEpoch s) : CorrsLeEpoch (s.afterCorr P) := by
  intro R e hmem
  rcases List.mem_cons.mp hmem with hhead | htail
  · cases hhead; exact le_rfl
  · exact h R e htail

theorem corrsLeEpoch_record {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    (Δ : ℕ) (P : Party) (st' : St) (rec_r : SM.Record Msg C) (isChall : Bool)
    (h : CorrsLeEpoch s) (hcorrs : s₁.corrs = s.corrs)
    (hep : ∀ R, s.epoch R ≤ s₁.epoch R) :
    CorrsLeEpoch (s₁.record Δ P st' rec_r isChall) := by
  intro R e hmem
  have hmem' : (R, e) ∈ s.corrs := hcorrs ▸ hmem
  exact le_trans (h R e hmem') (hep R)

theorem corrsLeEpoch_accept {St Msg C : Type} {s : SM.GameState St Msg C}
    (Q : Party) (st' : St) (pos : SM.Pos) (h : CorrsLeEpoch s) :
    CorrsLeEpoch (s.accept Q st' pos) := by
  intro R e hmem
  unfold SM.GameState.accept SM.GameState.delete at hmem ⊢
  dsimp only at hmem ⊢
  have hle := h R e hmem
  by_cases hRQ : R = Q
  · subst hRQ; rw [Function.update_self]; exact le_trans hle (le_max_left _ _)
  · rw [Function.update_of_ne hRQ]; exact hle

theorem corrsSnapIdxInv_of_corrs_nil {PQ St Msg C : Type}
    (snaps : List (Party × ℕ × GhostState PQ)) {s : SM.GameState St Msg C}
    (hnil : s.corrs = []) : CorrsSnapIdxInv snaps s := by
  intro P e hmem; rw [hnil] at hmem; cases hmem

theorem corrsSnapIdxInv_afterCorr {PQ St Msg C : Type}
    {snaps : List (Party × ℕ × GhostState PQ)} {s : SM.GameState St Msg C}
    (P : Party) (g₀ : GhostState PQ)
    (h : CorrsSnapIdxInv snaps s)
    (hnew : P.sendsIn (s.epoch P) = true →
      ∃ sc, g₀.session.senderChain = some sc ∧ sc.chainKey.index.toNat ≤ s.idx P) :
    CorrsSnapIdxInv ((P, s.epoch P, g₀) :: snaps) (s.afterCorr P) := by
  intro R e hmem hsend
  rcases List.mem_cons.mp hmem with hhead | htail
  · cases hhead
    rcases hnew hsend with ⟨sc, hsc, hidx⟩
    exact ⟨g₀, sc, List.mem_cons_self, hsc, fun _ => hidx⟩
  · rcases h R e htail hsend with ⟨g₁, sc, hg₁, hsc, hidx⟩
    exact ⟨g₁, sc, List.mem_cons_of_mem _ hg₁, hsc, hidx⟩

theorem corrsSnapIdxInv_record {PQ St Msg C : Type}
    {snaps : List (Party × ℕ × GhostState PQ)} {s s₁ : SM.GameState St Msg C}
    (Δ : ℕ) (P : Party) (st' : St) (rec_r : SM.Record Msg C) (isChall : Bool)
    (h : CorrsSnapIdxInv snaps s) (hle : CorrsLeEpoch s) (hcorrs : s₁.corrs = s.corrs)
    (hstep : ∀ R, s.epoch R < s₁.epoch R ∨
      (s₁.epoch R = s.epoch R ∧ s.idx R ≤ (s₁.record Δ P st' rec_r isChall).idx R)) :
    CorrsSnapIdxInv snaps (s₁.record Δ P st' rec_r isChall) := by
  intro R e hmem hsend
  have hmem' : (R, e) ∈ s.corrs := hcorrs ▸ hmem
  have he_le : e ≤ s.epoch R := hle R e hmem'
  rcases h R e hmem' hsend with ⟨g₀, sc, hg₀, hsc, hidx⟩
  refine ⟨g₀, sc, hg₀, hsc, fun hep => ?_⟩
  have hep₁ : s₁.epoch R = e := hep
  rcases hstep R with hlt | ⟨heq, hi_le⟩
  · omega
  · exact le_trans (hidx (heq.symm.trans hep₁)) hi_le

theorem corrsSnapIdxInv_accept {PQ St Msg C : Type}
    {snaps : List (Party × ℕ × GhostState PQ)} {s : SM.GameState St Msg C}
    (Q : Party) (st' : St) (pos : SM.Pos) (h : CorrsSnapIdxInv snaps s) (hle : CorrsLeEpoch s) :
    CorrsSnapIdxInv snaps (s.accept Q st' pos) := by
  intro R e hmem hsend
  unfold SM.GameState.accept SM.GameState.delete at hmem ⊢
  dsimp only at hmem ⊢
  have he_le : e ≤ s.epoch R := hle R e hmem
  rcases h R e hmem hsend with ⟨g₀, sc, hg₀, hsc, hidx⟩
  refine ⟨g₀, sc, hg₀, hsc, fun hep => ?_⟩
  by_cases hRQ : R = Q
  · subst hRQ; rw [Function.update_self] at hep
    exact hidx (by omega)
  · rw [Function.update_of_ne hRQ] at hep
    exact hidx hep

theorem corrsKeptRecvInv_of_corrs_nil {Pt PQ : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hnil : g.corrs = []) : CorrsKeptRecvInv sC g := by
  intro Q e hmem; rw [hnil] at hmem; cases hmem

theorem corrsLeEpoch_init_b {Key St Msg Coins C : Type}
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (k : Key) (b : Bool) :
    CorrsLeEpoch (SM.initState sm k b) :=
  corrsLeEpoch_of_corrs_nil rfl

theorem corrsSnapIdxInv_init_b {PQ Key St Msg Coins C : Type}
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C)
    (snaps : List (Party × ℕ × GhostState PQ)) (k : Key) (b : Bool) :
    CorrsSnapIdxInv snaps (SM.initState sm k b) :=
  corrsSnapIdxInv_of_corrs_nil snaps rfl

theorem corrsKeptRecvInv_init_b {Key Coins Pt PQ : Type} {ℓ : ℕ}
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) Coins (Fig8C Pt))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (k : Key) (b : Bool) :
    CorrsKeptRecvInv sC (SM.initState sm k b) :=
  corrsKeptRecvInv_of_corrs_nil sC rfl

theorem corrsKeptRecvInv_afterCorr {Pt PQ : Type} {ℓ : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)} (P : Party)
    (h : CorrsKeptRecvInv sC g)
    (hfull : (sC'.kept P).full.isSome = true)
    (hother : ∀ Q, Q ≠ P → sC'.kept Q = sC.kept Q) :
    CorrsKeptRecvInv sC' (g.afterCorr P) := by
  intro Q e hmem t hle hrecv
  by_cases hQP : Q = P
  · subst hQP; exact Or.inl hfull
  · rw [hother Q hQP]
    rcases List.mem_cons.mp hmem with hhead | htail
    · exact False.elim (hQP (Prod.mk.inj hhead).1)
    · exact h Q e htail t hle hrecv

theorem fig8SenderSync_afterCorr {Pt : Type} {ℓ : ℕ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)} (P : Party)
    (h : Fig8SenderSync g) :
    Fig8SenderSync (g.afterCorr P) :=
  ⟨h.htcur, h.hvS, h.hvR⟩

theorem corrsLeEpoch_record_of_epMgmt {St Msg C : Type} {s s₁ : SM.GameState St Msg C}
    {Δ qep_lim : ℕ} {P : Party} {bad : Bool}
    (st' : St) (rec_r : SM.Record Msg C) (isChall : Bool)
    (h : CorrsLeEpoch s) (hep : s.epMgmt Δ qep_lim P bad = some s₁)
    (hcorrs : s₁.corrs = s.corrs) :
    CorrsLeEpoch (s₁.record Δ P st' rec_r isChall) :=
  corrsLeEpoch_record Δ P st' rec_r isChall h hcorrs (fun _ => epMgmt_epoch_le hep)

theorem corrsSnapIdxInv_record_of_epMgmt {PQ St Msg C : Type}
    {snaps : List (Party × ℕ × GhostState PQ)} {s s₁ : SM.GameState St Msg C}
    {Δ qep_lim : ℕ} {P : Party} {bad : Bool}
    (st' : St) (rec_r : SM.Record Msg C) (isChall : Bool)
    (h : CorrsSnapIdxInv snaps s) (hle : CorrsLeEpoch s)
    (hep : s.epMgmt Δ qep_lim P bad = some s₁) (hcorrs : s₁.corrs = s.corrs)
    (hrec_idx : s₁.idx P ≤ rec_r.pos.idx) :
    CorrsSnapIdxInv snaps (s₁.record Δ P st' rec_r isChall) := by
  refine corrsSnapIdxInv_record Δ P st' rec_r isChall h hle hcorrs (fun R => ?_)
  have hep_le : s.epoch R ≤ s₁.epoch R := epMgmt_epoch_le hep
  rcases lt_or_eq_of_le hep_le with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq.symm, ?_⟩
    have hidx_eq : s₁.idx R = s.idx R := epMgmt_idx_eq_of_epoch_eq hep heq.symm
    rw [← hidx_eq]
    unfold SM.GameState.record
    dsimp only
    by_cases hRP : R = P
    · subst hRP; rw [Function.update_self]; exact hrec_idx
    · rw [Function.update_of_ne hRP]

end CryptoVerification.LibsignalSession.HeadlineV1
end
