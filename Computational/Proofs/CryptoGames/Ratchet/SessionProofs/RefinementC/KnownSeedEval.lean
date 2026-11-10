/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltK4
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync

/-!
# Corruption-snapshot receive prediction

**Checked by Lean.** Connects `predictReceiveWithSnapshots` (`snapshotMessageKeySeed` and `decryptWithKnownSeed` over the corruption snapshot log `snaps`) to Fig. 8 `receive` and derives the four-way corruption-window exclusion when `predictReceiveWithSnapshots` returns `none`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs.Correctness CryptoGames.LibsignalSM.Proofs.SaltMismatch
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## Snapshot receive prediction -/

abbrev SimStateCK (PQ Pt : Type) (ℓ : ℕ) := LibsignalToModularSchemeSimState PQ Pt ℓ

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem evalCK_of_evalC_some
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (P : Params PQ PQC) (s : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    {r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))}
    (heval : predictReceive (fig := fig) (fs := fs) s Q c c' = some r) :
    predictReceiveWithSnapshots fig fs P s Q w c c' = some r := by
  unfold predictReceiveWithSnapshots
  rw [heval]
  rfl

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem evalCK_of_evalC_none
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (P : Params PQ PQC) (s : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    (heval : predictReceive (fig := fig) (fs := fs) s Q c c' = none) :
    predictReceiveWithSnapshots fig fs P s Q w c c' =
      (snapshotMessageKeySeed P s.snaps Q c.1.1 w).map (kDecryptFig8 P ℓ Q w c') := by
  unfold predictReceiveWithSnapshots
  rw [heval]
  rfl

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem evalCK_eq_none_iff
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (P : Params PQ PQC) (s : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt) :
    predictReceiveWithSnapshots fig fs P s Q w c c' = none ↔
      predictReceive (fig := fig) (fs := fs) s Q c c' = none ∧
      snapshotMessageKeySeed P s.snaps Q c.1.1 w = none := by
  unfold predictReceiveWithSnapshots
  cases predictReceive (fig := fig) (fs := fs) s Q c c' <;>
    cases snapshotMessageKeySeed P s.snaps Q c.1.1 w <;>
    simp [Option.orElse]

/-! ## Snapshot invariant -/

def ratchetStateOf {PQ : Type} (g : GhostState PQ) : RatchetState :=
  { rootKey := g.session.rootKey
    senderChain := g.session.senderChain
    receiverChains := g.session.receiverChains
    previousCounter := g.session.previousCounter
    maxForwardJumps := 25000 }

/-- Invariant linking `s.snaps`, the `EpochTrace` `tr`, and the `EpochSyncK` keys `K` of `SimInvCX`. -/
structure SnapsInv (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (epExp : ℕ → BitVec 256)
    (tr : EpochTrace P.C.F Dh encPt)
    (K : ℕ → BitVec 256)
    (maxAcc : Party → ℕ → ℕ) : Prop where
  htFront : tr.tFront = max (maxActiveEp s.base.mir .A) (maxActiveEp s.base.mir .B)
  hx : ∀ t ≤ tr.tFront, tr.x t = epExp t
  hck : ∀ t ≤ tr.tFront, tr.ck t = K t
  hK : EpochSyncK P ℓ encT idOf Dh encPt s.base.honest s.sent s.snaps s_fig8.st K tr.rk epExp
  hsnaps : ∀ Q, ∀ snap ∈ s.snaps,
    SnapInv P.C Dh encPt encT tr Q (ratchetStateOf (s_R.st Q)) (maxAcc Q) snap
  hsnap_ep : ∀ Q e g, (Q, e, g) ∈ s.snaps → e ≤ s.base.mir.epoch Q
  hstored : ∀ Q e g t, (Q, e, g) ∈ s.snaps → t < e →
    t ∈ (s.base.chains Q).map (·.epoch) → t ∈ storedEpochs Q e
  hcur_chains : ∀ Q (ci : ℕ) (g : GhostChain), (s.base.chains Q)[ci]? = some g →
    ∃ c, (ratchetStateOf (s_R.st Q)).receiverChains[ci]? = some c ∧
      maxAcc Q g.epoch = g.last ∧
      RcvChainInv P.C.F (tr.ck g.epoch) g.last c

/-! ## Decryption equivalence -/

theorem lChainAt_eq_chainKeyValAt (F : ShaCompress) (ck0 : BitVec 256) :
    ∀ n : ℕ, lChainAt F ck0 n = chainKeyValAt F ck0 n
  | 0 => rfl
  | n + 1 => by
    simp only [lChainAt, chainKeyValAt, lChainAt_eq_chainKeyValAt F ck0 n]
    rfl

theorem keyToBytes32_lSeedAt (F : ShaCompress) (ck0 : BitVec 256) (i : ℕ) :
    keyToBytes32 (lSeedAt F ck0 i) = msgSeedAt F ck0 (i - 1) := by
  unfold lSeedAt msgSeedAt lChainPRG
  dsimp only
  rw [keyToBytes32_hmacPRF_tag, lChainAt_eq_chainKeyValAt]

omit [Inhabited PQ] [SampleableType PQC] in
theorem kDecrypt_eq_of_tryFrom (P : Params PQ PQC) (Q : Party) (w : List (BitVec 8))
    (salt : Salt) (seed : List (BitVec 8)) (msg : SignalMessage)
    (htry : SignalMessage.tryFrom P.codec w = .ok msg)
    (haddrs : addressCheckPasses msg.addresses (P.expectedAddrs Q) = true) :
    decryptWithKnownSeed P Q w salt seed =
      let mk := (MessageKeyGenerator.mk seed msg.counter).generateKeys P.C.F salt
      if SignalMessage.verifyMac P.C.F msg (idOfP P Q.other) (idOfP P Q) mk.macKey = true then
        aesCbcDecrypt P.C.D mk.cipherKey mk.iv msg.ciphertext
      else none := by
  unfold decryptWithKnownSeed MessageKeyGenerator.generateKeys
  rw [htry]
  dsimp only
  generalize deriveMessageKeys P.C.F salt seed = k
  unfold SignalMessage.verifyMacWithAddresses idOfP
  rw [haddrs, Bool.and_true]
  cases SignalMessage.verifyMac P.C.F msg
    (if Q.other == Party.A then P.idA else P.idB)
    (if Q == Party.A then P.idA else P.idB) k.2 <;> rfl

/-- On a parsed wire with valid addresses for `Q`, `kDecryptFig8` on `c'` at `keyToBytes32 key` agrees with Fig. 8 AEAD decryption under `key`. -/
theorem kDecryptFig8_eq_lAead_dec (P : Params PQ PQC) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (Q : Party) (t : ℕ) (T? : Option Pt) (hrecv : Q.sendsIn t = false)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hver : h.messageVersion = currentVersion)
    (hkey : (T?.map encT).getD dummyKey = h.senderRatchetKey)
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (c' : Fig8C Pt)
    (hc'_1 : c'.1 = (t, T?))
    (hc'_21 : c'.2.1 = h.counter.toNat + 1)
    (hc'_221 : c'.2.2.1 = (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))))
    (key : BitVec 256) :
    kDecryptFig8 P ℓ Q w c' (keyToBytes32 key) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (c'.2.1, c'.1) c'.2.2).map fun m => (c'.1.1, c'.2.1, m) := by
  have htry := tryFrom_of_parse P.codec w h body hw_len hparse
  have hc'_22 : c'.2.2 =
      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 (some c'.2.2.2)) := by
    rcases c' with ⟨hdr, i, raw, σ⟩
    dsimp only at hc'_221 ⊢
    rw [hc'_221]
    rfl
  have _ : DecidableEq PQ := Classical.typeDecidableEq PQ
  have hdec := lAead_pubMsg_dec_eq (ℓ := ℓ) P encT idOf hid Q t T? hrecv w hw_len h body
    hparse hver hkey key (some c'.2.2.2)
  dsimp only at hdec
  have hpub : lPubOf P.codec c'.2.2 =
      some ⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 (some c'.2.2.2), h.addresses⟩ := by
    rw [hc'_22]
    unfold lPubOf
    dsimp only
    rw [hparse]
    rfl
  have hkdec := kDecrypt_eq_of_tryFrom P Q w (some c'.2.2.2) (keyToBytes32 key)
    ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
      h.pqRatchet, h.addresses, w⟩ htry haddrs
  dsimp only at hkdec
  have hc'_11 : c'.1.1 = t := congrArg Prod.fst hc'_1
  have hrhs : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
      key (c'.2.1, c'.1) c'.2.2 =
      if SignalMessage.verifyMac P.C.F
          ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
            h.pqRatchet, h.addresses, w⟩
          (idOfP P Q.other) (idOfP P Q)
          ((MessageKeyGenerator.mk (keyToBytes32 key) h.counter).generateKeys P.C.F
            (some c'.2.2.2)).macKey = true then
        (aesCbcDecrypt P.C.D
          ((MessageKeyGenerator.mk (keyToBytes32 key) h.counter).generateKeys P.C.F
            (some c'.2.2.2)).cipherKey
          ((MessageKeyGenerator.mk (keyToBytes32 key) h.counter).generateKeys P.C.F
            (some c'.2.2.2)).iv body).map
          (fun m_raw => (⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 (some c'.2.2.2), h.addresses⟩,
            padOrTruncatePlain ℓ m_raw))
      else none := by
    rw [hc'_21, hc'_1, hc'_22]
    exact hdec
  unfold kDecryptFig8
  rw [hpub, hkdec, hrhs, hc'_11, hc'_21]
  generalize (MessageKeyGenerator.mk (keyToBytes32 key) h.counter).generateKeys P.C.F
    (some c'.2.2.2) = mk
  cases SignalMessage.verifyMac P.C.F
      ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩
      (idOfP P Q.other) (idOfP P Q) mk.macKey
  · rfl
  · cases aesCbcDecrypt P.C.D mk.cipherKey mk.iv body <;> rfl

/-! ## Soundness against Fig. 8 receive -/

private theorem kse_mem_of_lookup {α : Type} {l : List (ℕ × α)} {i : ℕ} {v : α}
    (h : l.lookup i = some v) : (i, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p ps ih =>
    simp only [List.lookup] at h
    cases hbeq : (i == p.1)
    · rw [hbeq] at h
      exact List.mem_cons_of_mem p (ih h)
    · rw [hbeq] at h
      injection h with hv
      subst hv
      rcases p with ⟨p1, p2⟩
      have hi : i = p1 := beq_iff_eq.1 hbeq
      subst hi
      exact List.mem_cons_self ..

private theorem kse_skipKeys_fst (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256) :
    ∀ (n p : ℕ) (acc : List (ℕ × BitVec 256)),
      (skipKeys (lChainPRG F) n (lChainAt F k p) p acc).1 = lChainAt F k (p + n)
  | 0, p, acc => by simp [skipKeys]
  | n + 1, p, acc => by
    simp only [skipKeys]
    have hstep : ((lChainPRG F p).gen (lChainAt F k p)).1 = lChainAt F k (p + 1) := rfl
    rw [hstep, kse_skipKeys_fst F k n (p + 1)]
    congr 1
    omega

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem kse_lFS_receive_of_recvAgrees (P : Params PQ PQC) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (k : BitVec 256)
    (v : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (hv : RecvAgrees P.C.F k v) (i : ℕ) :
    (∀ a e, (lFS P.C P.codec ℓ encT idOf 25000).receive v a (i, e) = none) ∨
    (∃ v', ∀ a e, (lFS P.C P.codec ℓ encT idOf 25000).receive v a (i, e) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (lSeedAt P.C.F k i) (i, a) e).map fun m => (v', i, m)) := by
  unfold lFS fromAEADPRG
  dsimp only
  cases hlk : v.skippedKeys.lookup i with
  | some key =>
    have hkey : key = lSeedAt P.C.F k i := hv.2 (i, key) (kse_mem_of_lookup hlk)
    subst hkey
    exact Or.inr ⟨{ v with skippedKeys := v.skippedKeys.filter (·.1 != i) },
      fun a e => by simp⟩
  | none =>
    by_cases hcond : i ≤ v.lastIndex ∨ 25000 < i - v.lastIndex - 1
    · exact Or.inl (fun a e => by simp [hcond])
    · have hw₁ : (skipKeys (lChainPRG P.C.F) (i - v.lastIndex - 1) v.chainKey v.lastIndex
          v.skippedKeys).1 = lChainAt P.C.F k (i - 1) := by
        rw [hv.1, kse_skipKeys_fst]
        congr 1
        omega
      rcases hsk : skipKeys (lChainPRG P.C.F) (i - v.lastIndex - 1) v.chainKey v.lastIndex
        v.skippedKeys with ⟨w₁, skipped'⟩
      have hw₁_eq : w₁ = lChainAt P.C.F k (i - 1) := by rw [← hw₁, hsk]
      subst hw₁_eq
      have hseed : ((lChainPRG P.C.F (i - 1)).gen (lChainAt P.C.F k (i - 1))).2 =
          lSeedAt P.C.F k i := rfl
      exact Or.inr ⟨⟨((lChainPRG P.C.F (i - 1)).gen (lChainAt P.C.F k (i - 1))).1, i, skipped'⟩,
        fun a e => by simp [hcond, hseed]⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem kse_lFS_receive_fresh (P : Params PQ PQC) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (k : BitVec 256) (i : ℕ) (hi : 1 ≤ i) (a : Header Pt) (e : LibsignalCiphertextWithSalt32) :
    (lFS P.C P.codec ℓ encT idOf 25000).receive
        ⟨lChainAt P.C.F k (i - 1), i - 1, []⟩ a (i, e) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (lSeedAt P.C.F k i) (i, a) e).map fun m =>
          (⟨((lChainPRG P.C.F (i - 1)).gen (lChainAt P.C.F k (i - 1))).1, i, []⟩, i, m) := by
  unfold lFS fromAEADPRG
  have hcond : ¬ (i ≤ i - 1 ∨ 25000 < i - (i - 1) - 1) := by omega
  have hsub : i - (i - 1) - 1 = 0 := by omega
  dsimp only [List.lookup]
  rw [ite_eq_right hcond, hsub]
  rfl

omit [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem kse_lFig8_receive_dichotomy (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (K rk : ℕ → BitVec 256)
    (hK : EpochSyncK P ℓ encT idOf Dh encPt sC.base.honest sC.sent sC.snaps s_fig8.st K rk epExp)
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hmem : (w, c) ∈ sC.base.honest) (hsnd : Party.senderOf c.1.1 = Q.other) :
    (∀ e, (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
        (c.1, (c.2.1, e)) = none) ∨
    (∃ st', ∀ e, (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
        (c.1, (c.2.1, e)) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) e).map fun m => (st', c.1.1, c.2.1, m)) := by
  by_cases hbad : ((s_fig8.st Q).id.sendsIn c.1.1 || decide ((s_fig8.st Q).tcur + 1 < c.1.1)) = true
  · exact Or.inl (fun e => by
      unfold lFig8 SM.Construction.scheme SM.Construction.receive
      dsimp only
      rw [ite_eq_left hbad])
  · by_cases hnew : c.1.1 = (s_fig8.st Q).tcur + 1
    · have ht_le_snd : c.1.1 ≤ (s_fig8.st Q.other).tcur := by
        have h1 := (hinv.hsim.hhon (w, c) hmem).2.2.2
        rw [hsnd, ← hinv.hsim.htcur Q.other] at h1
        exact h1
      have hother : Q.other.other = Q := by cases Q <;> rfl
      have hgap := hK.hgap Q.other
      rw [hother] at hgap
      have ht_other : (s_fig8.st Q.other).tcur = (s_fig8.st Q).tcur + 1 := by omega
      have hahead_eq : (s_fig8.st Q.other).tcur = (s_fig8.st Q.other.other).tcur + 1 := by
        rw [hother, ht_other]
      rcases hK.hahead Q.other hahead_eq with ⟨_, x, _, hTcur, hup⟩
      rw [hother, ht_other, ← hnew] at hup
      have hhdr : c.1.2 = some (Dh.dh x Dh.base) := by
        have hh := hK.hhdr (w, c) hmem (by rw [hsnd, ht_other, ← hnew])
        rw [hsnd, hTcur] at hh
        exact hh.symm
      set v₀ : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) :=
        (lFS P.C P.codec ℓ encT idOf 25000).initReceiver (K c.1.1)
      have hv₀ : RecvAgrees P.C.F (K c.1.1) v₀ := ⟨rfl, fun _ hp => by cases hp⟩
      set s₁ : Fig8St Pt :=
        { s_fig8.st Q with
          tcur := c.1.1
          γ := ((dhScheme Dh).receive (s_fig8.st Q).γ (Dh.dh x Dh.base)).1
          root := (s_fig8.st Q.other).root
          vR := Function.update (s_fig8.st Q).vR c.1.1 (some v₀) }
      rcases kse_lFS_receive_of_recvAgrees P ℓ encT idOf (K c.1.1) v₀ hv₀ c.2.1 with
        hnone | ⟨v', hv'⟩
      · refine Or.inl (fun e => ?_)
        unfold lFig8 SM.Construction.scheme SM.Construction.receive
        dsimp only
        rw [ite_eq_right hbad, ite_eq_left hnew, hhdr]
        dsimp only
        rw [hup, Function.update_self]
        dsimp only
        rw [hnone c.1 e]
      · refine Or.inr ⟨{ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, fun e => ?_⟩
        unfold lFig8 SM.Construction.scheme SM.Construction.receive
        dsimp only
        rw [ite_eq_right hbad, ite_eq_left hnew, hhdr]
        dsimp only
        rw [hup, Function.update_self]
        dsimp only
        rw [hv' c.1 e]
        cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) e <;> rfl
    · cases hv : (s_fig8.st Q).vR c.1.1 with
      | none =>
        refine Or.inl (fun e => ?_)
        unfold lFig8 SM.Construction.scheme SM.Construction.receive
        dsimp only
        rw [ite_eq_right hbad, ite_eq_right hnew]
        dsimp only
        rw [hv]
      | some v =>
        have hv_agrees : RecvAgrees P.C.F (K c.1.1) v := hK.hrecv Q c.1.1 v hv
        rcases kse_lFS_receive_of_recvAgrees P ℓ encT idOf (K c.1.1) v hv_agrees c.2.1 with
          hnone | ⟨v', hv'⟩
        · refine Or.inl (fun e => ?_)
          unfold lFig8 SM.Construction.scheme SM.Construction.receive
          dsimp only
          rw [ite_eq_right hbad, ite_eq_right hnew]
          dsimp only
          rw [hv]
          dsimp only
          rw [hnone c.1 e]
        · refine Or.inr
            ⟨{ s_fig8.st Q with vR := Function.update (s_fig8.st Q).vR c.1.1 (some v') },
            fun e => ?_⟩
          unfold lFig8 SM.Construction.scheme SM.Construction.receive
          dsimp only
          rw [ite_eq_right hbad, ite_eq_right hnew]
          dsimp only
          rw [hv]
          dsimp only
          rw [hv' c.1 e]
          cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
            (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) e <;> rfl

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
/-- Soundness of `snapshotMessageKeySeed` against `msgSeedAt` under `SnapSync`. -/
theorem knownSeedR_eq_msgSeedAt_of_snapSync (P : Params PQ PQC)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace P.C.F Dh encPt)
    {snaps : List (Party × ℕ × GhostState PQ)}
    (hsnaps : ∀ snap ∈ snaps, SnapSync P.C Dh encT tr.ck tr.rk tr.x tr.tFront snap)
    {Q : Party} {t : ℕ} (ht : t ≤ tr.tFront) {w : List (BitVec 8)} {msg : SignalMessage}
    (hw : SignalMessage.tryFrom P.codec w = .ok msg)
    (hY : msg.senderRatchetKey = encT (tr.T t))
    {seed : List (BitVec 8)} (hk : snapshotMessageKeySeed P snaps Q t w = some seed) :
    seed = msgSeedAt P.C.F (tr.ck t) msg.counter.toNat := by
  unfold snapshotMessageKeySeed at hk
  rw [hw] at hk
  dsimp only at hk
  have hor {a b : Option (List (BitVec 8))} (h : (a <|> b) = some seed) :
      a = some seed ∨ b = some seed := by
    cases a <;> cases b <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
  rcases hor hk with hk1 | hk324
  · rcases mem_of_findSome?_eq_some hk1 with ⟨snap, hmem, hbody⟩
    split at hbody
    · rw [Option.bind_eq_some_iff] at hbody
      rcases hbody with ⟨rc, hfind, hk1_rc⟩
      have hrc_mem := List.mem_of_find?_eq_some hfind
      have hrc_key : rc.senderRatchetKey = msg.senderRatchetKey := by
        simpa using List.find?_some hfind
      rcases hsnaps snap hmem with ⟨_, hsnap_tf, _, _, hrcs, _⟩
      rcases hrcs rc hrc_mem with ⟨ep, hep_le, hsrk, ⟨j, hj, hck⟩, hmk_eq⟩
      have hep_tf : ep ≤ tr.tFront := le_trans hep_le hsnap_tf
      have hep_eq : ep = t :=
        tr.hDistinct ep hep_tf t ht
          (Correctness.encT_injective hX (hsrk.symm.trans (hrc_key.trans hY)))
      subst hep_eq
      cases hmk : rc.messageKeys.find? (·.counter == msg.counter) with
      | some mk =>
        rw [hmk] at hk1_rc
        injection hk1_rc with hseed_eq
        rw [← hseed_eq, hmk_eq mk (List.mem_of_find?_eq_some hmk)]
        have hcnt : mk.counter = msg.counter := by simpa using List.find?_some hmk
        rw [hcnt, keyToBytes32_lSeedAt, Nat.add_sub_cancel]
      | none =>
        rw [hmk, hck, Option.bind_some, lChainAt_eq_chainKeyValAt] at hk1_rc
        by_cases hle : j ≤ msg.counter.toNat
        · rw [chainSeedAt_chainKeyValAt P.C.F (tr.ck ep) hj msg.counter hle] at hk1_rc
          exact (Option.some.inj hk1_rc).symm
        · unfold chainSeedAt at hk1_rc
          have hidx : (BitVec.ofNat 32 j).toNat = j := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
          simp [hidx, show msg.counter.toNat < j by omega] at hk1_rc
    · cases hbody
  rcases hor hk324 with hk3 | hk24
  · rcases mem_of_findSome?_eq_some hk3 with ⟨snap, hmem, hbody⟩
    split at hbody
    · rcases hsnaps snap hmem with ⟨_, hsnap_tf, _, ⟨j, hj, hsc_eq⟩, _, _⟩
      rw [hsc_eq, Option.bind_some, lChainAt_eq_chainKeyValAt] at hbody
      have hsc_key : (⟨KeyPair.generate P.C (tr.x snap.2.1),
          ⟨chainKeyValAt P.C.F (tr.ck snap.2.1) j, BitVec.ofNat 32 j⟩⟩ : SenderChain).chainKey =
          ⟨chainKeyValAt P.C.F (tr.ck snap.2.1) j, BitVec.ofNat 32 j⟩ := rfl
      have hpk : (KeyPair.generate P.C (tr.x snap.2.1)).publicKey = msg.senderRatchetKey := by
        split at hbody
        · rename_i h; exact h
        · cases hbody
      rw [KeyPair_generate_publicKey hX, hY] at hpk
      have hep : snap.2.1 = t := tr.hDistinct _ hsnap_tf _ ht (Correctness.encT_injective hX hpk)
      exact hep ▸ k3Seed_eq_msgSeedAt hj hsc_key hbody
    · cases hbody
  rcases hor hk24 with hk2 | hk4
  · rcases mem_of_findSome?_eq_some hk2 with ⟨snap, hmem, hbody⟩
    split at hbody
    · rename_i hcond
      rcases hcond with ⟨_, _, ht_eq⟩
      rcases hsnaps snap hmem with ⟨_, _, hrk_eq, ⟨j, _, hsc_eq⟩, _, _⟩
      rw [lChainAt_eq_chainKeyValAt] at hsc_eq
      have h2 := k2Seed_eq_some_of_trace hX hDh tr (e := snap.2.1) (by omega)
        (sc := ⟨KeyPair.generate P.C (tr.x snap.2.1),
          ⟨chainKeyValAt P.C.F (tr.ck snap.2.1) j, BitVec.ofNat 32 j⟩⟩) rfl msg.counter
      unfold k2Seed at h2
      simp only [hrk_eq, hsc_eq, Option.bind_some, hY, ht_eq] at hbody h2
      exact ht_eq ▸ Option.some.inj (hbody.symm.trans h2)
    · cases hbody
  · rw [Option.bind_eq_some_iff] at hk4
    rcases hk4 with ⟨p, hfind_cur, hfind_prev⟩
    rcases mem_of_findSome?_eq_some hfind_cur with ⟨e_cur, hmem_cur, hbody_cur⟩
    split at hbody_cur
    · rename_i hcur_cond
      rcases hcur_cond with ⟨hP_cur, ht_cur⟩
      rcases hsnaps e_cur hmem_cur with ⟨_, _, _, ⟨j_cur, _, hsc_cur_eq⟩, _, hlast_cur⟩
      rw [lChainAt_eq_chainKeyValAt] at hsc_cur_eq
      rw [hsc_cur_eq, Option.bind_some] at hbody_cur
      split at hbody_cur
      · rw [Option.map_eq_some_iff] at hbody_cur
        rcases hbody_cur with ⟨rc_last, hlast, hp_eq⟩
        subst hp_eq
        rcases mem_of_findSome?_eq_some hfind_prev with ⟨e_prev, hmem_prev, hbody_prev⟩
        split at hbody_prev
        · rename_i hprev_cond
          rcases hprev_cond with ⟨_, _, ht_prev⟩
          rcases hsnaps e_prev hmem_prev with ⟨_, _, hrk_prev, ⟨j_prev, _, hsc_prev_eq⟩, _, _⟩
          rw [lChainAt_eq_chainKeyValAt] at hsc_prev_eq
          rcases hlast_cur (by omega) with ⟨rc_last', hlast', hrc_last_rk⟩
          rw [hlast] at hlast'
          injection hlast' with hrc_eq
          subst hrc_eq
          rw [ht_cur] at hrc_last_rk
          have hprev_ep : e_prev.2.1 = t - 2 := by omega
          have h4 := k4Seed_eq_some_of_trace hX hDh tr (t := t) (by omega) ht
            (sc_cur := ⟨KeyPair.generate P.C (tr.x e_cur.2.1),
              ⟨chainKeyValAt P.C.F (tr.ck e_cur.2.1) j_cur, BitVec.ofNat 32 j_cur⟩⟩)
            (sc_prev := ⟨KeyPair.generate P.C (tr.x e_prev.2.1),
              ⟨chainKeyValAt P.C.F (tr.ck e_prev.2.1) j_prev, BitVec.ofNat 32 j_prev⟩⟩)
            (rc_last := rc_last)
            (by simp [ht_cur]) hrc_last_rk (by simp [hprev_ep]) msg.counter
          unfold k4Seed at h4
          have hpk_cur : (KeyPair.generate P.C (tr.x e_cur.2.1)).publicKey = encT (tr.T t) := by
            rw [ht_cur, KeyPair_generate_publicKey hX, EpochTrace.T]
          simp only [Option.bind_some, hpk_cur, ↓reduceIte, ← hprev_ep] at h4
          simp only [hrk_prev, hsc_prev_eq, Option.bind_some] at hbody_prev
          exact Option.some.inj (hbody_prev.symm.trans h4)
        · cases hbody_prev
      · cases hbody_cur
    · cases hbody_cur

/-- Soundness of `predictReceiveWithSnapshots` against `lFig8.receive` on `c'` and `c` under `SimInvCX`. -/
theorem KeptInv.evalCK_spec (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q r : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hDh : Dh.Commutes)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hwin : s_fig8.win = false)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    (hmem : (w, c) ∈ sC.base.honest) (hsnd : Party.senderOf c.1.1 = Q.other)
    (htr : (sC.base.mir.inTransit Q.other w).isSome)
    (h1 : c'.1 = c.1) (h2 : c'.2.1 = c.2.1) (h3 : c'.2.2.1 = c.2.2.1) :
    (predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = some none →
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' = none) ∧
    (∀ x, predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = some (some x) →
      (∃ st', (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
          some (st', x) ∧
        ∃ pm, (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
          some (st', (x.1, x.2.1, pm))) ∨
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' = none ∧
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c = none)) := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  have hspec := KeptInv.evalC_spec P Inv Dh encPt encT idOf lam qep q r x₀ s_R sC
    s_fig8 ec winBefore epExp hinv hwin Q w c c' hmem hsnd htr h1 h2 h3
  cases hevC : predictReceive (fig := fig) (fs := fs) sC Q c c' with
  | some r_e =>
    rw [evalCK_of_evalC_some fig fs P sC Q w c c' hevC]
    exact ⟨fun h => hspec.1 (hevC.trans h), fun x h => hspec.2 x (hevC.trans h)⟩
  | none =>
    rw [evalCK_of_evalC_none fig fs P sC Q w c c' hevC]
    obtain ⟨K, rk, hK⟩ := hinv.hsync hwin
    rcases hinv.hsim.hhon (w, c) hmem with ⟨hhon_c, hc_le_M, hsends_snd, hc_le_snd⟩
    rcases hhon_c with
      ⟨_, hw_len, ht1, hraw_c, hi_ge, _, hT_c, h, body, hparse, hver, hsrk, hctr, haddrs_raw, _⟩
    have hother_snd : (Party.senderOf c.1.1).other = Q := by
      rw [hsnd]; cases Q <;> rfl
    have haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true := hother_snd ▸ haddrs_raw
    have hQ_recv : Q.sendsIn c.1.1 = false := by
      have h := sendsIn_other_eq_not Q c.1.1
      rw [← hsnd, hsends_snd] at h
      simpa using h
    let tFront := max (s_fig8.st .A).tcur (s_fig8.st .B).tcur
    have htFront_le : tFront ≤ max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B) := by
      have hA : (s_fig8.st .A).tcur ≤ maxActiveEp sC.base.mir .A := by
        rw [hinv.hsim.htcur .A]; dsimp [maxActiveEp]; split_ifs <;> omega
      have hB : (s_fig8.st .B).tcur ≤ maxActiveEp sC.base.mir .B := by
        rw [hinv.hsim.htcur .B]; dsimp [maxActiveEp]; split_ifs <;> omega
      exact max_le (le_trans hA (Nat.le_max_left _ _)) (le_trans hB (Nat.le_max_right _ _))
    have ht_le : c.1.1 ≤ tFront := by
      have hc_le_snd' : c.1.1 ≤ (s_fig8.st (Party.senderOf c.1.1)).tcur := by
        rw [hinv.hsim.htcur (Party.senderOf c.1.1)]
        exact hc_le_snd
      cases hsnd_p : Party.senderOf c.1.1 <;> rw [hsnd_p] at hc_le_snd'
      · exact le_trans hc_le_snd' (Nat.le_max_left _ _)
      · exact le_trans hc_le_snd' (Nat.le_max_right _ _)
    let tr : EpochTrace P.C.F Dh encPt :=
      { tFront := tFront
        rk := rk
        ck := K
        x := epExp
        hFront_pos := le_trans ht1 ht_le
        hStep := hK.hStep
        hDistinct := fun e₁ he₁ e₂ he₂ hdh =>
          hinv.hsim.hcoll e₁ e₂ (le_trans he₁ htFront_le) (le_trans he₂ htFront_le) hdh }
    have htry := tryFrom_of_parse P.codec w h body hw_len hparse
    have hY : h.senderRatchetKey = encT (tr.T c.1.1) := hsrk
    have hkey_T : (c.1.2.map encT).getD dummyKey = h.senderRatchetKey := by
      rw [hT_c, Option.map_some, Option.getD_some, hsrk]
    have hc_eta : (c.1, (c.2.1, c.2.2)) = c := by rcases c with ⟨hdr, i, e⟩; rfl
    have hc'_eta : (c.1, (c.2.1, c'.2.2)) = c' := by
      rcases c' with ⟨hdr', i', e'⟩
      dsimp only at h1 h2
      subst h1 h2
      rfl
    have hkdec_eq : ∀ seed, snapshotMessageKeySeed P sC.snaps Q c.1.1 w = some seed →
        kDecryptFig8 P ℓ Q w c' seed =
          (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
            (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2).map
            fun m => (c.1.1, c.2.1, m) := by
      intro seed hk
      have hseed := knownSeedR_eq_msgSeedAt_of_snapSync P hX hDh tr hK.hsnaps ht_le htry hY hk
      have hseed_l : seed = keyToBytes32 (lSeedAt P.C.F (K c.1.1) c.2.1) := by
        rw [hseed, keyToBytes32_lSeedAt]
        dsimp only [tr] at hctr ⊢
        rw [← hctr, Nat.add_sub_cancel]
      rw [hseed_l, kDecryptFig8_eq_lAead_dec P encT idOf hid Q c.1.1 c.1.2 hQ_recv
        w hw_len h body hparse hver hkey_T haddrs c'
        (by rw [h1]) (by rw [h2, hctr]) (by rw [h3, hraw_c])
        (lSeedAt P.C.F (K c.1.1) c.2.1)]
      rw [h1, h2]
    obtain ⟨pm, hdec_c⟩ : ∃ pm,
        ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c.2.2 = some pm := by
      obtain ⟨res, hres⟩ := hK.hhon (w, c) hmem
      have hres' : (lFS P.C P.codec ℓ encT idOf 25000).receive
          ⟨lChainAt P.C.F (K c.1.1) (c.2.1 - 1), c.2.1 - 1, []⟩ c.1 (c.2.1, c.2.2) = some res :=
        hres
      rw [kse_lFS_receive_fresh P encT idOf (K c.1.1) c.2.1 hi_ge c.1 c.2.2,
        Option.map_eq_some_iff] at hres'
      rcases hres' with ⟨pm, hdec, _⟩
      exact ⟨pm, hdec⟩
    have hdich := kse_lFig8_receive_dichotomy P Inv Dh encPt encT idOf lam qep q r x₀
      s_R sC s_fig8 ec winBefore epExp hinv K rk hK Q w c hmem hsnd
    constructor
    · intro hmap
      rw [Option.map_eq_some_iff] at hmap
      rcases hmap with ⟨seed, hk, hkdec⟩
      rw [hkdec_eq seed hk] at hkdec
      have hdec_none : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2 = none := by
        cases hdec : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2 with
        | none => rfl
        | some m => rw [hdec] at hkdec; cases hkdec
      rcases hdich with hnone | ⟨st', hst'⟩
      · rw [← hc'_eta]; exact hnone c'.2.2
      · rw [← hc'_eta, hst' c'.2.2, hdec_none]; rfl
    · intro x hmap
      rw [Option.map_eq_some_iff] at hmap
      rcases hmap with ⟨seed, hk, hkdec⟩
      rw [hkdec_eq seed hk] at hkdec
      rcases hdich with hnone | ⟨st', hst'⟩
      · right
        have h1' := hnone c'.2.2
        have h2' := hnone c.2.2
        rw [hc'_eta] at h1'
        rw [hc_eta] at h2'
        exact ⟨h1', h2'⟩
      · left
        have hfig_c' := hst' c'.2.2
        rw [hc'_eta] at hfig_c'
        have hfig_c := hst' c.2.2
        rw [hc_eta, hdec_c] at hfig_c
        cases hdec' : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
            (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2 with
        | none => rw [hdec'] at hkdec; cases hkdec
        | some m' =>
          rw [hdec'] at hkdec hfig_c'
          dsimp only [Option.map] at hkdec hfig_c' hfig_c
          injection hkdec with hx_eq
          subst hx_eq
          exact ⟨st', hfig_c', pm, hfig_c⟩

/-! ## Corruption-window exclusion -/

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem no_corr_window_of_evalCK_none_gen
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (P : Params PQ PQC) (hX : X25519RealizesDh P.C Dh encPt encT) (hDh : Dh.Commutes)
    (tr : EpochTrace P.C.F Dh encPt)
    {s : SimStateCK PQ Pt ℓ} {Q : Party} {s_Q s_Q' : RatchetState} {maxAcc_Q : ℕ → ℕ}
    (hsnaps : ∀ snap ∈ s.snaps, SnapInv P.C Dh encPt encT tr Q s_Q maxAcc_Q snap)
    {w : List (BitVec 8)} {c c' : Fig8C Pt}
    {idx : ℕ} (ht : c.1.1 ≤ tr.tFront) (hsends : Q.other.sendsIn c.1.1 = true)
    {rc : ReceiverChain} {msg : SignalMessage} {msgType : MessageType} {key : MessageKeyGenerator}
    (hw : SignalMessage.tryFrom P.codec w = .ok msg)
    (hY : msg.senderRatchetKey = encT (tr.T c.1.1))
    (hfind : s_Q.findReceiverChainIndex (encT (tr.T c.1.1)) = some idx)
    (hget : s_Q.receiverChains[idx]? = some rc)
    (hinv : RcvChainInv P.C.F (tr.ck c.1.1) (maxAcc_Q c.1.1) rc)
    (hexec : Mut.exec
      (RatchetState.consumeMessageKey P.C.F (encT (tr.T c.1.1))
        ⟨chainKeyValAt P.C.F (tr.ck c.1.1) (maxAcc_Q c.1.1), BitVec.ofNat 32 (maxAcc_Q c.1.1)⟩
        msg.counter msgType) s_Q = (Except.ok key, s_Q'))
    (hstored : ∀ e g, (Q, e, g) ∈ s.snaps → c.1.1 < e → c.1.1 ∈ storedEpochs Q e)
    (heval : predictReceiveWithSnapshots fig fs P s Q w c c' = none) :
    predictReceive (fig := fig) (fs := fs) s Q c c' = none ∧
    snapshotMessageKeySeed P s.snaps Q c.1.1 w = none ∧
    (∀ e g, (Q, e, g) ∈ s.snaps → e + 3 ≤ c.1.1) ∧
    (∀ e g, (Q.other, e, g) ∈ s.snaps → c.1.1 ≠ e + 1) ∧
    (∀ g sc, (Q.other, c.1.1, g) ∈ s.snaps → g.session.senderChain = some sc →
      msg.counter.toNat < sc.chainKey.index.toNat) ∧
    ¬ ((∃ e₁ g₁, (Q.other, e₁, g₁) ∈ s.snaps ∧ c.1.1 = e₁ + 2) ∧
       (∃ g₂, (Q.other, c.1.1, g₂) ∈ s.snaps)) := by
  rcases (evalCK_eq_none_iff fig fs P s Q w c c').mp heval with ⟨hevC, hknone⟩
  refine ⟨hevC, hknone, ?_⟩
  exact knownSeedR_none_no_corr_window P hX hDh tr hsnaps ht hsends hw hY
    hfind hget hinv hexec hstored hknone

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
/-- When `predictReceiveWithSnapshots` returns `none` on an honest delivery to `Q` under `SnapsInv`, all four corruption-window exclusions of `knownSeedR_none_no_corr_window` hold. -/
theorem no_corr_window_of_evalCK_none
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (P : Params PQ PQC) (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hDh : Dh.Commutes)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimStateCK PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {epExp : ℕ → BitVec 256}
    {tr : EpochTrace P.C.F Dh encPt} {K : ℕ → BitVec 256} {maxAcc : Party → ℕ → ℕ}
    (hsnaps : SnapsInv P Dh encPt encT idOf s_R s s_fig8 epExp tr K maxAcc)
    {Q : Party} {w : List (BitVec 8)} {c c' : Fig8C Pt}
    {idx : ℕ} (ht : c.1.1 ≤ tr.tFront) (hsends : Q.other.sendsIn c.1.1 = true)
    {rc : ReceiverChain} {msg : SignalMessage} {msgType : MessageType}
    {key : MessageKeyGenerator} {s_Q' : RatchetState}
    (hw : SignalMessage.tryFrom P.codec w = .ok msg)
    (hY : msg.senderRatchetKey = encT (tr.T c.1.1))
    (hfind : (ratchetStateOf (s_R.st Q)).findReceiverChainIndex (encT (tr.T c.1.1)) = some idx)
    (hget : (ratchetStateOf (s_R.st Q)).receiverChains[idx]? = some rc)
    (hinv : RcvChainInv P.C.F (tr.ck c.1.1) (maxAcc Q c.1.1) rc)
    (hexec : Mut.exec
      (RatchetState.consumeMessageKey P.C.F (encT (tr.T c.1.1))
        ⟨chainKeyValAt P.C.F (tr.ck c.1.1) (maxAcc Q c.1.1), BitVec.ofNat 32 (maxAcc Q c.1.1)⟩
        msg.counter msgType) (ratchetStateOf (s_R.st Q)) = (Except.ok key, s_Q'))
    (hstored : ∀ e g, (Q, e, g) ∈ s.snaps → c.1.1 < e → c.1.1 ∈ storedEpochs Q e)
    (heval : predictReceiveWithSnapshots fig fs P s Q w c c' = none) :
    predictReceive (fig := fig) (fs := fs) s Q c c' = none ∧
    snapshotMessageKeySeed P s.snaps Q c.1.1 w = none ∧
    (∀ e g, (Q, e, g) ∈ s.snaps → e + 3 ≤ c.1.1) ∧
    (∀ e g, (Q.other, e, g) ∈ s.snaps → c.1.1 ≠ e + 1) ∧
    (∀ g sc, (Q.other, c.1.1, g) ∈ s.snaps → g.session.senderChain = some sc →
      msg.counter.toNat < sc.chainKey.index.toNat) ∧
    ¬ ((∃ e₁ g₁, (Q.other, e₁, g₁) ∈ s.snaps ∧ c.1.1 = e₁ + 2) ∧
       (∃ g₂, (Q.other, c.1.1, g₂) ∈ s.snaps)) :=
  no_corr_window_of_evalCK_none_gen fig fs P hX hDh tr (hsnaps.hsnaps Q) ht hsends hw hY
    hfind hget hinv hexec hstored heval

end CryptoGames.LibsignalSM.Proofs.Refinement
