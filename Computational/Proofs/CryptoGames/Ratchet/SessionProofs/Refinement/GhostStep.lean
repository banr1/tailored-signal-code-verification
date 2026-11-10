/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimShallow
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import Computational.Proofs.CryptoGames.AEAD.HKDFProofDefs
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs

/-!
# Single-step `toGhost` and `lFig8` correspondence

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves deterministic single-step correspondence between `toGhost` on libsignal session operations
(`initA`, `initB`, `send`, `receive`) and `lFig8` paired with `simSend` and `simRecv`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  [DecidableEq PQ] [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}

/-! ## Wire MAC and parsing helpers -/

private theorem getLsbD_step8 (b : BitVec 8) (acc : BitVec 64) (m : ℕ) (hm : m < 64) :
    ((acc <<< 8) ||| b.zeroExtend 64).getLsbD m =
      if m < 8 then b.getLsbD m else acc.getLsbD (m - 8) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hm,
    decide_true, Bool.true_and]
  by_cases h8 : m < 8
  · simp [h8]
  · have hge : 8 ≤ m := by omega
    simp [h8, BitVec.getLsbD_of_ge b m hge]

private theorem getLsbD_tag8 (bs : List (BitVec 8)) :
    ∀ (j k : ℕ), k < 8 → 8 * j + k < 64 →
      (bytesToWord64LE bs).getLsbD (8 * j + k) = (bs[j]?.getD 0#8).getLsbD k := by
  induction bs with
  | nil =>
    intro j k _ _
    simp [bytesToWord64LE]
  | cons b tl ih =>
    intro j k hk hlt
    change ((bytesToWord64LE tl <<< 8) ||| b.zeroExtend 64).getLsbD (8 * j + k) =
      ((b :: tl)[j]?.getD 0#8).getLsbD k
    rw [getLsbD_step8 b (bytesToWord64LE tl) (8 * j + k) hlt]
    cases j with
    | zero =>
      simp [hk]
    | succ j' =>
      have hnot8 : ¬ (8 * (j' + 1) + k < 8) := by omega
      have hsub : 8 * (j' + 1) + k - 8 = 8 * j' + k := by omega
      simp only [hnot8, ↓reduceIte, hsub, List.getElem?_cons_succ]
      exact ih j' k hk (by omega)

@[local simp]
theorem length_tagBytes (t : BitVec 64) : (tagBytes t).length = 8 := by
  simp [tagBytes]

theorem getElem?_tagBytes (t : BitVec 64) (j : ℕ) (hj : j < 8) :
    (tagBytes t)[j]? = some ((t >>> (8 * j)).truncate 8) := by
  simp [tagBytes, hj]

theorem tagBytes_tag8 {bs : List (BitVec 8)} (hbs : bs.length = 8) :
    tagBytes (bytesToWord64LE bs) = bs := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 8
  · have hj_len : j < bs.length := by omega
    rw [getElem?_tagBytes (bytesToWord64LE bs) j hj, List.getElem?_eq_getElem hj_len]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp only [hk, decide_true, Bool.true_and, Nat.add_comm (8 * j) k]
    have htag := getLsbD_tag8 bs j k hk (by omega)
    rw [Nat.add_comm k (8 * j), htag, List.getElem?_eq_getElem hj_len, Option.getD_some]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem tag8_tagBytes (t : BitVec 64) : bytesToWord64LE (tagBytes t) = t := by
  apply BitVec.eq_of_getLsbD_eq
  intro m hm
  have hdiv : m / 8 < 8 := by omega
  have hmod : m % 8 < 8 := Nat.mod_lt m (by decide)
  have heq : 8 * (m / 8) + m % 8 = m := Nat.div_add_mod m 8
  rw [← heq, getLsbD_tag8 (tagBytes t) (m / 8) (m % 8) hmod (by omega)]
  rw [getElem?_tagBytes t (m / 8) hdiv, Option.getD_some, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  simp [hmod, Nat.add_comm (8 * (m / 8)) (m % 8), heq]

theorem tag8_eq_iff {a b : List (BitVec 8)} (ha : a.length = 8) (hb : b.length = 8) :
    bytesToWord64LE a = bytesToWord64LE b ↔ a = b := by
  constructor
  · intro h
    rw [← tagBytes_tag8 ha, ← tagBytes_tag8 hb, h]
  · rintro rfl; rfl

theorem length_sha256With (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  generalize (chunks64 (sha256Pad m)).foldl F sha256IV = s
  rcases s with ⟨l, hl⟩
  simp [toBEBytes, List.length_flatMap, hl]

theorem length_hmacWith (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8)) :
    (hmacWith F k m).length = 32 :=
  length_sha256With F _

theorem length_hmac8 (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8)) :
    (hmacSha256Trunc8 F k m).length = 8 := by
  simp [hmacSha256Trunc8, length_hmacWith]

theorem length_computeMac (F : ShaCompress) (s r : IdentityKey) (mk : BitVec 256)
    (m : List (BitVec 8)) :
    (computeMac F s r mk m).length = 8 :=
  length_hmac8 F _ _

theorem tag8_computeMac (F : ShaCompress) (s r : IdentityKey) (mk : BitVec 256)
    (m : List (BitVec 8)) :
    bytesToWord64LE (computeMac F s r mk m) = (hmacScheme F).tag mk ((macIds s r).toList ++ m) := rfl

theorem tagBytes_hmacScheme_tag (F : ShaCompress) (s r : IdentityKey) (mk : BitVec 256)
    (m : List (BitVec 8)) :
    tagBytes ((hmacScheme F).tag mk ((macIds s r).toList ++ m)) = computeMac F s r mk m := by
  rw [← tag8_computeMac, tagBytes_tag8 (length_computeMac F s r mk m)]

theorem computeMac_beq_eq_hmacScheme_beq (F : ShaCompress) (s r : IdentityKey) (mk : BitVec 256)
    (m theirMac : List (BitVec 8)) (htheir : theirMac.length = 8) :
    (computeMac F s r mk m == theirMac) =
      ((hmacScheme F).tag mk ((macIds s r).toList ++ m) == bytesToWord64LE theirMac) := by
  rw [← tag8_computeMac]
  by_cases h : computeMac F s r mk m = theirMac
  · subst h; simp
  · have hne : bytesToWord64LE (computeMac F s r mk m) ≠ bytesToWord64LE theirMac :=
      mt (tag8_eq_iff (length_computeMac F s r mk m) htheir).1 h
    simp [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne.2 hne]

theorem tryFrom_of_parse (codec : SignalMessageProtoCodec) (w : List (BitVec 8))
    (h : SignalHeader) (body : List (BitVec 8))
    (hlen : ¬ w.length < 9)
    (hparse : (signalWireCodec codec).parse (w.take (w.length - 8)) = some (h, body)) :
    SignalMessage.tryFrom codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ := by
  unfold signalWireCodec at hparse
  dsimp only at hparse
  unfold SignalMessage.tryFrom at hparse ⊢
  have hmac : macLength = 8 := rfl
  rw [hmac] at hparse ⊢
  set ser := w.take (w.length - 8)
  have hser_len : ser.length = w.length - 8 := by simp [ser, List.length_take]
  have htot_len : (ser ++ List.replicate 8 0).length = w.length := by
    rw [List.length_append, hser_len, List.length_replicate]; omega
  have hhead : (ser ++ List.replicate 8 0).headD 0 = w.headD 0 := by
    have hpos : 0 < w.length - 8 := by omega
    rcases w with _ | ⟨b, bs⟩
    · simp at hpos
    · rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨k, hk⟩
      have hser_cons : ser = b :: bs.take k := by
        change List.take ((b :: bs).length - 8) (b :: bs) = b :: bs.take k
        rw [hk, List.take_succ_cons]
      rw [hser_cons]; rfl
  have htake : (ser ++ List.replicate 8 0).take (w.length - 8) = ser := by
    rw [← hser_len, List.take_left]
  have htake_w : w.take (w.length - 8) = ser := rfl
  simp only [htot_len, hlen, ↓reduceIte, hhead, htake, htake_w] at hparse ⊢
  by_cases hv1 : (w.headD 0) >>> 4 < preKyberVersion
  · simp only [hv1, ↓reduceIte, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hparse
    cases hparse
  · by_cases hv2 : currentVersion < (w.headD 0) >>> 4
    · simp only [hv1, hv2, ↓reduceIte, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hparse
      cases hparse
    · simp only [hv1, hv2, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hparse ⊢
      cases hd : codec.decode (ser.drop 1) with
      | none =>
        rw [hd] at hparse
        simp only [throw, throwThe, MonadExceptOf.throw] at hparse
        cases hparse
      | some p =>
        rw [hd] at hparse
        dsimp only at hparse ⊢
        cases hrk : p.ratchetKey with
        | none =>
          rw [hrk] at hparse
          simp only [throw, throwThe, MonadExceptOf.throw] at hparse
          cases hparse
        | some rk =>
          rw [hrk] at hparse
          dsimp only at hparse ⊢
          cases hdes : PublicKey.deserialize rk with
          | error e =>
            rw [hdes] at hparse
            simp only at hparse
            cases hparse
          | ok srk =>
            rw [hdes] at hparse
            dsimp only at hparse ⊢
            cases hctr : p.counter with
            | none =>
              rw [hctr] at hparse
              simp only [throw, throwThe, MonadExceptOf.throw] at hparse
              cases hparse
            | some ctr =>
              rw [hctr] at hparse
              dsimp only at hparse ⊢
              cases hct : p.ciphertext with
              | none =>
                rw [hct] at hparse
                simp only [throw, throwThe, MonadExceptOf.throw] at hparse
                cases hparse
              | some ct =>
                rw [hct] at hparse
                dsimp only at hparse ⊢
                injection hparse with hpair
                rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
                rfl

theorem tryFrom_isError_of_parse_none (codec : SignalMessageProtoCodec) (w : List (BitVec 8))
    (h : w.length < 9 ∨ (signalWireCodec codec).parse (w.take (w.length - 8)) = none) :
    ∃ e, SignalMessage.tryFrom codec w = .error e := by
  cases htm : SignalMessage.tryFrom codec w with
  | error e => exact ⟨e, rfl⟩
  | ok msg =>
    rcases tryFrom_parse_eq codec w msg htm with ⟨hlen, hparse⟩
    rcases h with hlt | hnone
    · exact False.elim (hlen hlt)
    · rw [hparse] at hnone; cases hnone

/-! ## Ghost-state and eager-sender helpers -/

def idOfP (P : Params PQ PQC) (R : Party) : IdentityKey :=
  if R == Party.A then P.idA else P.idB

@[local simp]
theorem idOfP_A (P : Params PQ PQC) : idOfP P .A = P.idA := rfl

@[local simp]
theorem idOfP_B (P : Params PQ PQC) : idOfP P .B = P.idB := rfl

theorem idOf_eq_idOfP (P : Params PQ PQC) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (R : Party) :
    idOf R = idOfP P R := by
  cases R
  · exact hid.1
  · exact hid.2

theorem lIds_eq_macIds_of_sendsIn (P : Params PQ PQC) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (Q : Party) (t : ℕ)
    (hsends : Q.sendsIn t = true) :
    lIds idOf t = macIds (idOfP P Q) (idOfP P Q.other) := by
  have hsender : Party.senderOf t = Q := by
    cases Q <;> simp [Party.sendsIn, Party.senderOf] at hsends ⊢ <;> omega
  unfold lIds
  rw [hsender, idOf_eq_idOfP P idOf hid Q, idOf_eq_idOfP P idOf hid Q.other]

theorem lIds_eq_macIds_of_not_sendsIn (P : Params PQ PQC) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (Q : Party) (t : ℕ)
    (hrecv : Q.sendsIn t = false) :
    lIds idOf t = macIds (idOfP P Q.other) (idOfP P Q) := by
  have hsender : Party.senderOf t = Q.other := by
    cases Q <;> simp [Party.sendsIn, Party.senderOf, Party.other] at hrecv ⊢ <;> omega
  have hother : Q.other.other = Q := by cases Q <;> rfl
  unfold lIds
  rw [hsender, hother, idOf_eq_idOfP P idOf hid Q.other, idOf_eq_idOfP P idOf hid Q]

def toRecvChain (st : Fig8St Pt) (g : GhostChain) : ReceiverChain :=
  match st.vR g.epoch with
  | some v =>
    ⟨g.key.getD dummyKey, some ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩,
      g.skipped.filterMap fun j =>
        (v.skippedKeys.lookup j).map fun mk => ⟨keyToBytes32 mk, BitVec.ofNat 32 (j - 1)⟩⟩
  | none => ⟨g.key.getD dummyKey, none, []⟩

@[local simp]
theorem toRecvChain_senderRatchetKey (st : Fig8St Pt) (g : GhostChain) :
    (toRecvChain st g).senderRatchetKey = g.key.getD dummyKey := by
  unfold toRecvChain
  cases st.vR g.epoch <;> rfl

def withEager (g : GhostState PQ) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (pn : BitVec 32) : GhostState PQ :=
  { g with session := { g.session with rootKey := rk, senderChain := sc, previousCounter := pn } }

@[local simp]
theorem withEager_party (g : GhostState PQ) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (pn : BitVec 32) :
    (withEager g rk sc pn).party = g.party := rfl

@[local simp]
theorem withEager_epoch (g : GhostState PQ) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (pn : BitVec 32) :
    (withEager g rk sc pn).epoch = g.epoch := rfl

@[local simp]
theorem withEager_chainEpochs (g : GhostState PQ) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (pn : BitVec 32) :
    (withEager g rk sc pn).chainEpochs = g.chainEpochs := rfl

@[local simp]
theorem withEager_receiverChains (g : GhostState PQ) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (pn : BitVec 32) :
    (withEager g rk sc pn).session.receiverChains = g.session.receiverChains := rfl

def fig8StepS (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (st : Fig8St Pt) (rc : BitVec 256) : Fig8St Pt :=
  let c := (dhScheme Dh).send st.γ rc
  let p := (rootPRNG C.F encPt).up st.root c.2.2
  { st with tcur := st.tcur + 1, γ := c.1, curCkaMsg := some c.2.1, root := p.1,
            vS := some ⟨p.2, 0⟩ }

theorem toGhost_fig8StepS (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (T : Pt) (hγ : st.γ = .pub T) (rc : BitVec 256) (pn : BitVec 32) :
    toGhost P { s with pn := Function.update s.pn Q pn } Q (fig8StepS Dh encPt P.C st rc) =
      let p := (rootPRNG P.C.F encPt).up st.root (Dh.dh rc T)
      withEager (toGhost P s Q st) p.1 (some ⟨KeyPair.generate P.C rc, ⟨p.2, 0⟩⟩) pn := by
  unfold toGhost fig8StepS withEager dhScheme
  rw [hγ]
  simp [Function.update_self]

/-! ## Initialization correspondence -/

theorem libSessionR_initB_toGhost_eq (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (k_root : Ratchet.RootKey) (x₀ x₁ pqrKey : BitVec 256) :
    (libsignalSessionScheme P ℓ encPt lam).initB (k_root, x₀, x₁, pqrKey) =
      toGhost (ℓ := ℓ) P (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) .B
        ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).initB (k_root, x₀)) := rfl

theorem initA_toGhost_eq (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (rk0 : Ratchet.RootKey) (ck0 x₀ x₁ pqrKey : BitVec 256) :
    let stA : Fig8St Pt :=
      { id := .A, root := rk0, vS := none,
        vR := fun t => if t = 0 then some ⟨ck0, 0, []⟩ else none,
        γ := .pub (Dh.dh x₀ Dh.base), curCkaMsg := none, tcur := 0 }
    let s₀ : SimState PQ Pt ℓ :=
      { initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey) with
        chains := fun Q =>
          if Q == Party.A then [⟨some (encT (Dh.dh x₀ Dh.base)), 0, 0, []⟩] else [] }
    let p := (rootPRNG P.C.F encPt).up rk0 (Dh.dh x₁ (Dh.dh x₀ Dh.base))
    P.initA ⟨rk0, ck0, x₀, x₁, pqrKey⟩ =
      withEager (toGhost P s₀ .A stA) p.1 (some ⟨KeyPair.generate P.C x₁, ⟨p.2, 0⟩⟩) 0 ∧
    P.initA ⟨rk0, ck0, x₀, x₁, pqrKey⟩ =
      toGhost P s₀ .A (fig8StepS Dh encPt P.C stA x₁) := by
  dsimp only
  have hM := libX25519Rel_model hX
  have hspk : (KeyPair.generate P.C x₀).publicKey = encT (Dh.dh x₀ Dh.base) :=
    keyPair_generate_publicKey hX x₀
  have hT0 : Dh.dh x₀ Dh.base ≠ 0 := hM.dh_ne_zero x₀ Dh.base hM.base_ne_zero
  have hpub : (encT (Dh.dh x₀ Dh.base)).bytes.toList = encPt (Dh.dh x₀ Dh.base) :=
    encT_bytes_toList hX (Dh.dh x₀ Dh.base)
  have hrc := rootCreateChain_generate_honest P.C hM rk0 x₁ hT0 hpub
  unfold Params.initA initializeInitiatorSession
  dsimp only
  rw [hspk, hrc]
  simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
    SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains, toGhost, withEager,
    fig8StepS, initSim, dhScheme]

theorem libSessionR_initA_toGhost_eq (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (lam : Pt) (k_root : Ratchet.RootKey) (x₀ x₁ pqrKey : BitVec 256) :
    let stA := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).initA (k_root, x₀)
    let s₀ : SimState PQ Pt ℓ :=
      { initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey) with
        chains := fun Q =>
          if Q == Party.A then [⟨some (encT (Dh.dh x₀ Dh.base)), 0, 0, []⟩] else [] }
    let p := (rootPRNG P.C.F encPt).up stA.root (Dh.dh x₁ (Dh.dh x₀ Dh.base))
    (libsignalSessionScheme P ℓ encPt lam).initA (k_root, x₀, x₁, pqrKey) =
      withEager (toGhost P s₀ .A stA) p.1 (some ⟨KeyPair.generate P.C x₁, ⟨p.2, 0⟩⟩) 0 ∧
    (libsignalSessionScheme P ℓ encPt lam).initA (k_root, x₀, x₁, pqrKey) =
      toGhost P s₀ .A (fig8StepS Dh encPt P.C stA x₁) :=
  initA_toGhost_eq P Dh encPt encT hX (rootKdf P.C.F k_root (encPt lam)).1
    (rootKdf P.C.F k_root (encPt lam)).2 x₀ x₁ pqrKey

/-! ## Send correspondence -/

private theorem getLsbD_step32 (b : BitVec 8) (acc : BitVec 256) (m : ℕ) (hm : m < 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).getLsbD m =
      if m < 8 then b.getLsbD m else acc.getLsbD (m - 8) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hm,
    decide_true, Bool.true_and]
  by_cases h8 : m < 8
  · simp [h8]
  · have hge : 8 ≤ m := by omega
    simp [h8, BitVec.getLsbD_of_ge b m hge]

private theorem getLsbD_bytesToKey32 (bs : List (BitVec 8)) :
    ∀ (j k : ℕ), k < 8 → 8 * j + k < 256 →
      (bytesToKey32 bs).getLsbD (8 * j + k) = (bs[j]?.getD 0#8).getLsbD k := by
  induction bs with
  | nil =>
    intro j k _ _
    simp [bytesToKey32]
  | cons b tl ih =>
    intro j k hk hlt
    change ((bytesToKey32 tl <<< 8) ||| b.zeroExtend 256).getLsbD (8 * j + k) =
      ((b :: tl)[j]?.getD 0#8).getLsbD k
    rw [getLsbD_step32 b (bytesToKey32 tl) (8 * j + k) hlt]
    cases j with
    | zero =>
      simp [hk]
    | succ j' =>
      have hnot8 : ¬ (8 * (j' + 1) + k < 8) := by omega
      have hsub : 8 * (j' + 1) + k - 8 = 8 * j' + k := by omega
      simp only [hnot8, ↓reduceIte, hsub, List.getElem?_cons_succ]
      exact ih j' k hk (by omega)

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 32
  · have hj_len : j < bs.length := by omega
    simp only [keyToBytes32, List.getElem?_ofFn, hj, ↓reduceDIte, List.getElem?_eq_getElem hj_len]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitVec.getLsbD_extractLsb']
    simp only [hk, decide_true, Bool.true_and]
    have htag := getLsbD_bytesToKey32 bs j k hk (by omega)
    rw [htag, List.getElem?_eq_getElem hj_len, Option.getD_some]
  · rw [List.getElem?_eq_none (by simp [keyToBytes32]; omega), List.getElem?_eq_none (by omega)]

theorem keyToBytes32_hmacPRF_tag (F : ShaState → List (BitVec 8) → ShaState)
    (ck : BitVec 256) (seed : BitVec 8) :
    keyToBytes32 ((hmacPRF F).tag ck seed) = Ratchet.chainHmac F ck seed :=
  keyToBytes32_bytesToKey32 _ (length_hmacWith F _ [seed])

theorem aesCbcEncrypt_plain (E : AesKey → Block → Block) (key : AesKey) (iv : Block)
    (m : Plain ℓ) :
    aesCbcEncrypt E key iv m.toList =
      ((cbcPkcs7EncryptOnly E ℓ).enc (key, iv) m).toList.flatMap blockToBytesLE := by
  rcases m with ⟨_, rfl⟩
  rfl

theorem ofNat32_ne_allOnes {n : ℕ} (h : n < 2 ^ 32 - 1) :
    BitVec.ofNat 32 n ≠ BitVec.allOnes 32 := by
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp [BitVec.toNat_ofNat, BitVec.toNat_allOnes] at h1
  omega

theorem ofNat32_add_one (n : ℕ) :
    BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem nextChainKey_of_lt (F : ShaCompress) (ck : BitVec 256) {n : ℕ} (h : n < 2 ^ 32 - 1) :
    ChainKey.nextChainKey F ⟨ck, BitVec.ofNat 32 n⟩ =
      .ok ⟨(hmacPRF F).tag ck Ratchet.chainKeySeed, BitVec.ofNat 32 (n + 1)⟩ := by
  unfold ChainKey.nextChainKey
  rw [ite_eq_right (ofNat32_ne_allOnes h), ofNat32_add_one]
  rfl

theorem generateKeys_messageKeys (F : ShaCompress) (ck : BitVec 256) (idx : BitVec 32)
    (salt : Salt) :
    ((ChainKey.messageKeys F ⟨ck, idx⟩).generateKeys F salt) =
      let seed := (hmacPRF F).tag ck Ratchet.messageKeySeed
      let k := deriveMessageKeys F salt (keyToBytes32 seed)
      ⟨k.1.1, k.2, k.1.2, idx⟩ := by
  unfold ChainKey.messageKeys MessageKeyGenerator.generateKeys
  dsimp only
  rw [keyToBytes32_hmacPRF_tag]

theorem sendsIn_succ_of_sendsIn (Q : Party) (t : ℕ) (h : Q.sendsIn t = true) :
    Q.sendsIn (t + 1) = false := by
  cases Q <;> simp [Party.sendsIn] at h ⊢ <;> omega

theorem sendsIn_succ_of_not_sendsIn (Q : Party) (t : ℕ) (h : Q.sendsIn t = false) :
    Q.sendsIn (t + 1) = true := by
  cases Q <;> simp [Party.sendsIn] at h ⊢ <;> omega

theorem encryptAddresses_toGhost (P : Params PQ PQC) (Q : Party) (unackA : Bool) :
    (if (Q == Party.A && unackA) = true then P.sendAddrs Q else none) =
      (if (Q == Party.A && unackA) = true then P.addrAB else none) := by
  cases Q <;> simp [Params.sendAddrs]

theorem send_toGhost_eq_gen (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (hst_id : st.id = Q)
    (hmir_ep : (if Q.sendsIn (s.mir.epoch Q) then s.mir.epoch Q else s.mir.epoch Q + 1) = st.tcur)
    (x : BitVec 256) (hγ : st.γ = .exp x)
    (v : RatchetSenderState (BitVec 256)) (hvS : st.vS = some v)
    (hv_lt : v.lastIndex < 2 ^ 32 - 1)
    (hT : (st.curCkaMsg.map encT).getD dummyKey = (KeyPair.generate P.C x).publicKey)
    (hsends : Q.sendsIn st.tcur = true)
    (m : Plain ℓ) (pqCoins : PQC) (pq' : PQ) (salt : Salt) (pqMsg : List (BitVec 8))
    (hspqr : P.spqr.send (s.pq Q) pqCoins = some (pq', salt, pqMsg))
    (hnp : P.spqr.sendPanics (s.pq Q) pqCoins = false)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hmir'_ep : mir'.epoch Q = st.tcur)
    (honest' : List (List (BitVec 8) × Fig8C Pt))
    (rc : BitVec 256) :
    let addrs := if Q == Party.A && s.unackA then P.addrAB else none
    let pub : LibsignalMsgPublicPart := ⟨s.pn Q, pqMsg, effectiveHkdfSalt32 salt, addrs⟩
    let (st', c) :=
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) rc
    let s' : SimState PQ Pt ℓ :=
      { s with mir := mir', pq := Function.update s.pq Q pq', honest := honest' }
    P.send (toGhost P s Q st) m.toList pqCoins = (toGhost P s' Q st', toWire c) := by
  dsimp only
  have hnot_succ : st.id.sendsIn (st.tcur + 1) = false := by
    rw [hst_id]; exact sendsIn_succ_of_sendsIn Q st.tcur hsends
  have hlids : lIds idOf st.tcur = macIds (idOfP P Q) (idOfP P Q.other) :=
    lIds_eq_macIds_of_sendsIn P idOf hid Q st.tcur hsends
  have hnext := nextChainKey_of_lt P.C.F v.chainKey hv_lt
  have hgen := generateKeys_messageKeys P.C.F v.chainKey (BitVec.ofNat 32 v.lastIndex) salt
  simp only [msgKeys_effSalt P.C.F salt] at hgen
  have hcbc := fun k iv => aesCbcEncrypt_plain P.C.E k iv m
  have hver1 : ¬ (BitVec.ofNat 32 currentVersion.toNat : BitVec 32) = 0 := by decide
  have hver2 : ¬ 256 ≤ (BitVec.ofNat 32 currentVersion.toNat : BitVec 32).toNat := by decide
  have hver3 : BitVec.ofNat 8 (BitVec.ofNat 32 currentVersion.toNat : BitVec 32).toNat =
      currentVersion := by decide
  have hloc : (if Q == Party.A then P.idA else P.idB) = idOfP P Q := rfl
  have hrem : (if Q.other == Party.A then P.idA else P.idB) = idOfP P Q.other := rfl
  have hidx_sub : v.lastIndex + 1 - 1 = v.lastIndex := by omega
  unfold Params.send SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    OutgoingTripleRatchet.encrypt OutgoingTripleRatchet.applyToSessionState
    SessionState.takePqRatchetState SessionState.encryptAddresses SessionState.version
    lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG
    AEADScheme.movePubPartToAD lAead lAeadK lWire libsignalWireAead wireEncode signalWireCodec
    lChainPRG lHeader toWire SignalMessage.new toGhost
  dsimp only
  simp only [hγ, hvS, hnot_succ, Bool.false_eq_true, ↓reduceIte,
    Mut.exec_bind, Mut.exec_get, Mut.exec_modifyGet, Mut.exec_pure,
    hnp, hspqr, hgen, hnext, Mut.exec_liftE_ok, Mut.exec_set,
    hmir_ep, hmir'_ep, Function.update_self, Option.map_some, Prod.mk.eta,
    encryptAddresses_toGhost P Q s.unackA,
    hver1, hver2, hver3, hloc, hrem, hcbc, ← hT, hidx_sub, hlids, tagBytes_hmacScheme_tag]

/-- Single-step send correspondence between `P.send` on `toGhost` and `lFig8` in a sending epoch. -/
theorem send_toGhost_eq (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (hst_id : st.id = Q) (hmir_ep : s.mir.epoch Q = st.tcur)
    (x : BitVec 256) (hγ : st.γ = .exp x)
    (v : RatchetSenderState (BitVec 256)) (hvS : st.vS = some v)
    (hv_lt : v.lastIndex < 2 ^ 32 - 1)
    (hT : (st.curCkaMsg.map encT).getD dummyKey = (KeyPair.generate P.C x).publicKey)
    (hsends : Q.sendsIn st.tcur = true)
    (m : Plain ℓ) (pqCoins : PQC) (pq' : PQ) (salt : Salt) (pqMsg : List (BitVec 8))
    (hspqr : P.spqr.send (s.pq Q) pqCoins = some (pq', salt, pqMsg))
    (hnp : P.spqr.sendPanics (s.pq Q) pqCoins = false)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hmir'_ep : mir'.epoch Q = st.tcur)
    (honest' : List (List (BitVec 8) × Fig8C Pt))
    (rc : BitVec 256) :
    let addrs := if Q == Party.A && s.unackA then P.addrAB else none
    let pub : LibsignalMsgPublicPart := ⟨s.pn Q, pqMsg, effectiveHkdfSalt32 salt, addrs⟩
    let (st', c) :=
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) rc
    let s' : SimState PQ Pt ℓ :=
      { s with mir := mir', pq := Function.update s.pq Q pq', honest := honest' }
    P.send (toGhost P s Q st) m.toList pqCoins = (toGhost P s' Q st', toWire c) :=
  send_toGhost_eq_gen P Dh encPt encT idOf lam hid s Q st hst_id
    (by simp [hmir_ep, hsends]) x hγ v hvS hv_lt hT hsends m pqCoins pq' salt pqMsg
    hspqr hnp mir' hmir'_ep honest' rc

theorem lFig8_send_of_sendsIn_succ (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (st : Fig8St Pt) (pm : LibsignalMsgPublicPart × Plain ℓ) (rc : BitVec 256)
    (hsends : st.id.sendsIn (st.tcur + 1) = true) :
    (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send st pm rc =
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send (fig8StepS Dh encPt C st rc) pm rc := by
  have hnot_succ2 : (fig8StepS Dh encPt C st rc).id.sendsIn
      ((fig8StepS Dh encPt C st rc).tcur + 1) = false := by
    change st.id.sendsIn (st.tcur + 1 + 1) = false
    exact sendsIn_succ_of_sendsIn st.id (st.tcur + 1) hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send
  dsimp only
  simp only [hsends, hnot_succ2, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Single-step send correspondence between `P.send` with eager sender state and `lFig8` in a
receiving window. -/
theorem send_withEager_toGhost_eq (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (hst_id : st.id = Q) (hmir_ep : s.mir.epoch Q = st.tcur)
    (T_other : Pt) (hγ : st.γ = .pub T_other)
    (hrecv : Q.sendsIn st.tcur = false)
    (pn : BitVec 32)
    (m : Plain ℓ) (pqCoins : PQC) (pq' : PQ) (salt : Salt) (pqMsg : List (BitVec 8))
    (hspqr : P.spqr.send (s.pq Q) pqCoins = some (pq', salt, pqMsg))
    (hnp : P.spqr.sendPanics (s.pq Q) pqCoins = false)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hmir'_ep : mir'.epoch Q = st.tcur + 1)
    (honest' : List (List (BitVec 8) × Fig8C Pt))
    (rc : BitVec 256) :
    let p := (rootPRNG P.C.F encPt).up st.root (Dh.dh rc T_other)
    let addrs := if Q == Party.A && s.unackA then P.addrAB else none
    let pub : LibsignalMsgPublicPart := ⟨pn, pqMsg, effectiveHkdfSalt32 salt, addrs⟩
    let (st', c) :=
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) rc
    let s' : SimState PQ Pt ℓ :=
      { s with mir := mir', pq := Function.update s.pq Q pq',
               pn := Function.update s.pn Q pn, honest := honest' }
    P.send (withEager (toGhost P s Q st) p.1 (some ⟨KeyPair.generate P.C rc, ⟨p.2, 0⟩⟩) pn)
        m.toList pqCoins =
      (toGhost P s' Q st', toWire c) := by
  have hsends_succ : Q.sendsIn (st.tcur + 1) = true :=
    sendsIn_succ_of_not_sendsIn Q st.tcur hrecv
  have hst_succ : st.id.sendsIn (st.tcur + 1) = true := by
    rw [hst_id]; exact hsends_succ
  change P.send
      (withEager (toGhost P s Q st)
        ((rootPRNG P.C.F encPt).up st.root (Dh.dh rc T_other)).1
        (some ⟨KeyPair.generate P.C rc,
          ⟨((rootPRNG P.C.F encPt).up st.root (Dh.dh rc T_other)).2, 0⟩⟩) pn)
      m.toList pqCoins =
    (toGhost P
      { s with mir := mir', pq := Function.update s.pq Q pq',
               pn := Function.update s.pn Q pn, honest := honest' } Q
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st
        (⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && s.unackA then P.addrAB else none⟩, m) rc).1,
      toWire ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st
        (⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && s.unackA then P.addrAB else none⟩, m) rc).2)
  rw [← toGhost_fig8StepS P Dh encPt s Q st T_other hγ rc pn,
    lFig8_send_of_sendsIn_succ Dh encPt P.C P.codec ℓ encT idOf lam st _ rc hst_succ]
  set st₁ := fig8StepS Dh encPt P.C st rc
  set s₀ : SimState PQ Pt ℓ := { s with pn := Function.update s.pn Q pn }
  have hstep := send_toGhost_eq_gen P Dh encPt encT idOf lam hid s₀ Q st₁ hst_id
    (by simp [s₀, st₁, fig8StepS, hmir_ep, hrecv]) rc (by simp [st₁, fig8StepS, hγ, dhScheme])
    ⟨((rootPRNG P.C.F encPt).up st.root (Dh.dh rc T_other)).2, 0⟩
    (by simp [st₁, fig8StepS, hγ, dhScheme])
    (by simp)
    (by simp [st₁, fig8StepS, hγ, dhScheme, keyPair_generate_publicKey hX rc])
    hsends_succ m pqCoins pq' salt pqMsg hspqr hnp mir' hmir'_ep honest' rc
  dsimp only [s₀] at hstep
  simpa [Function.update_self] using hstep

/-! ## Receiver-chain synchronization -/

def mkSkippedList (skipped : List ℕ) (dict : List (ℕ × BitVec 256)) : List MessageKeyGenerator :=
  skipped.filterMap fun j =>
    (dict.lookup j).map fun mk => ⟨keyToBytes32 mk, BitVec.ofNat 32 (j - 1)⟩

/-- Synchronization invariant between a `GhostChain` and its Fig. 6 `RatchetReceiverState`. -/
structure ChainSync (g : GhostChain)
    (v : RatchetReceiverState (BitVec 256) (BitVec 256)) : Prop where
  last_eq : g.last = v.lastIndex
  last_lt : v.lastIndex < 2 ^ 32
  nodup_skipped : g.skipped.Nodup
  len_skipped : g.skipped.length ≤ 2000
  mem_skipped : ∀ j ∈ g.skipped, 1 ≤ j ∧ j ≤ v.lastIndex ∧ (v.skippedKeys.lookup j).isSome
  skippedKeys_le : ∀ p ∈ v.skippedKeys, p.1 ≤ v.lastIndex

theorem ChainSync.init (key : Option PublicKey) (t : ℕ) (ck : BitVec 256) :
    ChainSync ⟨key, t, 0, []⟩ ⟨ck, 0, []⟩ where
  last_eq := rfl
  last_lt := by simp
  nodup_skipped := List.nodup_nil
  len_skipped := by simp
  mem_skipped := by intro _ h; cases h
  skippedKeys_le := by intro _ h; cases h

theorem lookup_filter_ne (dict : List (ℕ × BitVec 256)) {i j : ℕ} (hne : j ≠ i) :
    (dict.filter (fun p => p.1 != i)).lookup j = dict.lookup j := by
  induction dict with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨k, val⟩
    by_cases hkj : (j == k) = true
    · have hjk : j = k := beq_iff_eq.1 hkj
      subst hjk
      have hne' : (j != i) = true := bne_iff_ne.2 hne
      simp [List.filter, hne', List.lookup, hkj]
    · have hkj_f : (j == k) = false := Bool.eq_false_iff.2 hkj
      by_cases hki : (k != i) = true <;> simp [List.filter, hki, List.lookup, hkj_f, ih]

theorem mkSkippedList_filter_of_not_mem {l : List ℕ} {dict : List (ℕ × BitVec 256)} {i : ℕ}
    (hnot : i ∉ l) :
    mkSkippedList l (dict.filter (fun p => p.1 != i)) = mkSkippedList l dict := by
  unfold mkSkippedList
  apply List.filterMap_congr
  intro j hj
  have hne : j ≠ i := fun heq => hnot (heq ▸ hj)
  rw [lookup_filter_ne dict hne]

theorem findIdx_mkSkippedList_none_of_not_mem {l : List ℕ} {dict : List (ℕ × BitVec 256)}
    {counter : BitVec 32}
    (hmem : ∀ j ∈ l, 1 ≤ j ∧ j ≤ 2 ^ 32)
    (hnot : (counter.toNat + 1) ∉ l) :
    (mkSkippedList l dict).findIdx? (fun mk => mk.counter == counter) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro mk hmk
  unfold mkSkippedList at hmk
  rw [List.mem_filterMap] at hmk
  rcases hmk with ⟨j, hj, hmap⟩
  cases hlk : dict.lookup j with
  | none => rw [hlk] at hmap; cases hmap
  | some val =>
    rw [hlk] at hmap
    injection hmap with hmk_eq
    subst hmk_eq
    dsimp only
    apply beq_eq_false_iff_ne.2
    intro heq
    rcases hmem j hj with ⟨hj1, hj2⟩
    have hlt : j - 1 < 2 ^ 32 := by omega
    have htoNat := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at htoNat
    have hji : j = counter.toNat + 1 := by omega
    exact hnot (hji ▸ hj)

theorem findIdx_mkSkippedList_of_mem {l : List ℕ} {dict : List (ℕ × BitVec 256)}
    {counter : BitVec 32} {key : BitVec 256}
    (hnodup : l.Nodup)
    (hmem : ∀ j ∈ l, 1 ≤ j ∧ j ≤ 2 ^ 32 ∧ (dict.lookup j).isSome)
    (hi : (counter.toNat + 1) ∈ l)
    (hlk : dict.lookup (counter.toNat + 1) = some key) :
    ∃ pos,
      (mkSkippedList l dict).findIdx? (fun mk => mk.counter == counter) = some pos ∧
      (mkSkippedList l dict)[pos]? = some ⟨keyToBytes32 key, counter⟩ ∧
      (mkSkippedList l dict).eraseIdx pos =
        mkSkippedList (l.erase (counter.toNat + 1)) dict := by
  induction l with
  | nil => cases hi
  | cons j js ih =>
    rcases List.nodup_cons.1 hnodup with ⟨hj_not_mem, hnodup_js⟩
    rcases hmem j (List.mem_cons_self ..) with ⟨hj1, hj2, hlk_j⟩
    rcases Option.isSome_iff_exists.1 hlk_j with ⟨kj, hkj⟩
    have hcons : mkSkippedList (j :: js) dict =
        ⟨keyToBytes32 kj, BitVec.ofNat 32 (j - 1)⟩ :: mkSkippedList js dict := by
      unfold mkSkippedList
      simp [List.filterMap, hkj]
    by_cases hji : j = counter.toNat + 1
    · subst hji
      rw [hlk] at hkj
      injection hkj with hkj_eq
      subst hkj_eq
      have hctr : BitVec.ofNat 32 (counter.toNat + 1 - 1) = counter := by simp
      refine ⟨0, ?_, ?_, ?_⟩
      · rw [hcons, hctr]; simp [List.findIdx?_cons]
      · rw [hcons, hctr]; rfl
      · rw [hcons, List.erase_cons_head]; rfl
    · have hi_js : counter.toNat + 1 ∈ js := by
        rcases List.mem_cons.1 hi with rfl | h
        · exact False.elim (hji rfl)
        · exact h
      have hne_ctr : (BitVec.ofNat 32 (j - 1) == counter) = false := by
        apply beq_eq_false_iff_ne.2
        intro heq
        have hlt : j - 1 < 2 ^ 32 := by omega
        have htoNat := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at htoNat
        exact hji (by omega)
      rcases ih hnodup_js (fun x hx => hmem x (List.mem_cons_of_mem j hx)) hi_js with
        ⟨pos, hfind, hget, herase⟩
      have hne_j : ¬ (j == counter.toNat + 1) = true := by simp [hji]
      refine ⟨pos + 1, ?_, ?_, ?_⟩
      · rw [hcons, List.findIdx?_cons, hne_ctr, hfind]; rfl
      · rw [hcons, List.getElem?_cons_succ, hget]
      · rw [hcons, List.eraseIdx_cons_succ, herase, List.erase_cons_tail hne_j]
        unfold mkSkippedList
        simp [List.filterMap, hkj]

theorem ChainSync.accept_of_le {g : GhostChain}
    {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hsync : ChainSync g v) {i : ℕ} (hle : i ≤ g.last) (_hmem : i ∈ g.skipped) :
    ChainSync (g.accept i) { v with skippedKeys := v.skippedKeys.filter (·.1 != i) } := by
  have hlast_eq := hsync.last_eq
  have hlt : ¬ g.last < i := by omega
  have hlt_v : ¬ v.lastIndex < i := by omega
  have hnodup' : (g.skipped.erase i).Nodup := hsync.nodup_skipped.erase i
  have hnot_mem : i ∉ g.skipped.erase i :=
    (List.Nodup.mem_erase_iff hsync.nodup_skipped).not.2 (fun h => h.1 rfl)
  refine ⟨?_, hsync.last_lt, ?_, ?_, ?_, ?_⟩
  · simp [GhostChain.accept, hlast_eq, hlt_v]
  · simp [GhostChain.accept, hlt, hnodup']
  · simp only [GhostChain.accept, hlt, ↓reduceIte]
    exact Nat.le_trans (List.length_erase_le ..) hsync.len_skipped
  · intro j hj
    simp only [GhostChain.accept, hlt, ↓reduceIte] at hj
    have hj_orig : j ∈ g.skipped := List.mem_of_mem_erase hj
    have hne : j ≠ i := fun heq => hnot_mem (heq ▸ hj)
    rcases hsync.mem_skipped j hj_orig with ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rwa [lookup_filter_ne v.skippedKeys hne]
  · intro p hp
    exact hsync.skippedKeys_le p (List.mem_of_mem_filter hp)

theorem mkSkippedList_eq_map {l : List ℕ} {dict : List (ℕ × BitVec 256)}
    (h : ∀ j ∈ l, (dict.lookup j).isSome) :
    mkSkippedList l dict =
      l.map (fun j => ⟨keyToBytes32 ((dict.lookup j).getD 0), BitVec.ofNat 32 (j - 1)⟩) := by
  induction l with
  | nil => rfl
  | cons j js ih =>
    rcases Option.isSome_iff_exists.1 (h j (List.mem_cons_self ..)) with ⟨kj, hkj⟩
    unfold mkSkippedList at ih ⊢
    simp [List.filterMap, hkj, ih (fun x hx => h x (List.mem_cons_of_mem j hx))]

theorem length_mkSkippedList {l : List ℕ} {dict : List (ℕ × BitVec 256)}
    (h : ∀ j ∈ l, (dict.lookup j).isSome) :
    (mkSkippedList l dict).length = l.length := by
  rw [mkSkippedList_eq_map h, List.length_map]

theorem mkSkippedList_take {l : List ℕ} {dict : List (ℕ × BitVec 256)}
    (h : ∀ j ∈ l, (dict.lookup j).isSome) (n : ℕ) :
    mkSkippedList (l.take n) dict = (mkSkippedList l dict).take n := by
  have htake : ∀ j ∈ l.take n, (dict.lookup j).isSome :=
    fun j hj => h j (List.mem_of_mem_take hj)
  rw [mkSkippedList_eq_map htake, mkSkippedList_eq_map h, List.map_take]

theorem dropLast_eq_take {α : Type} (M : List α) : M.dropLast = M.take (M.length - 1) := by
  induction M with
  | nil => rfl
  | cons a ms ih =>
    cases ms with
    | nil => rfl
    | cons b rest =>
      change a :: (b :: rest).dropLast = a :: (b :: rest).take ((b :: rest).length - 1)
      rw [ih]

theorem storeSkipped_eq_take2000 {α : Type} {x : α} {L : List α} (hL : L.length ≤ 2000) :
    (if maxMessageKeys < (x :: L).length then (x :: L).dropLast else x :: L) =
      (x :: L).take 2000 := by
  have hmax : maxMessageKeys = 2000 := rfl
  rw [hmax]
  by_cases hlt : 2000 < (x :: L).length
  · rw [ite_eq_left hlt, dropLast_eq_take]
    have hlen : (x :: L).length - 1 = 2000 := by simp at hlt ⊢; omega
    rw [hlen]
  · rw [ite_eq_right hlt, List.take_of_length_le (by omega)]

theorem take_append_take {α : Type} (n : ℕ) (A B : List α) :
    (A ++ B.take n).take n = (A ++ B).take n := by
  simp [List.take_append, List.take_take, Nat.sub_le]

theorem range_map_sub_append (k p : ℕ) (sk : List ℕ) :
    (List.range (k + 1)).map (fun d => p + (k + 1) - d) ++ sk =
      (List.range k).map (fun d => (p + 1) + k - d) ++ ((p + 1) :: sk) := by
  rw [List.range_succ, List.map_append, List.append_assoc]
  congr 1
  · apply List.map_congr_left
    intro d hd
    omega
  · simp; omega

theorem mkSkippedList_cons_take2000 (F : ShaCompress) (w : BitVec 256) (p : ℕ)
    (sk : List ℕ) (dict : List (ℕ × BitVec 256))
    (hsk : ∀ j ∈ sk, j ≤ p ∧ (dict.lookup j).isSome)
    (hlen : sk.length ≤ 2000) :
    let keys := ChainKey.messageKeys F ⟨w, BitVec.ofNat 32 p⟩ :: mkSkippedList sk dict
    (if maxMessageKeys < keys.length then keys.dropLast else keys) =
      mkSkippedList (((p + 1) :: sk).take 2000)
        ((p + 1, ((lChainPRG F p).gen w).2) :: dict) := by
  dsimp only
  have hlen_mk : (mkSkippedList sk dict).length ≤ 2000 := by
    rw [length_mkSkippedList (fun j hj => (hsk j hj).2)]; exact hlen
  rw [storeSkipped_eq_take2000 hlen_mk]
  have hmem' : ∀ j ∈ (p + 1) :: sk,
      (List.lookup j ((p + 1, ((lChainPRG F p).gen w).2) :: dict)).isSome := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj'
    · simp [List.lookup]
    · have hne : (j == p + 1) = false := beq_eq_false_iff_ne.2 (by have := (hsk j hj').1; omega)
      simp [List.lookup, hne, (hsk j hj').2]
  rw [mkSkippedList_take hmem' 2000]
  congr 1
  unfold mkSkippedList ChainKey.messageKeys lChainPRG
  dsimp only [List.filterMap, List.lookup]
  rw [beq_self_eq_true, Option.map_some, keyToBytes32_hmacPRF_tag, Nat.add_sub_cancel]
  congr 1
  apply List.filterMap_congr
  intro j hj
  have hne : (j == p + 1) = false := beq_eq_false_iff_ne.2 (by have := (hsk j hj).1; omega)
  simp [List.lookup, hne]

theorem findIdx_set_same_key (cs : List ReceiverChain) (their : PublicKey) (ci : ℕ)
    (hfind : cs.findIdx? (fun c => c.senderRatchetKey == their) = some ci)
    (c' : ReceiverChain) (hc' : c'.senderRatchetKey = their) :
    (cs.set ci c').findIdx? (fun c => c.senderRatchetKey == their) = some ci := by
  induction cs generalizing ci with
  | nil => simp [List.findIdx?_nil] at hfind
  | cons c cs ih =>
    cases ci with
    | zero =>
      simp [List.set, List.findIdx?_cons, hc']
    | succ k =>
      simp only [List.findIdx?_cons] at hfind
      cases hck : c.senderRatchetKey == their with
      | true => simp [hck] at hfind
      | false =>
        simp only [hck, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hfind
        rcases hfind with ⟨k', hk', hsucc⟩
        injection hsucc with hk_eq
        subst hk_eq
        simp [List.set, List.findIdx?_cons, hck, ih k' hk']

theorem getElem?_of_findIdx_some (cs : List ReceiverChain) (their : PublicKey) (ci : ℕ)
    (hfind : cs.findIdx? (fun c => c.senderRatchetKey == their) = some ci) :
    ∃ c, cs[ci]? = some c ∧ c.senderRatchetKey = their := by
  induction cs generalizing ci with
  | nil => simp [List.findIdx?_nil] at hfind
  | cons c cs ih =>
    cases ci with
    | zero =>
      simp only [List.findIdx?_cons] at hfind
      cases hck : c.senderRatchetKey == their with
      | true => exact ⟨c, rfl, beq_iff_eq.1 hck⟩
      | false => simp [hck] at hfind
    | succ k =>
      simp only [List.findIdx?_cons] at hfind
      cases hck : c.senderRatchetKey == their with
      | true => simp [hck] at hfind
      | false =>
        simp only [hck, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hfind
        rcases hfind with ⟨k', hk', hsucc⟩
        injection hsucc with hk_eq
        subst hk_eq
        simpa using ih k' hk'

def updChain (s : RatchetState) (ci : ℕ) (their : PublicKey) (c₀ : Option LibsignalSession.ChainKey)
    (sk : List ℕ) (dict : List (ℕ × BitVec 256)) : RatchetState :=
  { s with receiverChains := s.receiverChains.set ci ⟨their, c₀, mkSkippedList sk dict⟩ }

theorem exec_advanceChain_skipKeys (F : ShaCompress) (s : RatchetState) (ci : ℕ)
    (their : PublicKey) (c₀ : Option LibsignalSession.ChainKey) (counter : BitVec 32)
    (hfind : s.findReceiverChainIndex their = some ci)
    (k : ℕ) :
    ∀ (p : ℕ) (w : BitVec 256) (sk : List ℕ) (dict : List (ℕ × BitVec 256)),
      p + k = counter.toNat →
      (∀ j ∈ sk, 1 ≤ j ∧ j ≤ p ∧ (dict.lookup j).isSome) →
      (∀ q ∈ dict, q.1 ≤ p) →
      sk.Nodup →
      sk.length ≤ 2000 →
      let (w₁, dict') := FSAEAD.skipKeys (lChainPRG F) k w p dict
      let sk' := ((List.range k).map (fun d => p + k - d) ++ sk).take 2000
      Mut.exec (RatchetState.advanceChain F their counter k ⟨w, BitVec.ofNat 32 p⟩)
          (updChain s ci their c₀ sk dict) =
        (.ok ⟨w₁, counter⟩, updChain s ci their c₀ sk' dict') ∧
      sk'.Nodup ∧
      sk'.length ≤ 2000 ∧
      (∀ j ∈ sk', 1 ≤ j ∧ j ≤ p + k ∧ (dict'.lookup j).isSome) ∧
      (∀ q ∈ dict', q.1 ≤ p + k) := by
  rcases getElem?_of_findIdx_some s.receiverChains their ci hfind with ⟨c_init, hc_init, _⟩
  have hci_lt : ci < s.receiverChains.length :=
    (List.getElem?_eq_some_iff.1 hc_init).1
  induction k with
  | zero =>
    intro p w sk dict hp hsk hdict hnodup hlen
    have htake : sk.take 2000 = sk := List.take_of_length_le hlen
    have hp_eq : p = counter.toNat := by omega
    have hctr : BitVec.ofNat 32 p = counter := by simp [hp_eq]
    simp only [FSAEAD.skipKeys, List.range_zero, List.map_nil, List.nil_append, htake, hctr]
    refine ⟨rfl, hnodup, hlen, ?_, ?_⟩
    · intro j hj; simpa using hsk j hj
    · intro q hq; simpa using hdict q hq
  | succ k ih =>
    intro p w sk dict hp hsk hdict hnodup hlen
    have hctr_lt : counter.toNat < 2 ^ 32 := counter.isLt
    have hp_lt : p < counter.toNat := by omega
    have hp_lt_max : p < 2 ^ 32 - 1 := by omega
    have hbv_lt : (BitVec.ofNat 32 p < counter) = true := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat]
      omega
    have hfind_upd : (updChain s ci their c₀ sk dict).findReceiverChainIndex their = some ci :=
      findIdx_set_same_key s.receiverChains their ci hfind _ rfl
    have hget_upd : (updChain s ci their c₀ sk dict).receiverChains[ci]? =
        some ⟨their, c₀, mkSkippedList sk dict⟩ := by
      simp [updChain, List.getElem?_set_self hci_lt]
    have hstore : Mut.exec (RatchetState.storeSkippedKey their
        (ChainKey.messageKeys F ⟨w, BitVec.ofNat 32 p⟩)) (updChain s ci their c₀ sk dict) =
        (.ok (), updChain s ci their c₀ (((p + 1) :: sk).take 2000)
          ((p + 1, ((lChainPRG F p).gen w).2) :: dict)) := by
      unfold RatchetState.storeSkippedKey
      simp only [Mut.exec_bind, Mut.exec_get, hfind_upd, hget_upd, Mut.exec_set]
      rw [mkSkippedList_cons_take2000 F w p sk dict
        (fun j hj => ⟨(hsk j hj).2.1, (hsk j hj).2.2⟩) hlen]
      simp [updChain, List.set_set]
    have hnext : ChainKey.nextChainKey F ⟨w, BitVec.ofNat 32 p⟩ =
        .ok ⟨((lChainPRG F p).gen w).1, BitVec.ofNat 32 (p + 1)⟩ :=
      nextChainKey_of_lt F w hp_lt_max
    set sk₁ := ((p + 1) :: sk).take 2000
    set dict₁ := (p + 1, ((lChainPRG F p).gen w).2) :: dict
    have hsk₁ : ∀ j ∈ sk₁, 1 ≤ j ∧ j ≤ p + 1 ∧ (dict₁.lookup j).isSome := by
      intro j hj
      have hj_cons := List.mem_of_mem_take hj
      rcases List.mem_cons.1 hj_cons with rfl | hj'
      · refine ⟨by omega, by omega, ?_⟩
        simp [dict₁, List.lookup]
      · rcases hsk j hj' with ⟨h1, h2, h3⟩
        have hne : (j == p + 1) = false := beq_eq_false_iff_ne.2 (by omega)
        refine ⟨h1, by omega, ?_⟩
        simp [dict₁, List.lookup, hne, h3]
    have hdict₁ : ∀ q ∈ dict₁, q.1 ≤ p + 1 := by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq'
      · exact Nat.le_refl (p + 1)
      · exact Nat.le_trans (hdict q hq') (Nat.le_succ p)
    have hnot_mem : p + 1 ∉ sk := fun hm => by
      have := (hsk (p + 1) hm).2.1; omega
    have hnodup₁ : sk₁.Nodup :=
      (List.take_sublist 2000 ((p + 1) :: sk)).nodup (List.nodup_cons.2 ⟨hnot_mem, hnodup⟩)
    have hlen₁ : sk₁.length ≤ 2000 := List.length_take_le 2000 ((p + 1) :: sk)
    have hih := ih (p + 1) ((lChainPRG F p).gen w).1 sk₁ dict₁ (by omega) hsk₁ hdict₁ hnodup₁ hlen₁
    have hsk_eq : ((List.range k).map (fun d => (p + 1) + k - d) ++ sk₁).take 2000 =
        ((List.range (k + 1)).map (fun d => p + (k + 1) - d) ++ sk).take 2000 := by
      rw [take_append_take, range_map_sub_append]
    have hadd_eq : p + 1 + k = p + (k + 1) := by omega
    rw [hsk_eq, hadd_eq] at hih
    dsimp only [FSAEAD.skipKeys] at hih ⊢
    rcases hih with ⟨hexec, hnodup', hlen', hsk', hdict'⟩
    refine ⟨?_, hnodup', hlen', hsk', hdict'⟩
    unfold RatchetState.advanceChain
    simp only [hbv_lt, ↓reduceIte, Mut.exec_bind, hstore, hnext, Mut.exec_liftE_ok]
    exact hexec

theorem toRecvChain_of_some (st : Fig8St Pt) (g : GhostChain)
    (v : RatchetReceiverState (BitVec 256) (BitVec 256)) (hv : st.vR g.epoch = some v) :
    toRecvChain st g =
      ⟨g.key.getD dummyKey, some ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩,
        mkSkippedList g.skipped v.skippedKeys⟩ := by
  simp [toRecvChain, hv, mkSkippedList]

theorem map_set_eq_of_getElem?_ne {α β : Type} (l : List α) (ci : ℕ) (a' : α) (f₁ f₂ : α → β)
    (h : ∀ j < l.length, j ≠ ci → ∀ a, l[j]? = some a → f₁ a = f₂ a) :
    (l.set ci a').map f₁ = (l.map f₂).set ci (f₁ a') := by
  rw [List.map_set]
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    by_cases hj : ci = j
    · subst hj
      simp [List.getElem_set_self]
    · rw [List.getElem_set_ne hj, List.getElem_set_ne hj, List.getElem_map, List.getElem_map]
      have hj_lt : j < l.length := by simp at hj₁; exact hj₁
      exact h j hj_lt (Ne.symm hj) l[j] (List.getElem?_eq_getElem hj_lt)

theorem ChainSync.accept_of_gt (F : ShaCompress) (s : RatchetState) (ci : ℕ)
    (their : PublicKey) (c₀ : Option LibsignalSession.ChainKey) (counter : BitVec 32)
    (hfind : s.findReceiverChainIndex their = some ci)
    {g : GhostChain} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hsync : ChainSync g v)
    (hlt : g.last < counter.toNat + 1)
    (hi_lt : counter.toNat + 1 < 2 ^ 32) :
    let k := counter.toNat - v.lastIndex
    let (w₁, dict') := FSAEAD.skipKeys (lChainPRG F) k v.chainKey v.lastIndex v.skippedKeys
    let (w', _) := (lChainPRG F counter.toNat).gen w₁
    Mut.exec (RatchetState.advanceChain F their counter k ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩)
        (updChain s ci their c₀ g.skipped v.skippedKeys) =
      (.ok ⟨w₁, counter⟩, updChain s ci their c₀ (g.accept (counter.toNat + 1)).skipped dict') ∧
    ChainSync (g.accept (counter.toNat + 1)) ⟨w', counter.toNat + 1, dict'⟩ := by
  have hlast_eq := hsync.last_eq
  have hp_le : v.lastIndex ≤ counter.toNat := by omega
  have hpk : v.lastIndex + (counter.toNat - v.lastIndex) = counter.toNat := by omega
  have hstep := exec_advanceChain_skipKeys F s ci their c₀ counter hfind
    (counter.toNat - v.lastIndex) v.lastIndex v.chainKey g.skipped v.skippedKeys
    hpk hsync.mem_skipped hsync.skippedKeys_le hsync.nodup_skipped hsync.len_skipped
  dsimp only at hstep ⊢
  rcases hstep with ⟨hexec, hnodup', hlen', hsk', hdict'⟩
  have hacc_sk : (g.accept (counter.toNat + 1)).skipped =
      ((List.range (counter.toNat - v.lastIndex)).map
        (fun d => v.lastIndex + (counter.toNat - v.lastIndex) - d) ++ g.skipped).take 2000 := by
    simp [GhostChain.accept, hlt, hlast_eq, hpk, hp_le]
  rw [← hacc_sk] at hexec hnodup' hlen' hsk'
  refine ⟨hexec, ?_⟩
  refine ⟨?_, hi_lt, hnodup', hlen', ?_, ?_⟩
  · simp [GhostChain.accept, hlt]
  · intro j hj
    rcases hsk' j hj with ⟨h1, h2, h3⟩
    dsimp only
    exact ⟨h1, by omega, h3⟩
  · intro q hq
    have := hdict' q hq
    dsimp only
    omega

theorem nextChainKey_counter_of_lt (F : ShaCompress) (ck : BitVec 256) (counter : BitVec 32)
    (h : counter.toNat + 1 < 2 ^ 32) :
    ChainKey.nextChainKey F ⟨ck, counter⟩ =
      .ok ⟨((lChainPRG F counter.toNat).gen ck).1, BitVec.ofNat 32 (counter.toNat + 1)⟩ := by
  have hlt : counter.toNat < 2 ^ 32 - 1 := by omega
  have h1 := nextChainKey_of_lt F ck hlt
  simpa [lChainPRG] using h1

theorem nextChainKey_counter_of_ge (F : ShaCompress) (ck : BitVec 256) (counter : BitVec 32)
    (h : 2 ^ 32 ≤ counter.toNat + 1) :
    ∃ e, ChainKey.nextChainKey F ⟨ck, counter⟩ = .error e := by
  have hlt : counter.toNat < 2 ^ 32 := counter.isLt
  have heq : counter = BitVec.allOnes 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_allOnes]
    omega
  unfold ChainKey.nextChainKey
  rw [ite_eq_left heq]
  exact ⟨_, rfl⟩

theorem lookup_none_of_gt {dict : List (ℕ × BitVec 256)} {last i : ℕ}
    (hdict : ∀ q ∈ dict, q.1 ≤ last) (hlt : last < i) :
    dict.lookup i = none := by
  induction dict with
  | nil => rfl
  | cons q qs ih =>
    have hq_le : q.1 ≤ last := hdict q (List.mem_cons_self ..)
    have hne : (i == q.1) = false := beq_eq_false_iff_ne.2 (by omega)
    simp [List.lookup, hne, ih (fun p hp => hdict p (List.mem_cons_of_mem q hp))]

theorem updChain_eq_self (s : RatchetState) (ci : ℕ) (their : PublicKey)
    (c₀ : Option LibsignalSession.ChainKey) (sk : List ℕ) (dict : List (ℕ × BitVec 256))
    (hget : s.receiverChains[ci]? = some ⟨their, c₀, mkSkippedList sk dict⟩) :
    updChain s ci their c₀ sk dict = s := by
  unfold updChain
  have hset : s.receiverChains.set ci ⟨their, c₀, mkSkippedList sk dict⟩ = s.receiverChains := by
    apply List.ext_getElem
    · simp
    · intro j hj₁ hj₂
      by_cases hj : ci = j
      · subst hj
        rw [List.getElem_set_self]
        exact Option.some.inj (hget.symm.trans (List.getElem?_eq_getElem hj₂))
      · rw [List.getElem_set_ne hj]
  cases s
  simp [hset]

theorem exec_setReceiverChainKey (s : RatchetState) (ci : ℕ) (their : PublicKey)
    (c₀ : Option LibsignalSession.ChainKey) (nextCk : LibsignalSession.ChainKey)
    (sk : List ℕ) (dict : List (ℕ × BitVec 256))
    (hfind : s.findReceiverChainIndex their = some ci) :
    Mut.exec (RatchetState.setReceiverChainKey their nextCk) (updChain s ci their c₀ sk dict) =
      (.ok (), updChain s ci their (some nextCk) sk dict) := by
  rcases getElem?_of_findIdx_some s.receiverChains their ci hfind with ⟨c_init, hc_init, _⟩
  have hci_lt : ci < s.receiverChains.length := (List.getElem?_eq_some_iff.1 hc_init).1
  have hfind_upd : (updChain s ci their c₀ sk dict).findReceiverChainIndex their = some ci :=
    findIdx_set_same_key s.receiverChains their ci hfind _ rfl
  have hget_upd : (updChain s ci their c₀ sk dict).receiverChains[ci]? =
      some ⟨their, c₀, mkSkippedList sk dict⟩ := by
    simp [updChain, List.getElem?_set_self hci_lt]
  unfold RatchetState.setReceiverChainKey
  simp only [Mut.exec_bind, Mut.exec_get, hfind_upd, hget_upd, Mut.exec_set]
  simp [updChain, List.set_set]

theorem exec_ensureReceiverChain_known (C : Crypto) (s : RatchetState) (ci : ℕ)
    (their : PublicKey) (ck : LibsignalSession.ChainKey) (coins : BitVec 256)
    (sk : List ℕ) (dict : List (ℕ × BitVec 256))
    (hfind : s.findReceiverChainIndex their = some ci) :
    Mut.exec (RatchetState.ensureReceiverChain C their coins)
        (updChain s ci their (some ck) sk dict) =
      (.ok ck, updChain s ci their (some ck) sk dict) := by
  rcases getElem?_of_findIdx_some s.receiverChains their ci hfind with ⟨c_init, hc_init, _⟩
  have hci_lt : ci < s.receiverChains.length := (List.getElem?_eq_some_iff.1 hc_init).1
  have hfind_upd : (updChain s ci their (some ck) sk dict).findReceiverChainIndex their = some ci :=
    findIdx_set_same_key s.receiverChains their ci hfind _ rfl
  have hget_upd : (updChain s ci their (some ck) sk dict).receiverChains[ci]? =
      some ⟨their, some ck, mkSkippedList sk dict⟩ := by
    simp [updChain, List.getElem?_set_self hci_lt]
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
  simp [Mut.exec_bind, Mut.exec_get, hfind_upd, hget_upd, Mut.exec_liftE_ok, Mut.exec_pure]

theorem exec_consumeMessageKey_rejects (F : ShaCompress) (s : RatchetState) (ci : ℕ)
    (their : PublicKey) (counter : BitVec 32) (msgType : MessageType)
    (hfind : s.findReceiverChainIndex their = some ci)
    (hmax : s.maxForwardJumps = 25000)
    {g : GhostChain} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hsync : ChainSync g v)
    (hrej : g.rejects (counter.toNat + 1) = true) :
    let ck : LibsignalSession.ChainKey := ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩
    ∃ e s_out,
      Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType)
        (updChain s ci their (some ck) g.skipped v.skippedKeys) = (.error e, s_out) := by
  dsimp only
  set ck : LibsignalSession.ChainKey := ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩
  rcases getElem?_of_findIdx_some s.receiverChains their ci hfind with ⟨c_init, hc_init, _⟩
  have hci_lt : ci < s.receiverChains.length := (List.getElem?_eq_some_iff.1 hc_init).1
  have hfind_upd :
      (updChain s ci their (some ck) g.skipped v.skippedKeys).findReceiverChainIndex their =
        some ci :=
    findIdx_set_same_key s.receiverChains their ci hfind _ rfl
  have hget_upd :
      (updChain s ci their (some ck) g.skipped v.skippedKeys).receiverChains[ci]? =
        some ⟨their, some ck, mkSkippedList g.skipped v.skippedKeys⟩ := by
    simp [updChain, List.getElem?_set_self hci_lt]
  have hlast_eq := hsync.last_eq
  have hlast_lt := hsync.last_lt
  have hctr_lt : counter.toNat < 2 ^ 32 := counter.isLt
  by_cases hle : counter.toNat + 1 ≤ g.last
  · have hbv_lt : (counter < BitVec.ofNat 32 v.lastIndex) = true := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat]
      omega
    have hnot_mem : counter.toNat + 1 ∉ g.skipped := by
      simp [GhostChain.rejects, hle] at hrej
      exact hrej
    have hfind_mk :
        (mkSkippedList g.skipped v.skippedKeys).findIdx? (fun mk => mk.counter == counter) =
          none :=
      findIdx_mkSkippedList_none_of_not_mem
        (fun j hj => ⟨(hsync.mem_skipped j hj).1, by have := (hsync.mem_skipped j hj).2.1; omega⟩)
        hnot_mem
    unfold RatchetState.consumeMessageKey RatchetState.takeSkippedKey
    simp [ck, hbv_lt, Mut.exec_bind, Mut.exec_get, hfind_upd, hget_upd, hfind_mk,
      Mut.exec_pure, Mut.exec_throw]
  · have hgt : g.last < counter.toNat + 1 := by omega
    have hbv_lt : (counter < BitVec.ofNat 32 v.lastIndex) = false := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat]
      omega
    have hjump : (counter - BitVec.ofNat 32 v.lastIndex).toNat = counter.toNat - v.lastIndex := by
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    have hmax_upd :
        (updChain s ci their (some ck) g.skipped v.skippedKeys).maxForwardJumps = 25000 := hmax
    by_cases hj_gt : 25000 < counter.toNat - v.lastIndex
    · unfold RatchetState.consumeMessageKey
      simp [ck, hbv_lt, hjump, Mut.exec_bind, Mut.exec_get, hmax_upd, hj_gt, Mut.exec_throw]
    · have hi_ge : 2 ^ 32 ≤ counter.toNat + 1 := by
        unfold GhostChain.rejects at hrej
        rw [ite_eq_right hle, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hrej
        rcases hrej with h1 | h2
        · omega
        · exact h2
      have hpk : v.lastIndex + (counter.toNat - v.lastIndex) = counter.toNat := by omega
      rcases exec_advanceChain_skipKeys F s ci their (some ck) counter hfind
        (counter.toNat - v.lastIndex) v.lastIndex v.chainKey g.skipped v.skippedKeys
        hpk hsync.mem_skipped hsync.skippedKeys_le hsync.nodup_skipped hsync.len_skipped with
        ⟨hadv, _⟩
      rcases nextChainKey_counter_of_ge F
        (FSAEAD.skipKeys (lChainPRG F) (counter.toNat - v.lastIndex) v.chainKey v.lastIndex
          v.skippedKeys).1 counter hi_ge with ⟨e, hnext_err⟩
      unfold RatchetState.consumeMessageKey
      simp [ck, hbv_lt, hjump, Mut.exec_bind, Mut.exec_get, hmax_upd, hj_gt,
        hadv, hnext_err, Mut.exec_liftE_error]

theorem exec_consumeMessageKey_accepts (F : ShaCompress) (s : RatchetState) (ci : ℕ)
    (their : PublicKey) (counter : BitVec 32) (msgType : MessageType)
    (hfind : s.findReceiverChainIndex their = some ci)
    (hmax : s.maxForwardJumps = 25000)
    {g : GhostChain} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hsync : ChainSync g v)
    (hacc : g.rejects (counter.toNat + 1) = false) :
    let i := counter.toNat + 1
    let ck : LibsignalSession.ChainKey := ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩
    ∃ (key : BitVec 256) (v' : RatchetReceiverState (BitVec 256) (BitVec 256)),
      Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType)
        (updChain s ci their (some ck) g.skipped v.skippedKeys) =
        (.ok ⟨keyToBytes32 key, counter⟩,
          updChain s ci their (some ⟨v'.chainKey, BitVec.ofNat 32 v'.lastIndex⟩)
            (g.accept i).skipped v'.skippedKeys) ∧
      ChainSync (g.accept i) v' ∧
      ∀ {α M E : Type} (ae : AEADScheme (BitVec 256) (ℕ × α) M E) (a : α) (e : E),
        (FSAEAD.fromAEADPRG ae (lChainPRG F) 25000).receive v a (i, e) =
          (ae.dec key (i, a) e).map (fun m => (v', i, m)) := by
  dsimp only
  set ck : LibsignalSession.ChainKey := ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩
  rcases getElem?_of_findIdx_some s.receiverChains their ci hfind with ⟨c_init, hc_init, _⟩
  have hci_lt : ci < s.receiverChains.length := (List.getElem?_eq_some_iff.1 hc_init).1
  have hfind_upd :
      (updChain s ci their (some ck) g.skipped v.skippedKeys).findReceiverChainIndex their =
        some ci :=
    findIdx_set_same_key s.receiverChains their ci hfind _ rfl
  have hget_upd :
      (updChain s ci their (some ck) g.skipped v.skippedKeys).receiverChains[ci]? =
        some ⟨their, some ck, mkSkippedList g.skipped v.skippedKeys⟩ := by
    simp [updChain, List.getElem?_set_self hci_lt]
  have hlast_eq := hsync.last_eq
  have hlast_lt := hsync.last_lt
  have hctr_lt : counter.toNat < 2 ^ 32 := counter.isLt
  by_cases hle : counter.toNat + 1 ≤ g.last
  · have hbv_lt : (counter < BitVec.ofNat 32 v.lastIndex) = true := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat]
      omega
    have hmem : counter.toNat + 1 ∈ g.skipped := by
      simp [GhostChain.rejects, hle] at hacc
      exact hacc
    rcases Option.isSome_iff_exists.1 (hsync.mem_skipped (counter.toNat + 1) hmem).2.2 with ⟨key, hlk⟩
    rcases findIdx_mkSkippedList_of_mem hsync.nodup_skipped
      (fun j hj => ⟨(hsync.mem_skipped j hj).1,
        by have := (hsync.mem_skipped j hj).2.1; omega,
        (hsync.mem_skipped j hj).2.2⟩) hmem hlk with ⟨pos, hpos_find, hpos_get, hpos_erase⟩
    set v' : RatchetReceiverState (BitVec 256) (BitVec 256) :=
      { v with skippedKeys := v.skippedKeys.filter (fun x => x.1 != counter.toNat + 1) }
    have hnot_erase : counter.toNat + 1 ∉ g.skipped.erase (counter.toNat + 1) :=
      (List.Nodup.mem_erase_iff hsync.nodup_skipped).not.2 (fun h => h.1 rfl)
    have hlt_false : ¬ g.last < counter.toNat + 1 := by omega
    have hacc_sk : (g.accept (counter.toNat + 1)).skipped = g.skipped.erase (counter.toNat + 1) := by
      simp [GhostChain.accept, hlt_false]
    have herase_eq :
        (mkSkippedList g.skipped v.skippedKeys).eraseIdx pos =
          mkSkippedList (g.accept (counter.toNat + 1)).skipped v'.skippedKeys := by
      rw [hpos_erase, hacc_sk, ← mkSkippedList_filter_of_not_mem hnot_erase]
    refine ⟨key, v', ?_, ChainSync.accept_of_le hsync hle hmem, ?_⟩
    · unfold RatchetState.consumeMessageKey RatchetState.takeSkippedKey
      simp only [ck, hbv_lt, ↓reduceIte, Mut.exec_bind, Mut.exec_get, hfind_upd, hget_upd,
        hpos_find, hpos_get, Mut.exec_set, Mut.exec_pure, herase_eq, v']
      simp [updChain, List.set_set]
    · intro α M E ae a e
      simp [FSAEAD.fromAEADPRG, hlk, v']
  · have hgt : g.last < counter.toNat + 1 := by omega
    have hbv_lt : (counter < BitVec.ofNat 32 v.lastIndex) = false := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat]
      omega
    have hjump : (counter - BitVec.ofNat 32 v.lastIndex).toNat = counter.toNat - v.lastIndex := by
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    have hmax_upd :
        (updChain s ci their (some ck) g.skipped v.skippedKeys).maxForwardJumps = 25000 := hmax
    have hacc' : ¬ 25000 < counter.toNat - v.lastIndex ∧ counter.toNat + 1 < 2 ^ 32 := by
      unfold GhostChain.rejects at hacc
      rw [ite_eq_right hle, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not] at hacc
      omega
    rcases hacc' with ⟨hj_le, hi_lt⟩
    rcases ChainSync.accept_of_gt F s ci their (some ck) counter hfind hsync hgt hi_lt with
      ⟨hadv, hsync'⟩
    set step := FSAEAD.skipKeys (lChainPRG F) (counter.toNat - v.lastIndex)
      v.chainKey v.lastIndex v.skippedKeys
    set gen := (lChainPRG F counter.toNat).gen step.1
    set v' : RatchetReceiverState (BitVec 256) (BitVec 256) := ⟨gen.1, counter.toNat + 1, step.2⟩
    have hnext : ChainKey.nextChainKey F ⟨step.1, counter⟩ =
        .ok ⟨gen.1, BitVec.ofNat 32 (counter.toNat + 1)⟩ :=
      nextChainKey_counter_of_lt F step.1 counter hi_lt
    have hset := exec_setReceiverChainKey s ci their (some ck)
      ⟨gen.1, BitVec.ofNat 32 (counter.toNat + 1)⟩ (g.accept (counter.toNat + 1)).skipped step.2 hfind
    have hmk : ChainKey.messageKeys F ⟨step.1, counter⟩ = ⟨keyToBytes32 gen.2, counter⟩ := by
      unfold ChainKey.messageKeys
      dsimp only [gen, lChainPRG]
      rw [keyToBytes32_hmacPRF_tag]
    have hlk_none : v.skippedKeys.lookup (counter.toNat + 1) = none :=
      lookup_none_of_gt hsync.skippedKeys_le (by omega)
    have hcond_false : ¬ (counter.toNat + 1 ≤ v.lastIndex ∨ 25000 < counter.toNat + 1 - v.lastIndex - 1) := by omega
    have hsub_eq : counter.toNat + 1 - v.lastIndex - 1 = counter.toNat - v.lastIndex := by omega
    have hi_sub : counter.toNat + 1 - 1 = counter.toNat := by omega
    refine ⟨gen.2, v', ?_, hsync', ?_⟩
    · unfold RatchetState.consumeMessageKey
      simp only [ck, hbv_lt, Bool.false_eq_true, ↓reduceIte, hjump, Mut.exec_bind, Mut.exec_get,
        hmax_upd, hj_le, hadv, hnext, Mut.exec_liftE_ok, hset, Mut.exec_pure, hmk, v']
    · intro α M E ae a e
      unfold FSAEAD.fromAEADPRG
      dsimp only
      rw [hlk_none, ite_eq_right hcond_false, hsub_eq, hi_sub]

theorem lHeader_eq_of_version (encT : Pt → PublicKey) (h : SignalHeader) (t : ℕ) (T? : Option Pt)
    (salt : Salt32) (hver : h.messageVersion = currentVersion)
    (hkey : (T?.map encT).getD dummyKey = h.senderRatchetKey) :
    lHeader encT (h.counter.toNat + 1) (t, T?) ⟨h.previousCounter, h.pqRatchet, salt, h.addresses⟩ = h := by
  cases h
  dsimp only [lHeader] at hver hkey ⊢
  simp [hver, hkey]

theorem lHeader_ne_of_version_ne (encT : Pt → PublicKey) (h : SignalHeader) (i : ℕ)
    (ad : Header Pt) (pub : LibsignalMsgPublicPart) (hver : h.messageVersion ≠ currentVersion) :
    h ≠ lHeader encT i ad pub := by
  intro heq
  exact hver (congrArg SignalHeader.messageVersion heq)

theorem version_toNat_ne_iff (v : BitVec 8) :
    (BitVec.ofNat 32 currentVersion.toNat : BitVec 32).toNat ≠ v.toNat ↔ v ≠ currentVersion := by
  have hc : (BitVec.ofNat 32 currentVersion.toNat : BitVec 32).toNat = currentVersion.toNat := by
    decide
  rw [hc]
  constructor
  · intro h heq; exact h (congrArg BitVec.toNat heq).symm
  · intro h heq; exact h (BitVec.eq_of_toNat_eq heq.symm)

theorem lAead_pubMsg_dec_of_version_ne (P : Params PQ PQC) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey)
    (w : List (BitVec 8)) (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hver : h.messageVersion ≠ currentVersion)
    (key : BitVec 256) (i : ℕ) (ad : Header Pt) (salt : Salt32) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, ad) ((ser, tag), salt) = none := by
  dsimp only
  have hne := lHeader_ne_of_version_ne encT h i ad
    ⟨h.previousCounter, h.pqRatchet, salt, h.addresses⟩ hver
  unfold AEADScheme.movePubPartToAD lPubOf lAead lAeadK lWire libsignalWireAead libsignalReceiveWire
  simp only [hparse, Option.map_some, ne_eq, not_true_eq_false, ↓reduceIte]
  by_cases hmac :
      ((hmacScheme P.C.F).tag (deriveMessageKeys P.C.F (some salt) (keyToBytes32 key)).2
        ((lIds idOf ad.1).toList ++ w.take (w.length - 8)) ==
          bytesToWord64LE (w.drop (w.length - 8))) = true
  · simp only [hmac, ↓reduceIte]
    cases cbcDecRaw P.C.D (deriveMessageKeys P.C.F (some salt) (keyToBytes32 key)).1.1
        (deriveMessageKeys P.C.F (some salt) (keyToBytes32 key)).1.2 body with
    | none => rfl
    | some m => simp [addressCheckPasses, hne]
  · simp [hmac]

theorem lAead_pubMsg_dec_eq (P : Params PQ PQC) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (Q : Party) (t : ℕ) (T? : Option Pt) (hrecv : Q.sendsIn t = false)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hver : h.messageVersion = currentVersion)
    (hkey : (T?.map encT).getD dummyKey = h.senderRatchetKey)
    (key : BitVec 256) (salt : Salt) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let pub : LibsignalMsgPublicPart := ⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 salt, h.addresses⟩
    let msg : SignalMessage :=
      ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩
    let mk := (MessageKeyGenerator.mk (keyToBytes32 key) h.counter).generateKeys P.C.F salt
    let macOk := SignalMessage.verifyMac P.C.F msg (idOfP P Q.other) (idOfP P Q) mk.macKey
    ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, (t, T?)) ((ser, tag), effectiveHkdfSalt32 salt) =
      if macOk = true then
        (aesCbcDecrypt P.C.D mk.cipherKey mk.iv body).map (fun m_raw => (pub, padOrTruncatePlain ℓ m_raw))
      else
        none := by
  dsimp only
  set ser := w.take (w.length - 8)
  set tag := bytesToWord64LE (w.drop (w.length - 8))
  set pub : LibsignalMsgPublicPart := ⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 salt, h.addresses⟩
  set mk := (MessageKeyGenerator.mk (keyToBytes32 key) h.counter).generateKeys P.C.F salt
  have hdrop_len : (w.drop (w.length - 8)).length = 8 := by
    simp [List.length_drop]; omega
  have hlids : lIds idOf t = macIds (idOfP P Q.other) (idOfP P Q) :=
    lIds_eq_macIds_of_not_sendsIn P idOf hid Q t hrecv
  have hmac_len : macLength = 8 := rfl
  have hmac_eq :
      ((hmacScheme P.C.F).tag mk.macKey ((lIds idOf t).toList ++ ser) == tag) =
        SignalMessage.verifyMac P.C.F
          ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
            h.pqRatchet, h.addresses, w⟩
          (idOfP P Q.other) (idOfP P Q) mk.macKey := by
    unfold SignalMessage.verifyMac
    dsimp only
    rw [hmac_len, hlids]
    exact (computeMac_beq_eq_hmacScheme_beq P.C.F (idOfP P Q.other) (idOfP P Q)
      mk.macKey ser (w.drop (w.length - 8)) hdrop_len).symm
  have hhdr : lHeader encT (h.counter.toNat + 1) (t, T?) pub = h :=
    lHeader_eq_of_version encT h t T? (effectiveHkdfSalt32 salt) hver hkey
  have had_ok : addressCheckPasses none none = true := rfl
  have hmk_mac : (deriveMessageKeys P.C.F (some (effectiveHkdfSalt32 salt)) (keyToBytes32 key)).2 = mk.macKey := by
    rw [← msgKeys_effSalt]; rfl
  have hmk_cip : (deriveMessageKeys P.C.F (some (effectiveHkdfSalt32 salt)) (keyToBytes32 key)).1.1 = mk.cipherKey := by
    rw [← msgKeys_effSalt]; rfl
  have hmk_iv : (deriveMessageKeys P.C.F (some (effectiveHkdfSalt32 salt)) (keyToBytes32 key)).1.2 = mk.iv := by
    rw [← msgKeys_effSalt]; rfl
  unfold AEADScheme.movePubPartToAD lPubOf lAead lAeadK lWire libsignalWireAead libsignalReceiveWire aesCbcDecrypt
  simp only [ser, tag, pub, hparse, Option.map_some, ne_eq, not_true_eq_false, ↓reduceIte,
    hmk_mac, hmk_cip, hmk_iv, hmac_eq, had_ok]
  by_cases hmac :
      SignalMessage.verifyMac P.C.F
        ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
          h.pqRatchet, h.addresses, w⟩
        (idOfP P Q.other) (idOfP P Q) mk.macKey = true
  · simp only [hmac, ↓reduceIte]
    cases cbcDecRaw P.C.D mk.cipherKey mk.iv body with
    | none => rfl
    | some m_raw =>
      dsimp only
      rw [ite_eq_left hhdr.symm]
      rfl
  · simp [hmac]

theorem pendingPreKey_after_accept (Q : Party) (unackA : Bool) :
    (Q == Party.A && (unackA && Q != Party.A)) = false := by
  cases Q <;> simp

theorem getElem?_of_findIdx_ghost (cs : List GhostChain) (their : PublicKey) (ci : ℕ)
    (hfind : cs.findIdx? (fun g => g.key == some their) = some ci) :
    ∃ g, cs[ci]? = some g ∧ g.key = some their := by
  induction cs generalizing ci with
  | nil => simp [List.findIdx?_nil] at hfind
  | cons g cs ih =>
    cases ci with
    | zero =>
      simp only [List.findIdx?_cons] at hfind
      cases hgk : g.key == some their with
      | true => exact ⟨g, rfl, beq_iff_eq.1 hgk⟩
      | false => simp [hgk] at hfind
    | succ k =>
      simp only [List.findIdx?_cons] at hfind
      cases hgk : g.key == some their with
      | true => simp [hgk] at hfind
      | false =>
        simp only [hgk, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hfind
        rcases hfind with ⟨k', hk', hsucc⟩
        injection hsucc with hk_eq
        subst hk_eq
        simpa using ih k' hk'

theorem findIdx_toRecvChain_gen (st : Fig8St Pt) (cs : List GhostChain) (their : PublicKey)
    (h : ∀ g ∈ cs, g.key = none → their ≠ dummyKey) :
    (cs.map (toRecvChain st)).findIdx? (fun c => c.senderRatchetKey == their) =
      cs.findIdx? (fun g => g.key == some their) := by
  induction cs with
  | nil => rfl
  | cons g cs ih =>
    have hg : ((toRecvChain st g).senderRatchetKey == their) = (g.key == some their) := by
      rw [toRecvChain_senderRatchetKey]
      cases hgk : g.key with
      | none =>
        have hne := h g (List.mem_cons_self ..) hgk
        simp [Option.getD, beq_eq_false_iff_ne.2 hne.symm]
      | some k => simp [Option.getD]
    simp only [List.map, List.findIdx?_cons, hg, ih (fun x hx => h x (List.mem_cons_of_mem g hx))]

@[local simp]
theorem accept_epoch (g : GhostChain) (i : ℕ) : (g.accept i).epoch = g.epoch := by
  unfold GhostChain.accept
  split <;> rfl

@[local simp]
theorem accept_key (g : GhostChain) (i : ℕ) : (g.accept i).key = g.key := by
  unfold GhostChain.accept
  split <;> rfl

theorem map_epoch_set_accept (cs : List GhostChain) (ci : ℕ) (g : GhostChain) (i : ℕ)
    (hget : cs[ci]? = some g) :
    ((cs.set ci (g.accept i)).map (·.epoch)) = cs.map (·.epoch) := by
  rw [List.map_set, accept_epoch]
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    by_cases hj : ci = j
    · subst hj
      rw [List.getElem_set_self, List.getElem_map]
      have hci : ci < cs.length := by simp at hj₂; exact hj₂
      have heq : cs[ci] = g := Option.some.inj ((List.getElem?_eq_getElem hci).symm.trans hget)
      rw [heq]
    · rw [List.getElem_set_ne hj]

theorem tryDecryptFromRecord_of_stepChain_error (P : Params PQ PQC) (Q : Party)
    (msg : SignalMessage) (rc : BitVec 256) (rec : SessionState PQ)
    (hrec_rem : rec.remoteIdentity = some (idOfP P Q.other))
    (e : SignalProtocolError) (r_out : RatchetState)
    (hstep : Mut.exec
      (do
        let ck ← RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc
        RatchetState.consumeMessageKey P.C.F msg.senderRatchetKey ck msg.counter .whisper)
      { rootKey := rec.rootKey, senderChain := rec.senderChain,
        receiverChains := rec.receiverChains, previousCounter := rec.previousCounter,
        maxForwardJumps := 25000 } =
      (.error e, r_out)) :
    ∃ e', SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs Q)
      msg .whisper rc rec = (.error e', rec) := by
  unfold SessionState.tryDecryptFromRecord
  by_cases hver : rec.version.toNat ≠ msg.messageVersion.toNat
  · rw [ite_eq_left hver]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hver]
    have hmax : maxForwardJumps = 25000 := rfl
    unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
      SessionState.takeRatchetState SessionState.takePqRatchetState
      TripleRatchet.decrypt TripleRatchet.onRatchet zoom
    cases h_ens : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
        { rootKey := rec.rootKey, senderChain := rec.senderChain,
          receiverChains := rec.receiverChains, previousCounter := rec.previousCounter,
          maxForwardJumps := 25000 } with
    | mk r_ens s_ens =>
      rw [Mut.exec_bind, h_ens] at hstep
      cases r_ens with
      | error e_ens =>
        simp [Mut.exec_bind, Mut.exec_modifyGet, Mut.exec_get, Mut.exec_set,
          hrec_rem, Mut.exec_pure, hmax, h_ens, Mut.exec_liftE_error]
      | ok ck =>
        dsimp only at hstep
        simp [Mut.exec_bind, Mut.exec_modifyGet, Mut.exec_get, Mut.exec_set,
          hrec_rem, Mut.exec_pure, hmax, h_ens, hstep, Mut.exec_liftE_ok, Mut.exec_liftE_error]

@[local simp]
theorem Mut_exec_map {σ α β : Type} (f : α → β) (m : Mut σ α) (s : σ) :
    Mut.exec (f <$> m) s =
      match Mut.exec m s with
      | (.ok a, s') => (.ok (f a), s')
      | (.error e, s') => (.error e, s') := by
  change Mut.exec (m >>= fun a => pure (f a)) s = _
  rw [Mut.exec_bind]
  cases Mut.exec m s with
  | mk r s' => cases r <;> rfl

theorem tryDecryptFromRecord_of_stepChain_ok (P : Params PQ PQC) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (Q : Party) (t : ℕ) (T? : Option Pt) (hrecv : Q.sendsIn t = false)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (hkey : (T?.map encT).getD dummyKey = h.senderRatchetKey)
    (rec : SessionState PQ)
    (hrec_ver : rec.sessionVersion = BitVec.ofNat 32 currentVersion.toNat)
    (hrec_loc : rec.localIdentity = idOfP P Q)
    (hrec_rem : rec.remoteIdentity = some (idOfP P Q.other))
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv rec.pqRatchetState h.pqRatchet = .ok (pq', salt))
    (hnpR : P.spqr.recvPanics rec.pqRatchetState h.pqRatchet = false)
    (rc : BitVec 256) (key : BitVec 256) (r_out : RatchetState)
    (hstep : Mut.exec
      (do
        let ck ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
        RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck h.counter .whisper)
      { rootKey := rec.rootKey, senderChain := rec.senderChain,
        receiverChains := rec.receiverChains, previousCounter := rec.previousCounter,
        maxForwardJumps := 25000 } =
      (.ok ⟨keyToBytes32 key, h.counter⟩, r_out)) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let msg : SignalMessage :=
      ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩
    match ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, (t, T?)) ((ser, tag), effectiveHkdfSalt32 salt) with
    | none =>
      ∃ e', SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs Q)
        msg .whisper rc rec = (.error e', rec)
    | some (pub, m) =>
      pub = ⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 salt, h.addresses⟩ ∧
      ∃ m_raw : List (BitVec 8),
        m = padOrTruncatePlain ℓ m_raw ∧
        SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs Q)
          msg .whisper rc rec =
          (.ok m_raw,
            { sessionVersion := rec.sessionVersion,
              localIdentity := rec.localIdentity,
              remoteIdentity := rec.remoteIdentity,
              rootKey := r_out.rootKey,
              previousCounter := r_out.previousCounter,
              senderChain := r_out.senderChain,
              receiverChains := r_out.receiverChains,
              pendingPreKey := false,
              pqRatchetState := pq' }) := by
  dsimp only
  set ser := w.take (w.length - 8)
  set tag := bytesToWord64LE (w.drop (w.length - 8))
  set i := h.counter.toNat + 1
  set msg : SignalMessage :=
    ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
      h.pqRatchet, h.addresses, w⟩
  have hver_rec : rec.version = BitVec.ofNat 32 currentVersion.toNat := by
    unfold SessionState.version
    rw [hrec_ver]
    have hne0 : ¬ (BitVec.ofNat 32 currentVersion.toNat : BitVec 32) = 0 := by decide
    rw [ite_eq_right hne0]
  by_cases hver : h.messageVersion = currentVersion
  · have hver_not : ¬ rec.version.toNat ≠ msg.messageVersion.toNat := by
      rw [hver_rec]
      exact (version_toNat_ne_iff h.messageVersion).not.2 (not_not.2 hver)
    have hdec := lAead_pubMsg_dec_eq (ℓ := ℓ) P encT idOf hid Q t T? hrecv w hw_len h body hparse hver hkey key salt
    dsimp only at hdec
    rw [hdec]
    set mk := (MessageKeyGenerator.mk (keyToBytes32 key) h.counter).generateKeys P.C.F salt
    set macOk := SignalMessage.verifyMac P.C.F msg (idOfP P Q.other) (idOfP P Q) mk.macKey
    have hmax : maxForwardJumps = 25000 := rfl
    have hmac_addrs :
        SignalMessage.verifyMacWithAddresses P.C.F msg (P.expectedAddrs Q)
          (idOfP P Q.other) rec.localIdentity mk.macKey = macOk := by
      unfold SignalMessage.verifyMacWithAddresses
      rw [hrec_loc]
      change (macOk && addressCheckPasses h.addresses (P.expectedAddrs Q)) = macOk
      rw [haddrs, Bool.and_true]
    unfold SessionState.tryDecryptFromRecord
    rw [ite_eq_right hver_not]
    unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
      SessionState.takeRatchetState SessionState.takePqRatchetState
      TripleRatchet.decrypt TripleRatchet.onRatchet zoom
    cases h_ens : Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc)
        { rootKey := rec.rootKey, senderChain := rec.senderChain,
          receiverChains := rec.receiverChains, previousCounter := rec.previousCounter,
          maxForwardJumps := 25000 } with
    | mk r_ens s_ens =>
      rw [Mut.exec_bind, h_ens] at hstep
      cases r_ens with
      | error e_ens => cases hstep
      | ok ck =>
        dsimp only at hstep
        dsimp only [msg, mk] at hmac_addrs
        simp only [msg, Mut.exec_bind, Mut.exec_modifyGet, Mut.exec_get, Mut.exec_set,
          Mut.exec_liftE_ok, hrec_rem, Mut.exec_pure, hmax, h_ens, hstep, hnpR, Bool.false_eq_true,
          ↓reduceIte, hspqr, hmac_addrs]
        by_cases hmac : macOk = true
        · simp only [hmac, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hcbc : aesCbcDecrypt P.C.D mk.cipherKey mk.iv body with
          | none =>
            dsimp only [mk] at hcbc
            simp [hcbc, Mut.exec_throw, Mut.exec_liftE_error]
          | some m_raw =>
            dsimp only [mk] at hcbc
            simp [hcbc, Mut.exec_modify, Mut.exec_pure, Mut.exec_liftE_ok,
              TripleRatchet.applyToSessionState, SessionState.clearUnacknowledgedPreKeyMessage,
              hrec_rem]
        · have hmac_f : macOk = false := Bool.eq_false_iff.2 hmac
          simp [hmac_f, Mut.exec_throw, Mut.exec_liftE_error]
  · have hver_ne : rec.version.toNat ≠ msg.messageVersion.toNat := by
      rw [hver_rec]
      exact (version_toNat_ne_iff h.messageVersion).2 hver
    have hdec := lAead_pubMsg_dec_of_version_ne (ℓ := ℓ) P encT idOf w h body hparse hver key i (t, T?)
      (effectiveHkdfSalt32 salt)
    dsimp only at hdec
    rw [hdec]
    unfold SessionState.tryDecryptFromRecord
    rw [ite_eq_left hver_ne]
    exact ⟨_, rfl⟩

/-- Single-step receive correspondence on a known receiver chain. -/
theorem receive_knownChain_withEager_toGhost_eq (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (hst_id : st.id = Q)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hnpR : P.spqr.recvPanics (s.pq Q) h.pqRatchet = false)
    (ci : ℕ)
    (hfind_g : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = some ci)
    (hdummy : ∀ g ∈ s.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey)
    (g : GhostChain) (hg_get : (s.chains Q)[ci]? = some g)
    (hg_ep : g.epoch ≤ st.tcur) (hrecv : Q.sendsIn g.epoch = false)
    (v : RatchetReceiverState (BitVec 256) (BitVec 256)) (hvR : st.vR g.epoch = some v)
    (hsync : ChainSync g v)
    (T? : Option Pt) (hT : (T?.map encT).getD dummyKey = h.senderRatchetKey)
    (hdistinct : ∀ j < (s.chains Q).length, j ≠ ci →
      ∀ g_j, (s.chains Q)[j]? = some g_j → g_j.epoch ≠ g.epoch)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hmir' : mir'.epoch Q = s.mir.epoch Q)
    (rk : LibsignalSession.RootKey) (sc : Option SenderChain) (pn : BitVec 32)
    (rc : BitVec 256) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let c : Fig8C Pt := ((g.epoch, T?), i, (ser, tag), effectiveHkdfSalt32 salt)
    let g_in := withEager (toGhost P s Q st) rk sc pn
    (g.rejects i = true → P.receive g_in w rc = none) ∧
    (g.rejects i = false →
      match (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c with
      | none => P.receive g_in w rc = none
      | some (st', t', i', (pub, m)) =>
        t' = g.epoch ∧ i' = i ∧
        pub = ⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 salt, h.addresses⟩ ∧
        (∃ v', st' = { st with vR := Function.update st.vR g.epoch (some v') } ∧
          ChainSync (g.accept i) v') ∧
        ∃ m_raw : List (BitVec 8),
          m = padOrTruncatePlain ℓ m_raw ∧
          let s' : SimState PQ Pt ℓ :=
            { s with
              mir := mir',
              pq := Function.update s.pq Q pq',
              unackA := s.unackA && Q != Party.A,
              chains := Function.update s.chains Q ((s.chains Q).set ci (g.accept i)) }
          P.receive g_in w rc =
            some (withEager (toGhost P s' Q st') rk sc pn, g.epoch, i, m_raw)) := by
  dsimp only
  set ser := w.take (w.length - 8)
  set tag := bytesToWord64LE (w.drop (w.length - 8))
  set i := h.counter.toNat + 1
  set c : Fig8C Pt := ((g.epoch, T?), i, (ser, tag), effectiveHkdfSalt32 salt)
  set g_in := withEager (toGhost P s Q st) rk sc pn
  have htry : SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ :=
    tryFrom_of_parse P.codec w h body hw_len hparse
  rcases getElem?_of_findIdx_ghost (s.chains Q) h.senderRatchetKey ci hfind_g with
    ⟨g₀, hg₀_get, hg₀_key⟩
  have hg_eq : g₀ = g := Option.some.inj (hg₀_get.symm.trans hg_get)
  subst hg_eq
  have hci_lt : ci < (s.chains Q).length := (List.getElem?_eq_some_iff.1 hg₀_get).1
  set ck : LibsignalSession.ChainKey := ⟨v.chainKey, BitVec.ofNat 32 v.lastIndex⟩
  set r_in : RatchetState :=
    { rootKey := rk, senderChain := sc,
      receiverChains := (s.chains Q).map (toRecvChain st),
      previousCounter := pn, maxForwardJumps := 25000 }
  have hfind_r : r_in.findReceiverChainIndex h.senderRatchetKey = some ci := by
    unfold RatchetState.findReceiverChainIndex
    dsimp only [r_in]
    rw [findIdx_toRecvChain_gen st (s.chains Q) h.senderRatchetKey hdummy]
    exact hfind_g
  have hget_r : r_in.receiverChains[ci]? =
      some ⟨h.senderRatchetKey, some ck, mkSkippedList g₀.skipped v.skippedKeys⟩ := by
    dsimp only [r_in]
    rw [List.getElem?_map, hg₀_get, Option.map_some, toRecvChain_of_some st g₀ v hvR, hg₀_key]
    rfl
  have hupd_self : updChain r_in ci h.senderRatchetKey (some ck) g₀.skipped v.skippedKeys = r_in :=
    updChain_eq_self r_in ci h.senderRatchetKey (some ck) g₀.skipped v.skippedKeys hget_r
  have hens : Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc) r_in =
      (.ok ck, r_in) := by
    rw [← hupd_self]
    exact exec_ensureReceiverChain_known P.C r_in ci h.senderRatchetKey ck rc g₀.skipped v.skippedKeys hfind_r
  have hrec_ver : g_in.session.sessionVersion = BitVec.ofNat 32 currentVersion.toNat := rfl
  have hrec_loc : g_in.session.localIdentity = idOfP P Q := rfl
  have hrec_rem : g_in.session.remoteIdentity = some (idOfP P Q.other) := by
    simp [g_in, withEager, toGhost, idOfP]
  have hrec_pq : g_in.session.pqRatchetState = s.pq Q := rfl
  constructor
  · intro hrej
    rcases exec_consumeMessageKey_rejects P.C.F r_in ci h.senderRatchetKey h.counter .whisper
      hfind_r rfl hsync hrej with ⟨e, r_out, hcons⟩
    rw [hupd_self] at hcons
    have hstep : Mut.exec
        (do
          let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
          RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
        r_in = (.error e, r_out) := by
      rw [Mut.exec_bind, hens]
      exact hcons
    rcases tryDecryptFromRecord_of_stepChain_error P Q
      ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩
      rc g_in.session hrec_rem e r_out hstep with ⟨e', hdec_err⟩
    unfold Params.receive
    have hparty : g_in.party = Q := rfl
    rw [htry, hparty]
    dsimp only
    rw [hdec_err]
  · intro hacc
    rcases exec_consumeMessageKey_accepts P.C.F r_in ci h.senderRatchetKey h.counter .whisper
      hfind_r rfl hsync hacc with ⟨key, v', hcons, hsync', hfs⟩
    rw [hupd_self] at hcons
    set r_out := updChain r_in ci h.senderRatchetKey
      (some ⟨v'.chainKey, BitVec.ofNat 32 v'.lastIndex⟩) (g₀.accept i).skipped v'.skippedKeys
    have hstep : Mut.exec
        (do
          let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
          RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
        r_in = (.ok ⟨keyToBytes32 key, h.counter⟩, r_out) := by
      rw [Mut.exec_bind, hens]
      exact hcons
    have hfig8 : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c =
        (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          key (i, (g₀.epoch, T?)) ((ser, tag), effectiveHkdfSalt32 salt)).map
          (fun pm => ({ st with vR := Function.update st.vR g₀.epoch (some v') }, g₀.epoch, i, pm)) := by
      unfold lFig8 SM.Construction.scheme SM.Construction.receive lFS
      dsimp only [c]
      have hcond1 : (st.id.sendsIn g₀.epoch || decide (st.tcur + 1 < g₀.epoch)) = false := by
        rw [hst_id, hrecv]
        simp; omega
      have hcond2 : ¬ g₀.epoch = st.tcur + 1 := by omega
      simp only [hcond1, Bool.false_eq_true, ↓reduceIte, hcond2]
      rw [hvR]
      dsimp only
      rw [hfs ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)) (g₀.epoch, T?) ((ser, tag), effectiveHkdfSalt32 salt)]
      cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, (g₀.epoch, T?)) ((ser, tag), effectiveHkdfSalt32 salt) <;> rfl
    have htry_ok := tryDecryptFromRecord_of_stepChain_ok (ℓ := ℓ) P encT idOf hid Q g₀.epoch T?
      hrecv w hw_len h body hparse haddrs hT g_in.session hrec_ver hrec_loc hrec_rem pq' salt
      (by rw [hrec_pq]; exact hspqr) (by rw [hrec_pq]; exact hnpR) rc key r_out hstep
    dsimp only at htry_ok
    rw [hfig8]
    cases hdec : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, (g₀.epoch, T?)) ((ser, tag), effectiveHkdfSalt32 salt) with
    | none =>
      rw [hdec] at htry_ok
      rcases htry_ok with ⟨e', hdec_err⟩
      unfold Params.receive
      have hparty : g_in.party = Q := rfl
      rw [htry, hparty]
      dsimp only
      rw [hdec_err]
      rfl
    | some pm =>
      rcases pm with ⟨pub, m⟩
      rw [hdec] at htry_ok
      rcases htry_ok with ⟨hpub, m_raw, hm_eq, hdec_ok⟩
      dsimp only [Option.map]
      refine ⟨rfl, rfl, hpub, ⟨v', rfl, hsync'⟩, m_raw, hm_eq, ?_⟩
      unfold Params.receive
      have hparty : g_in.party = Q := rfl
      rw [htry, hparty]
      dsimp only
      rw [hdec_ok]
      dsimp only
      set st' : Fig8St Pt := { st with vR := Function.update st.vR g₀.epoch (some v') }
      have hfind_in :
          g_in.session.receiverChains.findIdx? (fun x => x.senderRatchetKey == h.senderRatchetKey) =
            some ci := hfind_r
      have hgetD_ep : g_in.chainEpochs.getD ci 0 = g₀.epoch := by
        change ((s.chains Q).map (·.epoch))[ci]?.getD 0 = g₀.epoch
        rw [List.getElem?_map, hg₀_get, Option.map_some, Option.getD_some]
      have hlen_drop :
          List.drop (g_in.chainEpochs.length - r_out.receiverChains.length) g_in.chainEpochs =
            ((s.chains Q).set ci (g₀.accept i)).map (·.epoch) := by
        have hlen_eq : g_in.chainEpochs.length - r_out.receiverChains.length = 0 := by
          simp [g_in, withEager, toGhost, r_out, updChain, r_in]
        rw [hlen_eq, List.drop_zero]
        exact (map_epoch_set_accept (s.chains Q) ci g₀ i hg₀_get).symm
      have hrc_eq :
          r_out.receiverChains =
            ((s.chains Q).set ci (g₀.accept i)).map (toRecvChain st') := by
        have hacc_chain :
            toRecvChain st' (g₀.accept i) =
              ⟨h.senderRatchetKey, some ⟨v'.chainKey, BitVec.ofNat 32 v'.lastIndex⟩,
                mkSkippedList (g₀.accept i).skipped v'.skippedKeys⟩ := by
          have hvR' : st'.vR (g₀.accept i).epoch = some v' := by
            simp [st', accept_epoch, Function.update_self]
          rw [toRecvChain_of_some st' (g₀.accept i) v' hvR', accept_key, hg₀_key, Option.getD_some]
        dsimp only [r_out, updChain, r_in]
        rw [← hacc_chain]
        symm
        apply map_set_eq_of_getElem?_ne (s.chains Q) ci (g₀.accept i) (toRecvChain st') (toRecvChain st)
        intro j hj_lt hj_ne g_j hg_j
        have hne_ep : g_j.epoch ≠ g₀.epoch := hdistinct j hj_lt hj_ne g_j hg_j
        unfold toRecvChain
        simp [st', Function.update_of_ne hne_ep]
      rw [hfind_in]
      dsimp only
      rw [hgetD_ep, hlen_drop, hrc_eq]
      simp [g_in, withEager, toGhost, toRecvChain, mkSkippedList, i, r_out, updChain, r_in, hmir',
        Function.update_self, pendingPreKey_after_accept]
      rfl

/-! ## New-chain receive correspondence -/

theorem evictReceiverChains_append_singleton (cs : List ReceiverChain) (c : ReceiverChain) :
    RatchetState.evictReceiverChains (cs ++ [c]) =
      List.drop ((cs.length + 1) - 5) cs ++ [c] := by
  unfold RatchetState.evictReceiverChains
  have hmax : maxReceiverChains = 5 := rfl
  rw [hmax, List.length_append, List.length_singleton]
  exact List.drop_append_of_le_length (by omega)

theorem pushChain_eq_drop_append (cs : List GhostChain) (g : GhostChain) :
    pushChain cs g = List.drop ((cs.length + 1) - 5) cs ++ [g] := by
  unfold pushChain
  dsimp only
  rw [List.length_append, List.length_singleton]
  exact List.drop_append_of_le_length (by omega)

theorem findIdx_drop_none_of_none {α : Type} (l : List α) (p : α → Bool) (k : ℕ)
    (hnone : l.findIdx? p = none) :
    (l.drop k).findIdx? p = none := by
  rw [List.findIdx?_eq_none_iff] at hnone ⊢
  intro x hx
  exact hnone x (List.mem_of_mem_drop hx)

theorem findIdx_append_singleton_of_none {α : Type} (l : List α) (x : α) (p : α → Bool)
    (hnone : l.findIdx? p = none) (hx : p x = true) :
    (l ++ [x]).findIdx? p = some l.length := by
  induction l with
  | nil => simp [List.findIdx?_cons, hx]
  | cons a as ih =>
    simp only [List.findIdx?_cons] at hnone
    cases ha : p a with
    | true => simp [ha] at hnone
    | false =>
      simp only [ha, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at hnone
      simp [List.findIdx?_cons, ha, ih hnone]

theorem set_append_singleton_length {α : Type} (l : List α) (x x' : α) :
    (l ++ [x]).set l.length x' = l ++ [x'] := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.set, ih]

theorem drop_chainEpochs_new (cs : List GhostChain) (g_new : GhostChain)
    (rcs_len : ℕ)
    (hlen : rcs_len = (List.drop ((cs.length + 1) - 5) cs).length + 1) :
    List.drop ((cs.map (·.epoch) ++ [g_new.epoch]).length - rcs_len)
      (cs.map (·.epoch) ++ [g_new.epoch]) =
    (pushChain cs g_new).map (·.epoch) := by
  rw [pushChain_eq_drop_append, List.map_append, List.map_singleton, List.map_drop]
  have h1 : (cs.map (·.epoch) ++ [g_new.epoch]).length - rcs_len = (cs.length + 1) - 5 := by
    rw [hlen, List.length_append, List.length_map, List.length_singleton, List.length_drop]
    omega
  rw [h1]
  exact List.drop_append_of_le_length (by rw [List.length_map]; omega)

theorem exec_dhRatchetStep_honest (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (rk : Ratchet.RootKey) (x_prev : BitVec 256) (ck_prev : BitVec 256) (idx_prev : BitVec 32)
    (rcs : List ReceiverChain) (pn : BitVec 32)
    (their : PublicKey) (T : Pt) (hT_ne0 : T ≠ 0) (hencT : encT T = their)
    (rc : BitVec 256) :
    let p₁ := (rootPRNG P.C.F encPt).up rk (Dh.dh x_prev T)
    let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
    let pn_new := if idx_prev = 0 then 0 else idx_prev - 1
    Mut.exec (RatchetState.dhRatchetStep P.C their rc)
      { rootKey := rk,
        senderChain := some ⟨KeyPair.generate P.C x_prev, ⟨ck_prev, idx_prev⟩⟩,
        receiverChains := rcs,
        previousCounter := pn,
        maxForwardJumps := 25000 } =
      (.ok ⟨p₁.2, 0⟩,
        { rootKey := p₂.1,
          senderChain := some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩,
          receiverChains := RatchetState.evictReceiverChains
            (rcs ++ [⟨their, some ⟨p₁.2, 0⟩, []⟩]),
          previousCounter := pn_new,
          maxForwardJumps := 25000 }) := by
  dsimp only
  have hM := libX25519Rel_model hX
  have hpub : their.bytes.toList = encPt T := by
    rw [← hencT]
    exact encT_bytes_toList hX T
  have hrc1 := rootCreateChain_generate_honest P.C hM rk x_prev hT_ne0 hpub
  have hrc2 := rootCreateChain_generate_honest P.C hM
    ((rootPRNG P.C.F encPt).up rk (Dh.dh x_prev T)).1 rc hT_ne0 hpub
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey
  simp [Mut.exec_bind, Mut.exec_get, Mut.exec_modifyGet, Mut.exec_modify, Mut.exec_pure,
    hrc1, hrc2, Mut.exec_liftE_ok]

theorem exec_ensureReceiverChain_new (C : Crypto) (s : RatchetState)
    (their : PublicKey) (rc : BitVec 256)
    (hfind : s.findReceiverChainIndex their = none) :
    Mut.exec (RatchetState.ensureReceiverChain C their rc) s =
      Mut.exec (RatchetState.dhRatchetStep C their rc) s := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
  simp [Mut.exec_bind, Mut.exec_get, hfind, Mut.exec_liftE_ok]

/-- Single-step receive correspondence on a new receiver chain, matching `dhRatchetStep` and FIFO
chain eviction. -/
theorem receive_newChain_toGhost_eq (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (hst_id : st.id = Q) (hmir_ep : s.mir.epoch Q = st.tcur)
    (hrecv : Q.sendsIn (st.tcur + 1) = false)
    (x_prev : BitVec 256) (hγ : st.γ = .exp x_prev)
    (v_prev : RatchetSenderState (BitVec 256)) (hvS : st.vS = some v_prev)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hnpR : P.spqr.recvPanics (s.pq Q) h.pqRatchet = false)
    (hfind_none : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hdummy : ∀ g ∈ s.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey)
    (hchains_ep : ∀ g ∈ s.chains Q, g.epoch ≠ st.tcur + 1)
    (T : Pt) (hT_ne0 : T ≠ 0) (hencT : encT T = h.senderRatchetKey)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (hmir' : mir'.epoch Q = st.tcur + 1)
    (rc : BitVec 256) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let t := st.tcur + 1
    let c : Fig8C Pt := ((t, some T), i, (ser, tag), effectiveHkdfSalt32 salt)
    let g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
    let p₁ := (rootPRNG P.C.F encPt).up st.root (Dh.dh x_prev T)
    let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
    let pn_new : BitVec 32 :=
      if BitVec.ofNat 32 v_prev.lastIndex = 0 then 0 else BitVec.ofNat 32 v_prev.lastIndex - 1
    (g_init.rejects i = true → P.receive (toGhost P s Q st) w rc = none) ∧
    (g_init.rejects i = false →
      match (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c with
      | none => P.receive (toGhost P s Q st) w rc = none
      | some (st', t', i', (pub, m)) =>
        t' = t ∧ i' = i ∧
        pub = ⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 salt, h.addresses⟩ ∧
        (∃ v', st' = { st with root := p₁.1, vR := Function.update st.vR t (some v'),
                               γ := .pub T, tcur := t } ∧
          ChainSync (g_init.accept i) v') ∧
        ∃ m_raw : List (BitVec 8),
          m = padOrTruncatePlain ℓ m_raw ∧
          let s' : SimState PQ Pt ℓ :=
            { s with
              mir := mir',
              pq := Function.update s.pq Q pq',
              unackA := s.unackA && Q != Party.A,
              chains := Function.update s.chains Q (pushChain (s.chains Q) (g_init.accept i)) }
          P.receive (toGhost P s Q st) w rc =
            some (withEager (toGhost P s' Q st') p₂.1
              (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new, t, i, m_raw) ∧
          P.receive (toGhost P s Q st) w rc =
            some (toGhost P { s' with pn := Function.update s'.pn Q pn_new } Q
              (fig8StepS Dh encPt P.C st' rc), t, i, m_raw)) := by
  dsimp only
  set ser := w.take (w.length - 8)
  set tag := bytesToWord64LE (w.drop (w.length - 8))
  set i := h.counter.toNat + 1
  set t := st.tcur + 1
  set c : Fig8C Pt := ((t, some T), i, (ser, tag), effectiveHkdfSalt32 salt)
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  set p₁ := (rootPRNG P.C.F encPt).up st.root (Dh.dh x_prev T)
  set p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
  set pn_new : BitVec 32 :=
    if BitVec.ofNat 32 v_prev.lastIndex = 0 then 0 else BitVec.ofNat 32 v_prev.lastIndex - 1
  set g_in := toGhost P s Q st
  have htry : SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ :=
    tryFrom_of_parse P.codec w h body hw_len hparse
  set r_in : RatchetState :=
    { rootKey := st.root,
      senderChain := some ⟨KeyPair.generate P.C x_prev,
        ⟨v_prev.chainKey, BitVec.ofNat 32 v_prev.lastIndex⟩⟩,
      receiverChains := (s.chains Q).map (toRecvChain st),
      previousCounter := s.pn Q,
      maxForwardJumps := 25000 }
  have hr_in_eq :
      ({ rootKey := g_in.session.rootKey, senderChain := g_in.session.senderChain,
         receiverChains := g_in.session.receiverChains,
         previousCounter := g_in.session.previousCounter,
         maxForwardJumps := 25000 } : RatchetState) = r_in := by
    dsimp only [g_in, toGhost, r_in]
    rw [hγ, hvS]
    rfl
  have hfind_r_in : r_in.findReceiverChainIndex h.senderRatchetKey = none := by
    unfold RatchetState.findReceiverChainIndex
    dsimp only [r_in]
    rw [findIdx_toRecvChain_gen st (s.chains Q) h.senderRatchetKey hdummy]
    exact hfind_none
  set L₁ := List.drop (((s.chains Q).map (toRecvChain st)).length + 1 - 5)
    ((s.chains Q).map (toRecvChain st))
  set r_mid : RatchetState :=
    { rootKey := p₂.1,
      senderChain := some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩,
      receiverChains := RatchetState.evictReceiverChains
        ((s.chains Q).map (toRecvChain st) ++ [⟨h.senderRatchetKey, some ⟨p₁.2, 0⟩, []⟩]),
      previousCounter := pn_new,
      maxForwardJumps := 25000 }
  have hens : Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc) r_in =
      (.ok ⟨p₁.2, 0⟩, r_mid) := by
    rw [exec_ensureReceiverChain_new P.C r_in h.senderRatchetKey rc hfind_r_in]
    exact exec_dhRatchetStep_honest P Dh encPt encT hX st.root x_prev v_prev.chainKey
      (BitVec.ofNat 32 v_prev.lastIndex) ((s.chains Q).map (toRecvChain st)) (s.pn Q)
      h.senderRatchetKey T hT_ne0 hencT rc
  have hmid_rc : r_mid.receiverChains =
      L₁ ++ [⟨h.senderRatchetKey, some ⟨p₁.2, 0⟩, []⟩] :=
    evictReceiverChains_append_singleton ((s.chains Q).map (toRecvChain st)) _
  set ci_new := L₁.length
  have hfind_mid : r_mid.findReceiverChainIndex h.senderRatchetKey = some ci_new := by
    unfold RatchetState.findReceiverChainIndex
    rw [hmid_rc]
    apply findIdx_append_singleton_of_none L₁ _ (fun c => c.senderRatchetKey == h.senderRatchetKey)
    · exact findIdx_drop_none_of_none _ _ _ hfind_r_in
    · simp
  set v_init : RatchetReceiverState (BitVec 256) (BitVec 256) := ⟨p₁.2, 0, []⟩
  have hsync_init : ChainSync g_init v_init := ChainSync.init (some h.senderRatchetKey) t p₁.2
  have hget_mid : r_mid.receiverChains[ci_new]? =
      some ⟨h.senderRatchetKey,
        some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩,
        mkSkippedList g_init.skipped v_init.skippedKeys⟩ := by
    rw [hmid_rc, List.getElem?_append_right (Nat.le_refl L₁.length), Nat.sub_self]
    rfl
  have hupd_mid :
      updChain r_mid ci_new h.senderRatchetKey
        (some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩) g_init.skipped v_init.skippedKeys =
        r_mid :=
    updChain_eq_self r_mid ci_new h.senderRatchetKey
      (some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩) g_init.skipped v_init.skippedKeys hget_mid
  have hrec_ver : g_in.session.sessionVersion = BitVec.ofNat 32 currentVersion.toNat := rfl
  have hrec_loc : g_in.session.localIdentity = idOfP P Q := rfl
  have hrec_rem : g_in.session.remoteIdentity = some (idOfP P Q.other) := by
    simp [g_in, toGhost, idOfP]
  have hrec_pq : g_in.session.pqRatchetState = s.pq Q := rfl
  have hT_map : ((some T).map encT).getD dummyKey = h.senderRatchetKey := by
    simp [hencT]
  constructor
  · intro hrej
    rcases exec_consumeMessageKey_rejects P.C.F r_mid ci_new h.senderRatchetKey h.counter .whisper
      hfind_mid rfl hsync_init hrej with ⟨e, r_out, hcons⟩
    rw [hupd_mid] at hcons
    have hstep : Mut.exec
        (do
          let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
          RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
        r_in = (.error e, r_out) := by
      rw [Mut.exec_bind, hens]
      exact hcons
    rw [← hr_in_eq] at hstep
    rcases tryDecryptFromRecord_of_stepChain_error P Q
      ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩
      rc g_in.session hrec_rem e r_out hstep with ⟨e', hdec_err⟩
    unfold Params.receive
    have hparty : g_in.party = Q := rfl
    rw [htry, hparty]
    dsimp only
    rw [hdec_err]
  · intro hacc
    rcases exec_consumeMessageKey_accepts P.C.F r_mid ci_new h.senderRatchetKey h.counter .whisper
      hfind_mid rfl hsync_init hacc with ⟨key, v', hcons, hsync', hfs⟩
    rw [hupd_mid] at hcons
    set r_out := updChain r_mid ci_new h.senderRatchetKey
      (some ⟨v'.chainKey, BitVec.ofNat 32 v'.lastIndex⟩) (g_init.accept i).skipped v'.skippedKeys
    have hstep : Mut.exec
        (do
          let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
          RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
        r_in = (.ok ⟨keyToBytes32 key, h.counter⟩, r_out) := by
      rw [Mut.exec_bind, hens]
      exact hcons
    rw [← hr_in_eq] at hstep
    have hfig8 : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c =
        (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          key (i, (t, some T)) ((ser, tag), effectiveHkdfSalt32 salt)).map
          (fun pm => ({ st with root := p₁.1, vR := Function.update st.vR t (some v'),
                                γ := .pub T, tcur := t }, t, i, pm)) := by
      unfold lFig8 SM.Construction.scheme SM.Construction.receive lFS dhScheme
      dsimp only [c, t]
      have hcond1 : (st.id.sendsIn (st.tcur + 1) || decide (st.tcur + 1 < st.tcur + 1)) = false := by
        rw [hst_id, hrecv]; simp
      have hv_init_eq :
          (FSAEAD.fromAEADPRG ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec))
            (lChainPRG P.C.F) 25000).initReceiver
            ((rootPRNG P.C.F encPt).up st.root (Dh.dh x_prev T)).2 = v_init := rfl
      simp only [hcond1, Bool.false_eq_true, ↓reduceIte, hγ, hv_init_eq, Function.update_self]
      rw [hfs ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)) (t, some T) ((ser, tag), effectiveHkdfSalt32 salt)]
      cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, (t, some T)) ((ser, tag), effectiveHkdfSalt32 salt) with
      | none => rfl
      | some pm =>
        simp [Function.update_idem, p₁, i]
    have htry_ok := tryDecryptFromRecord_of_stepChain_ok (ℓ := ℓ) P encT idOf hid Q t (some T)
      hrecv w hw_len h body hparse haddrs hT_map g_in.session hrec_ver hrec_loc hrec_rem pq' salt
      (by rw [hrec_pq]; exact hspqr) (by rw [hrec_pq]; exact hnpR) rc key r_out hstep
    dsimp only at htry_ok
    rw [hfig8]
    cases hdec : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        key (i, (t, some T)) ((ser, tag), effectiveHkdfSalt32 salt) with
    | none =>
      rw [hdec] at htry_ok
      rcases htry_ok with ⟨e', hdec_err⟩
      unfold Params.receive
      have hparty : g_in.party = Q := rfl
      rw [htry, hparty]
      dsimp only
      rw [hdec_err]
      rfl
    | some pm =>
      rcases pm with ⟨pub, m⟩
      rw [hdec] at htry_ok
      rcases htry_ok with ⟨hpub, m_raw, hm_eq, hdec_ok⟩
      dsimp only [Option.map]
      set st' : Fig8St Pt :=
        { st with root := p₁.1, vR := Function.update st.vR t (some v'),
                  γ := .pub T, tcur := t }
      set s' : SimState PQ Pt ℓ :=
        { s with
          mir := mir',
          pq := Function.update s.pq Q pq',
          unackA := s.unackA && Q != Party.A,
          chains := Function.update s.chains Q (pushChain (s.chains Q) (g_init.accept i)) }
      have hrecv_eq :
          P.receive g_in w rc =
            some (withEager (toGhost P s' Q st') p₂.1
              (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new, t, i, m_raw) := by
        unfold Params.receive
        have hparty : g_in.party = Q := rfl
        rw [htry, hparty]
        dsimp only
        rw [hdec_ok]
        dsimp only
        have hfind_in :
            g_in.session.receiverChains.findIdx? (fun x => x.senderRatchetKey == h.senderRatchetKey) =
              none := hfind_r_in
        have hr_out_rc :
            r_out.receiverChains =
              L₁ ++ [⟨h.senderRatchetKey, some ⟨v'.chainKey, BitVec.ofNat 32 v'.lastIndex⟩,
                mkSkippedList (g_init.accept i).skipped v'.skippedKeys⟩] := by
          dsimp only [r_out, updChain]
          rw [hmid_rc, set_append_singleton_length]
        have hlen_drop :
            List.drop ((g_in.chainEpochs ++ [g_in.epoch + 1]).length - r_out.receiverChains.length)
              (g_in.chainEpochs ++ [g_in.epoch + 1]) =
            (pushChain (s.chains Q) (g_init.accept i)).map (·.epoch) := by
          have hep_in : g_in.epoch + 1 = (g_init.accept i).epoch := by
            simp [g_in, toGhost, hmir_ep, g_init, t]
          have hlen_out : r_out.receiverChains.length =
              (List.drop (((s.chains Q).length + 1) - 5) (s.chains Q)).length + 1 := by
            rw [hr_out_rc, List.length_append, List.length_singleton]
            simp [L₁, List.length_drop]
          rw [hep_in]
          exact drop_chainEpochs_new (s.chains Q) (g_init.accept i) r_out.receiverChains.length hlen_out
        have hrc_eq :
            r_out.receiverChains =
              (pushChain (s.chains Q) (g_init.accept i)).map (toRecvChain st') := by
          have hmap_old : (s.chains Q).map (toRecvChain st') = (s.chains Q).map (toRecvChain st) := by
            apply List.map_congr_left
            intro g hg
            have hne := hchains_ep g hg
            unfold toRecvChain
            simp [st', Function.update_of_ne hne]
          have hacc_chain :
              toRecvChain st' (g_init.accept i) =
                ⟨h.senderRatchetKey, some ⟨v'.chainKey, BitVec.ofNat 32 v'.lastIndex⟩,
                  mkSkippedList (g_init.accept i).skipped v'.skippedKeys⟩ := by
            have hvR' : st'.vR (g_init.accept i).epoch = some v' := by
              simp [st', g_init, accept_epoch, Function.update_self]
            rw [toRecvChain_of_some st' (g_init.accept i) v' hvR', accept_key]
            rfl
          rw [hr_out_rc, pushChain_eq_drop_append, List.map_append, List.map_singleton,
            List.map_drop, hmap_old, hacc_chain]
          simp [L₁]
        have hep_cur : g_in.epoch + 1 = t := by simp [g_in, toGhost, hmir_ep, t]
        rw [hfind_in]
        dsimp only
        rw [hlen_drop, hrc_eq, hep_cur]
        simp [g_in, s', st', withEager, toGhost, toRecvChain, mkSkippedList, i, r_out, updChain,
          r_mid, hmir', Function.update_self, pendingPreKey_after_accept]
        intro _ _
        rfl
      have hstepS_eq :
          withEager (toGhost P s' Q st') p₂.1
            (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new =
          toGhost P { s' with pn := Function.update s'.pn Q pn_new } Q
            (fig8StepS Dh encPt P.C st' rc) :=
        (toGhost_fig8StepS P Dh encPt s' Q st' T rfl rc pn_new).symm
      refine ⟨rfl, rfl, hpub, ⟨v', rfl, hsync'⟩, m_raw, hm_eq, hrecv_eq, ?_⟩
      rw [hrecv_eq, hstepS_eq]

end CryptoGames.LibsignalSM.Proofs.Refinement
