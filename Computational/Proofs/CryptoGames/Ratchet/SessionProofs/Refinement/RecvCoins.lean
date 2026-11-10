/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.CreateChainProofDefs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Defs

/-!
# Receive-coin independence for the refinement

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves that receiver-chain operations commute with sender-field updates and that zero-point DH
ratchet steps fail independently of receive coins.
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
  [DecidableEq PQ] [Inhabited PQ] [SampleableType PQC]

@[local simp]
theorem Mut.exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

@[local simp]
theorem Mut.exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

@[local simp]
theorem Mut.exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp]
theorem Mut.exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok ⟨⟩, s') := rfl

@[local simp]
theorem Mut.exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok ⟨⟩, f s) := rfl

@[local simp]
theorem Mut.exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

@[local simp]
theorem Mut.exec_liftE_ok {σ α : Type} (a : α) (s : σ) :
    Mut.exec (liftE (.ok a) : Mut σ α) s = (.ok a, s) := rfl

@[local simp]
theorem Mut.exec_liftE_error {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (liftE (.error e) : Mut σ α) s = (.error e, s) := rfl

@[local simp]
theorem Mut.exec_bind {σ α β : Type} (m : Mut σ α) (k : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= k) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (k a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases m.run.run s with ⟨r, s'⟩
  cases r <;> rfl

@[local simp]
theorem Mut.exec_takeRootKey (s : RatchetState) :
    Mut.exec RatchetState.takeRootKey s = (.ok s.rootKey, { s with rootKey := 0 }) := rfl

@[local simp]
theorem Mut.exec_takeRatchetState (s : SessionState PQ) :
    Mut.exec SessionState.takeRatchetState s =
      (.ok ⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩,
        { s with receiverChains := [] }) := rfl

@[local simp]
theorem Mut.exec_takePqRatchetState (s : SessionState PQ) :
    Mut.exec SessionState.takePqRatchetState s =
      (.ok s.pqRatchetState, { s with pqRatchetState := default }) := rfl

theorem vec32_of_length {bs : List (BitVec 8)} (h : bs.length = 32) :
    vec32 bs = ⟨bs, h⟩ := by
  apply Subtype.ext
  dsimp only [vec32]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem vec32_toList_of_length {bs : List (BitVec 8)} (h : bs.length = 32) :
    (vec32 bs).toList = bs := by
  rw [vec32_of_length h]
  rfl

theorem vec32_keyToBytes32 (x : BitVec 256) :
    vec32 (keyToBytes32 x) = keyToBytesVec32 x :=
  vec32_of_length (keyToBytesVec32 x).2

theorem libX25519Rel_model {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh C Dh encPt encT) :
    CKA.X25519Model Dh encPt C.X.toListFn (fun x => (C.pubKey (vec32 x)).toList) := by
  rcases hX with ⟨hM, _⟩
  refine { hM with hook := fun x P => ?_ }
  have hk : (keyToBytes32 x).length = 32 := by simp [keyToBytes32]
  have hp : (encPt P).length = 32 := hM.enc_length P
  unfold X25519Fn.toListFn
  simp only [hk, hp, ↓reduceDIte]
  rw [← vec32_of_length hk, ← vec32_of_length hp]
  exact hM.hook x P

theorem encT_bytes_toList {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh C Dh encPt encT) (T : Pt) :
    (encT T).bytes.toList = encPt T := by
  rw [hX.2 T, vec32_toList_of_length (hX.1.enc_length T)]

theorem keyPair_generate_publicKey {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh C Dh encPt encT) (x : BitVec 256) :
    (KeyPair.generate C x).publicKey = encT (Dh.dh x Dh.base) := by
  unfold KeyPair.generate
  dsimp only
  rw [clampScalar_keyVec, ← vec32_keyToBytes32 (CKA.clamp256 x)]
  rcases h : encT (Dh.dh x Dh.base) with ⟨b⟩
  congr 1
  apply Subtype.ext
  have hb : b.toList = encPt (Dh.dh x Dh.base) := by
    have := encT_bytes_toList hX (Dh.dh x Dh.base)
    rwa [h] at this
  change (C.pubKey (vec32 (keyToBytes32 (CKA.clamp256 x)))).toList = b.toList
  rw [hX.1.pubKey_hook (CKA.clamp256 x), hX.1.dh_clamp x Dh.base, hb]

def withSender (s : RatchetState) (rk : LibsignalSession.RootKey) (sc : Option SenderChain) : RatchetState :=
  { s with rootKey := rk, senderChain := sc }

@[local simp]
theorem withSender_rootKey (s : RatchetState) (rk : LibsignalSession.RootKey) (sc : Option SenderChain) :
    (withSender s rk sc).rootKey = rk := rfl

@[local simp]
theorem withSender_senderChain (s : RatchetState) (rk : LibsignalSession.RootKey) (sc : Option SenderChain) :
    (withSender s rk sc).senderChain = sc := rfl

@[local simp]
theorem withSender_receiverChains (s : RatchetState) (rk : LibsignalSession.RootKey) (sc : Option SenderChain) :
    (withSender s rk sc).receiverChains = s.receiverChains := rfl

@[local simp]
theorem withSender_previousCounter (s : RatchetState) (rk : LibsignalSession.RootKey) (sc : Option SenderChain) :
    (withSender s rk sc).previousCounter = s.previousCounter := rfl

@[local simp]
theorem withSender_maxForwardJumps (s : RatchetState) (rk : LibsignalSession.RootKey) (sc : Option SenderChain) :
    (withSender s rk sc).maxForwardJumps = s.maxForwardJumps := rfl

@[local simp]
theorem withSender_withSender (s : RatchetState) (rk₁ rk₂ : LibsignalSession.RootKey)
    (sc₁ sc₂ : Option SenderChain) :
    withSender (withSender s rk₁ sc₁) rk₂ sc₂ = withSender s rk₂ sc₂ := rfl

@[local simp]
theorem withSender_self (s : RatchetState) :
    withSender s s.rootKey s.senderChain = s := by
  cases s; rfl

@[local simp]
theorem findReceiverChainIndex_withSender (s : RatchetState) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (their : PublicKey) :
    (withSender s rk sc).findReceiverChainIndex their = s.findReceiverChainIndex their := rfl

@[local simp]
theorem findReceiverChainKey_withSender (s : RatchetState) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (their : PublicKey) :
    (withSender s rk sc).findReceiverChainKey their = s.findReceiverChainKey their := rfl

theorem exec_takeSkippedKey_withSender (s : RatchetState) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (their : PublicKey) (counter : BitVec 32) :
    Mut.exec (RatchetState.takeSkippedKey their counter) (withSender s rk sc) =
      let res := Mut.exec (RatchetState.takeSkippedKey their counter) s
      (res.1, withSender res.2 rk sc) := by
  unfold RatchetState.takeSkippedKey
  simp only [Mut.exec_bind, Mut.exec_get, findReceiverChainIndex_withSender,
    withSender_receiverChains]
  cases s.findReceiverChainIndex their with
  | none => rfl
  | some chainIdx =>
    dsimp only
    cases s.receiverChains[chainIdx]? with
    | none => rfl
    | some c =>
      dsimp only
      cases c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
      | none => rfl
      | some pos =>
        dsimp only
        cases c.messageKeys[pos]? <;> rfl

theorem exec_storeSkippedKey_withSender (s : RatchetState) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (their : PublicKey) (key : MessageKeyGenerator) :
    Mut.exec (RatchetState.storeSkippedKey their key) (withSender s rk sc) =
      let res := Mut.exec (RatchetState.storeSkippedKey their key) s
      (res.1, withSender res.2 rk sc) := by
  unfold RatchetState.storeSkippedKey
  simp only [Mut.exec_bind, Mut.exec_get, findReceiverChainIndex_withSender,
    withSender_receiverChains]
  cases s.findReceiverChainIndex their with
  | none => rfl
  | some chainIdx =>
    dsimp only
    cases s.receiverChains[chainIdx]? <;> rfl

theorem exec_setReceiverChainKey_withSender (s : RatchetState) (rk : LibsignalSession.RootKey)
    (sc : Option SenderChain) (their : PublicKey) (ck : LibsignalSession.ChainKey) :
    Mut.exec (RatchetState.setReceiverChainKey their ck) (withSender s rk sc) =
      let res := Mut.exec (RatchetState.setReceiverChainKey their ck) s
      (res.1, withSender res.2 rk sc) := by
  unfold RatchetState.setReceiverChainKey
  simp only [Mut.exec_bind, Mut.exec_get, findReceiverChainIndex_withSender,
    withSender_receiverChains]
  cases s.findReceiverChainIndex their with
  | none => rfl
  | some chainIdx =>
    dsimp only
    cases s.receiverChains[chainIdx]? <;> rfl

theorem exec_advanceChain_withSender (F : ShaCompress) (their : PublicKey) (counter : BitVec 32)
    (fuel : ℕ) :
    ∀ (ck : LibsignalSession.ChainKey) (s : RatchetState) (rk : LibsignalSession.RootKey)
        (sc : Option SenderChain),
      Mut.exec (RatchetState.advanceChain F their counter fuel ck) (withSender s rk sc) =
        let res := Mut.exec (RatchetState.advanceChain F their counter fuel ck) s
        (res.1, withSender res.2 rk sc) := by
  induction fuel with
  | zero =>
    intro ck s rk sc
    rfl
  | succ fuel ih =>
    intro ck s rk sc
    unfold RatchetState.advanceChain
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, Mut.exec_bind, exec_storeSkippedKey_withSender]
      rcases Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) s with ⟨r1, s1⟩
      cases r1 with
      | error e => rfl
      | ok _ =>
        dsimp only
        cases ck.nextChainKey F with
        | error e => rfl
        | ok ck' =>
          dsimp only [Mut.exec_liftE_ok]
          exact ih ck' s1 rk sc
    · simp only [hlt, ↓reduceIte, Mut.exec_pure]

theorem exec_consumeMessageKey_withSender (F : ShaCompress) (their : PublicKey)
    (chainKey : LibsignalSession.ChainKey) (counter : BitVec 32) (msgType : MessageType)
    (s : RatchetState) (rk : LibsignalSession.RootKey) (sc : Option SenderChain) :
    Mut.exec (RatchetState.consumeMessageKey F their chainKey counter msgType)
        (withSender s rk sc) =
      let res := Mut.exec (RatchetState.consumeMessageKey F their chainKey counter msgType) s
      (res.1, withSender res.2 rk sc) := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < chainKey.index
  · simp only [hlt, ↓reduceIte, Mut.exec_bind, exec_takeSkippedKey_withSender]
    rcases Mut.exec (RatchetState.takeSkippedKey their counter) s with ⟨r1, s1⟩
    cases r1 with
    | error e => rfl
    | ok k? =>
      cases k? <;> rfl
  · simp only [hlt, ↓reduceIte, Mut.exec_bind, Mut.exec_get, withSender_maxForwardJumps]
    by_cases hj : s.maxForwardJumps < (counter - chainKey.index).toNat
    · simp only [hj, ↓reduceIte, Mut.exec_throw, Mut.exec_bind]
    · simp only [hj, Bool.false_eq_true, ↓reduceIte, Mut.exec_pure, Mut.exec_bind,
        exec_advanceChain_withSender]
      rcases Mut.exec (RatchetState.advanceChain F their counter
        (counter - chainKey.index).toNat chainKey) s with ⟨r1, s1⟩
      cases r1 with
      | error e => rfl
      | ok ck' =>
        dsimp only
        cases ck'.nextChainKey F with
        | error e => rfl
        | ok nextCk =>
          simp only [Mut.exec_liftE_ok, Mut.exec_bind, exec_setReceiverChainKey_withSender]
          rcases Mut.exec (RatchetState.setReceiverChainKey their nextCk) s1 with ⟨r2, s2⟩
          cases r2 <;> rfl

theorem createChain_zero {D : CKA.DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} (F : ShaState → List (BitVec 8) → ShaState) (X : X25519Fn)
    {pubKey : List (BitVec 8) → List (BitVec 8)}
    (hM : CKA.X25519Model D encPt X.toListFn pubKey)
    (hz : ∀ x, D.dh x 0 = 0) (rk : Ratchet.RootKey)
    (x : BitVec 256) (pub : List.Vector (BitVec 8) 32)
    (hpub : pub.toList = encPt 0) :
    createChain F X rk pub (keyToBytesVec32 x) = none := by
  have hss : (X (clampScalar (keyToBytesVec32 x)) pub).toList = encPt (D.dh x 0) := by
    rw [clampScalar_keyVec, ← hM.dh_clamp x 0, ← hM.hook (CKA.clamp256 x) 0, ← hpub,
      ← toListFn_vec]
    rfl
  rw [hz x, hM.enc_zero] at hss
  simp [createChain, hss]

theorem createChain_zero_clamped {D : CKA.DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} (F : ShaState → List (BitVec 8) → ShaState) (X : X25519Fn)
    {pubKey : List (BitVec 8) → List (BitVec 8)}
    (hM : CKA.X25519Model D encPt X.toListFn pubKey)
    (hz : ∀ x, D.dh x 0 = 0) (rk : Ratchet.RootKey)
    (x : BitVec 256) (pub : List.Vector (BitVec 8) 32)
    (hpub : pub.toList = encPt 0) :
    createChain F X rk pub (keyToBytesVec32 (CKA.clamp256 x)) = none :=
  createChain_zero F X hM hz rk (CKA.clamp256 x) pub hpub

theorem rootCreateChain_generate_honest {D : CKA.DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} (C : Crypto)
    {pubKey : List (BitVec 8) → List (BitVec 8)}
    (hM : CKA.X25519Model D encPt C.X.toListFn pubKey)
    (rk : LibsignalSession.RootKey) (coins : BitVec 256) {T : Pt} (hT : T ≠ 0)
    {their : PublicKey} (hpub : their.bytes.toList = encPt T) :
    rootCreateChain C rk their (KeyPair.generate C coins).privateKey =
      let p := (rootPRNG C.F encPt).up rk (D.dh coins T)
      .ok (p.1, ⟨p.2, 0⟩) := by
  unfold rootCreateChain KeyPair.generate
  dsimp only
  rw [clampScalar_keyVec, createChain_honest_clamped C.F C.X hM rk coins T hT their.bytes hpub]

theorem rootCreateChain_generate_zero {D : CKA.DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} (C : Crypto)
    {pubKey : List (BitVec 8) → List (BitVec 8)}
    (hM : CKA.X25519Model D encPt C.X.toListFn pubKey)
    (hz : ∀ x, D.dh x 0 = 0)
    (rk : LibsignalSession.RootKey) (coins : BitVec 256)
    {their : PublicKey} (hpub : their.bytes.toList = encPt 0) :
    rootCreateChain C rk their (KeyPair.generate C coins).privateKey =
      .error .invalidKeyAgreement := by
  unfold rootCreateChain KeyPair.generate
  dsimp only
  rw [clampScalar_keyVec, createChain_zero_clamped C.F C.X hM hz rk coins their.bytes hpub]

theorem tryFrom_parse_eq (codec : SignalMessageProtoCodec) (w : List (BitVec 8)) (msg : SignalMessage)
    (h : SignalMessage.tryFrom codec w = .ok msg) :
    ¬ w.length < 9 ∧
      (signalWireCodec codec).parse (w.take (w.length - 8)) = some (msg.header, msg.ciphertext) := by
  unfold SignalMessage.tryFrom at h
  have hmac : macLength = 8 := rfl
  rw [hmac] at h
  by_cases hlen : w.length < 8 + 1
  · simp only [hlen, ↓reduceIte] at h; cases h
  · refine ⟨hlen, ?_⟩
    unfold signalWireCodec
    dsimp only
    unfold SignalMessage.tryFrom
    rw [hmac]
    set ser := w.take (w.length - 8)
    have hser_len : ser.length = w.length - 8 := by
      simp [ser, List.length_take]
    have htot_len : (ser ++ List.replicate 8 0).length = w.length := by
      rw [List.length_append, hser_len, List.length_replicate]
      omega
    have hhead : (ser ++ List.replicate 8 0).headD 0 = w.headD 0 := by
      have hpos : 0 < w.length - 8 := by omega
      rcases w with _ | ⟨b, bs⟩
      · simp at hpos
      · rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨k, hk⟩
        have hser_cons : ser = b :: bs.take k := by
          change List.take ((b :: bs).length - 8) (b :: bs) = b :: bs.take k
          rw [hk, List.take_succ_cons]
        rw [hser_cons]
        rfl
    have htake : (ser ++ List.replicate 8 0).take (w.length - 8) = ser := by
      rw [← hser_len, List.take_left]
    have htake_w : w.take (w.length - 8) = ser := rfl
    simp only [htot_len, hlen, ↓reduceIte, hhead, htake, htake_w] at h ⊢
    dsimp only [bind, Except.bind, pure, Except.pure] at h ⊢
    by_cases hv1 : (w.headD 0) >>> 4 < preKyberVersion
    · simp only [hv1, ↓reduceIte] at h; cases h
    · by_cases hv2 : currentVersion < (w.headD 0) >>> 4
      · simp only [hv1, hv2, ↓reduceIte] at h; cases h
      · simp only [hv1, hv2, ↓reduceIte] at h ⊢
        cases hd : codec.decode (ser.drop 1) with
        | none => rw [hd] at h; cases h
        | some p =>
          rw [hd] at h
          dsimp only at h ⊢
          cases hrk : p.ratchetKey with
          | none => rw [hrk] at h; cases h
          | some rk =>
            rw [hrk] at h
            dsimp only at h ⊢
            cases hdes : PublicKey.deserialize rk with
            | error e => rw [hdes] at h; cases h
            | ok srk =>
              rw [hdes] at h
              dsimp only at h ⊢
              cases hctr : p.counter with
              | none => rw [hctr] at h; cases h
              | some ctr =>
                rw [hctr] at h
                dsimp only at h ⊢
                cases hct : p.ciphertext with
                | none => rw [hct] at h; cases h
                | some ct =>
                  rw [hct] at h
                  dsimp only at h ⊢
                  injection h with hmsg
                  subst hmsg
                  rfl

end CryptoGames.LibsignalSM.Proofs.Refinement
