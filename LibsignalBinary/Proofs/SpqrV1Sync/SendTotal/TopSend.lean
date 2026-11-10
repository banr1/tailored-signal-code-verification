/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs

/-!
# Top-Level Invariant Preservation Under Sends

Proves `TopSendClosedStmt`: `(spqrV1 F K).send` advances `TopAdv F K n` to `TopAdv F K (n + 1)`
whenever `n + 1 < 2 ^ 32`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoGames.LibsignalSession (ShaCompress)

theorem tsnd_addEpoch_opt (hkdf : HkdfFn) (chE chain1 : Chain) (key : Option EpochSecret)
    (hs : SendPrevNil chE)
    (hadd : (match key with
      | some es => chE.addEpoch hkdf es
      | none => .ok chE) = .ok chain1) : SendPrevNil chain1 := by
  cases key with
  | none =>
    cases hadd
    exact hs
  | some es =>
    exact addEpoch_sendPrevNil hkdf chE chain1 es hs hadd

theorem tsnd_keyAt_isEmpty (F : ShaCompress) (seed : Bytes) (n : ℕ) :
    (keyAt F seed n).isEmpty = false := by
  have hlen := length_keyAt F seed n
  cases hk : keyAt F seed n with
  | nil => rw [hk] at hlen; cases hlen
  | cons _ _ => rfl

theorem tsnd_messageKeyToSalt_keyAt (F : ShaCompress) (seed : Bytes) (n : ℕ) :
    messageKeyToSalt? (some (keyAt F seed n)) =
      some (some ⟨keyAt F seed n, length_keyAt F seed n⟩) := by
  simp [messageKeyToSalt?, length_keyAt]

theorem tsnd_spqrDeps_msgEpoch (F : ShaCompress) (K : MlKem) :
    (spqrDeps F K).msgEpoch = Message.epoch := rfl

theorem tsnd_spqrDeps_msgSerialize (F : ShaCompress) (K : MlKem) :
    (spqrDeps F K).msgSerialize = Message.serialize := rfl

theorem tsnd_spqrDeps_statesIntoPb (F : ShaCompress) (K : MlKem) :
    (spqrDeps F K).statesIntoPb = States.into_pb := rfl

theorem tsnd_sendAfterStates_ok (F : ShaCompress) (K : MlKem) (authKey : Bytes)
    (dir : Direction) (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (vn? : Option VersionNegotiationPB) (ch? : Option Chain)
    (chE chain1 chain2 : Chain)
    (hch : ch? = some chE ∨
      (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
        chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE))
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (m : Msg) (key : Option EpochSecret)
    (hadd : (match key with
      | some es => chE.addEpoch (spqrHkdfWith F) es
      | none => .ok chE) = .ok chain1)
    (he_ne0 : (m.epoch == 0#64) = false)
    (idx : BitVec 32) (n : ℕ) (seed : Bytes)
    (hsk : chain1.sendKey (spqrHkdfWith F) (m.epoch - 1#64) = .ok (chain2, (idx, keyAt F seed n))) :
    sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (topPb st vn? ch?) m key st' =
      .ok {
        state := topBytes F K st' vn? (some chain2)
        msg := Message.serialize m idx
        key := some (keyAt F seed n)
      } := by
  rcases serialize_head m idx with ⟨rest, hser⟩
  have hver_ok : ((1#8 != Version.v1.toU8) = false) := by decide
  unfold sendAfterStates
  rcases hch with rfl | ⟨rfl, rfl, hvnE⟩
  · have hfpb := chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hok
    cases key with
    | none =>
      cases hadd
      simp only [topPb, topBytes, Option.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
        hfpb, SpqrApiResult.ofError, tsnd_spqrDeps_msgEpoch, he_ne0, Bool.false_eq_true,
        ↓reduceIte, hsk, SpqrApiResult.ofChainResult, tsnd_spqrDeps_msgSerialize, hser, hver_ok,
        tsnd_spqrDeps_statesIntoPb, tsnd_keyAt_isEmpty]
      rfl
    | some es =>
      dsimp only at hadd
      simp only [topPb, topBytes, Option.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
        hfpb, SpqrApiResult.ofError, hadd, SpqrApiResult.ofChainPanic, tsnd_spqrDeps_msgEpoch,
        he_ne0, Bool.false_eq_true, ↓reduceIte, hsk, SpqrApiResult.ofChainResult,
        tsnd_spqrDeps_msgSerialize, hser, hver_ok, tsnd_spqrDeps_statesIntoPb, tsnd_keyAt_isEmpty]
      rfl
  · have hslt : BitVec.slt Version.v0.toI32 Version.v1.toI32 = true := by decide
    have hmin : (vnOf dir authKey).minVersion = Version.v1.toI32 := rfl
    cases key with
    | none =>
      cases hadd
      simp only [topPb, topBytes, Option.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
        hmin, hslt, ↓reduceIte, hvnE, SpqrApiResult.ofError, tsnd_spqrDeps_msgEpoch, he_ne0,
        Bool.false_eq_true, hsk, SpqrApiResult.ofChainResult, tsnd_spqrDeps_msgSerialize, hser,
        hver_ok, tsnd_spqrDeps_statesIntoPb, tsnd_keyAt_isEmpty]
      rfl
    | some es =>
      dsimp only at hadd
      simp only [topPb, topBytes, Option.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
        hmin, hslt, ↓reduceIte, hvnE, SpqrApiResult.ofError, hadd, SpqrApiResult.ofChainPanic,
        tsnd_spqrDeps_msgEpoch, he_ne0, Bool.false_eq_true, hsk, SpqrApiResult.ofChainResult,
        tsnd_spqrDeps_msgSerialize, hser, hver_ok, tsnd_spqrDeps_statesIntoPb, tsnd_keyAt_isEmpty]
      rfl

theorem tsnd_send_addEpoch (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (chE : Chain) (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (hcur : chE.currentEpoch.toNat = chainCur st) (hep_pos : 1 ≤ st.epoch.toNat)
    (tape tape' : Bytes) (m : Msg) (key : Option EpochSecret)
    (hsendB : st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape'))
    (hsec : ∀ es, key = some es → es.secret = secret es.epoch.toNat) :
    ∃ chain1 : Chain,
      (match key with
       | some es => chE.addEpoch (spqrHkdfWith F) es
       | none => .ok chE) = .ok chain1 ∧
      ChainOk F authKey dir secret sendCtr recvSet chain1 ∧
      chain1.currentEpoch.toNat = chainCur st' ∧
      chain1.sendEpoch = chE.sendEpoch ∧
      chainCur st ≤ chain1.currentEpoch.toNat := by
  cases key with
  | none =>
    have hcur' := chainCur_send_none F K st st' tape tape' m hsendB
    exact ⟨chE, rfl, hok, by omega, rfl, by omega⟩
  | some es =>
    rcases chainCur_send_key F K st st' tape tape' m es hep_pos hsendB with ⟨hes_ep, hcur'⟩
    have hep_es : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by omega
    have hsec_es : es.secret = secret (chE.currentEpoch.toNat + 1) := by
      rw [hsec es rfl, hes_ep, hcur]
    rcases addEpoch_ok F authKey dir secret sendCtr recvSet chE hok es hep_es hsec_es with
      ⟨chain1, hadd, hce, hse, hok1⟩
    refine ⟨chain1, hadd, hok1, ?_, hse, ?_⟩
    · rw [hce]
      omega
    · rw [hce]
      omega

theorem st_topSend (F : ShaCompress) (K : MlKem) (hTS : TopSizeStmt F K) (hBC : BCodecStmt F)
    (hSC : BSendClosedStmt F K) (hPhi : BPhiStmt F K) (hAdd : RecvSmallAddStmt)
    (hSnd : RecvSmallSendStmt) : TopSendClosedStmt F K := by
  intro n bytes tape bytes' salt msg hAdv hn hsendTop
  have hsize : bytes.length < 2 ^ 64 := hTS n bytes hAdv (by omega)
  rcases hAdv with ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩
  have hpt : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes :=
    ⟨vn?, ch?, chE, hw.htop⟩
  have hep_pos : 1 ≤ st.epoch.toNat := partyTop_epoch_pos hpt
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st := hBC st hw.hbok
  have hsize_top : (topBytes F K st vn? ch?).length < 2 ^ 64 := by
    rw [← hw.htop.hbytes]; exact hsize
  have hdec := decodeState_topBytes F K st vn? ch? hsize_top
  have hfrom : (spqrDeps F K).statesFromPb st.into_pb = .ok st := by
    simp [spqrDeps, liftStatesResult, hcodec]
  have hsendB_ex : ∃ (m : Msg) (key : Option EpochSecret) (st' : St F) (tape' : Bytes),
      st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape') := by
    cases hB : st.send K tape with
    | ok vt =>
      rcases vt with ⟨⟨m, key, st'⟩, tape'⟩
      exact ⟨m, key, st', tape', rfl⟩
    | error err =>
      have hbad : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) bytes tape).1.isOk = false := by
        rw [hw.htop.hbytes]
        unfold LibsignalSpqrV1.send
        rw [hdec]
        dsimp only [topPb]
        rw [hfrom]
        dsimp only
        cases err <;> (simp [spqrDeps, hB]; rfl)
      have hok_top : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) bytes tape).1.isOk = true := by
        change (match (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) bytes tape).1 with
          | .ok s => match messageKeyToSalt? s.key with
            | some salt => some (s.state, salt, s.msg)
            | none => none
          | .error _ => none) = some (bytes', salt, msg) at hsendTop
        cases h1 : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) bytes tape).1 with
        | error _ => rw [h1] at hsendTop; cases hsendTop
        | ok _ => rfl
      rw [hbad] at hok_top
      cases hok_top
  rcases hsendB_ex with ⟨m, key, st', tape', hsendB⟩
  have htop_eq := send_topBytes F K st st' vn? ch? tape tape' m key hsize_top hcodec hsendB
  rcases send_facts F K st st' tape tape' m key hsendB with ⟨hm_ep, hst'_ep, _, hkey_fact⟩
  let secret' : ℕ → Bytes :=
    match key with
    | none => secret
    | some es => Function.update secret es.epoch.toNat es.secret
  have hok' : ChainOk F authKey dir secret' sendCtr recvSet chE := by
    refine chainOk_congr F authKey dir secret secret' sendCtr recvSet chE hw.htop.hok ?_
    intro e _ he_hi
    cases key with
    | none => rfl
    | some es =>
      rcases chainCur_send_key F K st st' tape tape' m es hep_pos hsendB with ⟨hes_ep, _⟩
      have := hw.htop.hcur
      have hne : e ≠ es.epoch.toNat := by omega
      exact Function.update_of_ne hne es.secret secret
  have hsec' : ∀ es, key = some es → es.secret = secret' es.epoch.toNat := by
    intro es hkeq
    subst hkeq
    simp [secret']
  rcases tsnd_send_addEpoch F K authKey dir secret' st st' sendCtr recvSet chE hok' hw.htop.hcur
      hep_pos tape tape' m key hsendB hsec' with
    ⟨chain1, hadd, hok1, hcur1, hsendEp1, hle1⟩
  have hprev1 : SendPrevNil chain1 :=
    tsnd_addEpoch_opt (spqrHkdfWith F) chE chain1 key hw.htop.hsendPrev hadd
  have hsmall1 : RecvSmall chain1 := by
    cases key with
    | none => cases hadd; exact hw.hsmall
    | some es => exact hAdd (spqrHkdfWith F) chE chain1 es hw.hsmall hadd
  have hm_pos : 1 ≤ m.epoch.toNat := by rw [hm_ep]; exact hep_pos
  have he_ne0 : (m.epoch == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h0
    rw [h0] at hm_pos
    simp at hm_pos
  have hsub_toNat : (m.epoch - 1#64).toNat = st.epoch.toNat - 1 := by
    rw [hm_ep]
    have := st.epoch.isLt
    simp [BitVec.toNat_sub]
    omega
  have hlo : chain1.sendEpoch.toNat ≤ (m.epoch - 1#64).toNat := by
    have := hw.htop.hsendEp
    have := hw.htop.hsendLe
    rw [hsendEp1]
    omega
  have hhi : (m.epoch - 1#64).toNat ≤ chain1.currentEpoch.toNat := by
    have := epoch_sub_one_le_chainCur st
    omega
  have hn_ctr : sendCtr (m.epoch - 1#64).toNat + 1 < 2 ^ 32 := by
    have := hw.hctr (m.epoch - 1#64).toNat
    omega
  rcases sendKey_ok F authKey dir secret' sendCtr recvSet chain1 hok1 (m.epoch - 1#64) hlo hhi
      hn_ctr with
    ⟨chain2, hsk, hce2, hse2, hok2⟩
  have hsas := tsnd_sendAfterStates_ok F K authKey dir secret' st st' sendCtr recvSet vn? ch?
    chE chain1 chain2 hw.htop.hch hok' m key hadd he_ne0
    (BitVec.ofNat 32 (sendCtr (m.epoch - 1#64).toNat + 1))
    (sendCtr (m.epoch - 1#64).toNat)
    (seedAt F authKey secret' dir (m.epoch - 1#64).toNat) hsk
  have hbytes' : bytes' = topBytes F K st' vn? (some chain2) := by
    change (match (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) bytes tape).1 with
      | .ok s => match messageKeyToSalt? s.key with
        | some salt => some (s.state, salt, s.msg)
        | none => none
      | .error _ => none) = some (bytes', salt, msg) at hsendTop
    rw [hw.htop.hbytes, htop_eq] at hsendTop
    dsimp only at hsendTop
    rw [hsas] at hsendTop
    dsimp only at hsendTop
    rw [tsnd_messageKeyToSalt_keyAt] at hsendTop
    cases hsendTop
    rfl
  have hprev2 : SendPrevNil chain2 :=
    sendKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 (m.epoch - 1#64) _ hprev1 hsk
  have hsmall2 : RecvSmall chain2 :=
    hSnd (spqrHkdfWith F) chain1 chain2 (m.epoch - 1#64) _ hsmall1 hsk
  refine ⟨authKey, dir, secret', st', st.epoch.toNat - 1,
    Function.update sendCtr (m.epoch - 1#64).toNat (sendCtr (m.epoch - 1#64).toNat + 1),
    recvSet, vn?, some chain2, chain2, ?_⟩
  refine
    { htop :=
        { hbytes := hbytes'
          hvn := hw.htop.hvn
          hch := Or.inl rfl
          hok := hok2
          hcur := by rw [hce2]; exact hcur1
          hsendEp := by rw [hse2]; exact hsub_toNat
          hsendLe := by rw [hst'_ep]; omega
          hsendPrev := hprev2 }
      hauth := hw.hauth
      hbok := hSC st st' tape tape' m key hw.hbok hsendB
      hphi := by
        have := hPhi.1 st st' tape tape' m key hsendB
        have := hw.hphi
        omega
      hctr := by
        intro e
        by_cases he : e = (m.epoch - 1#64).toNat
        · subst he
          simp only [Function.update_self]
          have := hw.hctr (m.epoch - 1#64).toNat
          omega
        · rw [Function.update_of_ne he]
          have := hw.hctr e
          omega
      hsmall := hsmall2 }

end CryptoVerification.SpqrV1Sync.SendTotal
