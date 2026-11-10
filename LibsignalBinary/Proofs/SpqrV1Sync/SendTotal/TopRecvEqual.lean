/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs

/-!
# Top-Level Invariant Preservation on Version-1 Receives

Proves `TopRecvEqualStmt`: the `Ordering::Equal` (`version = 1`) branch `recvEqual` of `Top.recv`
preserves `TopAdvW` across braid state updates, optional epoch secret derivation, and
`Chain.recvKey`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoGames.LibsignalSession (ShaCompress)

private theorem treq_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem treq_recv_epoch_le (F : ShaCompress) (K : MlKem) (st st' : St F) (m : Msg)
    (key : Option EpochSecret) (h : st.recv K m = .ok { key := key, state := st' }) :
    st.epoch.toNat ≤ st'.epoch.toNat := by
  rcases recv_facts F K st st' m key h with ⟨_, ⟨_, ⟨hEq, _⟩ | ⟨h1, _⟩⟩ | ⟨_, _, _, h1, _⟩⟩
  · rw [hEq]
  · omega
  · omega

theorem treq_spqrDeps_statesFromPb (F : ShaCompress) (K : MlKem) (st : St F)
    (hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st) :
    (spqrDeps F K).statesFromPb st.into_pb = .ok st := by
  simp [spqrDeps, liftStatesResult, hcodec]

theorem treq_statesRecv_ok (F : ShaCompress) (K : MlKem) (st st' : St F)
    (m : Msg) (key : Option EpochSecret)
    (h : (spqrDeps F K).statesRecv st m = .ok (key, st')) :
    st.recv K m = .ok { key := key, state := st' } := by
  cases hr : st.recv K m with
  | error err =>
    cases err <;> simp [spqrDeps, hr] at h
  | ok rOut =>
    simp [spqrDeps, hr] at h
    rcases rOut with ⟨k0, s0⟩
    rcases h with ⟨rfl, rfl⟩
    rfl

theorem st_topRecvEqual (F : ShaCompress) (K : MlKem) (hBC : BCodecStmt F)
    (hEk : BRecvEkStmt F K) (hCt : BRecvCtStmt F K) (hPhi : BPhiStmt F K)
    (hCR : ChainRecvStmt F) (hAdd : RecvSmallAddStmt) : TopRecvEqualStmt F K := by
  intro n bytes authKey dir secret st sendEp sendCtr recvSet vn? ch? chE pre r hw _ hre
  unfold recvEqual at hre
  rcases treq_bind_ok hre with ⟨m, _, hre1⟩
  rcases treq_bind_ok hre1 with ⟨st0, hst0, hre2⟩
  have hst0_ok := treq_spqrDeps_statesFromPb F K st (hBC st hw.hbok)
  rw [hst0_ok] at hst0
  cases hst0
  rcases treq_bind_ok hre2 with ⟨⟨key, st1⟩, hsr, hre3⟩
  have hrecvB := treq_statesRecv_ok F K st st1 m key hsr
  have hep_pos : 1 ≤ st.epoch.toNat := partyTop_epoch_pos ⟨vn?, ch?, chE, hw.htop⟩
  have hep_le : st.epoch.toNat ≤ st1.epoch.toNat := treq_recv_epoch_le F K st st1 m key hrecvB
  have hbok1 : BOk st1 := by
    cases hek : isEkSide st with
    | true => exact hEk st st1 m key hek hw.hbok hrecvB
    | false => exact hCt st st1 m key hek hw.hbok hrecvB
  have hphi1 : phiB st1 ≤ n := by
    have := hPhi.2 st st1 m key hrecvB
    have := hw.hphi
    omega
  cases he0 : (pre.epoch == 0#64) with
  | true =>
    rw [he0] at hre3
    cases hre3
  | false =>
    rw [he0] at hre3
    dsimp only [↓reduceIte] at hre3
    rcases treq_bind_ok hre3 with ⟨chain0, hch0, hre4⟩
    have hch0_eq :
        SpqrApiResult.ofError (chainFrom (spqrHkdfWith F) (ch?.map Chain.intoPb) vn?) = .ok chE := by
      rcases hw.htop.hch with rfl | ⟨rfl, rfl, hvnE⟩
      · have hfpb := chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hw.htop.hok
        simp [chainFrom, hfpb, SpqrApiResult.ofError]
      · simp [chainFrom, hvnE, SpqrApiResult.ofError]
    rw [hch0_eq] at hch0
    cases hch0
    have hstep1 :
        ∃ chain1 : Chain,
          (match key with
           | some epochSecret => SpqrApiResult.ofChainPanic (chE.addEpoch (spqrHkdfWith F) epochSecret)
           | none => (pure chE : SpqrApiResult Chain)) = .ok chain1 ∧
          (do
            let (chain2, msgKey) ←
              SpqrApiResult.ofChainResult (chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index)
            let newStateBytes := (spqrDeps F K).encodeState {
              inner := some ((spqrDeps F K).statesIntoPb st1)
              versionNegotiation := none
              chain := some chain2.intoPb
            }
            let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
            (.ok { state := newStateBytes, key := outKey } : SpqrApiResult Recv)) = .ok r := by
      cases key with
      | none => exact ⟨chE, rfl, hre4⟩
      | some es => exact treq_bind_ok hre4
    rcases hstep1 with ⟨chain1, hch1, hre5⟩
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
        rcases chainCur_recv_key F K st st1 m es hep_pos hrecvB with ⟨hes_ep, _⟩
        have := hw.htop.hcur
        have hne : e ≠ es.epoch.toNat := by omega
        exact Function.update_of_ne hne es.secret secret
    have hchain1_facts :
        ChainOk F authKey dir secret' sendCtr recvSet chain1 ∧
        chain1.currentEpoch.toNat = chainCur st1 ∧
        chain1.sendEpoch = chE.sendEpoch ∧
        SendPrevNil chain1 ∧
        RecvSmall chain1 := by
      cases key with
      | none =>
        change (pure chE : SpqrApiResult Chain) = .ok chain1 at hch1
        cases hch1
        have hcur1 := chainCur_recv_none F K st st1 m hep_pos hrecvB
        exact ⟨hok', by rw [hw.htop.hcur, hcur1], rfl, hw.htop.hsendPrev, hw.hsmall⟩
      | some es =>
        have hadd : chE.addEpoch (spqrHkdfWith F) es = .ok chain1 := by
          cases ha : chE.addEpoch (spqrHkdfWith F) es with
          | error p => simp [SpqrApiResult.ofChainPanic, ha] at hch1
          | ok c1 =>
            simp [SpqrApiResult.ofChainPanic, ha] at hch1
            subst hch1
            rfl
        rcases chainCur_recv_key F K st st1 m es hep_pos hrecvB with ⟨hes_ep, hcur1⟩
        have hep_es : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by
          have := hw.htop.hcur
          omega
        have hsec_es : es.secret = secret' (chE.currentEpoch.toNat + 1) := by
          have hEq : es.epoch.toNat = chE.currentEpoch.toNat + 1 := hep_es
          simp [secret', ← hEq]
        rcases addEpoch_ok F authKey dir secret' sendCtr recvSet chE hok' es hep_es hsec_es with
          ⟨chain1', hadd', hce1, hse1, hok1'⟩
        rw [hadd] at hadd'
        cases hadd'
        exact ⟨hok1', by rw [hce1]; omega, hse1,
          addEpoch_sendPrevNil (spqrHkdfWith F) chE chain1 es hw.htop.hsendPrev hadd,
          hAdd (spqrHkdfWith F) chE chain1 es hw.hsmall hadd⟩
    rcases hchain1_facts with ⟨hok1, hcur1, hse1, hprev1, hsmall1⟩
    rcases treq_bind_ok hre5 with ⟨⟨chain2, msgKey⟩, hrk_res, hre6⟩
    have hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, msgKey) := by
      cases hr : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
      | error e =>
        cases e <;> simp [SpqrApiResult.ofChainResult, hr] at hrk_res
      | ok cm =>
        simp [SpqrApiResult.ofChainResult, hr] at hrk_res
        subst hrk_res
        rfl
    rcases hCR authKey dir secret' sendCtr recvSet chain1 chain2 (pre.epoch - 1#64) pre.index
        msgKey hok1 hsmall1 hrk with
      ⟨recvSet', hok2, hsmall2, hce2, hse2⟩
    have hprev2 : SendPrevNil chain2 :=
      recvKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 (pre.epoch - 1#64) pre.index msgKey hprev1 hrk
    change (.ok { state := topBytes F K st1 none (some chain2), key := _ } : SpqrApiResult Recv) = .ok r at hre6
    cases hre6
    refine ⟨authKey, dir, secret', st1, sendEp, sendCtr, recvSet', none, some chain2, chain2, ?_⟩
    refine
      { htop :=
          { hbytes := rfl
            hvn := Or.inl rfl
            hch := Or.inl rfl
            hok := hok2
            hcur := by rw [hce2]; exact hcur1
            hsendEp := by rw [hse2, hse1]; exact hw.htop.hsendEp
            hsendLe := by
              have := hw.htop.hsendLe
              omega
            hsendPrev := hprev2 }
        hauth := hw.hauth
        hbok := hbok1
        hphi := hphi1
        hctr := hw.hctr
        hsmall := hsmall2 }

end CryptoVerification.SpqrV1Sync.SendTotal
