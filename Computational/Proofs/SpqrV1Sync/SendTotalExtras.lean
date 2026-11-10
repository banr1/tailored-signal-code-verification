/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopBytesSize
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecvEqual
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainRecv
import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Assembly
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidPhi
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidRecvCt
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidRecvEk
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidSendClosed
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidSize
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainDir
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainPrev
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainSmall
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Erasure
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ErasureDecAdd
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ErasureDecMsg
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
import ProofLib.BV.WidthNorm
import ProofLib.SepLogic.WP.StateNorm

/-!
# SPQR V1 Reachable-State Invariant and Message-Length Bound

Defines the unbounded reachable-state invariant `TopStateW` (`phiB st ≤ sendEp + 1`) and
deterministic receive-salt evaluation `evalSaltFromSeed` for `spqrV1SessionUniformCoins`, and
proves that every sent message fits within `rustLenBound` (`spqrV1Send_msg_len_lt`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawVN rawChain rawEpochDir rawV1State)
open CryptoGames.LibsignalSession (ShaCompress SpqrDirection)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSM.Corr

/-! ## Unbounded reachable-state invariant -/

/-- Witness bundle for a reachable SPQR V1 party state. -/
structure TopWitness (F : ShaCompress) where
  authKey : Bytes
  dir : Direction
  secret : ℕ → Bytes
  st : St F
  sendEp : ℕ
  sendCtr : ℕ → ℕ
  recvSet : ℕ → Finset ℕ
  vn? : Option VersionNegotiationPB
  ch? : Option Chain
  chE : Chain

/-- Unbounded reachable-state invariant bounding active chain links via `phiB w.st ≤ w.sendEp + 1`
so that `bytes.length < 2 ^ 64`. -/
structure TopStateW (F : ShaCompress) (K : MlKem) (bytes : Bytes) (w : TopWitness F) : Prop where
  htop : PartyTopW F K w.authKey w.dir w.secret w.st w.sendEp w.sendCtr w.recvSet bytes
    w.vn? w.ch? w.chE
  hauth : w.authKey.length = 32
  hbok : BOk w.st
  hphi : phiB w.st ≤ w.sendEp + 1
  hsmall : RecvSmall w.chE

def TopState (F : ShaCompress) (K : MlKem) (bytes : Bytes) : Prop :=
  ∃ w : TopWitness F, TopStateW F K bytes w

theorem topStateW_length_lt (F : ShaCompress) (K : MlKem) {bytes : Bytes} {w : TopWitness F}
    (hw : TopStateW F K bytes w) : bytes.length < 2 ^ 64 := by
  have htop := topBytes_length_le F K w.st w.vn? w.ch?
  rw [← hw.htop.hbytes] at htop
  have hvn : optRaw rawVN w.vn? ≤ w.authKey.length := by
    rcases hw.htop.hvn with h | h <;> rw [h]
    · exact Nat.zero_le _
    · exact le_refl _
  have hch : optRaw rawChain (w.ch?.map Chain.intoPb) ≤ 3 * (2 ^ 20 + 264) + 32 := by
    rcases hw.htop.hch with h | ⟨h, -, -⟩
    · rw [h]
      dsimp only [Option.map, optRaw]
      have hroot : w.chE.nextRoot.length = 32 := by rw [hw.htop.hok.hroot]; simp
      have hlen := hw.htop.hok.hlen
      have hcur := hw.htop.hcur
      have hsendEp := hw.htop.hsendEp
      have hcur_le := chainCur_le_phiB w.st
      have hphi := hw.hphi
      have hlinks :
          (w.chE.links.map (fun l =>
            rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb + 200)).sum ≤
            w.chE.links.length * (2 ^ 20 + 264) := by
        have hsum := List.sum_le_length_nsmul
          (w.chE.links.map (fun l =>
            rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb + 200))
          (2 ^ 20 + 264) (fun x hx => by
            rcases List.mem_map.mp hx with ⟨l, hl, rfl⟩
            exact tsz_link_le F w.authKey w.dir w.secret w.sendCtr w.recvSet w.chE
              hw.htop.hok hw.htop.hsendPrev hw.hsmall l hl)
        simpa using hsum
      have heq : rawChain w.chE.intoPb =
          (w.chE.links.map (fun l =>
            rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb + 200)).sum +
            w.chE.nextRoot.length := by
        simp only [rawChain, Chain.intoPb, List.map_map, Function.comp_def]
        rfl
      rw [heq, hroot]
      omega
    · rw [h]; exact Nat.zero_le _
  have hbraid : rawV1State w.st.into_pb ≤ 2 ^ 40 := st_bSize F w.st hw.hbok
  have hauth := hw.hauth
  omega

theorem topState_init (F : ShaCompress) (K : MlKem) (dir : SpqrDirection) (k : BitVec 256) :
    TopState F K ((spqrV1SessionUniformCoins F K).init dir k) := by
  obtain ⟨authKey, d, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ :=
    (topStmts F K).init dir k
  exact ⟨⟨authKey, d, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE⟩,
    hw.htop, hw.hauth, hw.hbok, hw.hphi.trans (Nat.zero_le _), hw.hsmall⟩

private theorem nextKey_err_of_ge (F : ShaCompress) (seed : Bytes) (hseed : seed.length = 32)
    (n : ℕ) (d : ChainEpochDirection) (hd : SendDirOk F seed n d) (hn : ¬ (n + 1 < 2 ^ 32)) :
    d.nextKey (spqrHkdfWith F) = .error .ctrOverflow := by
  have hlen : (d.next.length != 32) = false := by
    rw [hd.hnext, length_nextAt F seed hseed n]
    rfl
  have heq : (d.ctr == 0xffffffff#32) = true := by
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    have hlt := d.ctr.isLt
    have hctr := hd.hctr
    change d.ctr.toNat = 4294967295
    omega
  unfold ChainEpochDirection.nextKey ChainEpochDirection.nextKeyInternal
  rw [hlen, heq]
  rfl

private theorem sendKey_at_sendEpoch_err_of_ge (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch1 : Chain)
    (h1 : ChainOk F authKey dir secret sendCtr recvSet ch1) (e : Epoch)
    (he : ch1.sendEpoch = e) (hhi : e.toNat ≤ ch1.currentEpoch.toNat)
    (hn : ¬ (sendCtr e.toNat + 1 < 2 ^ 32))
    (epochIndex : ℕ) (hidx : epochIndex = e.toNat - (e.toNat - 1)) :
    ((match ch1.links[epochIndex]? with
      | none => .error (.panic .linksOutOfBounds)
      | some link => do
        let (send', out) ← ChainResult.ofPanic (link.send.nextKey (spqrHkdfWith F))
        let links' := ch1.links.set epochIndex { link with send := send' }
        return ({ ch1 with links := links' }, out)) :
        ChainResult (Chain × (BitVec 32 × Bytes))) = .error (.panic .ctrOverflow) := by
  have he_lo : ch1.sendEpoch.toNat ≤ e.toNat := by rw [he]
  rcases h1.hsendDir e.toNat he_lo hhi with ⟨link, hlink, hsendOk⟩
  have hidx_eq : epochIndex = e.toNat - (ch1.sendEpoch.toNat - 1) := by rw [he, hidx]
  rw [← hidx_eq] at hlink
  have hnk := nextKey_err_of_ge F (seedAt F authKey secret dir e.toNat)
    (length_seedAt F authKey secret dir e.toNat) (sendCtr e.toNat) link.send hsendOk hn
  rw [hlink]
  dsimp only
  rw [hnk]
  rfl

theorem sendKey_err_of_ge (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (e : Epoch)
    (hlo : ch.sendEpoch.toNat ≤ e.toNat) (hhi : e.toNat ≤ ch.currentEpoch.toNat)
    (hn : ¬ (sendCtr e.toNat + 1 < 2 ^ 32)) :
    ch.sendKey (spqrHkdfWith F) e = .error (.panic .ctrOverflow) := by
  have hlt_false : ¬(e < ch.sendEpoch) := by
    simp only [BitVec.lt_def, not_lt]
    exact hlo
  have hepIdx := chs_epochIdx_eq ch e h.hlen (by omega) hhi
  unfold Chain.sendKey
  simp only [hlt_false, ↓reduceIte, hepIdx, ChainResult.ofError, bind, Except.bind]
  by_cases hne : (ch.sendEpoch != e) = true
  · simp only [hne, ↓reduceIte]
    have hlt : ch.sendEpoch.toNat < e.toNat := by
      have hne' : ch.sendEpoch ≠ e := by simpa [bne_iff_ne] using hne
      have : ch.sendEpoch.toNat ≠ e.toNat := fun heq => hne' (BitVec.eq_of_toNat_eq heq)
      omega
    have h1 := chs_advance_sendEpoch_ok F authKey dir secret sendCtr recvSet ch h e hlt hhi
    let epochIndex0 := e.toNat - (ch.sendEpoch.toNat - 1)
    let dropCount := epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
    let epochIndex' := epochIndex0 - dropCount
    exact sendKey_at_sendEpoch_err_of_ge F authKey dir secret sendCtr recvSet _ h1 e rfl hhi hn
      epochIndex'
      (by dsimp [epochIndex', dropCount, epochIndex0, EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH]; omega)
  · simp only [Bool.not_eq_true] at hne
    have heq : ch.sendEpoch = e := by simpa [bne_eq_false_iff_eq] using hne
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact sendKey_at_sendEpoch_err_of_ge F authKey dir secret sendCtr recvSet ch h e heq hhi hn
      (e.toNat - (ch.sendEpoch.toNat - 1)) (by rw [heq])

private theorem seedAt_congr (F : ShaCompress) (authKey : Bytes) (secret secret' : ℕ → Bytes)
    (dir : Direction) (e : ℕ) (hs : ∀ i, 1 ≤ i → i ≤ e → secret' i = secret i) :
    seedAt F authKey secret' dir e = seedAt F authKey secret dir e := by
  simp only [seedAt, genAt_congr F authKey secret secret' e hs]

theorem sendAfterStates_err_of_sendKey_err (F : ShaCompress) (K : MlKem) (authKey : Bytes)
    (dir : Direction) (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (vn? : Option VersionNegotiationPB) (ch? : Option Chain)
    (chE chain1 : Chain)
    (hch : ch? = some chE ∨
      (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
        chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE))
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (m : Msg) (key : Option EpochSecret)
    (hadd : (match key with
      | some es => chE.addEpoch (spqrHkdfWith F) es
      | none => .ok chE) = .ok chain1)
    (he_ne0 : (m.epoch == 0#64) = false)
    (hsk : chain1.sendKey (spqrHkdfWith F) (m.epoch - 1#64) = .error (.panic .ctrOverflow)) :
    sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (topPb st vn? ch?) m key st' =
      .error (.panic (.chain .ctrOverflow)) := by
  have hfp := chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hok
  have hslt : BitVec.slt Version.v0.toI32 (vnOf dir authKey).minVersion = true := rfl
  cases key with
  | none =>
    cases hadd
    rcases hch with rfl | ⟨rfl, rfl, hvnE⟩
    · simp [sendAfterStates, topPb, Option.map, tsnd_spqrDeps_msgEpoch,
        hfp, he_ne0, hsk, SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
        SpqrApiError.ofChainError, bind, Except.bind, pure, Except.pure]
    · simp [sendAfterStates, topPb, Option.map, tsnd_spqrDeps_msgEpoch,
        hslt, hvnE, he_ne0, hsk, SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
        SpqrApiError.ofChainError, bind, Except.bind, pure, Except.pure]
  | some es =>
    dsimp only at hadd
    rcases hch with rfl | ⟨rfl, rfl, hvnE⟩
    · simp [sendAfterStates, topPb, Option.map, tsnd_spqrDeps_msgEpoch,
        hfp, hadd, he_ne0, hsk, SpqrApiResult.ofError, SpqrApiResult.ofChainPanic,
        SpqrApiResult.ofChainResult, SpqrApiError.ofChainError, bind, Except.bind, pure, Except.pure]
    · simp [sendAfterStates, topPb, Option.map, tsnd_spqrDeps_msgEpoch,
        hslt, hvnE, hadd, he_ne0, hsk, SpqrApiResult.ofError, SpqrApiResult.ofChainPanic,
        SpqrApiResult.ofChainResult, SpqrApiError.ofChainError, bind, Except.bind, pure, Except.pure]

theorem topStateW_send (F : ShaCompress) (K : MlKem) {bytes bytes' : Bytes} {r : BitVec 512}
    {salt : Salt} {msg : Bytes} {w : TopWitness F} (hw : TopStateW F K bytes w)
    (hsend : (spqrV1SessionUniformCoins F K).send bytes r = some (bytes', salt, msg)) :
    ∃ w' : TopWitness F,
      TopStateW F K bytes' w' ∧
      w'.authKey = w.authKey ∧
      w'.dir = w.dir ∧
      w.chE.currentEpoch.toNat ≤ w'.chE.currentEpoch.toNat ∧
      (∀ e ≤ w.chE.currentEpoch.toNat,
        seedAt F w'.authKey w'.secret w'.dir.switch e =
          seedAt F w.authKey w.secret w.dir.switch e) := by
  have hsize : bytes.length < 2 ^ 64 := topStateW_length_lt F K hw
  have hsize' : (topBytes F K w.st w.vn? w.ch?).length < 2 ^ 64 := hw.htop.hbytes ▸ hsize
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) w.st.into_pb = .ok w.st :=
    st_bCodec F w.st hw.hbok
  let tape := coinBytes r
  rcases hsendB : w.st.send K tape with err | ⟨⟨m, key, st'⟩, tape'⟩
  · exfalso
    change (spqrV1 F K).send bytes tape = some (bytes', salt, msg) at hsend
    rw [spqrV1_eq, toSpqrModel] at hsend
    dsimp only at hsend
    rw [hw.htop.hbytes] at hsend
    unfold LibsignalSpqrV1.send at hsend
    rw [decodeState_topBytes F K w.st w.vn? w.ch? hsize'] at hsend
    rcases err with e | p <;> simp [topPb, spqrDeps, hcodec, liftStatesResult, hsendB] at hsend
  · have hep_pos : 1 ≤ w.st.epoch.toNat := by have := hw.htop.hsendLe; omega
    obtain ⟨hm_ep, hst'_ep, -, -⟩ := send_facts F K w.st st' tape tape' m key hsendB
    have htop := send_topBytes F K w.st st' w.vn? w.ch? tape tape' m key hsize' hcodec hsendB
    let secret' : ℕ → Bytes :=
      match key with
      | none => w.secret
      | some es => Function.update w.secret (chainCur w.st + 1) es.secret
    have hsec_eq : ∀ e, 1 ≤ e → e ≤ w.chE.currentEpoch.toNat → secret' e = w.secret e := by
      intro e _ he
      have hcur := hw.htop.hcur
      cases key with
      | none => rfl
      | some es => exact Function.update_of_ne (by omega) _ _
    have hok' : ChainOk F w.authKey w.dir secret' w.sendCtr w.recvSet w.chE :=
      chainOk_congr F w.authKey w.dir w.secret secret' w.sendCtr w.recvSet w.chE hw.htop.hok hsec_eq
    have hsec : ∀ es, key = some es → es.secret = secret' es.epoch.toNat := by
      intro es hk
      subst hk
      obtain ⟨hes_ep, -⟩ := chainCur_send_key F K w.st st' tape tape' m es hep_pos hsendB
      change es.secret = Function.update w.secret (chainCur w.st + 1) es.secret es.epoch.toNat
      rw [hes_ep, Function.update_self]
    obtain ⟨chain1, hadd, hok1, hcur1, hsend1, hle1⟩ :=
      tsnd_send_addEpoch F K w.authKey w.dir secret' w.st st' w.sendCtr w.recvSet w.chE hok'
        hw.htop.hcur hep_pos tape tape' m key hsendB hsec
    have he_ne0 : (m.epoch == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
      rw [hm_ep] at this
      omega
    have hebv_nat : (m.epoch - 1#64).toNat = w.st.epoch.toNat - 1 := by
      rw [hm_ep, BitVec.toNat_sub_of_le]
      · rfl
      · show 1 ≤ w.st.epoch.toNat
        exact hep_pos
    have hlo : chain1.sendEpoch.toNat ≤ (m.epoch - 1#64).toNat := by
      rw [hsend1, hw.htop.hsendEp, hebv_nat]
      have := hw.htop.hsendLe
      omega
    have hhi : (m.epoch - 1#64).toNat ≤ chain1.currentEpoch.toNat := by
      rw [hebv_nat]
      exact (epoch_sub_one_le_chainCur w.st).trans hle1
    have hctr_lt : w.sendCtr (m.epoch - 1#64).toNat + 1 < 2 ^ 32 := by
      by_contra hge
      have herr := sendKey_err_of_ge F w.authKey w.dir secret' w.sendCtr w.recvSet chain1 hok1
        (m.epoch - 1#64) hlo hhi hge
      have hafter := sendAfterStates_err_of_sendKey_err F K w.authKey w.dir secret' w.st st'
        w.sendCtr w.recvSet w.vn? w.ch? w.chE chain1 hw.htop.hch hok' m key hadd he_ne0 herr
      change (spqrV1 F K).send bytes tape = some (bytes', salt, msg) at hsend
      rw [spqrV1_eq, toSpqrModel] at hsend
      dsimp only at hsend
      rw [hw.htop.hbytes, htop, hafter] at hsend
      nomatch hsend
    obtain ⟨chain2, hsk, hcur2, hsend2, hok2⟩ :=
      sendKey_ok F w.authKey w.dir secret' w.sendCtr w.recvSet chain1 hok1 (m.epoch - 1#64)
        hlo hhi hctr_lt
    rw [hebv_nat] at hsk hok2
    have hafter := tsnd_sendAfterStates_ok F K w.authKey w.dir secret' w.st st' w.sendCtr w.recvSet
      w.vn? w.ch? w.chE chain1 chain2 hw.htop.hch hok' m key hadd he_ne0
      (BitVec.ofNat 32 (w.sendCtr (w.st.epoch.toNat - 1) + 1))
      (w.sendCtr (w.st.epoch.toNat - 1))
      (seedAt F w.authKey secret' w.dir (w.st.epoch.toNat - 1)) hsk
    change (spqrV1 F K).send bytes tape = some (bytes', salt, msg) at hsend
    rw [spqrV1_eq, toSpqrModel] at hsend
    dsimp only at hsend
    rw [hw.htop.hbytes, htop, hafter] at hsend
    dsimp only at hsend
    rw [tsnd_messageKeyToSalt_keyAt] at hsend
    simp only [Option.some.injEq, Prod.mk.injEq] at hsend
    obtain ⟨hbytes', -, -⟩ := hsend
    have hsp1 := tsnd_addEpoch_opt (spqrHkdfWith F) w.chE chain1 key hw.htop.hsendPrev hadd
    have hsmall1 : RecvSmall chain1 := by
      cases key with
      | none => cases hadd; exact hw.hsmall
      | some es => exact st_recvSmallAdd (spqrHkdfWith F) w.chE chain1 es hw.hsmall hadd
    have hSC := st_bSendClosed F K st_encNew st_encNext
    refine ⟨⟨w.authKey, w.dir, secret', st', w.st.epoch.toNat - 1,
      Function.update w.sendCtr (w.st.epoch.toNat - 1) (w.sendCtr (w.st.epoch.toNat - 1) + 1),
      w.recvSet, w.vn?, some chain2, chain2⟩, ?_, rfl, rfl, ?_, ?_⟩
    · refine
        { htop :=
            { hbytes := hbytes'.symm
              hvn := hw.htop.hvn
              hch := .inl rfl
              hok := hok2
              hcur := by rw [hcur2, hcur1]
              hsendEp := by rw [hsend2, hebv_nat]
              hsendLe := by dsimp only; rw [hst'_ep]; omega
              hsendPrev := sendKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 _ _ hsp1 hsk }
          hauth := hw.hauth
          hbok := hSC w.st st' tape tape' m key hw.hbok hsendB
          hphi := by
            dsimp only [phiB]
            rw [hst'_ep]
            split <;> omega
          hsmall := st_recvSmallSend (spqrHkdfWith F) chain1 chain2 _ _ hsmall1 hsk }
    · dsimp only
      rw [hcur2, hw.htop.hcur]
      exact hle1
    · intro e he
      exact seedAt_congr F w.authKey w.secret secret' w.dir.switch e
        (fun i h1 hi => hsec_eq i h1 (hi.trans he))

/-! ## Receive-salt evaluation and `SpqrReachFrom` preservation -/

/-- Chain epoch queried by `Top.recv` (`0` when `pre.version > 1`, `(pre.epoch - 1).toNat` otherwise). -/
def msgChainEpoch (pre : MsgPreamble) : ℕ :=
  if pre.version > 1#8 then 0 else (pre.epoch - 1#64).toNat

/-- Deterministic receive-salt evaluator from the seed of `msgChainEpoch pre`. -/
def evalSaltFromSeed (F : ShaCompress) (pre : MsgPreamble) (seed : Bytes) : Salt :=
  if msgChainEpoch pre = 0 ∧ pre.index = 0#32 then
    none
  else
    some ⟨keyAt F seed (pre.index.toNat - 1), length_keyAt F seed (pre.index.toNat - 1)⟩

private theorem message_deserialize_epoch (P : PolyApi) (ep : Epoch) (rem : Bytes)
    (m : Message P) (h : Message.deserialize P ep rem = .ok m) : m.epoch = ep := by
  rcases rem with _ | ⟨b0, rest⟩
  · cases h
  · dsimp only [Message.deserialize] at h
    cases hmt : MessageType.tryFromU8 b0 with
    | none => rw [hmt] at h; cases h
    | some mt =>
      rw [hmt] at h
      dsimp only [bind, Except.bind, pure, Except.pure] at h
      cases mt <;>
        (try (cases hdec : decode_chunk P rest <;> rw [hdec] at h)) <;>
        cases h <;> rfl

private theorem msgDeserialize_epoch (F : ShaCompress) (K : MlKem) (ep : Epoch) (rem : Bytes)
    (m : Msg) (h : (spqrDeps F K).msgDeserialize ep rem = .ok m) : m.epoch = ep := by
  apply message_deserialize_epoch spqrPolyApi ep rem m
  dsimp only [spqrDeps] at h
  revert h
  cases Message.deserialize spqrPolyApi ep rem <;> simp

private theorem recv_epoch_le_of_keyedB_false (F : ShaCompress) (K : MlKem) (st : St F)
    (m : Msg) (v : V1Recv spqrPolyApi (spqrAuthApi F)) (hk : keyedB st = false)
    (h : st.recv K m = .ok v) : m.epoch.toNat ≤ st.epoch.toNat := by
  cases st <;> try cases hk
  all_goals
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      simp only [gt_iff_lt, BitVec.lt_def, not_lt] at hgt
      exact hgt

private theorem recvKey_eval (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch ch' : Chain)
    (e : Epoch) (idx : BitVec 32) (rawKey : Bytes)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch)
    (hrecv : ch.recvKey (spqrHkdfWith F) e idx = .ok (ch', rawKey)) :
    e.toNat ≤ ch.currentEpoch.toNat ∧
      ((e.toNat = 0 ∧ idx = 0#32 ∧ rawKey = []) ∨
       (1 ≤ idx.toNat ∧
        rawKey = keyAt F (seedAt F authKey secret dir.switch e.toNat) (idx.toNat - 1))) := by
  unfold Chain.recvKey at hrecv
  by_cases hzero : (e == 0#64 && idx == 0#32) = true
  · simp only [hzero, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hrecv
    simp only [Bool.and_eq_true, beq_iff_eq] at hzero
    rcases hzero with ⟨rfl, rfl⟩
    exact ⟨Nat.zero_le _, Or.inl ⟨rfl, rfl, hrecv.2.symm⟩⟩
  · simp only [Bool.not_eq_true] at hzero
    simp only [hzero, Bool.false_eq_true, ↓reduceIte] at hrecv
    cases hep : ch.epochIdx e with
    | error _ => rw [hep] at hrecv; nomatch hrecv
    | ok epochIndex =>
      obtain ⟨hlo, hhi, rfl⟩ := crcv_epochIdx_eq h.hsend_le h.hlen hep
      obtain ⟨link, hlink, hrecvD⟩ := h.hrecvDir e.toNat hlo hhi
      rw [hep] at hrecv
      simp only [ChainResult.ofError, bind, Except.bind, hlink] at hrecv
      cases hkey : link.recv.key (spqrHkdfWith F) idx ch.params with
      | error _ => rw [hkey] at hrecv; nomatch hrecv
      | ok p =>
        rcases p with ⟨recv', out'⟩
        rw [hkey] at hrecv
        cases hrecv
        rw [h.hparams] at hkey
        have hseed := length_seedAt F authKey secret dir.switch e.toNat
        obtain ⟨_, h1, hout, _⟩ :=
          st_recvDir F (seedAt F authKey secret dir.switch e.toNat) (recvSet e.toNat)
            link.recv recv' idx out' hseed hrecvD hkey
        exact ⟨hhi, Or.inr ⟨h1, hout⟩⟩

private theorem recvKeyToSalt?_of_length_eq_32 (k : Bytes) (hk : k.length = 32) :
    recvKeyToSalt? (some k) = some (some ⟨k, hk⟩) := by
  cases k with
  | nil => cases hk
  | cons b bs => simp [recvKeyToSalt?, messageKeyToSalt?, hk]

private theorem recvKeyToSalt_keyAt (F : ShaCompress) (seed : Bytes) (n : ℕ) :
    recvKeyToSalt? (some (keyAt F seed n)) =
      some (some ⟨keyAt F seed n, length_keyAt F seed n⟩) :=
  recvKeyToSalt?_of_length_eq_32 (keyAt F seed n) (length_keyAt F seed n)

private def addEpochSecret (secret : ℕ → Bytes) (cur : ℕ) : Option EpochSecret → ℕ → Bytes
  | none => secret
  | some es => Function.update secret (cur + 1) es.secret

private theorem recv_addEpoch_explicit (F : ShaCompress) (K : MlKem) (authKey : Bytes)
    (dir : Direction) (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (chE : Chain)
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (hcur : chE.currentEpoch.toNat = chainCur st) (hep_pos : 1 ≤ st.epoch.toNat)
    (hsmall : RecvSmall chE) (hsp : SendPrevNil chE)
    (m : Msg) (key : Option EpochSecret)
    (hrecvB : st.recv K m = .ok { key := key, state := st' }) :
    ∃ chain1 : Chain,
      (match key with
       | some es => SpqrApiResult.ofChainPanic (chE.addEpoch (spqrHkdfWith F) es)
       | none => pure chE) = .ok chain1 ∧
      ChainOk F authKey dir (addEpochSecret secret chE.currentEpoch.toNat key)
        sendCtr recvSet chain1 ∧
      chain1.currentEpoch.toNat = chainCur st' ∧
      chain1.sendEpoch = chE.sendEpoch ∧
      chE.currentEpoch.toNat ≤ chain1.currentEpoch.toNat ∧
      RecvSmall chain1 ∧
      SendPrevNil chain1 := by
  cases key with
  | none =>
    have hc := chainCur_recv_none F K st st' m hep_pos hrecvB
    exact ⟨chE, rfl, hok, by rw [hcur, hc], rfl, le_rfl, hsmall, hsp⟩
  | some es =>
    obtain ⟨hes_ep, hc'⟩ := chainCur_recv_key F K st st' m es hep_pos hrecvB
    have hep : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by omega
    have hok1 : ChainOk F authKey dir
        (addEpochSecret secret chE.currentEpoch.toNat (some es)) sendCtr recvSet chE :=
      chainOk_congr F authKey dir secret _ sendCtr recvSet chE hok
        (fun _ _ he => Function.update_of_ne (by omega) _ _)
    have hsec1 : es.secret =
        addEpochSecret secret chE.currentEpoch.toNat (some es) (chE.currentEpoch.toNat + 1) :=
      (Function.update_self (chE.currentEpoch.toNat + 1) es.secret secret).symm
    obtain ⟨ch1, hadd, hcur1, hsend1, hok'⟩ :=
      addEpoch_ok F authKey dir _ sendCtr recvSet chE hok1 es hep hsec1
    refine ⟨ch1, ?_, hok', ?_, hsend1, ?_,
      st_recvSmallAdd (spqrHkdfWith F) chE ch1 es hsmall hadd,
      addEpoch_sendPrevNil (spqrHkdfWith F) chE ch1 es hsp hadd⟩
    · simp [hadd, SpqrApiResult.ofChainPanic]
    · rw [hcur1, hes_ep, hc']
    · rw [hcur1, hes_ep]; omega

theorem topStateW_recv (F : ShaCompress) (K : MlKem) {bytes msg bytes' : Bytes} {salt : Salt}
    {w : TopWitness F} (hw : TopStateW F K bytes w)
    (hrecv : (spqrV1SessionUniformCoins F K).recv bytes msg = .ok (bytes', salt)) :
    ∃ (pre : MsgPreamble) (w' : TopWitness F),
      msgPreamble msg = .ok pre ∧
      msgChainEpoch pre ≤ w.chE.currentEpoch.toNat ∧
      salt = evalSaltFromSeed F pre
        (seedAt F w.authKey w.secret w.dir.switch (msgChainEpoch pre)) ∧
      TopStateW F K bytes' w' ∧
      w'.authKey = w.authKey ∧
      w'.dir = w.dir ∧
      w.chE.currentEpoch.toNat ≤ w'.chE.currentEpoch.toNat ∧
      (∀ e ≤ w.chE.currentEpoch.toNat,
        seedAt F w'.authKey w'.secret w'.dir.switch e =
          seedAt F w.authKey w.secret w.dir.switch e) := by
  have hsize : bytes.length < 2 ^ 64 := topStateW_length_lt F K hw
  have htop := hw.htop
  have hCR : ChainRecvStmt F := st_chainRecv F (st_recvDir F) (st_recvPrev F)
  have hBC : BCodecStmt F := st_bCodec F
  have hPhi : BPhiStmt F K := st_bPhi F K
  have hEk : BRecvEkStmt F K := st_bRecvEk F K st_decFresh st_decAdd st_decMsg st_encNew
  have hCt : BRecvCtStmt F K := st_bRecvCt F K st_decFresh st_decAdd st_decMsg st_encNew
  change (spqrV1 F K).recv bytes msg = .ok (bytes', salt) at hrecv
  rw [spqrV1_eq] at hrecv
  dsimp only [toSpqrModel] at hrecv
  cases hr : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) bytes msg with
  | error e =>
    rw [hr] at hrecv
    cases e <;> contradiction
  | ok r =>
    rw [hr] at hrecv
    dsimp only at hrecv
    cases hs : recvKeyToSalt? r.key with
    | none => rw [hs] at hrecv; contradiction
    | some s =>
      rw [hs] at hrecv
      cases hrecv
      have hsize' : (topBytes F K w.st w.vn? w.ch?).length < 2 ^ 64 := htop.hbytes ▸ hsize
      rw [htop.hbytes] at hr
      cases hpre : msgPreamble msg with
      | error e =>
        unfold LibsignalSpqrV1.recv at hr
        simp [hpre, SpqrApiResult.ofError, bind, Except.bind] at hr
      | ok pre =>
        by_cases hver : pre.version = 1#8
        · rw [recv_topBytes F K w.authKey w.dir w.st w.vn? w.ch? msg pre hsize' htop.hvn
            hpre hver] at hr
          have hep_pos : 1 ≤ w.st.epoch.toNat := partyTop_epoch_pos ⟨w.vn?, w.ch?, w.chE, htop⟩
          unfold recvEqual at hr
          cases hdes : (spqrDeps F K).msgDeserialize pre.epoch pre.remaining with
          | error _ => rw [hdes] at hr; contradiction
          | ok m =>
            rw [hdes, treq_spqrDeps_statesFromPb F K w.st (hBC w.st hw.hbok)] at hr
            dsimp [bind, Except.bind] at hr
            cases hsr : (spqrDeps F K).statesRecv w.st m with
            | error _ => rw [hsr] at hr; contradiction
            | ok ks =>
              rcases ks with ⟨key, st'⟩
              rw [hsr] at hr
              dsimp [bind, Except.bind] at hr
              have hrecvB := treq_statesRecv_ok F K w.st st' m key hsr
              split_ifs at hr with hep0
              have hcf := st_chainFrom_ok F w.authKey w.dir w.secret w.sendCtr w.recvSet
                w.vn? w.ch? w.chE htop.hch htop.hok
              let secret1 : ℕ → Bytes := addEpochSecret w.secret w.chE.currentEpoch.toNat key
              have hsec_eq : ∀ e, 1 ≤ e → e ≤ w.chE.currentEpoch.toNat →
                  secret1 e = w.secret e := by
                intro e _ he
                cases key with
                | none => rfl
                | some es => exact Function.update_of_ne (by omega) _ _
              obtain ⟨chain1, hadd, hok1, hcur1, hsend1, hle_cur1, hsmall1, hsp1⟩ :=
                recv_addEpoch_explicit F K w.authKey w.dir w.secret w.st st'
                  w.sendCtr w.recvSet w.chE htop.hok htop.hcur hep_pos hw.hsmall
                  htop.hsendPrev m key hrecvB
              rw [hcf] at hr
              obtain ⟨chain2, msgKey, hrk, rfl⟩ :
                  ∃ chain2 msgKey,
                    chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index =
                      .ok (chain2, msgKey) ∧
                    r = { state := (spqrDeps F K).encodeState
                            { inner := some ((spqrDeps F K).statesIntoPb st'),
                              versionNegotiation := none,
                              chain := some chain2.intoPb },
                          key := if msgKey.isEmpty then none else some msgKey } := by
                cases key with
                | none =>
                  cases hadd
                  dsimp [SpqrApiResult.ofError, SpqrApiResult.ofChainResult, pure, Except.pure,
                    bind, Except.bind] at hr
                  cases hrk : w.chE.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
                  | error _ => rw [hrk] at hr; contradiction
                  | ok cm => rw [hrk] at hr; cases hr; exact ⟨cm.1, cm.2, rfl, rfl⟩
                | some es =>
                  dsimp [SpqrApiResult.ofError, SpqrApiResult.ofChainResult, bind, Except.bind] at hadd hr
                  rw [hadd] at hr
                  dsimp at hr
                  cases hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
                  | error _ => rw [hrk] at hr; contradiction
                  | ok cm => rw [hrk] at hr; cases hr; exact ⟨cm.1, cm.2, rfl, rfl⟩
              obtain ⟨recvSet', hok2, hsmall2, hcur2, hsend2⟩ :=
                hCR w.authKey w.dir secret1 w.sendCtr w.recvSet chain1 chain2
                  (pre.epoch - 1#64) pre.index msgKey hok1 hsmall1 hrk
              obtain ⟨hle_ch1, hkey_eval⟩ :=
                recvKey_eval F w.authKey w.dir secret1 w.sendCtr w.recvSet chain1 chain2
                  (pre.epoch - 1#64) pre.index msgKey hok1 hrk
              have hmce : msgChainEpoch pre = (pre.epoch - 1#64).toNat := by
                simp [msgChainEpoch, hver]
              have hmce_le : msgChainEpoch pre ≤ w.chE.currentEpoch.toNat := by
                rw [hmce]
                cases key with
                | none =>
                  cases hadd
                  exact hle_ch1
                | some es =>
                  obtain ⟨-, hk⟩ := recv_facts F K w.st st' m (some es) hrecvB
                  rcases hk with ⟨h1, -⟩ | ⟨es', _, _, _, hk_false, _⟩
                  · exact absurd h1 (by simp)
                  · have hm_le :=
                      recv_epoch_le_of_keyedB_false F K w.st m _ hk_false hrecvB
                    have hm_eq := msgDeserialize_epoch F K pre.epoch pre.remaining m hdes
                    have hep_pos' : 1 ≤ pre.epoch.toNat := by
                      simp only [beq_iff_eq] at hep0
                      have : pre.epoch.toNat ≠ 0 := fun h => hep0 (BitVec.eq_of_toNat_eq h)
                      omega
                    have hsub : (pre.epoch - 1#64).toNat = pre.epoch.toNat - 1 := by
                      apply BitVec.toNat_sub_of_le
                      show 1 ≤ pre.epoch.toNat
                      exact hep_pos'
                    have hcur_eq : chainCur w.st = w.st.epoch.toNat - 1 := by
                      simp [chainCur, hk_false]
                    rw [hsub, ← hm_eq, htop.hcur, hcur_eq]
                    omega
              have hseed_eq :
                  seedAt F w.authKey secret1 w.dir.switch (pre.epoch - 1#64).toNat =
                    seedAt F w.authKey w.secret w.dir.switch (msgChainEpoch pre) := by
                rw [← hmce]
                exact seedAt_congr F w.authKey w.secret secret1 w.dir.switch (msgChainEpoch pre)
                  (fun i h1 hi => hsec_eq i h1 (hi.trans hmce_le))
              have hsalt : salt = evalSaltFromSeed F pre
                  (seedAt F w.authKey w.secret w.dir.switch (msgChainEpoch pre)) := by
                dsimp only at hs
                unfold evalSaltFromSeed
                rcases hkey_eval with ⟨he0, hidx0, rfl⟩ | ⟨hidx1, rfl⟩
                · have hcond : msgChainEpoch pre = 0 ∧ pre.index = 0#32 :=
                    ⟨hmce.trans he0, hidx0⟩
                  simp only [hcond, and_self, ↓reduceIte]
                  exact (Option.some.inj hs).symm
                · have hcond : ¬ (msgChainEpoch pre = 0 ∧ pre.index = 0#32) := by
                    rintro ⟨_, h0⟩
                    simp [h0] at hidx1
                  simp only [tsnd_keyAt_isEmpty, Bool.false_eq_true, ↓reduceIte, hseed_eq,
                    recvKeyToSalt_keyAt, Option.some.injEq] at hs
                  simp only [hcond, ↓reduceIte, hs.symm]
              refine ⟨pre, ⟨w.authKey, w.dir, secret1, st', w.sendEp, w.sendCtr, recvSet',
                none, some chain2, chain2⟩, rfl, hmce_le, hsalt, ?_, rfl, rfl, ?_, ?_⟩
              · refine
                  { htop :=
                      { hbytes := rfl
                        hvn := .inl rfl
                        hch := .inl rfl
                        hok := hok2
                        hcur := by rw [hcur2, hcur1]
                        hsendEp := by rw [hsend2, hsend1, htop.hsendEp]
                        hsendLe := htop.hsendLe.trans (treq_recv_epoch_le F K w.st st' m key hrecvB)
                        hsendPrev :=
                          recvKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 _ _ _ hsp1 hrk }
                    hauth := hw.hauth
                    hbok := by
                      cases hek : isEkSide w.st
                      · exact hCt w.st st' m key hek hw.hbok hrecvB
                      · exact hEk w.st st' m key hek hw.hbok hrecvB
                    hphi := (hPhi.2 w.st st' m key hrecvB).trans hw.hphi
                    hsmall := hsmall2 }
              · dsimp only
                rw [hcur2]
                exact hle_cur1
              · intro e he
                exact seedAt_congr F w.authKey w.secret secret1 w.dir.switch e
                  (fun i h1 hi => hsec_eq i h1 (hi.trans he))
        · have hcf := st_chainFrom_ok F w.authKey w.dir w.secret w.sendCtr w.recvSet
            w.vn? w.ch? w.chE htop.hch htop.hok
          rcases htop.hvn with hvn | hvn
          · rw [hvn] at hsize' hr hcf
            unfold LibsignalSpqrV1.recv at hr
            rw [hpre, decodeState_topBytes F K w.st none w.ch? hsize'] at hr
            dsimp only [spqrDeps, SpqrApiResult.ofError, bind, Except.bind, topPb, stateVersion,
              Version.toU8] at hr
            have hbne : (pre.version != 1#8) = true := bne_iff_ne.mpr hver
            by_cases hlt : pre.version < 1#8 <;> simp [hlt, hbne] at hr
          · rw [hvn] at hsize' hr hcf
            unfold LibsignalSpqrV1.recv at hr
            rw [hpre, decodeState_topBytes F K w.st (some (vnOf w.dir w.authKey)) w.ch? hsize']
              at hr
            by_cases hlt : pre.version < 1#8
            · change (if pre.version < 1#8 then
                Except.error (SpqrApiError.err Error.minimumVersion) else _) = Except.ok r at hr
              simp only [hlt, ↓reduceIte] at hr
              contradiction
            · have hgt : pre.version > 1#8 := by
                simp only [gt_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat] at hlt ⊢
                have hne : pre.version.toNat ≠ 1 := fun h => hver (BitVec.eq_of_toNat_eq h)
                omega
              change (if pre.version < 1#8 then _
                else if (pre.version != 1#8 && !true) = true then _
                else if (1#8 == 0#8) = true then _
                else if pre.version > 1#8 then
                  do
                    let chain0 ← SpqrApiResult.ofError
                      (chainFrom (spqrHkdfWith F) (w.ch?.map Chain.intoPb)
                        (some (vnOf w.dir w.authKey)))
                    let __x ← SpqrApiResult.ofChainResult
                      (chain0.recvKey (spqrHkdfWith F) 0#64 pre.index)
                    Except.ok {
                      key := some __x.2
                      state := topBytes F K w.st (some (vnOf w.dir w.authKey)) (some __x.1)
                    }
                else _) = Except.ok r at hr
              simp only [hlt, hgt, Bool.not_true, Bool.and_false, ↓reduceIte] at hr
              rw [hcf] at hr
              dsimp only [SpqrApiResult.ofError, SpqrApiResult.ofChainResult, bind, Except.bind] at hr
              cases hrk : w.chE.recvKey (spqrHkdfWith F) 0#64 pre.index with
              | error _ => rw [hrk] at hr; contradiction
              | ok cm =>
                rcases cm with ⟨chain1, rawKey⟩
                rw [hrk] at hr
                cases hr
                obtain ⟨recvSet', hok', hsmall', hcur', hsendEp'⟩ :=
                  hCR w.authKey w.dir w.secret w.sendCtr w.recvSet w.chE chain1 0#64 pre.index
                    rawKey htop.hok hw.hsmall hrk
                obtain ⟨_, hkey_eval⟩ :=
                  recvKey_eval F w.authKey w.dir w.secret w.sendCtr w.recvSet w.chE chain1
                    0#64 pre.index rawKey htop.hok hrk
                have hmce : msgChainEpoch pre = 0 := by simp [msgChainEpoch, hgt]
                have hsalt : salt = evalSaltFromSeed F pre
                    (seedAt F w.authKey w.secret w.dir.switch (msgChainEpoch pre)) := by
                  dsimp only at hs
                  unfold evalSaltFromSeed
                  rw [hmce]
                  rcases hkey_eval with ⟨_, hidx0, rfl⟩ | ⟨hidx1, rfl⟩
                  · have hcond : (0 : ℕ) = 0 ∧ pre.index = 0#32 := ⟨rfl, hidx0⟩
                    simp only [recvKeyToSalt?_some_nil, Option.some.injEq] at hs
                    simp only [hcond, and_self, ↓reduceIte, hs.symm]
                  · have hcond : pre.index ≠ 0#32 := by
                      intro h0
                      simp [h0] at hidx1
                    change recvKeyToSalt?
                      (some (keyAt F (seedAt F w.authKey w.secret w.dir.switch 0)
                        (pre.index.toNat - 1))) = some salt at hs
                    rw [recvKeyToSalt_keyAt, Option.some.injEq] at hs
                    simp only [true_and, hcond, ↓reduceIte, hs.symm]
                refine ⟨pre, ⟨w.authKey, w.dir, w.secret, w.st, w.sendEp, w.sendCtr, recvSet',
                  some (vnOf w.dir w.authKey), some chain1, chain1⟩,
                  rfl, by rw [hmce]; exact Nat.zero_le _, hsalt, ?_, rfl, rfl, ?_,
                  fun _ _ => rfl⟩
                · refine
                    { htop :=
                        { hbytes := rfl
                          hvn := Or.inr rfl
                          hch := Or.inl rfl
                          hok := hok'
                          hcur := by rw [hcur', htop.hcur]
                          hsendEp := by rw [hsendEp', htop.hsendEp]
                          hsendLe := htop.hsendLe
                          hsendPrev := recvKey_sendPrevNil (spqrHkdfWith F) w.chE chain1 0#64
                            pre.index rawKey htop.hsendPrev hrk }
                      hauth := hw.hauth
                      hbok := hw.hbok
                      hphi := hw.hphi
                      hsmall := hsmall' }
                · dsimp only
                  rw [hcur']

theorem spqrReachFrom_topStateW (F : ShaCompress) (K : MlKem) {bytes bytes' : Bytes}
    {w₀ : TopWitness F} (hw₀ : TopStateW F K bytes w₀)
    (h : SpqrReachFrom (spqrV1SessionUniformCoins F K) bytes bytes') :
    ∃ w' : TopWitness F,
      TopStateW F K bytes' w' ∧
      w'.authKey = w₀.authKey ∧
      w'.dir = w₀.dir ∧
      w₀.chE.currentEpoch.toNat ≤ w'.chE.currentEpoch.toNat ∧
      (∀ e ≤ w₀.chE.currentEpoch.toNat,
        seedAt F w'.authKey w'.secret w'.dir.switch e =
          seedAt F w₀.authKey w₀.secret w₀.dir.switch e) := by
  induction h with
  | refl =>
    exact ⟨w₀, hw₀, rfl, rfl, le_rfl, fun _ _ => rfl⟩
  | send _ hsend ih =>
    obtain ⟨w, hw, hauth, hdir, hcur, hseed⟩ := ih
    obtain ⟨w', hw', hauth', hdir', hcur', hseed'⟩ := topStateW_send F K hw hsend
    refine ⟨w', hw', hauth'.trans hauth, hdir'.trans hdir, hcur.trans hcur', ?_⟩
    intro e he
    exact (hseed' e (he.trans hcur)).trans (hseed e he)
  | recv _ hrecv ih =>
    obtain ⟨w, hw, hauth, hdir, hcur, hseed⟩ := ih
    obtain ⟨_, w', -, -, -, hw', hauth', hdir', hcur', hseed'⟩ := topStateW_recv F K hw hrecv
    refine ⟨w', hw', hauth'.trans hauth, hdir'.trans hdir, hcur.trans hcur', ?_⟩
    intro e he
    exact (hseed' e (he.trans hcur)).trans (hseed e he)

/-! ## Sent-message length bound -/

private theorem encode_varint_length_le (v : BitVec 64) :
    (encode_varint v []).length ≤ 10 := by
  simp only [encode_varint, MAX_VARINT_BYTES_LEN, List.nil_append, Codec.encodeVarintLoop_eq_proto]
  exact (Codec.proto_encodeVarint_length v).2

private theorem payloadBytes_length_le {P : PolyApi} (p : MessagePayload P) :
    (Codec.payloadBytes p).length ≤ 42 := by
  rcases p with _ | c | c | c | _ | c | c <;>
    simp only [Codec.payloadBytes, encode_chunk, List.length_append, List.length_nil]
  all_goals
    try omega
    try
      have h1 := encode_varint_length_le ((P.chunkIndex c).zeroExtend 64)
      have h2 := (P.chunkData c).toList_length
      omega

private theorem serialize_length_le {P : PolyApi} (m : Message P) (index : BitVec 32) :
    (m.serialize index).length ≤ 64 := by
  rw [Codec.serialize_eq]
  simp only [List.length_cons, List.length_append]
  have h1 := encode_varint_length_le m.epoch
  have h2 := encode_varint_length_le (index.zeroExtend 64)
  have h3 := payloadBytes_length_le m.payload
  omega

private def IsSendMsg (D : SpqrApiDeps) (msg : D.MessageV1) : SpqrApiResult Send → Prop
  | .error _ => True
  | .ok s => ∃ index, s.msg = D.msgSerialize msg index

private theorem isSendMsg_bind {D : SpqrApiDeps} {msg : D.MessageV1} {α : Type}
    (m : SpqrApiResult α) (f : α → SpqrApiResult Send) (hf : ∀ a, IsSendMsg D msg (f a)) :
    IsSendMsg D msg (m >>= f) := by
  cases m with
  | error _ => trivial
  | ok a => exact hf a

private theorem isSendMsg_jp2 (D : SpqrApiDeps) (vn? : Option VersionNegotiationPB)
    (msg : D.MessageV1) (state : D.States) (x : BitVec 32 × Bytes × Option ChainPB) :
    IsSendMsg D msg
      (match x with
       | (index, msgKey, chainPb) =>
         have msgBytes := D.msgSerialize msg index
         match msgBytes with
         | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
         | b0 :: _ =>
           if (b0 != Version.v1.toU8) = true then
             Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
           else
             have newStateBytes := D.encodeState
               { inner := some (D.statesIntoPb state)
                 versionNegotiation := vn?
                 chain := chainPb }
             have outKey := if msgKey.isEmpty = true then none else some msgKey
             Except.ok { state := newStateBytes, msg := msgBytes, key := outKey }) := by
  rcases x with ⟨index, msgKey, chainPb⟩
  dsimp only
  cases hser : D.msgSerialize msg index with
  | nil => trivial
  | cons b0 tl =>
    dsimp only
    split
    · trivial
    · exact ⟨index, hser.symm⟩

private theorem isSendMsg_jp1 (D : SpqrApiDeps) (hkdf : HkdfFn) (msg : D.MessageV1)
    (key : Option EpochSecret) (k : BitVec 32 × Bytes × Option ChainPB → SpqrApiResult Send)
    (hk : ∀ x, IsSendMsg D msg (k x)) (chain : Option Chain) :
    IsSendMsg D msg
      (match chain with
       | none =>
         if key.isNone = true then do
           let __x ← pure (0#32, [], none)
           k __x
         else do
           let __x ← Except.error (SpqrApiError.panic SpqrApiPanic.sendKeySomeWithoutChain)
           k __x
       | some chain0 =>
         have __do_jp := fun chain1 =>
           have epoch := D.msgEpoch msg
           if (epoch == 0#64) = true then do
             let __x ← Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
             k __x
           else do
             let __x ← SpqrApiResult.ofChainResult (Chain.sendKey hkdf chain1 (epoch - 1#64))
             match __x with
             | (chain2, idx, mk) => do
               let __x ← pure (idx, mk, some chain2.intoPb)
               k __x
         match key with
         | some epochSecret => do
           let chain1 ← SpqrApiResult.ofChainPanic (Chain.addEpoch hkdf chain0 epochSecret)
           __do_jp chain1
         | none => do
           let chain1 ← pure chain0
           __do_jp chain1) := by
  cases chain with
  | none =>
    by_cases hkn : key.isNone = true
    · simp only [hkn, ↓reduceIte, pure, Except.pure, bind, Except.bind]
      exact hk _
    · simp only [hkn, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
      trivial
  | some chain0 =>
    have h1 : ∀ chain1, IsSendMsg D msg
        (have epoch := D.msgEpoch msg
         if (epoch == 0#64) = true then do
           let __x ← Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
           k __x
         else do
           let __x ← SpqrApiResult.ofChainResult (Chain.sendKey hkdf chain1 (epoch - 1#64))
           match __x with
           | (chain2, idx, mk) => do
             let __x ← pure (idx, mk, some chain2.intoPb)
             k __x) := by
      intro chain1
      dsimp only
      by_cases hep : (D.msgEpoch msg == 0#64) = true
      · simp only [hep, ↓reduceIte, bind, Except.bind]
        trivial
      · simp only [hep, Bool.false_eq_true, ↓reduceIte]
        refine isSendMsg_bind _ _ ?_
        rintro ⟨chain2, idx, mk⟩
        exact hk _
    cases key with
    | none =>
      dsimp only [pure, Except.pure, bind, Except.bind]
      exact h1 chain0
    | some epochSecret => exact isSendMsg_bind _ _ h1

private theorem isSendMsg_sendAfterStates (D : SpqrApiDeps) (hkdf : HkdfFn)
    (statePb : PqRatchetStatePB D.V1StatePB) (msg : D.MessageV1) (key : Option EpochSecret)
    (state : D.States) : IsSendMsg D msg (sendAfterStates D hkdf statePb msg key state) := by
  unfold sendAfterStates
  have h1 (vn? : Option VersionNegotiationPB) (chain : Option Chain) :=
    isSendMsg_jp1 D hkdf msg key _ (isSendMsg_jp2 D vn? msg state) chain
  cases statePb.chain with
  | some pb =>
    refine isSendMsg_bind (SpqrApiResult.ofError (Chain.fromPb pb)) _ fun c => ?_
    have hc := h1 statePb.versionNegotiation (some c)
    dsimp only [pure, Except.pure, bind, Except.bind] at hc ⊢
    cases key <;> exact hc
  | none =>
    cases statePb.versionNegotiation with
    | none => trivial
    | some vn =>
      by_cases hslt : Version.v0.toI32.slt vn.minVersion = true
      · simp only [hslt, ↓reduceIte]
        refine isSendMsg_bind (SpqrApiResult.ofError (chainFromVersionNegotiation hkdf vn)) _
          fun c => ?_
        have hc := h1 (some vn) (some c)
        dsimp only [pure, Except.pure, bind, Except.bind] at hc ⊢
        cases key <;> exact hc
      · have hc := h1 (some vn) none
        simp only [hslt, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind]
          at hc ⊢
        exact hc

theorem sendAfterStates_msg_eq (D : SpqrApiDeps) (hkdf : HkdfFn)
    (statePb : PqRatchetStatePB D.V1StatePB) (msg : D.MessageV1) (key : Option EpochSecret)
    (state : D.States) {s : Send} (h : sendAfterStates D hkdf statePb msg key state = .ok s) :
    ∃ index, s.msg = D.msgSerialize msg index := by
  have hm := isSendMsg_sendAfterStates D hkdf statePb msg key state
  rw [h] at hm
  exact hm

theorem spqrV1Send_msg_len_le (F : ShaCompress) (K : MlKem) (st : Bytes) (r : BitVec 512)
    (st' : Bytes) (salt : Salt) (pm : Bytes)
    (h : (spqrV1SessionUniformCoins F K).send st r = some (st', salt, pm)) : pm.length ≤ 64 := by
  change (spqrV1 F K).send st (coinBytes r) = some (st', salt, pm) at h
  rw [spqrV1_eq] at h
  dsimp only [toSpqrModel] at h
  rcases hs : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) st (coinBytes r)).1 with e | s
  · rw [hs] at h; cases h
  · rw [hs] at h; dsimp only at h
    rcases hk : messageKeyToSalt? s.key with _ | salt'
    · rw [hk] at h; cases h
    · rw [hk] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      unfold LibsignalSpqrV1.send at hs
      split at hs
      · cases hs
      · split at hs
        · simp only [Except.ok.injEq] at hs; subst hs; simp
        · split at hs
          · cases hs
          · split at hs
            split at hs
            · simp at hs
            · dsimp only at hs
              obtain ⟨index, hidx⟩ := sendAfterStates_msg_eq _ _ _ _ _ _ hs
              rw [hidx]
              exact serialize_length_le _ index

/-- Every message returned by `(spqrV1SessionUniformCoins F K).send` fits `rustLenBound`. -/
theorem spqrV1Send_msg_len_lt (F : ShaCompress) (K : MlKem) (st : Bytes) (r : BitVec 512)
    (st' : Bytes) (salt : Salt) (pm : Bytes)
    (h : (spqrV1SessionUniformCoins F K).send st r = some (st', salt, pm)) :
    pm.length < CryptoGames.LibsignalSession.rustLenBound := by
  have h64 := spqrV1Send_msg_len_le F K st r st' salt pm h
  unfold CryptoGames.LibsignalSession.rustLenBound
  omega

end CryptoVerification.SpqrV1Sync.SendTotal

