/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpqrV1Sync.SendTotalExtras
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TightSize
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecvEqual
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidPhi
import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
import ProofLib.BV.WidthNorm

/-!
# SPQR V1 Tight Reachable-State Size Invariant

Refines `TopStateW` with `BOkTight` and `RecvSmallTight` into `TopStateTight`, proving closure
under initialization, send, and receive, and bounding every reachable serialized state by
`286,196` bytes (`topStateTight_length_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawVN rawChain rawEpochDir rawV1State)
open CryptoGames.LibsignalSession (ShaCompress SpqrDirection)
open CryptoGames.HKDF (Salt)

/-- Tight unbounded reachable-state invariant for `spqrV1 F K`. -/
structure TopStateTightW (F : ShaCompress) (K : MlKem) (bytes : Bytes) (w : TopWitness F) : Prop where
  htop : PartyTopW F K w.authKey w.dir w.secret w.st w.sendEp w.sendCtr w.recvSet bytes
    w.vn? w.ch? w.chE
  hauth : w.authKey.length = 32
  hbok : BOkTight w.st
  hphi : phiB w.st ≤ w.sendEp + 1
  hsmall : RecvSmallTight w.chE

def TopStateTight (F : ShaCompress) (K : MlKem) (bytes : Bytes) : Prop :=
  ∃ w : TopWitness F, TopStateTightW F K bytes w

theorem TopStateTightW.toTopStateW {F : ShaCompress} {K : MlKem} {bytes : Bytes}
    {w : TopWitness F} (hw : TopStateTightW F K bytes w) : TopStateW F K bytes w :=
  ⟨hw.htop, hw.hauth, hw.hbok.1, hw.hphi, hw.hsmall.toRecvSmall⟩

theorem topStateTightW_length_le (F : ShaCompress) (K : MlKem) {bytes : Bytes} {w : TopWitness F}
    (hw : TopStateTightW F K bytes w) : bytes.length ≤ 286196 := by
  have htop := topBytes_length_le F K w.st w.vn? w.ch?
  rw [← hw.htop.hbytes] at htop
  have hvn : optRaw rawVN w.vn? ≤ w.authKey.length := by
    rcases hw.htop.hvn with h | h <;> rw [h]
    · exact Nat.zero_le _
    · exact le_refl _
  have hch : optRaw rawChain (w.ch?.map Chain.intoPb) ≤ 238532 := by
    rcases hw.htop.hch with h | ⟨h, -, -⟩
    · rw [h]
      dsimp only [Option.map, optRaw]
      have hlen := hw.htop.hok.hlen
      have hcur := hw.htop.hcur
      have hsendEp := hw.htop.hsendEp
      have hcur_le := chainCur_le_phiB w.st
      have hphi := hw.hphi
      exact tsz_rawChain_tight_le F w.authKey w.dir w.secret w.sendCtr w.recvSet w.chE
        hw.htop.hok hw.htop.hsendPrev hw.hsmall (by omega)
    · rw [h]; exact Nat.zero_le _
  have hbraid : rawV1State w.st.into_pb ≤ 46880 := st_bSize_tight F w.st hw.hbok
  have hauth := hw.hauth
  omega

/-- Every `TopStateTight` serialized SPQR V1 state has length at most `286,196` bytes. -/
theorem topStateTight_length_le (F : ShaCompress) (K : MlKem) {bytes : Bytes}
    (h : TopStateTight F K bytes) : bytes.length ≤ 286196 := by
  obtain ⟨w, hw⟩ := h
  exact topStateTightW_length_le F K hw

private theorem ti_initStates_facts' (F : ShaCompress) (K : MlKem) (spqrdir : SpqrDirection)
    (k : BitVec 256) (st : St F)
    (hst : initStates F (CryptoGames.HMAC.keyToBytes32 k) (Direction.ofSpqrDirection spqrdir) =
      .ok st) :
    spqrV1Init F K spqrdir k =
      topBytes F K st
        (some (vnOf (Direction.ofSpqrDirection spqrdir) (CryptoGames.HMAC.keyToBytes32 k)))
        none ∧
      st.epoch.toNat = 1 ∧ chainCur st = 0 := by
  have hdec : ∀ n, n = 96 → spqrPolyApi.decoder_new n = .ok (.ok (freshDec 96)) := by
    rintro n rfl
    simp only [spqrPolyApi, decoderNew_eq 96 (by decide), Except.mapError]
  cases spqrdir with
  | a2b =>
    change States.init_a spqrPolyApi (spqrAuthApi F) (CryptoGames.HMAC.keyToBytes32 k) = .ok st at hst
    have ha : States.init_a spqrPolyApi (spqrAuthApi F) (CryptoGames.HMAC.keyToBytes32 k) =
        .ok (.keysUnsampled
          { uc := { epoch := 1#64, auth := Authenticator.new F (CryptoGames.HMAC.keyToBytes32 k) 1#64 } }) := rfl
    rw [ha] at hst
    cases hst
    exact ⟨rfl, rfl, rfl⟩
  | b2a =>
    change States.init_b spqrPolyApi (spqrAuthApi F) (CryptoGames.HMAC.keyToBytes32 k) = .ok st at hst
    have hb : States.init_b spqrPolyApi (spqrAuthApi F) (CryptoGames.HMAC.keyToBytes32 k) =
        .ok (.noHeaderReceived
          { uc := { epoch := 1#64, auth := Authenticator.new F (CryptoGames.HMAC.keyToBytes32 k) 1#64 },
            receiving_hdr := freshDec 96 }) := by
      simp only [States.init_b, Chunked.SendCt.NoHeaderReceived.new]
      rw [hdec]
      all_goals rfl
    rw [hb] at hst
    cases hst
    refine ⟨?_, rfl, rfl⟩
    simp only [spqrV1Init, spqrV1InitialStateFor, initialState, libsignalSpqrParams,
      libsignalChainParams_false, Direction.ofSpqrDirection, initInner, spqrDeps, hb,
      SpqrApiResult.ofPanic, topBytes, topPb, vnOf, dparams]
    rfl

theorem topStateTight_init (F : ShaCompress) (K : MlKem) (spqrdir : SpqrDirection)
    (k : BitVec 256) : TopStateTight F K (spqrV1Init F K spqrdir k) := by
  have hlen : (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by
    simp [CryptoGames.HMAC.keyToBytes32]
  obtain ⟨st, hst, hbok, hphi⟩ :=
    st_bInit_tight F (dir := Direction.ofSpqrDirection spqrdir) hlen
  obtain ⟨hbytes, hep_st, hcur_st⟩ := ti_initStates_facts' F K spqrdir k st hst
  obtain ⟨chE, hvn_ok, hok⟩ :=
    chainFromVN_ok F (CryptoGames.HMAC.keyToBytes32 k) (Direction.ofSpqrDirection spqrdir)
      Version.v1.toI32 (fun _ => []) (fun _ => 0) (fun _ => ∅) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨hcur_ch, hsend_ch⟩ :=
    chainFromVN_fresh F (Direction.ofSpqrDirection spqrdir) (CryptoGames.HMAC.keyToBytes32 k)
      chE hvn_ok
  refine ⟨⟨CryptoGames.HMAC.keyToBytes32 k, Direction.ofSpqrDirection spqrdir, fun _ => [], st, 0,
    fun _ => 0, fun _ => ∅,
    some (vnOf (Direction.ofSpqrDirection spqrdir) (CryptoGames.HMAC.keyToBytes32 k)), none, chE⟩,
    ?_⟩
  exact
    { htop :=
        { hbytes := hbytes
          hvn := Or.inr rfl
          hch := Or.inr ⟨rfl, rfl, hvn_ok⟩
          hok := hok
          hcur := by rw [hcur_ch, hcur_st]; rfl
          hsendEp := by rw [hsend_ch]; rfl
          hsendLe := by dsimp only; rw [hep_st]
          hsendPrev := chainFromVN_sendPrevNil F _ _ chE hvn_ok }
      hauth := hlen
      hbok := hbok
      hphi := by dsimp only; rw [hphi]; omega
      hsmall := st_recvSmallVN_tight F hvn_ok }

theorem topStateTightW_send (F : ShaCompress) (K : MlKem) {bytes tape bytes' : Bytes}
    {salt : Salt} {msg : Bytes} {w : TopWitness F} (hw : TopStateTightW F K bytes w)
    (hsend : (spqrV1 F K).send bytes tape = some (bytes', salt, msg)) :
    ∃ w' : TopWitness F, TopStateTightW F K bytes' w' := by
  have hsize : bytes.length < 2 ^ 64 := topStateW_length_lt F K hw.toTopStateW
  have hsize' : (topBytes F K w.st w.vn? w.ch?).length < 2 ^ 64 := hw.htop.hbytes ▸ hsize
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) w.st.into_pb = .ok w.st :=
    st_bCodec F w.st hw.hbok.1
  rcases hsendB : w.st.send K tape with err | ⟨⟨m, key, st'⟩, tape'⟩
  · exfalso
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
    rw [spqrV1_eq, toSpqrModel] at hsend
    dsimp only at hsend
    rw [hw.htop.hbytes, htop, hafter] at hsend
    dsimp only at hsend
    rw [tsnd_messageKeyToSalt_keyAt] at hsend
    simp only [Option.some.injEq, Prod.mk.injEq] at hsend
    obtain ⟨hbytes', -, -⟩ := hsend
    have hsp1 := tsnd_addEpoch_opt (spqrHkdfWith F) w.chE chain1 key hw.htop.hsendPrev hadd
    have hsmall1 : RecvSmallTight chain1 := by
      cases key with
      | none => cases hadd; exact hw.hsmall
      | some _ => exact st_recvSmallAdd_tight hw.hsmall hadd
    refine ⟨⟨w.authKey, w.dir, secret', st', w.st.epoch.toNat - 1,
      Function.update w.sendCtr (w.st.epoch.toNat - 1) (w.sendCtr (w.st.epoch.toNat - 1) + 1),
      w.recvSet, w.vn?, some chain2, chain2⟩, ?_⟩
    exact
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
        hbok := st_bSendClosed_tight F K hw.hbok hsendB
        hphi := by
          dsimp only [phiB]
          rw [hst'_ep]
          split <;> omega
        hsmall := st_recvSmallSend_tight hsmall1 hsk }

theorem topStateTight_send (F : ShaCompress) (K : MlKem) {bytes tape bytes' : Bytes}
    {salt : Salt} {msg : Bytes} (h : TopStateTight F K bytes)
    (hsend : (spqrV1 F K).send bytes tape = some (bytes', salt, msg)) :
    TopStateTight F K bytes' := by
  obtain ⟨w, hw⟩ := h
  exact topStateTightW_send F K hw hsend

private def addEpochSecret' (secret : ℕ → Bytes) (cur : ℕ) : Option EpochSecret → ℕ → Bytes
  | none => secret
  | some es => Function.update secret (cur + 1) es.secret

private theorem recv_addEpoch_tight (F : ShaCompress) (K : MlKem) (authKey : Bytes)
    (dir : Direction) (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (chE : Chain)
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (hcur : chE.currentEpoch.toNat = chainCur st) (hep_pos : 1 ≤ st.epoch.toNat)
    (hsmall : RecvSmallTight chE) (hsp : SendPrevNil chE)
    (m : Msg) (key : Option EpochSecret)
    (hrecvB : st.recv K m = .ok { key := key, state := st' }) :
    ∃ chain1 : Chain,
      (match key with
       | some es => SpqrApiResult.ofChainPanic (chE.addEpoch (spqrHkdfWith F) es)
       | none => pure chE) = .ok chain1 ∧
      ChainOk F authKey dir (addEpochSecret' secret chE.currentEpoch.toNat key)
        sendCtr recvSet chain1 ∧
      chain1.currentEpoch.toNat = chainCur st' ∧
      chain1.sendEpoch = chE.sendEpoch ∧
      RecvSmallTight chain1 ∧
      SendPrevNil chain1 := by
  cases key with
  | none =>
    have hc := chainCur_recv_none F K st st' m hep_pos hrecvB
    exact ⟨chE, rfl, hok, by rw [hcur, hc], rfl, hsmall, hsp⟩
  | some es =>
    obtain ⟨hes_ep, hc'⟩ := chainCur_recv_key F K st st' m es hep_pos hrecvB
    have hep : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by omega
    have hok1 : ChainOk F authKey dir
        (addEpochSecret' secret chE.currentEpoch.toNat (some es)) sendCtr recvSet chE :=
      chainOk_congr F authKey dir secret _ sendCtr recvSet chE hok
        (fun _ _ he => Function.update_of_ne (by omega) _ _)
    have hsec1 : es.secret =
        addEpochSecret' secret chE.currentEpoch.toNat (some es) (chE.currentEpoch.toNat + 1) :=
      (Function.update_self (chE.currentEpoch.toNat + 1) es.secret secret).symm
    obtain ⟨ch1, hadd, hcur1, hsend1, hok'⟩ :=
      addEpoch_ok F authKey dir _ sendCtr recvSet chE hok1 es hep hsec1
    refine ⟨ch1, ?_, hok', ?_, hsend1, st_recvSmallAdd_tight hsmall hadd,
      addEpoch_sendPrevNil (spqrHkdfWith F) chE ch1 es hsp hadd⟩
    · simp [hadd, SpqrApiResult.ofChainPanic]
    · rw [hcur1, hes_ep, hc']

theorem topStateTightW_recv (F : ShaCompress) (K : MlKem) {bytes msg bytes' : Bytes} {salt : Salt}
    {w : TopWitness F} (hw : TopStateTightW F K bytes w)
    (hrecv : (spqrV1 F K).recv bytes msg = .ok (bytes', salt)) :
    ∃ w' : TopWitness F, TopStateTightW F K bytes' w' := by
  have hsize : bytes.length < 2 ^ 64 := topStateW_length_lt F K hw.toTopStateW
  have htop := hw.htop
  have hBC : BCodecStmt F := st_bCodec F
  have hPhi : BPhiStmt F K := st_bPhi F K
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
    | some _ =>
      rw [hs] at hrecv
      cases hrecv
      have hsize' : (topBytes F K w.st w.vn? w.ch?).length < 2 ^ 64 := htop.hbytes ▸ hsize
      rw [htop.hbytes] at hr
      cases hpre : msgPreamble msg with
      | error _ =>
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
            rw [hdes, treq_spqrDeps_statesFromPb F K w.st (hBC w.st hw.hbok.1)] at hr
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
              let secret1 : ℕ → Bytes := addEpochSecret' w.secret w.chE.currentEpoch.toNat key
              obtain ⟨chain1, hadd, hok1, hcur1, hsend1, hsmall1, hsp1⟩ :=
                recv_addEpoch_tight F K w.authKey w.dir w.secret w.st st'
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
                | some _ =>
                  dsimp [SpqrApiResult.ofError, SpqrApiResult.ofChainResult, bind, Except.bind] at hadd hr
                  rw [hadd] at hr
                  dsimp at hr
                  cases hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
                  | error _ => rw [hrk] at hr; contradiction
                  | ok cm => rw [hrk] at hr; cases hr; exact ⟨cm.1, cm.2, rfl, rfl⟩
              obtain ⟨recvSet', hok2, hsmall2, hcur2, hsend2⟩ :=
                st_chainRecv_tight F hok1 hsmall1 hrk
              refine ⟨⟨w.authKey, w.dir, secret1, st', w.sendEp, w.sendCtr, recvSet',
                none, some chain2, chain2⟩, ?_⟩
              exact
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
                    · exact st_bRecvCt_tight F K hek hw.hbok hrecvB
                    · exact st_bRecvEk_tight F K hek hw.hbok hrecvB
                  hphi := (hPhi.2 w.st st' m key hrecvB).trans hw.hphi
                  hsmall := hsmall2 }
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
                  st_chainRecv_tight F htop.hok hw.hsmall hrk
                refine ⟨⟨w.authKey, w.dir, w.secret, w.st, w.sendEp, w.sendCtr, recvSet',
                  some (vnOf w.dir w.authKey), some chain1, chain1⟩, ?_⟩
                exact
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

theorem topStateTight_recv (F : ShaCompress) (K : MlKem) {bytes msg bytes' : Bytes} {salt : Salt}
    (h : TopStateTight F K bytes)
    (hrecv : (spqrV1 F K).recv bytes msg = .ok (bytes', salt)) :
    TopStateTight F K bytes' := by
  obtain ⟨w, hw⟩ := h
  exact topStateTightW_recv F K hw hrecv

end CryptoVerification.SpqrV1Sync.SendTotal
