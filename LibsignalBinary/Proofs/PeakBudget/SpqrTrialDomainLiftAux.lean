/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TightSize
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.DecoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidPhi
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecvEqual
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
import ProofLib.BV.WidthNorm

@[expose] public section

set_option autoImplicit false

/-!
# Tight SPQR V1 State Invariant and Decoded Trial Caps

Defines the counter-free SPQR V1 serialized-state invariant `TopStateTight F K bytes` (`≤ 286,196` B)
and proves its closure under `spqrV1Init`, `(spqrV1 F K).send`, and `(spqrV1 F K).recv`, along with
decoded and post-step size bounds (`topStateTight_decode_props`) for per-trial `SpqrRecvTightDomain` lifting.
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux

open CryptoGames.HKDF (Salt)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ShaCompress SpqrDirection)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Chain ChainEpoch ChainEpochDirection ChainPanic ChainResult
   Direction EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH Epoch EpochSecret Error HkdfFn Message MlKem
   PqRatchetState States V1Recv V1State Version VersionNegotiationPB chainFrom
   chainFromVersionNegotiation initInner initialState libsignalChainParams
   libsignalChainParams_false libsignalSpqrParams liftStatesResult messageKeyToSalt? msgPreamble
   pbToPqRatchetState recv recvKeyToSalt? send sendAfterStates spqrAuthApi spqrDeps spqrHkdfWith
   spqrPolyApi spqrV1 spqrV1Init spqrV1InitialStateFor spqrV1_eq stateVersion toSpqrModel)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.SpqrV1.Top.StateSize
  (optRaw optRaw_some rawChain rawV1State rawVN)
open CryptoVerification.SpqrV1Sync.ChainSync
  (ChainOk addEpoch_ok chainFromVN_ok chainOk_congr dparams keyAt length_keyAt seedAt sendKey_ok)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.InSync (Msg St decoderNew_eq freshDec)
open CryptoVerification.SpqrV1Sync.SendTotal
  (BOkTight RecvSmallTight chainCur_le_phiB freshB isEkSide phiB st_bCodec st_bInit_tight st_bPhi
   st_bRecvCt_tight st_bRecvEk_tight st_bSendClosed_tight st_bSize_tight st_chainFrom_ok
   st_chainRecv_tight st_recvSmallAdd_tight st_recvSmallSend_tight st_recvSmallVN_tight
   treq_recv_epoch_le treq_spqrDeps_statesFromPb treq_statesRecv_ok tsnd_addEpoch_opt
   tsnd_messageKeyToSalt_keyAt tsnd_sendAfterStates_ok tsnd_send_addEpoch tsnd_spqrDeps_msgEpoch
   tsz_rawChain_tight_le)
open CryptoVerification.SpqrV1Sync.TopSync
  (PartyTopW SendPrevNil addEpoch_sendPrevNil chainCur chainCur_recv_key chainCur_recv_none
   chainCur_send_key chainFromVN_fresh chainFromVN_sendPrevNil chain_fromPb_intoPb
   decodeState_topBytes epoch_sub_one_le_chainCur initStates partyTop_epoch_pos recvEqual
   recvKey_sendPrevNil recv_topBytes sendKey_sendPrevNil send_facts send_topBytes topBytes
   topBytes_length_le topPb vnOf)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (ValidChainParams ValidChainParamsPB ValidEncoderPts640 ValidStateChainParams ValidStatePtsAt
   validChainParams_of_validStateChainParams validEncoderPtsAt_of_validStatePtsAt
   validStateChainParams_spqrV1Init validStateChainParams_spqrV1_recv
   validStateChainParams_spqrV1_send validStatePtsAt_spqrV1Init validStatePtsAt_spqrV1_recv
   validStatePtsAt_spqrV1_send)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
  (StatesPtsBoundedAt ValidV1PtsAt chainAddEpoch_params_eq chainRecvKey_params_eq
   statesPtsBoundedAt_of_from_pb validChainParamsPB_of_chainFrom)

@[local simp] private theorem optRaw_none {α : Type} (f : α → Nat) :
    optRaw f none = 0 := rfl

/-! ## 1. `TopStateTightW`, `TopStateTight`, and `SpqrStateTight640` -/

/-- Counter-free tight SPQR V1 party invariant with exposed witnesses `(vn?, ch?, chE)`. -/
structure TopStateTightW (F : ShaCompress) (K : MlKem) (bytes authKey : Bytes)
    (dir : Direction) (secret : Nat → Bytes) (st : St F) (sendEp : Nat)
    (sendCtr : Nat → Nat) (recvSet : Nat → Finset Nat)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) (chE : Chain) : Prop where
  htop : PartyTopW F K authKey dir secret st sendEp sendCtr recvSet bytes vn? ch? chE
  hauth : authKey.length = 32
  hbok : BOkTight st
  hphi_send : phiB st ≤ sendEp + 1
  hsmall : RecvSmallTight chE
  hpts640 : ValidStatePtsAt 640 bytes
  hcp : ValidStateChainParams bytes

/-- Existentially packaged tight SPQR V1 serialized state (`V1`, always non-empty). -/
def TopStateTight (F : ShaCompress) (K : MlKem) (bytes : Bytes) : Prop :=
  ∃ authKey dir secret st sendEp sendCtr recvSet vn? ch? chE,
    TopStateTightW F K bytes authKey dir secret st sendEp sendCtr recvSet vn? ch? chE

/-- Either empty (`V0`) or a `TopStateTight` V1 state. -/
def SpqrStateTight640 (F : ShaCompress) (K : MlKem) (bytes : Bytes) : Prop :=
  bytes = [] ∨ TopStateTight F K bytes

theorem TopStateTight.toSpqrStateTight640 {F : ShaCompress} {K : MlKem} {bytes : Bytes}
    (h : TopStateTight F K bytes) : SpqrStateTight640 F K bytes :=
  Or.inr h

theorem topStateTightW_links_le_three {F : ShaCompress} {K : MlKem} {bytes authKey : Bytes}
    {dir : Direction} {secret : Nat → Bytes} {st : St F} {sendEp : Nat}
    {sendCtr : Nat → Nat} {recvSet : Nat → Finset Nat}
    {vn? : Option VersionNegotiationPB} {ch? : Option Chain} {chE : Chain}
    (hw : TopStateTightW F K bytes authKey dir secret st sendEp sendCtr recvSet vn? ch? chE) :
    chE.links.length ≤ 3 := by
  have hlen := hw.htop.hok.hlen
  have hcur := hw.htop.hcur
  have hsend := hw.htop.hsendEp
  have hc_le := chainCur_le_phiB st
  have hphi := hw.hphi_send
  omega

theorem topStateTightW_length_le {F : ShaCompress} {K : MlKem} {bytes authKey : Bytes}
    {dir : Direction} {secret : Nat → Bytes} {st : St F} {sendEp : Nat}
    {sendCtr : Nat → Nat} {recvSet : Nat → Finset Nat}
    {vn? : Option VersionNegotiationPB} {ch? : Option Chain} {chE : Chain}
    (hw : TopStateTightW F K bytes authKey dir secret st sendEp sendCtr recvSet vn? ch? chE) :
    bytes.length ≤ spqrStateTightCapBytes := by
  rw [hw.htop.hbytes]
  have htop_le := topBytes_length_le F K st vn? ch?
  have hvn_le : optRaw rawVN vn? ≤ 32 := by
    rcases hw.htop.hvn with rfl | rfl
    · simp
    · simp [optRaw_some, rawVN, vnOf, hw.hauth]
  have hch_le : optRaw rawChain (ch?.map Chain.intoPb) ≤ 238532 := by
    rcases hw.htop.hch with rfl | ⟨rfl, -, -⟩
    · simp only [Option.map, optRaw_some]
      exact tsz_rawChain_tight_le F authKey dir secret sendCtr recvSet chE
        hw.htop.hok hw.htop.hsendPrev hw.hsmall (topStateTightW_links_le_three hw)
    · simp [Option.map]
  have hv1_le : rawV1State st.into_pb ≤ 46880 := st_bSize_tight F st hw.hbok
  unfold spqrStateTightCapBytes
  omega

theorem topStateTight_length_le {F : ShaCompress} {K : MlKem} {bytes : Bytes}
    (h : TopStateTight F K bytes) : bytes.length ≤ spqrStateTightCapBytes := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hw⟩ := h
  exact topStateTightW_length_le hw

theorem spqrStateTight640_length_le {F : ShaCompress} {K : MlKem} {bytes : Bytes}
    (h : SpqrStateTight640 F K bytes) : bytes.length ≤ spqrStateTightCapBytes := by
  rcases h with rfl | h
  · simp [spqrStateTightCapBytes]
  · exact topStateTight_length_le h

theorem topStateTight_to_tightValid640 {F : ShaCompress} {K : MlKem} {s : Bytes}
    (h : TopStateTight F K s) :
    ValidEncoderPts640 s ∧ ValidChainParams s ∧ s.length < 2 ^ 31 := by
  have hle := topStateTight_length_le h
  have hlt31 : s.length < 2 ^ 31 :=
    Nat.lt_of_le_of_lt hle (by unfold spqrStateTightCapBytes; decide)
  have hlt64 : s.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hw⟩ := h
  exact ⟨validEncoderPtsAt_of_validStatePtsAt hlt64 hw.hpts640,
    validChainParams_of_validStateChainParams hlt64 hw.hcp, hlt31⟩

theorem spqrStateTight640_to_tightValid640 {F : ShaCompress} {K : MlKem} {s : Bytes}
    (h : SpqrStateTight640 F K s) :
    ValidEncoderPts640 s ∧ ValidChainParams s ∧ s.length < 2 ^ 31 := by
  rcases h with rfl | h
  · exact ⟨validEncoderPtsAt_of_validStatePtsAt (by decide) (Or.inl rfl),
      validChainParams_of_validStateChainParams (by decide) (Or.inl rfl), by decide⟩
  · exact topStateTight_to_tightValid640 h

/-! ## 2. `spqrV1Init`, `spqrV1.send`, and `spqrV1.recv` Closure -/

private theorem initStates_facts (F : ShaCompress) (K : MlKem) (spqrdir : SpqrDirection)
    (k : BitVec 256) (st : St F)
    (hst : initStates F (keyToBytes32 k) (Direction.ofSpqrDirection spqrdir) = .ok st) :
    spqrV1Init F K spqrdir k =
      topBytes F K st (some (vnOf (Direction.ofSpqrDirection spqrdir) (keyToBytes32 k))) none ∧
      st.epoch.toNat = 1 ∧ chainCur st = 0 := by
  have hdec : ∀ n, n = 96 → spqrPolyApi.decoder_new n = .ok (.ok (freshDec 96)) := by
    rintro n rfl
    simp only [spqrPolyApi, decoderNew_eq 96 (by decide), Except.mapError]
  cases spqrdir with
  | a2b =>
    change States.init_a spqrPolyApi (spqrAuthApi F) (keyToBytes32 k) = .ok st at hst
    have ha : States.init_a spqrPolyApi (spqrAuthApi F) (keyToBytes32 k) =
        .ok (.keysUnsampled
          { uc := { epoch := 1#64, auth := Authenticator.new F (keyToBytes32 k) 1#64 } }) := rfl
    rw [ha] at hst
    cases hst
    exact ⟨rfl, rfl, rfl⟩
  | b2a =>
    change States.init_b spqrPolyApi (spqrAuthApi F) (keyToBytes32 k) = .ok st at hst
    have hb : States.init_b spqrPolyApi (spqrAuthApi F) (keyToBytes32 k) =
        .ok (.noHeaderReceived
          { uc := { epoch := 1#64, auth := Authenticator.new F (keyToBytes32 k) 1#64 },
            receiving_hdr := freshDec 96 }) := by
      simp only [States.init_b, CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new]
      rw [hdec]
      all_goals rfl
    rw [hb] at hst
    cases hst
    refine ⟨?_, rfl, rfl⟩
    simp only [spqrV1Init, spqrV1InitialStateFor, initialState, libsignalSpqrParams,
      libsignalChainParams_false, Direction.ofSpqrDirection, initInner, spqrDeps, hb,
      CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofPanic, topBytes, topPb, vnOf, dparams]
    rfl

theorem topStateTight_spqrV1Init (F : ShaCompress) (K : MlKem) (spqrdir : SpqrDirection)
    (k : BitVec 256) : TopStateTight F K (spqrV1Init F K spqrdir k) := by
  have hlen : (keyToBytes32 k).length = 32 := by simp [keyToBytes32]
  obtain ⟨st, hst, hbok, hphi⟩ :=
    st_bInit_tight F (dir := Direction.ofSpqrDirection spqrdir) hlen
  obtain ⟨hbytes, hep, hcur_st⟩ := initStates_facts F K spqrdir k st hst
  obtain ⟨chE, hvn_ok, hok⟩ :=
    chainFromVN_ok F (keyToBytes32 k) (Direction.ofSpqrDirection spqrdir)
      Version.v1.toI32 (fun _ => []) (fun _ => 0) (fun _ => ∅) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨hcur_ch, hsend_ch⟩ :=
    chainFromVN_fresh F (Direction.ofSpqrDirection spqrdir) (keyToBytes32 k) chE hvn_ok
  exact ⟨keyToBytes32 k, Direction.ofSpqrDirection spqrdir, fun _ => [], st, 0,
    fun _ => 0, fun _ => ∅,
    some (vnOf (Direction.ofSpqrDirection spqrdir) (keyToBytes32 k)), none, chE,
    { htop :=
        { hbytes := hbytes
          hvn := Or.inr rfl
          hch := Or.inr ⟨rfl, rfl, hvn_ok⟩
          hok := hok
          hcur := by rw [hcur_ch, hcur_st]; rfl
          hsendEp := by rw [hsend_ch]; rfl
          hsendLe := by omega
          hsendPrev := chainFromVN_sendPrevNil F _ _ chE hvn_ok }
      hauth := hlen
      hbok := hbok
      hphi_send := by omega
      hsmall := st_recvSmallVN_tight F hvn_ok
      hpts640 := (validStatePtsAt_spqrV1Init 640 F K spqrdir k).1
      hcp := validStateChainParams_spqrV1Init F K spqrdir k }⟩

private theorem getElem?_clearSendNextPrefix_self :
    ∀ (n : Nat) (xs : List ChainEpoch),
      (Chain.clearSendNextPrefix n xs)[n]? = xs[n]?
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: xs => getElem?_clearSendNextPrefix_self n xs

private theorem nextKey_ctr_lt {hkdf : HkdfFn} {d : ChainEpochDirection}
    {v : ChainEpochDirection × (BitVec 32 × Bytes)}
    (h : ChainResult.ofPanic (d.nextKey hkdf) = .ok v) :
    d.ctr.toNat + 1 < 2 ^ 32 := by
  cases hnk : d.nextKey hkdf with
  | error _ => simp [hnk, ChainResult.ofPanic] at h
  | ok r =>
    unfold ChainEpochDirection.nextKey ChainEpochDirection.nextKeyInternal at hnk
    split at hnk <;> [contradiction; skip]
    split at hnk
    · contradiction
    · rename_i hctr_ne
      have hne : d.ctr ≠ 0xffffffff#32 := by simpa using hctr_ne
      have hlt := d.ctr.isLt
      have hnat_ne : d.ctr.toNat ≠ 4294967295 :=
        fun heq => hne (BitVec.eq_of_toNat_eq heq)
      omega

private theorem sendKey_ctr_lt {F : ShaCompress} {authKey : Bytes} {dir : Direction}
    {secret : Nat → Bytes} {sendCtr : Nat → Nat} {recvSet : Nat → Finset Nat}
    {ch ch' : Chain} {e : Epoch} {out : BitVec 32 × Bytes}
    (hok : ChainOk F authKey dir secret sendCtr recvSet ch)
    (hlo : ch.sendEpoch.toNat ≤ e.toNat) (hhi : e.toNat ≤ ch.currentEpoch.toNat)
    (hsk : ch.sendKey (spqrHkdfWith F) e = .ok (ch', out)) :
    sendCtr e.toNat + 1 < 2 ^ 32 := by
  obtain ⟨link0, hlink0, hsendOk⟩ := hok.hsendDir e.toNat hlo hhi
  unfold Chain.sendKey at hsk
  split at hsk <;> [contradiction; skip]
  cases hep : ch.epochIdx e with
  | error _ => simp [hep, ChainResult.ofError, bind, Except.bind] at hsk
  | ok idx0 =>
    have hidx0 : idx0 = e.toNat - (ch.sendEpoch.toNat - 1) := by
      unfold Chain.epochIdx at hep
      split at hep <;> [contradiction; skip]
      dsimp only at hep
      split at hep <;> [contradiction; skip]
      have hinj := Except.ok.inj hep
      have hsub : (ch.currentEpoch - e).toNat = ch.currentEpoch.toNat - e.toNat :=
        BitVec.toNat_sub_of_le hhi
      have hlen := hok.hlen
      omega
    simp only [hep, ChainResult.ofError, bind, Except.bind] at hsk
    by_cases hne : (ch.sendEpoch != e) = true
    · simp only [hne, ↓reduceIte, getElem?_clearSendNextPrefix_self, List.getElem?_drop] at hsk
      have hadd :
          idx0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH +
            (idx0 - (idx0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH)) = idx0 := by
        unfold EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH; omega
      rw [hadd, hidx0, hlink0] at hsk
      dsimp only at hsk
      cases hnk : ChainResult.ofPanic (link0.send.nextKey (spqrHkdfWith F)) with
      | error _ => rw [hnk] at hsk; contradiction
      | ok v =>
        have hlt := nextKey_ctr_lt hnk
        rw [hsendOk.hctr] at hlt
        exact hlt
    · simp only [hne, Bool.false_eq_true, ↓reduceIte, hidx0, hlink0] at hsk
      cases hnk : ChainResult.ofPanic (link0.send.nextKey (spqrHkdfWith F)) with
      | error _ => rw [hnk] at hsk; contradiction
      | ok v =>
        have hlt := nextKey_ctr_lt hnk
        rw [hsendOk.hctr] at hlt
        exact hlt

private theorem sendAfterStates_extract_sendKey {F : ShaCompress} {K : MlKem}
    {authKey : Bytes} {dir : Direction} {secret : Nat → Bytes}
    {st st' : St F} {sendCtr : Nat → Nat} {recvSet : Nat → Finset Nat}
    {vn? : Option VersionNegotiationPB} {ch? : Option Chain} {chE chain1 : Chain}
    (hch : ch? = some chE ∨
      (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
        chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE))
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    {m : Msg} {key : Option EpochSecret}
    (hadd : (match key with
      | some es => chE.addEpoch (spqrHkdfWith F) es
      | none => .ok chE) = .ok chain1)
    (he_ne0 : (m.epoch == 0#64) = false)
    {out : CryptoVerification.LibsignalSpqrV1.Send}
    (hafter : sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (topPb st vn? ch?) m key st' = .ok out) :
    ∃ chain2 outSk, chain1.sendKey (spqrHkdfWith F) (m.epoch - 1#64) = .ok (chain2, outSk) := by
  have hfp := chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hok
  have hslt : BitVec.slt Version.v0.toI32 (vnOf dir authKey).minVersion = true := rfl
  cases key with
  | none =>
    cases hadd
    rcases hch with rfl | ⟨rfl, rfl, hvnE⟩
    · simp only [sendAfterStates, topPb, Option.map, tsnd_spqrDeps_msgEpoch, hfp, he_ne0,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
        bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at hafter
      cases hsk : chE.sendKey (spqrHkdfWith F) (m.epoch - 1#64) with
      | error _ => rw [hsk] at hafter; contradiction
      | ok p => exact ⟨p.1, p.2, rfl⟩
    · simp only [sendAfterStates, topPb, Option.map, tsnd_spqrDeps_msgEpoch, hslt, hvnE, he_ne0,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
        bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at hafter
      cases hsk : chE.sendKey (spqrHkdfWith F) (m.epoch - 1#64) with
      | error _ => rw [hsk] at hafter; contradiction
      | ok p => exact ⟨p.1, p.2, rfl⟩
  | some es =>
    dsimp only at hadd
    rcases hch with rfl | ⟨rfl, rfl, hvnE⟩
    · simp only [sendAfterStates, topPb, Option.map, tsnd_spqrDeps_msgEpoch, hfp, hadd, he_ne0,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
        bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at hafter
      cases hsk : chain1.sendKey (spqrHkdfWith F) (m.epoch - 1#64) with
      | error _ => rw [hsk] at hafter; contradiction
      | ok p => exact ⟨p.1, p.2, rfl⟩
    · simp only [sendAfterStates, topPb, Option.map, tsnd_spqrDeps_msgEpoch, hslt, hvnE, hadd,
        he_ne0, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic,
        CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
        bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at hafter
      cases hsk : chain1.sendKey (spqrHkdfWith F) (m.epoch - 1#64) with
      | error _ => rw [hsk] at hafter; contradiction
      | ok p => exact ⟨p.1, p.2, rfl⟩

theorem topStateTight_spqrV1_send {F : ShaCompress} {K : MlKem}
    {bytes tape bytes' : Bytes} {salt : Salt} {msg : Bytes}
    (h : TopStateTight F K bytes)
    (hsend : (spqrV1 F K).send bytes tape = some (bytes', salt, msg)) :
    TopStateTight F K bytes' := by
  have hsize : bytes.length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (topStateTight_length_le h) (by unfold spqrStateTightCapBytes; decide)
  obtain ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ := h
  have hpts' := validStatePtsAt_spqrV1_send (by decide) F K bytes tape bytes' salt msg
    hw.hpts640 hsize hsend
  have hcp' := validStateChainParams_spqrV1_send F K bytes tape bytes' salt msg
    hw.hcp hsize hsend
  have hsize' : (topBytes F K st vn? ch?).length < 2 ^ 64 := hw.htop.hbytes ▸ hsize
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st :=
    st_bCodec F st hw.hbok.1
  rcases hsendB : st.send K tape with err | ⟨⟨m, key, st'⟩, tape'⟩
  · exfalso
    rw [spqrV1_eq, toSpqrModel] at hsend
    dsimp only at hsend
    rw [hw.htop.hbytes] at hsend
    unfold send at hsend
    rw [decodeState_topBytes F K st vn? ch? hsize'] at hsend
    rcases err with e | p <;> simp [topPb, spqrDeps, hcodec, liftStatesResult, hsendB] at hsend
  · have hep_pos : 1 ≤ st.epoch.toNat := by have := hw.htop.hsendLe; omega
    obtain ⟨hm_ep, hst'_ep, -, -⟩ := send_facts F K st st' tape tape' m key hsendB
    have htop := send_topBytes F K st st' vn? ch? tape tape' m key hsize' hcodec hsendB
    let secret' : Nat → Bytes :=
      match key with
      | none => secret
      | some es => Function.update secret (chainCur st + 1) es.secret
    have hok' : ChainOk F authKey dir secret' sendCtr recvSet chE := by
      refine chainOk_congr F authKey dir secret secret' sendCtr recvSet chE hw.htop.hok ?_
      intro e _ he
      have hcur := hw.htop.hcur
      cases key with
      | none => rfl
      | some es => exact Function.update_of_ne (by omega) _ _
    have hsec : ∀ es, key = some es → es.secret = secret' es.epoch.toNat := by
      intro es hk
      subst hk
      obtain ⟨hes_ep, -⟩ := chainCur_send_key F K st st' tape tape' m es hep_pos hsendB
      change es.secret = Function.update secret (chainCur st + 1) es.secret es.epoch.toNat
      rw [hes_ep, Function.update_self]
    obtain ⟨chain1, hadd, hok1, hcur1, hsend1, hle1⟩ :=
      tsnd_send_addEpoch F K authKey dir secret' st st' sendCtr recvSet chE hok'
        hw.htop.hcur hep_pos tape tape' m key hsendB hsec
    have he_ne0 : (m.epoch == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
      rw [hm_ep] at this
      omega
    have hebv_nat : (m.epoch - 1#64).toNat = st.epoch.toNat - 1 := by
      rw [hm_ep, BitVec.toNat_sub_of_le]
      · rfl
      · show 1 ≤ st.epoch.toNat
        exact hep_pos
    have hlo : chain1.sendEpoch.toNat ≤ (m.epoch - 1#64).toNat := by
      rw [hsend1, hw.htop.hsendEp, hebv_nat]
      have := hw.htop.hsendLe
      omega
    have hhi : (m.epoch - 1#64).toNat ≤ chain1.currentEpoch.toNat := by
      rw [hebv_nat]
      exact (epoch_sub_one_le_chainCur st).trans hle1
    have hafter_raw : ∃ out,
        sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (topPb st vn? ch?) m key st' = .ok out := by
      have hs := hsend
      rw [spqrV1_eq, toSpqrModel] at hs
      dsimp only at hs
      rw [hw.htop.hbytes, htop] at hs
      cases ha : sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (topPb st vn? ch?) m key st' with
      | error _ => rw [ha] at hs; contradiction
      | ok out => exact ⟨out, rfl⟩
    obtain ⟨out_raw, hafter0⟩ := hafter_raw
    obtain ⟨ch2_raw, outSk_raw, hsk_raw⟩ :=
      sendAfterStates_extract_sendKey hw.htop.hch hok' hadd he_ne0 hafter0
    have hctr_lt : sendCtr (m.epoch - 1#64).toNat + 1 < 2 ^ 32 :=
      sendKey_ctr_lt hok1 hlo hhi hsk_raw
    obtain ⟨chain2, hsk, hcur2, hsend2, hok2⟩ :=
      sendKey_ok F authKey dir secret' sendCtr recvSet chain1 hok1 (m.epoch - 1#64) hlo hhi hctr_lt
    rw [hebv_nat] at hsk hok2
    have hafter := tsnd_sendAfterStates_ok F K authKey dir secret' st st' sendCtr recvSet vn? ch?
      chE chain1 chain2 hw.htop.hch hok' m key hadd he_ne0
      (BitVec.ofNat 32 (sendCtr (st.epoch.toNat - 1) + 1))
      (sendCtr (st.epoch.toNat - 1))
      (seedAt F authKey secret' dir (st.epoch.toNat - 1)) hsk
    rw [spqrV1_eq, toSpqrModel] at hsend
    dsimp only at hsend
    rw [hw.htop.hbytes, htop, hafter] at hsend
    dsimp only at hsend
    rw [tsnd_messageKeyToSalt_keyAt] at hsend
    simp only [Option.some.injEq, Prod.mk.injEq] at hsend
    obtain ⟨hbytes', -, -⟩ := hsend
    have hsp1 := tsnd_addEpoch_opt (spqrHkdfWith F) chE chain1 key hw.htop.hsendPrev hadd
    have hsmall1 : RecvSmallTight chain1 := by
      cases key with
      | none => cases hadd; exact hw.hsmall
      | some es => exact st_recvSmallAdd_tight hw.hsmall hadd
    exact ⟨authKey, dir, secret', st', st.epoch.toNat - 1,
      Function.update sendCtr (st.epoch.toNat - 1) (sendCtr (st.epoch.toNat - 1) + 1),
      recvSet, vn?, some chain2, chain2,
      { htop :=
          { hbytes := hbytes'.symm
            hvn := hw.htop.hvn
            hch := .inl rfl
            hok := hok2
            hcur := by rw [hcur2, hcur1]
            hsendEp := by rw [hsend2, hebv_nat]
            hsendLe := by rw [hst'_ep]; omega
            hsendPrev := sendKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 _ _ hsp1 hsk }
        hauth := hw.hauth
        hbok := st_bSendClosed_tight F K hw.hbok hsendB
        hphi_send := by
          unfold phiB
          rw [hst'_ep]
          cases freshB st' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        hsmall := st_recvSmallSend_tight hsmall1 hsk
        hpts640 := hpts'
        hcp := hcp' }⟩

private theorem recv_addEpoch_tight (F : ShaCompress) (K : MlKem)
    (authKey : Bytes) (dir : Direction) (secret : Nat → Bytes) (st st' : St F)
    (sendCtr : Nat → Nat) (recvSet : Nat → Finset Nat) (chE : Chain)
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (hcur : chE.currentEpoch.toNat = chainCur st) (hep_pos : 1 ≤ st.epoch.toNat)
    (hsmall : RecvSmallTight chE) (hsp : SendPrevNil chE)
    (m : Msg) (key : Option EpochSecret)
    (hrecvB : st.recv K m = .ok { key := key, state := st' }) :
    ∃ (chain1 : Chain) (secret1 : Nat → Bytes),
      (match key with
       | some es =>
         CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic
           (chE.addEpoch (spqrHkdfWith F) es)
       | none => pure chE) = .ok chain1 ∧
      ChainOk F authKey dir secret1 sendCtr recvSet chain1 ∧
      chain1.currentEpoch.toNat = chainCur st' ∧
      chain1.sendEpoch = chE.sendEpoch ∧
      RecvSmallTight chain1 ∧
      SendPrevNil chain1 ∧
      chain1.params = chE.params := by
  cases key with
  | none =>
    have hc := chainCur_recv_none F K st st' m hep_pos hrecvB
    exact ⟨chE, secret, rfl, hok, by rw [hcur, hc], rfl, hsmall, hsp, rfl⟩
  | some es =>
    obtain ⟨hes_ep, hc'⟩ := chainCur_recv_key F K st st' m es hep_pos hrecvB
    have hep : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by omega
    let secret1 : Nat → Bytes := Function.update secret (chE.currentEpoch.toNat + 1) es.secret
    have hok1 : ChainOk F authKey dir secret1 sendCtr recvSet chE :=
      chainOk_congr F authKey dir secret secret1 sendCtr recvSet chE hok
        (fun _ _ _ => Function.update_of_ne (by omega) _ _)
    have hsec1 : es.secret = secret1 (chE.currentEpoch.toNat + 1) :=
      (Function.update_self (chE.currentEpoch.toNat + 1) es.secret secret).symm
    obtain ⟨ch1, hadd, hcur1, hsend1, hok'⟩ :=
      addEpoch_ok F authKey dir secret1 sendCtr recvSet chE hok1 es hep hsec1
    refine ⟨ch1, secret1, ?_, hok', ?_, hsend1,
      st_recvSmallAdd_tight hsmall hadd,
      addEpoch_sendPrevNil (spqrHkdfWith F) chE ch1 es hsp hadd,
      chainAddEpoch_params_eq hadd⟩
    · simp [hadd, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic]
    · rw [hcur1, hes_ep, hc']

theorem topStateTight_spqrV1_recv {F : ShaCompress} {K : MlKem}
    {bytes msg bytes' : Bytes} {salt : Salt}
    (h : TopStateTight F K bytes)
    (hrecv : (spqrV1 F K).recv bytes msg = .ok (bytes', salt)) :
    TopStateTight F K bytes' := by
  have hsize : bytes.length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (topStateTight_length_le h) (by unfold spqrStateTightCapBytes; decide)
  obtain ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ := h
  have hpts' := validStatePtsAt_spqrV1_recv (by decide) F K bytes msg bytes' salt
    hw.hpts640 hsize hrecv
  have hcp' := validStateChainParams_spqrV1_recv F K bytes msg bytes' salt
    hw.hcp hsize hrecv
  have htop := hw.htop
  rw [spqrV1_eq] at hrecv
  dsimp only [toSpqrModel] at hrecv
  cases hr : recv (spqrDeps F K) (spqrHkdfWith F) bytes msg with
  | error e => rw [hr] at hrecv; cases e <;> contradiction
  | ok r =>
    rw [hr] at hrecv
    dsimp only at hrecv
    cases hs : recvKeyToSalt? r.key with
    | none => rw [hs] at hrecv; contradiction
    | some _ =>
      rw [hs] at hrecv
      cases hrecv
      have hsize' : (topBytes F K st vn? ch?).length < 2 ^ 64 := htop.hbytes ▸ hsize
      rw [htop.hbytes] at hr
      cases hpre : msgPreamble msg with
      | error _ =>
        unfold recv at hr
        simp [hpre, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
          bind, Except.bind] at hr
      | ok pre =>
        by_cases hver : pre.version = 1#8
        · rw [recv_topBytes F K authKey dir st vn? ch? msg pre hsize' htop.hvn hpre hver] at hr
          have hep_pos : 1 ≤ st.epoch.toNat := partyTop_epoch_pos ⟨vn?, ch?, chE, htop⟩
          unfold recvEqual at hr
          cases hdes : (spqrDeps F K).msgDeserialize pre.epoch pre.remaining with
          | error _ => rw [hdes] at hr; contradiction
          | ok m =>
            rw [hdes, treq_spqrDeps_statesFromPb F K st (st_bCodec F st hw.hbok.1)] at hr
            dsimp [bind, Except.bind] at hr
            cases hsr : (spqrDeps F K).statesRecv st m with
            | error _ => rw [hsr] at hr; contradiction
            | ok ks =>
              rcases ks with ⟨key, st'⟩
              rw [hsr] at hr
              dsimp [bind, Except.bind] at hr
              have hrecvB := treq_statesRecv_ok F K st st' m key hsr
              split_ifs at hr
              have hcf := st_chainFrom_ok F authKey dir secret sendCtr recvSet vn? ch? chE
                htop.hch htop.hok
              obtain ⟨chain1, secret1, hadd, hok1, hcur1, hsend1, hsmall1, hsp1, _⟩ :=
                recv_addEpoch_tight F K authKey dir secret st st' sendCtr recvSet chE
                  htop.hok htop.hcur hep_pos hw.hsmall htop.hsendPrev m key hrecvB
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
                  dsimp [CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
                    CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
                    pure, Except.pure, bind, Except.bind] at hr
                  cases hrk : chE.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
                  | error _ => rw [hrk] at hr; contradiction
                  | ok cm => rw [hrk] at hr; cases hr; exact ⟨cm.1, cm.2, rfl, rfl⟩
                | some es =>
                  dsimp [CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
                    CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
                    bind, Except.bind] at hadd hr
                  rw [hadd] at hr; dsimp at hr
                  cases hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
                  | error _ => rw [hrk] at hr; contradiction
                  | ok cm => rw [hrk] at hr; cases hr; exact ⟨cm.1, cm.2, rfl, rfl⟩
              obtain ⟨recvSet', hok2, hsmall2, hcur2, hsend2⟩ :=
                st_chainRecv_tight F hok1 hsmall1 hrk
              have hbok' : BOkTight st' := by
                cases hek : isEkSide st
                · exact st_bRecvCt_tight F K hek hw.hbok hrecvB
                · exact st_bRecvEk_tight F K hek hw.hbok hrecvB
              exact ⟨authKey, dir, secret1, st', sendEp, sendCtr, recvSet', none,
                some chain2, chain2,
                { htop :=
                    { hbytes := rfl
                      hvn := .inl rfl
                      hch := .inl rfl
                      hok := hok2
                      hcur := by rw [hcur2, hcur1]
                      hsendEp := by rw [hsend2, hsend1, htop.hsendEp]
                      hsendLe := htop.hsendLe.trans (treq_recv_epoch_le F K st st' m key hrecvB)
                      hsendPrev := recvKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 _ _ _
                        hsp1 hrk }
                  hauth := hw.hauth
                  hbok := hbok'
                  hphi_send := ((st_bPhi F K).2 st st' m key hrecvB).trans hw.hphi_send
                  hsmall := hsmall2
                  hpts640 := hpts'
                  hcp := hcp' }⟩
        · have hcf := st_chainFrom_ok F authKey dir secret sendCtr recvSet vn? ch? chE
            htop.hch htop.hok
          rcases htop.hvn with rfl | rfl
          · unfold recv at hr
            rw [hpre, decodeState_topBytes F K st none ch? hsize'] at hr
            dsimp only [spqrDeps, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
              bind, Except.bind, topPb, stateVersion, Version.toU8] at hr
            have hbne : (pre.version != 1#8) = true := bne_iff_ne.mpr hver
            by_cases hlt : pre.version < 1#8 <;> simp [hlt, hbne] at hr
          · unfold recv at hr
            rw [hpre, decodeState_topBytes F K st (some (vnOf dir authKey)) ch? hsize'] at hr
            by_cases hlt : pre.version < 1#8
            · change (if pre.version < 1#8 then
                  Except.error
                    (CryptoVerification.LibsignalSpqrV1.SpqrApiError.err Error.minimumVersion)
                else _) = Except.ok r at hr
              simp only [hlt, ↓reduceIte] at hr; contradiction
            · have hgt : pre.version > 1#8 := by
                simp only [gt_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat] at hlt ⊢
                have hne : pre.version.toNat ≠ 1 := fun h => hver (BitVec.eq_of_toNat_eq h)
                omega
              change (if pre.version < 1#8 then _
                else if (pre.version != 1#8 && !true) = true then _
                else if (1#8 == 0#8) = true then _
                else if pre.version > 1#8 then
                  do
                    let chain0 ← CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError
                      (chainFrom (spqrHkdfWith F) (ch?.map Chain.intoPb) (some (vnOf dir authKey)))
                    let __x ← CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult
                      (chain0.recvKey (spqrHkdfWith F) 0#64 pre.index)
                    Except.ok {
                      key := some __x.2
                      state := topBytes F K st (some (vnOf dir authKey)) (some __x.1)
                    }
                else _) = Except.ok r at hr
              simp only [hlt, hgt, Bool.not_true, Bool.and_false, ↓reduceIte] at hr
              rw [hcf] at hr
              dsimp only [CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
                CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult,
                bind, Except.bind] at hr
              cases hrk : chE.recvKey (spqrHkdfWith F) 0#64 pre.index with
              | error _ => rw [hrk] at hr; contradiction
              | ok cm =>
                rcases cm with ⟨chain1, rawKey⟩
                rw [hrk] at hr; cases hr
                obtain ⟨recvSet', hok', hsmall', hcur', hsendEp'⟩ :=
                  st_chainRecv_tight F htop.hok hw.hsmall hrk
                exact ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet',
                  some (vnOf dir authKey), some chain1, chain1,
                  { htop :=
                      { hbytes := rfl
                        hvn := Or.inr rfl
                        hch := Or.inl rfl
                        hok := hok'
                        hcur := by rw [hcur', htop.hcur]
                        hsendEp := by rw [hsendEp', htop.hsendEp]
                        hsendLe := htop.hsendLe
                        hsendPrev := recvKey_sendPrevNil (spqrHkdfWith F) chE chain1 0#64
                          pre.index rawKey htop.hsendPrev hrk }
                    hauth := hw.hauth
                    hbok := hw.hbok
                    hphi_send := hw.hphi_send
                    hsmall := hsmall'
                    hpts640 := hpts'
                    hcp := hcp' }⟩

/-! ## 3. Decoded and Post-Step Bounds for `SpqrRecvTightDomain` -/

/-- Decoded `spqrDecodeState` and post-`States.recv` / post-`addEpoch` / post-`recvKey` tight bounds
implied by `TopStateTight F K stBytes`. -/
theorem topStateTight_decode_props {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (h : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb) :
    (∀ vn, pre_pb.versionNegotiation = some vn → vn.authKey.length ≤ 32 ∧ rawVN vn ≤ 32) ∧
    (∀ c, pre_pb.chain = some c → c.links.length ≤ 3) ∧
    (∀ pb, pre_pb.inner = some (.v1 pb) → rawV1State pb ≤ 46880 ∧ ValidV1PtsAt 640 pb) ∧
    (∃ ch0 : Chain,
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok ch0 ∧
      ch0.links.length ≤ 3 ∧
      RecvSmallTight ch0 ∧
      ValidChainParamsPB ch0.params ∧
      (∀ (c : Chain) (ep : Epoch) (idx : BitVec 32) (rawKey : Bytes),
        ch0.recvKey (spqrHkdfWith F) ep idx = .ok (c, rawKey) →
        rawChain c.intoPb ≤ 238532) ∧
      (∀ (pb : V1State) (st0 : States spqrPolyApi (spqrAuthApi F))
          (sckaMsg : Message spqrPolyApi) (v : V1Recv spqrPolyApi (spqrAuthApi F)),
        pre_pb.inner = some (.v1 pb) →
        States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
        States.recv K st0 sckaMsg = .ok v →
        rawV1State v.state.into_pb ≤ 46880 ∧
        ∃ ch1 : Chain,
          (match v.key with
           | some es => ch0.addEpoch (spqrHkdfWith F) es
           | none => .ok ch0) = .ok ch1 ∧
          ch1.links.length ≤ 3 ∧
          RecvSmallTight ch1 ∧
          ValidChainParamsPB ch1.params ∧
          (∀ (c : Chain) (ep : Epoch) (idx : BitVec 32) (rawKey : Bytes),
            ch1.recvKey (spqrHkdfWith F) ep idx = .ok (c, rawKey) →
            rawChain c.intoPb ≤ 238532))) := by
  obtain ⟨hpts640, hcp, hlt31⟩ := topStateTight_to_tightValid640 h
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ := h
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq : stBytes = encodeState (pbToPqRatchetState (topPb st vn? ch?)) := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hdec
  have hpre := Except.ok.inj hdec; subst hpre
  have hlinks3 : chE.links.length ≤ 3 := topStateTightW_links_le_three hw
  have hcf : chainFrom (spqrHkdfWith F)
      (pbToPqRatchetState (topPb st vn? ch?)).chain
      (pbToPqRatchetState (topPb st vn? ch?)).versionNegotiation = .ok chE :=
    st_chainFrom_ok F authKey dir secret sendCtr recvSet vn? ch? chE hw.htop.hch hw.htop.hok
  have hcp_dec : LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux.ValidPqChainParams
      (pbToPqRatchetState (topPb st vn? ch?)) := by
    unfold ValidChainParams at hcp
    rw [hdec_eq] at hcp
    exact hcp
  have hpts_dec : LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux.ValidPqPtsAt 640
      (pbToPqRatchetState (topPb st vn? ch?)) := by
    unfold ValidEncoderPts640 LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux.ValidEncoderPtsAt at hpts640
    rw [hdec_eq] at hpts640
    exact hpts640
  have hchE_params : ValidChainParamsPB chE.params :=
    validChainParamsPB_of_chainFrom hcp_dec.1 hcp_dec.2 hcf
  refine ⟨?_, ?_, ?_, ⟨chE, hcf, hlinks3, hw.hsmall, hchE_params, ?_, ?_⟩⟩
  · intro vn hvn
    rcases hw.htop.hvn with rfl | rfl
    · simp [pbToPqRatchetState, topPb] at hvn
    · simp only [pbToPqRatchetState, topPb, Option.some.injEq] at hvn
      subst hvn
      simp [vnOf, rawVN, hw.hauth]
  · intro c hc
    rcases hw.htop.hch with rfl | ⟨rfl, -, -⟩
    · simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hc
      subst hc
      simpa [Chain.intoPb] using hlinks3
    · simp [pbToPqRatchetState, topPb, Option.map] at hc
  · intro pb hpb
    simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hpb
    cases hpb
    have hv1_pts : ValidV1PtsAt 640 st.into_pb := by
      simpa [LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux.ValidPqPtsAt,
        pbToPqRatchetState, topPb] using hpts_dec
    exact ⟨st_bSize_tight F st hw.hbok, hv1_pts⟩
  · intro c ep idx rawKey hrk
    obtain ⟨recvSet', hok', hsmall', hcur', hsend'⟩ :=
      st_chainRecv_tight F hw.htop.hok hw.hsmall hrk
    have hsp' := recvKey_sendPrevNil (spqrHkdfWith F) chE c ep idx rawKey hw.htop.hsendPrev hrk
    have hc_links : c.links.length ≤ 3 := by
      have := hok'.hlen
      have := hw.htop.hok.hlen
      rw [hcur', hsend'] at *
      omega
    exact tsz_rawChain_tight_le F authKey dir secret sendCtr recvSet' c hok' hsp' hsmall' hc_links
  · intro pb st0 sckaMsg v hpb hfrom hrecv_st
    simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hpb
    cases hpb
    have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st :=
      st_bCodec F st hw.hbok.1
    rw [hcodec] at hfrom
    have hst0 := Except.ok.inj hfrom; subst hst0
    rcases v with ⟨key, st1⟩
    have hbok1 : BOkTight st1 := by
      cases hek : isEkSide st
      · exact st_bRecvCt_tight F K hek hw.hbok hrecv_st
      · exact st_bRecvEk_tight F K hek hw.hbok hrecv_st
    have hep_pos : 1 ≤ st.epoch.toNat := partyTop_epoch_pos ⟨vn?, ch?, chE, hw.htop⟩
    obtain ⟨ch1, secret1, hadd_api, hok1, hcur1, hsend1, hsmall1, hsp1, hparams1⟩ :=
      recv_addEpoch_tight F K authKey dir secret st st1 sendCtr recvSet chE
        hw.htop.hok hw.htop.hcur hep_pos hw.hsmall hw.htop.hsendPrev sckaMsg key hrecv_st
    have hadd_raw : (match key with
        | some es => chE.addEpoch (spqrHkdfWith F) es
        | none => .ok chE) = .ok ch1 := by
      cases key with
      | none =>
        dsimp only at hadd_api ⊢
        cases hadd_api
        rfl
      | some es =>
        cases ha : chE.addEpoch (spqrHkdfWith F) es with
        | error _ =>
          simp [ha, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hadd_api
        | ok c =>
          simp only [ha, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic,
            Except.ok.injEq] at hadd_api
          subst hadd_api
          dsimp only
          exact ha
    have hphi1 : phiB st1 ≤ sendEp + 1 :=
      ((st_bPhi F K).2 st st1 sckaMsg key hrecv_st).trans hw.hphi_send
    have hch1_links : ch1.links.length ≤ 3 := by
      have hlen1 := hok1.hlen
      have hse : ch1.sendEpoch.toNat = sendEp := by rw [hsend1, hw.htop.hsendEp]
      have hcphi := chainCur_le_phiB st1
      rw [hcur1, hse] at hlen1
      omega
    refine ⟨st_bSize_tight F st1 hbok1, ch1, hadd_raw, hch1_links, hsmall1,
      hparams1 ▸ hchE_params, ?_⟩
    intro c ep idx rawKey hrk
    obtain ⟨recvSet', hok2, hsmall2, hcur2, hsend2⟩ :=
      st_chainRecv_tight F hok1 hsmall1 hrk
    have hsp2 := recvKey_sendPrevNil (spqrHkdfWith F) ch1 c ep idx rawKey hsp1 hrk
    have hc_links : c.links.length ≤ 3 := by
      have := hok2.hlen
      have := hok1.hlen
      rw [hcur2, hsend2] at *
      omega
    exact tsz_rawChain_tight_le F authKey dir secret1 sendCtr recvSet' c hok2 hsp2 hsmall2 hc_links

end LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
