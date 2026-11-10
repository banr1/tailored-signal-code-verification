/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementIdsModel
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.E2E.Record.Support.Phi
import LibsignalBinary.Proofs.TripleRatchet.Seeds.Model
import ProofLib.SepLogic.WP.StepsCore
import VCVio.EvalDist.Monad.Basic
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionSMProofDefs

/-!
# Helper lemmas for the `.ij` arm of the binary-harness adapter coupling

Proves tag-byte wire rejection, one-step SPQR-V1 state growth bounds (`+ 8000` send, `+ 80000`
receive), and session invariant preservation across accepted whisper-receive steps.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.BhAdapterIjHelpersV1

open CryptoGames CryptoGames.LibsignalSession

theorem tryFrom_error_of_head (codec : SignalMessageProtoCodec) (value : List (BitVec 8))
    (h : value = [] ∨ (value.headD 0) >>> 4 < preKyberVersion) :
    ∃ e, SignalMessage.tryFrom codec value = .error e := by
  unfold SignalMessage.tryFrom
  by_cases hlen : value.length < macLength + 1
  · simp only [hlen, ↓reduceIte]
    exact ⟨_, rfl⟩
  · rcases h with rfl | hv
    · simp at hlen
    · simp only [hlen, ↓reduceIte, List.headD_eq_head?_getD] at hv ⊢
      simp only [hv, ↓reduceIte]
      exact ⟨_, rfl⟩

theorem wireWhisper_shr_lt : (wireWhisper : BitVec 8) >>> 4 < preKyberVersion := by
  unfold wireWhisper preKyberVersion; decide
theorem wirePrekey_shr_lt : (wirePrekey : BitVec 8) >>> 4 < preKyberVersion := by
  unfold wirePrekey preKyberVersion; decide

theorem params_receive_none_of_head {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC)
    (g : GhostState PQ) (c : List (BitVec 8)) (rc : BitVec 256)
    (h : c = [] ∨ (c.headD 0) >>> 4 < preKyberVersion) :
    P.receive g c rc = none := by
  rcases tryFrom_error_of_head P.codec c h with ⟨e, he⟩
  unfold Params.receive
  rw [he]

theorem params_receive_nil {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC)
    (g : GhostState PQ) (rc : BitVec 256) : P.receive g [] rc = none :=
  params_receive_none_of_head P g [] rc (Or.inl rfl)

theorem params_receive_wireWhisper_cons {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC)
    (g : GhostState PQ) (rest : List (BitVec 8)) (rc : BitVec 256) :
    P.receive g (wireWhisper :: rest) rc = none :=
  params_receive_none_of_head P g _ rc (Or.inr wireWhisper_shr_lt)

theorem params_receive_wirePrekey_cons {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC)
    (g : GhostState PQ) (rest : List (BitVec 8)) (rc : BitVec 256) :
    P.receive g (wirePrekey :: rest) rc = none :=
  params_receive_none_of_head P g _ rc (Or.inr wirePrekey_shr_lt)

section InjectR
open OracleComp OracleSpec
variable {Key St Msg Coins RCoins C : Type} [DecidableEq C] [SampleableType RCoins]

def injectPost (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (s : SM.GameState St Msg C) (P : Party) (c : C) (rc : RCoins) :
    Option (SM.RecvResult Msg) × SM.GameState St Msg C :=
  match sm.receive (s.st P) c rc with
  | none => (some .rejected, s)
  | some (st', t', i', m') =>
    if qep + 1 < t' then (some .rejected, s)
    else if s.trivial Δ ⟨P.other, t', i'⟩ then
      (some (.accepted t' i' (some m')), s.accept P st' ⟨P.other, t', i'⟩)
    else if cfg.base.injectFull t' then (some .rejected, { s with win := true })
    else (some .rejected, s)

theorem injectR_run [DecidableEq Msg] [SampleableType Coins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (s : SM.GameState St Msg C) (P : Party) (c : C) :
    (SM.injectR sm Δ qep cfg ⟨P, c⟩).run s =
      if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c) then
        pure (none, s)
      else ($ᵗ RCoins : ProbComp RCoins) >>= fun rc => pure (injectPost sm Δ qep cfg s P c rc) := by
  unfold SM.injectR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with h
  · simp
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    congr 1; funext rc
    unfold injectPost
    rcases sm.receive (s.st P) c rc with _ | ⟨st', t', i', m'⟩
    · simp
    · simp only
      split_ifs <;> simp

end InjectR

theorem ratchetKeyOnCurve_of_head_lt {Pt : Type} [DecidableEq PublicKey] (codec : SignalMessageProtoCodec)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (t : BitVec 8) (rest : List (BitVec 8))
    (ht : t >>> 4 < preKyberVersion) :
    Ratchet.LibsignalInst.ratchetKeyAdmissible codec decT encT (t :: rest) = true := by
  unfold Ratchet.LibsignalInst.ratchetKeyAdmissible
  split_ifs with hlen
  · rfl
  · have hpos : 0 < (t :: rest).length - 8 := by simp at hlen ⊢; omega
    obtain ⟨k, hk⟩ : ∃ k, (t :: rest).length - 8 = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hk]
    rcases tryFrom_error_of_head codec
        ((t :: rest).take (k + 1) ++ List.replicate macLength 0) (Or.inr (by simpa using ht))
      with ⟨e, he⟩
    simp only [signalWireCodec, he]

theorem ratchetKeyOnCurve_wireWhisper_cons {Pt : Type} [DecidableEq PublicKey] (codec : SignalMessageProtoCodec)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (rest : List (BitVec 8)) :
    Ratchet.LibsignalInst.ratchetKeyAdmissible codec decT encT (wireWhisper :: rest) = true :=
  ratchetKeyOnCurve_of_head_lt codec decT encT _ rest wireWhisper_shr_lt

theorem ratchetKeyOnCurve_wirePrekey_cons {Pt : Type} [DecidableEq PublicKey] (codec : SignalMessageProtoCodec)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (rest : List (BitVec 8)) :
    Ratchet.LibsignalInst.ratchetKeyAdmissible codec decT encT (wirePrekey :: rest) = true :=
  ratchetKeyOnCurve_of_head_lt codec decT encT _ rest wirePrekey_shr_lt

/-! ## One-step SPQR-V1 state growth bounds -/

section TightSpqrGrowth

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.HKDF (Salt)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1Sync.Codec (decodeState_spqrDeps_encodeState_pb)

@[local simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (pure x >>= f) = f x := rfl
@[local simp] private theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'}
    {m : Except ε α} {a : α} : m.mapError f = .ok a ↔ m = .ok a := by cases m <;> simp [Except.mapError]
@[local simp] private theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [liftSpqrPanic]
@[local simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [StatesResult.ofPanic]

private theorem poly_nextChunk_liftM_eq_ok {enc enc' : PolyEncoder} {chunk : Chunk}
    (h : (liftM (spqrPolyApi.next_chunk enc) :
      Except StatesPanic (spqrPolyApi.PolyEncoder × spqrPolyApi.Chunk)) = .ok (enc', chunk)) :
    enc.nextChunk = .ok (enc', chunk) := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
private theorem poly_addChunk_liftM_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : (liftM (spqrPolyApi.add_chunk dec chunk) : Except StatesPanic spqrPolyApi.PolyDecoder) = .ok dec') :
    dec.addChunk chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
private theorem poly_addChunk_ofPanic_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : StatesResult.ofPanic (spqrPolyApi.add_chunk dec chunk) = .ok dec') :
    dec.addChunk chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only at h; exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)
private theorem poly_decodedMessage_liftM_eq_ok {dec : PolyDecoder} {msg? : Option Bytes}
    (h : (liftM (spqrPolyApi.decoded_message dec) : Except StatesPanic (Option Bytes)) = .ok msg?) :
    dec.decodedMessage = .ok msg? := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
private theorem poly_decoderNew_ofPanic_eq_ok {lenBytes : Nat}
    {res : Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder}
    (h : StatesResult.ofPanic (spqrPolyApi.decoder_new lenBytes) = .ok res) :
    PolyDecoder.new lenBytes = .ok res := by
  unfold spqrPolyApi at h; dsimp only at h; exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)

private theorem flatMap_u16ToBeBytes_length (l : List GF16) :
    (l.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have : (u16ToBeBytes g.value).length = 2 := rfl
    omega

private theorem map_intoPb_encoder_pts' (pts : List Point) :
    ((pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).map (fun b => b.length + 22)) =
      pts.map pointRaw := by
  induction pts with
  | nil => rfl
  | cons pt ps ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [pointRaw, flatMap_u16ToBeBytes_length]

theorem PolyEncoder.encodeBytes_raw_le_msg {msg : List (BitVec 8)} {enc : PolyEncoder}
    (h : PolyEncoder.encodeBytes msg = .ok (.ok enc)) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase at h; split at h
  · simp [Pure.pure, Except.pure] at h
  · split at h
    · simp [Pure.pure, Except.pure] at h
    · rcases hpts : PolyEncoder.distributeMsgChunks 0 msg (List.replicate NUM_POLYS { value := [] }) with e | pts
      · simp [hpts, Bind.bind, Except.bind] at h
      · simp only [hpts, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at h; subst h
        have hsum := PolyEncoder.distributeMsgChunks_sum_le 0 msg (List.replicate NUM_POLYS { value := [] }) hpts
        have hinit : ((List.replicate NUM_POLYS ({ value := [] } : Point)).map pointRaw).sum = 352 := rfl
        simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, rawPolyEnc,
          map_intoPb_encoder_pts', List.map_nil, List.sum_nil]; omega

theorem expectEncodeBytes_raw_le_msg {site : String} {msg : Bytes} {enc : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold expectEncodeBytes spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
  have h1' := except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h1); cases res with
  | error _ => contradiction
  | ok enc' => have hinj := Except.ok.inj h2; subst hinj; exact PolyEncoder.encodeBytes_raw_le_msg h1'

private theorem encaps2_length {K : MlKem} {ek es ct2 : Bytes}
    (h : encaps2 K ek es = .ok ct2) : ct2.length = 128 := by
  unfold encaps2 at h
  rcases except_bind_eq_ok h with ⟨maybeFix, _, h⟩; dsimp only [] at h
  split at h <;> try contradiction
  injection h with h; subst h; exact List.Vector.toList_length _

private theorem spqrAuthApi_macHdr_length {F : ShaCompress} {auth : Authenticator} {ep : Epoch} {hdr macB : Bytes}
    (h : (liftM ((spqrAuthApi F).mac_hdr auth ep hdr) : Except StatesPanic Bytes) = .ok macB) :
    macB.length = 32 := by
  unfold spqrAuthApi Authenticator.macHdr at h
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rw [liftSpqrPanic_eq_ok] at h
  split at h <;> [skip; contradiction]
  injection h with h; subst h; exact Authenticator.length_macHdrUnchecked F auth ep hdr

private theorem spqrAuthApi_macCt_length {F : ShaCompress} {auth : Authenticator} {ep : Epoch} {ct macB : Bytes}
    (h : (liftM ((spqrAuthApi F).mac_ct auth ep ct) : Except StatesPanic Bytes) = .ok macB) :
    macB.length = 32 := by
  unfold spqrAuthApi Authenticator.macCt at h
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rw [liftSpqrPanic_eq_ok] at h
  split at h <;> [skip; contradiction]
  injection h with h; subst h; exact Authenticator.length_macCtUnchecked F auth ep ct

@[local simp] private theorem spqrPolyApi_encoder_into_pb (enc : spqrPolyApi.PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl
@[local simp] private theorem spqrPolyApi_encoder_into_pb' (enc : PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl
@[local simp] private theorem spqrPolyApi_decoder_into_pb (dec : spqrPolyApi.PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl
@[local simp] private theorem spqrPolyApi_decoder_into_pb' (dec : PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl
@[local simp] private theorem spqrAuthApi_into_pb {F : ShaCompress}
    (a : (spqrAuthApi F).Authenticator) : (spqrAuthApi F).into_pb a = Authenticator.intoPb a := rfl
@[local simp] private theorem spqrAuthApi_into_pb' {F : ShaCompress} (a : Authenticator) :
    (spqrAuthApi F).into_pb a = Authenticator.intoPb a := rfl
@[local simp] private theorem spqrAuthApi_from_pb {F : ShaCompress} (pb : ProtoAuthenticator) :
    (spqrAuthApi F).from_pb pb = Authenticator.fromPb pb := rfl

attribute [local simp]
  States.into_pb Chunked.SendEk.KeysUnsampled.into_pb Chunked.SendEk.KeysSampled.into_pb
  Chunked.SendEk.HeaderSent.into_pb Chunked.SendEk.Ct1Received.into_pb
  Chunked.SendEk.EkSentCt1Received.into_pb Chunked.SendCt.NoHeaderReceived.into_pb
  Chunked.SendCt.HeaderReceived.into_pb Chunked.SendCt.Ct1Sampled.into_pb
  Chunked.SendCt.EkReceivedCt1Sampled.into_pb Chunked.SendCt.Ct1Acknowledged.into_pb
  Chunked.SendCt.Ct2Sampled.into_pb
  Unchunked.SendEk.KeysUnsampled.into_pb Unchunked.SendEk.HeaderSent.into_pb
  Unchunked.SendEk.EkSent.into_pb Unchunked.SendEk.EkSentCt1Received.into_pb
  Unchunked.SendCt.NoHeaderReceived.into_pb Unchunked.SendCt.HeaderReceived.into_pb
  Unchunked.SendCt.Ct1Sent.into_pb Unchunked.SendCt.Ct1SentEkReceived.into_pb
  Unchunked.SendCt.Ct2Sent.into_pb
  rawV1State rawInnerState rawChKeysUnsampled rawChKeysSampled
  rawChHeaderSent rawChCt1Received rawChEkSentCt1Received rawChNoHeaderReceived rawChHeaderReceived
  rawChCt1Sampled rawChEkReceivedCt1Sampled rawChCt1Acknowledged rawChCt2Sampled
  rawUcKeysUnsampled rawUcHeaderSent rawUcEkSent rawUcEkSentCt1Received
  rawUcNoHeaderReceived rawUcHeaderReceived rawUcCt1Sent rawUcCt1SentEkReceived rawUcCt2Sent
  Option.map optRaw_none optRaw_some Authenticator.rawAuth_intoPb_fromPb

private theorem States.send_raw_le_tight {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {tape tape' : Bytes}
    {sendOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hpts : StatesPtsNeededBound self) (h : self.send K tape = .ok (sendOut, tape')) :
    rawV1State sendOut.state.into_pb ≤ rawV1State self.into_pb + 4960 ∧
      StatesPtsNeededBound sendOut.state := by
  have hpts' := (States.send_raw_le hpts h).2
  refine ⟨?_, hpts'⟩
  unfold States.send at h; cases self with
  | keysUnsampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk, tape1⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk Unchunked.SendEk.KeysUnsampled.send_header at h1
    dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨⟨uc, toSend, mac, tape2⟩, huc, h1b⟩
    rcases except_bind_eq_ok huc with ⟨⟨keys, tape3⟩, hgen, huc2⟩; rcases except_bind_eq_ok huc2 with ⟨mac', hmac', huc3⟩
    have huc_inj := Prod.mk.inj (Except.ok.inj huc3)
    have huc_eq := huc_inj.1
    have htoSend_eq : toSend = keys.hdr := (Prod.mk.inj huc_inj.2).1.symm
    have hmac_eq : mac = mac' := (Prod.mk.inj (Prod.mk.inj huc_inj.2).2).1.symm
    subst huc_eq htoSend_eq hmac_eq
    rcases except_bind_eq_ok h1b with ⟨enc0, henc0, h1c⟩; rcases except_bind_eq_ok h1c with ⟨⟨enc1, chunk1⟩, hnext, h1d⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1d)).1; subst hst_eq
    rcases generate_lengths hgen with ⟨hek, hdk, hhdr⟩
    have hmac_len := spqrAuthApi_macHdr_length hmac'
    have henc0_le := expectEncodeBytes_raw_le_msg henc0
    rw [List.length_append, hhdr, hmac_len] at henc0_le
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
    simp [hek, hdk]; omega
  | keysSampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendEk.KeysSampled.send_hdr_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); simp; omega
  | headerSent state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendEk.HeaderSent.send_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); simp; omega
  | ct1Received state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendEk.Ct1Received.send_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); simp; omega
  | ekSentCt1Received state =>
    dsimp only [] at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; dsimp only []; omega
  | noHeaderReceived state =>
    dsimp only [] at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; dsimp only []; omega
  | headerReceived state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk, sec, tape1⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk Unchunked.SendCt.HeaderReceived.send_ct1 at h1
    dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨⟨uc, ct1, sec1, tape2⟩, huc, h1b⟩
    rcases except_bind_eq_ok huc with ⟨⟨⟨ct1', es, ss⟩, tape3⟩, henc1, huc2⟩; rcases except_bind_eq_ok huc2 with ⟨secret, _, huc3⟩
    rcases except_bind_eq_ok huc3 with ⟨auth, hauth, huc4⟩; unfold spqrAuthApi at hauth
    dsimp only [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic] at hauth
    have hauth_eq := Except.ok.inj hauth; subst hauth_eq; have huc_inj := Prod.mk.inj (Except.ok.inj huc4)
    have huc_eq := huc_inj.1; have hct1_eq := (Prod.mk.inj huc_inj.2).1; subst huc_eq; subst hct1_eq
    rcases except_bind_eq_ok h1b with ⟨enc0, henc0, h1c⟩; rcases except_bind_eq_ok h1c with ⟨⟨enc1, chunk1⟩, hnext, h1d⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1d)).1; subst hst_eq; rcases encaps1_lengths henc1 with ⟨hct1_len, hes_len, _⟩
    have hauth_le := Authenticator.update_rawAuth_le F state.uc.auth state.uc.epoch secret
    have henc0_le := expectEncodeBytes_raw_le_msg henc0
    rw [hct1_len] at henc0_le
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
    simp [hct1_len, hes_len]; omega
  | ct1Sampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendCt.Ct1Sampled.send_ct1_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); simp; omega
  | ekReceivedCt1Sampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); simp; omega
  | ct1Acknowledged state =>
    dsimp only [] at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; dsimp only []; omega
  | ct2Sampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendCt.Ct2Sampled.send_ct2_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); simp; omega

private theorem send_ct2_encode_raw_le_tight {F : ShaCompress} {K : MlKem}
    {uc : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    {uc2 : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)}
    {ct2 macB : Bytes} {sendingCt2 : PolyEncoder}
    (hct2 : uc.send_ct2 K = .ok (uc2, ct2, macB))
    (henc2 : expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:162" (ct2 ++ macB) = .ok sendingCt2) :
    uc2 = { epoch := uc.epoch, auth := uc.auth } ∧
      rawPolyEnc (protoPolyEncoderToPb sendingCt2.intoPb) ≤ 512 := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at hct2; dsimp only [] at hct2
  rcases except_bind_eq_ok hct2 with ⟨ct2', hcap, hct2b⟩
  rcases except_bind_eq_ok hct2b with ⟨mac', hmac, hct2c⟩
  have hinj := Except.ok.inj hct2c
  have huc2 : uc2 = { epoch := uc.epoch, auth := uc.auth } := (Prod.mk.inj hinj).1.symm
  have hct2_eq : ct2 = ct2' := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
  have hmac_eq : macB = mac' := (Prod.mk.inj (Prod.mk.inj hinj).2).2.symm
  subst huc2 hct2_eq hmac_eq
  have hlen1 := encaps2_length hcap
  have hlen2 := spqrAuthApi_macCt_length hmac
  have henc := expectEncodeBytes_raw_le_msg henc2
  rw [List.length_append, hlen1, hlen2] at henc; exact ⟨rfl, by omega⟩

set_option maxHeartbeats 400000 in
private theorem States.recv_raw_le_tight {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hpts : StatesPtsNeededBound self) (h : self.recv K msg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State self.into_pb + 4960 ∧
      StatesPtsNeededBound recvOut.state := by
  have hpts' := (States.recv_raw_le hpts h).2
  refine ⟨?_, hpts'⟩
  unfold States.recv at h; cases self with
  | keysUnsampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | keysSampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      have hinj := Except.ok.inj h2; subst hinj
      unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec0, hdec0, h1b⟩; rcases except_bind_eq_ok h1b with ⟨dec1, hadd, h1c⟩
      rcases except_bind_eq_ok h1c with ⟨enc0, henc0, h1d⟩; have hs' := Except.ok.inj h1d; subst hs'
      rcases expectDecoderNew_raw_le hdec0 with ⟨hdec0_le, _⟩
      have hadd' := poly_addChunk_liftM_eq_ok hadd; have hadd_le := PolyDecoder.addChunk_raw_le hadd'
      have henc0_le := expectEncodeBytes_raw_le_msg henc0
      simp [Unchunked.SendEk.HeaderSent.send_ek] at henc0_le ⊢; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | headerSent state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, hmsg, h1c⟩
      have hadd' := poly_addChunk_liftM_eq_ok hadd; have hmsg' := poly_decodedMessage_liftM_eq_ok hmsg
      have hadd_le := PolyDecoder.addChunk_raw_le hadd'; have hadd_pts := PolyDecoder.addChunk_ptsNeeded hadd'
      cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; simp; omega
      | some decoded =>
        rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
        have hres := Except.ok.inj h1d; subst hres; have hinj := Except.ok.inj h2; subst hinj
        unfold Unchunked.SendEk.EkSent.recv_ct1 at huc; split at huc <;> [contradiction; skip]
        have huc_eq := Except.ok.inj huc; subst huc_eq; have hdec_len := PolyDecoder.decodedMessage_length hmsg'
        simp only [StatesPtsNeededBound] at hpts; simp [hdec_len, hadd_pts]; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | ct1Received state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      have hinj := Except.ok.inj h2; subst hinj
      unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec0, hdec0, h1b⟩; rcases except_bind_eq_ok h1b with ⟨dec1, hadd, h1c⟩
      have hs' := Except.ok.inj h1c; subst hs'; have hdec0_le := (expectDecoderNew_raw_le hdec0).1
      have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_liftM_eq_ok hadd); simp; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | ekSentCt1Received state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      unfold Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd); cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; simp; omega
      | some ct2Full =>
        dsimp only [] at h1c; split at h1c <;> [contradiction; skip]
        rcases except_bind_eq_ok h1c with ⟨⟨uc, sec⟩, huc, h1d⟩; rcases except_bind_eq_ok h1d with ⟨receivingHdr, hdec0, h1e⟩
        rw [statesResult_ofPanic_eq_ok] at hdec0; have hres := Except.ok.inj h1e; subst hres; have hinj := Except.ok.inj h2; subst hinj
        unfold Unchunked.SendEk.EkSentCt1Received.recv_ct2 at huc; dsimp only [] at huc
        rcases except_bind_eq_ok huc with ⟨ss0, _, huc1⟩; rcases except_bind_eq_ok huc1 with ⟨ss, _, huc2⟩
        rcases except_bind_eq_ok huc2 with ⟨auth, hauth, huc3⟩; rcases except_bind_eq_ok huc3 with ⟨verifyRes, _, huc4⟩
        unfold spqrAuthApi at hauth; dsimp only [StatesResult.ofPanic] at hauth
        have hauth_eq := Except.ok.inj hauth; subst hauth_eq; cases verifyRes with
        | error _ => contradiction
        | ok u =>
          cases u; dsimp only [] at huc4; split at huc4 <;> [contradiction; skip]
          have huc_eq := (Prod.mk.inj (Except.ok.inj huc4)).1; subst huc_eq
          have hauth_le := Authenticator.update_rawAuth_le F state.uc.auth state.uc.epoch ss
          have hdec0_le := (expectDecoderNew_raw_le hdec0).1; simp; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | noHeaderReceived state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      unfold Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd); cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; simp; omega
      | some hdrFull =>
        dsimp only [] at h1c; split at h1c <;> [contradiction; skip]
        rcases except_bind_eq_ok h1c with ⟨receivingEkRes, hek0, h1d⟩; rcases except_bind_eq_ok h1d with ⟨uc, huc, h1e⟩
        have hek0' := poly_decoderNew_ofPanic_eq_ok hek0; cases receivingEkRes with
        | error _ => contradiction
        | ok receivingEk =>
          have hres := Except.ok.inj h1e; subst hres; have hinj := Except.ok.inj h2; subst hinj
          unfold Unchunked.SendCt.NoHeaderReceived.recv_header at huc; split at huc <;> [contradiction; skip]
          rcases except_bind_eq_ok huc with ⟨verifyRes, _, huc2⟩; cases verifyRes with
          | error _ => contradiction
          | ok u =>
            cases u; have huc_eq := Except.ok.inj huc2; subst huc_eq
            have hek_le := PolyDecoder.new_raw_le hek0'; simp [HEADER_SIZE]; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | headerReceived state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | ct1Sampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨receivingEk, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd); cases decoded? with
    | none =>
      dsimp only [] at h1c; split at h1c <;>
        (have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; simp; omega)
    | some decoded =>
      dsimp only [] at h1c; rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      unfold Unchunked.SendCt.Ct1Sent.recv_ek at huc; split at huc <;> [contradiction; skip]
      split at huc <;> [skip; contradiction]; rename_i hek_match; have huc_eq := Except.ok.inj huc; subst huc_eq
      have hek_len := ek_matches_header_length hek_match; split at h1d
      · rcases except_bind_eq_ok h1d with ⟨⟨uc2, ct2, mac⟩, hct2, h1e⟩
        rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩; rw [statesResult_ofPanic_eq_ok] at hct2 henc2
        have hres := Except.ok.inj h1f; subst hres; have hinj := Except.ok.inj h2; subst hinj
        obtain ⟨huc2_eq, henc2_le⟩ := send_ct2_encode_raw_le_tight hct2 henc2
        subst huc2_eq; simp; omega
      · have hres := Except.ok.inj h1d; subst hres; have hinj := Except.ok.inj h2; subst hinj
        simp [hek_len]; omega
  | ekReceivedCt1Sampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    have hisAck : ∀ b : Bool, (if b = true then do
        let s' ← StatesResult.ofPanic (state.recv_ct1_ack K msg.epoch)
        Except.ok ({ state := States.ct2Sampled s', key := none } : V1Recv spqrPolyApi (spqrAuthApi F))
      else Except.ok { state := States.ekReceivedCt1Sampled state, key := none }) = .ok recvOut →
      rawV1State recvOut.state.into_pb ≤ rawV1State (States.ekReceivedCt1Sampled state).into_pb + 4960 := by
      intro b hb; cases b
      · have hinj := Except.ok.inj hb; subst hinj; dsimp only []; omega
      · simp only [ite_true] at hb; rcases except_bind_eq_ok hb with ⟨s', h1, h2⟩
        rw [statesResult_ofPanic_eq_ok] at h1; have hinj := Except.ok.inj h2; subst hinj
        unfold Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at h1
        dsimp only [] at h1; split at h1 <;> [contradiction; skip]
        rcases except_bind_eq_ok h1 with ⟨⟨uc2, ct2, mac⟩, hct2, h1b⟩
        rcases except_bind_eq_ok h1b with ⟨sendingCt2, henc2, h1c⟩; have hs' := Except.ok.inj h1c; subst hs'
        obtain ⟨huc2_eq, henc2_le⟩ := send_ct2_encode_raw_le_tight hct2 henc2
        subst huc2_eq; simp; omega
    exact hisAck _ h
  | ct1Acknowledged state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨receivingEk, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd); cases decoded? with
    | none =>
      have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; simp; omega
    | some decoded =>
      dsimp only [] at h1c; rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      rcases except_bind_eq_ok h1d with ⟨⟨uc2, ct2, mac⟩, hct2, h1e⟩
      rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩; rw [statesResult_ofPanic_eq_ok] at hct2 henc2
      have hres := Except.ok.inj h1f; subst hres; have hinj := Except.ok.inj h2; subst hinj
      unfold Unchunked.SendCt.Ct1Sent.recv_ek at huc; split at huc <;> [contradiction; skip]
      split at huc <;> [skip; contradiction]; have huc_eq := Except.ok.inj huc; subst huc_eq
      obtain ⟨huc2_eq, henc2_le⟩ := send_ct2_encode_raw_le_tight hct2 henc2
      subst huc2_eq; simp; omega
  | ct2Sampled state =>
    dsimp only [] at h; split at h
    · split at h <;> [skip; contradiction]; rcases except_bind_eq_ok h with ⟨s', h1, h2⟩
      rw [statesResult_ofPanic_eq_ok] at h1; have hinj := Except.ok.inj h2; subst hinj
      unfold Chunked.SendCt.Ct2Sampled.recv_next_epoch Unchunked.SendCt.Ct2Sent.recv_next_epoch at h1
      dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨uc, huc, h1b⟩
      have hs' := Except.ok.inj h1b; subst hs'; split at huc <;> [contradiction; skip]; split at huc <;> [contradiction; skip]
      have huc_eq := Except.ok.inj huc; subst huc_eq; simp; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega

theorem send_validState_length_le_tight (F : ShaCompress) (K : MlKem) (hkdf : HkdfFn)
    (s : SerializedState) (rng : Bytes) (out : Send)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (hsend : (send (spqrDeps F K) hkdf s rng).1 = .ok out) :
    ValidState out.state ∧ out.state.length ≤ s.length + 8000 := by
  have hval_out := (send_validState_length_le F K hkdf s rng out hval hlen hsend).1
  refine ⟨hval_out, ?_⟩
  obtain ⟨st, rfl, hst_val⟩ := hval.exists_encodeState
  have hdec := decodeState_spqrDeps_encodeState_pb F K st hlen
  unfold send at hsend; rw [hdec] at hsend; dsimp only [] at hsend
  cases hinner : (pqRatchetStateToPb st).inner with
  | none =>
    rw [hinner] at hsend; have hinj := Except.ok.inj hsend; subst hinj; simp
  | some pb =>
    have hst_inner : st.inner = some (.v1 pb) := by
      cases hin : st.inner with
      | none => simp [pqRatchetStateToPb, hin] at hinner
      | some i => cases i with | v1 v => simp [pqRatchetStateToPb, hin] at hinner; subst hinner; rfl
    rw [hinner] at hsend; dsimp only [] at hsend
    cases hfrom : (spqrDeps F K).statesFromPb pb with
    | error _ => rw [hfrom] at hsend; contradiction
    | ok st0' =>
      rw [hfrom] at hsend; dsimp only [] at hsend
      unfold spqrDeps liftStatesResult at hfrom; dsimp only [] at hfrom
      cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
      | error e => rw [hs0] at hfrom; cases e <;> contradiction
      | ok st0 =>
        have hfrom' := hfrom; rw [hs0] at hfrom'; have hst0_eq := Except.ok.inj hfrom'; subst hst0_eq
        rcases States.from_pb_raw_le hs0 with ⟨hst0_raw, hst0_pts⟩
        have hpb_enc := States.from_pb_rawV1State_le_encode hs0
        cases hsend_st : ((spqrDeps F K).statesSend st0 rng).1 with
        | error _ => rw [hsend_st] at hsend; contradiction
        | ok val =>
          rcases val with ⟨msg, key, st1⟩; rw [hsend_st] at hsend; dsimp only [] at hsend
          unfold spqrDeps at hsend_st; dsimp only [] at hsend_st
          cases hsend0 : st0.send K rng with
          | error se => rw [hsend0] at hsend_st; cases se <;> contradiction
          | ok p =>
            rcases p with ⟨sOut, tape'⟩; have hsend' := hsend_st; rw [hsend0] at hsend'
            have hst1 := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hsend')).2).2; subst hst1
            have hst1_raw := (States.send_raw_le_tight hst0_pts hsend0).1
            rcases sendAfterStates_wire_le hst_val hsend with ⟨chainPb, hch_le, _, hout_eq⟩
            rw [hout_eq, encodeState_length_eq, encodeState_length_eq st]
            have hch_low := chainWireCore_le_encodeOpt st.chain
            have hch_up := encodeOpt_chain_le_chainWireCore chainPb
            have hin_up := pqInner_encode_length_le (.v1 sOut.state.into_pb)
            simp only [pbToPqRatchetState, Option.map, hst_inner, PqRatchetState.Inner.encode, rawPqInner] at hin_up ⊢
            omega

private theorem if_error_eq_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε} {rest : Except ε α}
    {v : α} (h : (if c then Except.error e else rest) = .ok v) : rest = .ok v := by
  by_cases hc : c <;> simp [hc] at h; exact h

private theorem if_eq_ok_cases {ε α : Type} {c : Prop} [Decidable c] {t f : Except ε α} {v : α}
    (h : (if c then t else f) = .ok v) : t = .ok v ∨ f = .ok v := by
  by_cases hc : c <;> simp [hc] at h <;> [exact Or.inl h; exact Or.inr h]

private theorem if_pure_bind_eq_ok {ε α β : Type} {c : Prop} [Decidable c]
    {a : α} {K : α → Except ε β} {f : Except ε β} {v : β}
    (h : (if c then (Pure.pure a >>= K) else f) = .ok v) (P : α → Prop) (ha : P a)
    (hf : f = .ok v → ∃ a', P a' ∧ K a' = .ok v) : ∃ a', P a' ∧ K a' = .ok v := by
  rcases if_eq_ok_cases h with h1 | h1; · (rw [pure_bind_except] at h1; exact ⟨a, ha, h1⟩)
  exact hf h1

set_option maxHeartbeats 400000 in
theorem recv_validState_length_le_tight (F : ShaCompress) (K : MlKem) (hkdf : HkdfFn)
    (s : SerializedState) (msgBytes : SerializedMessage) (out : Recv)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (hrecv : recv (spqrDeps F K) hkdf s msgBytes = .ok out) :
    ValidState out.state ∧ out.state.length ≤ s.length + 80000 := by
  have hval_out := (recv_validState_length_le F K hkdf s msgBytes out hval hlen hrecv).1
  refine ⟨hval_out, ?_⟩
  obtain ⟨st, rfl, hst_val⟩ := hval.exists_encodeState
  have hdec_eq := decodeState_spqrDeps_encodeState_pb F K st hlen
  unfold recv at hrecv; dsimp only [] at hrecv
  rcases except_bind_eq_ok hrecv with ⟨msg, _, h1⟩; rcases except_bind_eq_ok h1 with ⟨prePb, hdec, h2⟩
  rw [SpqrApiResult.ofError_eq_ok, hdec_eq] at hdec
  have hpre := Except.ok.inj hdec; subst hpre
  have hpre_vn : (pqRatchetStateToPb st).versionNegotiation = st.versionNegotiation := rfl
  have hpre_ch : (pqRatchetStateToPb st).chain = st.chain := rfl
  replace h2 := if_error_eq_ok (if_error_eq_ok h2); rcases if_eq_ok_cases h2 with h2 | h2
  · have hinj := Except.ok.inj h2; subst hinj; simp
  · rcases if_eq_ok_cases h2 with h2 | h2
    · rcases except_bind_eq_ok h2 with ⟨chain0, hc0, h3⟩; rcases except_bind_eq_ok h3 with ⟨⟨chain1, rawKey⟩, hc1, h4⟩
      rw [SpqrApiResult.ofError_eq_ok] at hc0; rw [SpqrApiResult.ofChainResult_eq_ok] at hc1
      dsimp only [] at h4; have hinj := Except.ok.inj h4; subst hinj
      rw [hpre_ch, hpre_vn] at hc0
      have hc0_le := (chainFrom_wire_le hkdf st.chain st.versionNegotiation hc0).1
      have hc0_val := validChainParams_of_chainFrom hst_val hc0
      obtain ⟨hc1_le, _⟩ := Chain.recvKey_wire_le hkdf chain0 0#64 msg.index hc0_val hc1
      dsimp only [spqrDeps]; rw [encodeState_length_eq, encodeState_length_eq st]
      have hch_low := chainWireCore_le_encodeOpt st.chain
      have hch_up := encodeOpt_chain_le_chainWireCore (some chain1.intoPb)
      have hin_eq : ((pqRatchetStateToPb st).inner.map PqRatchetState.Inner.v1) = st.inner := by
        cases hin : st.inner with
        | none => simp [pqRatchetStateToPb, hin]
        | some i => cases i; simp [pqRatchetStateToPb, hin]
      simp only [pbToPqRatchetState, hin_eq, optRaw_some, hpre_vn] at hch_up ⊢; omega
    · have hinner_st : ∀ pb, (pqRatchetStateToPb st).inner = some pb →
          (Proto.encodeMessage V1State.encodeRaw 3#32 pb).length =
            (match st.inner with | none => 0 | some i => (PqRatchetState.Inner.encode i).length) := by
        intro pb hpb; cases hin : st.inner with
        | none => simp [pqRatchetStateToPb, hin] at hpb
        | some i => cases i with | v1 v => simp [pqRatchetStateToPb, hin] at hpb; subst hpb; rfl
      rcases if_pure_bind_eq_ok h2
        (fun statePb =>
          ValidPqState (pbToPqRatchetState statePb) ∧
          optRaw chainWireCore statePb.chain ≤ optRaw chainWireCore st.chain + 294 ∧
          (∀ pb, statePb.inner = some pb →
            (∀ st0, States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
              rawV1State pb ≤ (match st.inner with | none => 0 | some i => (PqRatchetState.Inner.encode i).length) + 704)))
        ⟨⟨hst_val.1, hst_val.2⟩, by simp [hpre_ch],
          fun pb hpb st0 hs0 => by rw [← hinner_st pb hpb]; exact States.from_pb_rawV1State_le_encode hs0⟩
        (by
          intro h2; rcases if_eq_ok_cases h2 with h2 | h2
          · dsimp only [Bind.bind, Except.bind] at h2; contradiction
          · rw [hpre_vn, hpre_ch] at h2
            cases hvn : st.versionNegotiation with
            | none => rw [hvn] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
            | some vn =>
              rw [hvn] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
              cases hv : Version.fromU8? msg.version with
              | none => rw [hv] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
              | some v =>
                rw [hv] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
                cases hd : Direction.fromI32? vn.direction with
                | none => rw [hd] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                | some dir =>
                  rw [hd] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
                  rcases except_bind_eq_ok h2 with ⟨inner', hinit, hst4⟩
                  rcases except_bind_eq_ok hst4 with ⟨chain', hch', hst5⟩
                  rw [SpqrApiResult.ofPanic_eq_ok] at hinit; rw [SpqrApiResult.ofError_eq_ok] at hch'
                  have hinit_le := initInner_spqrDeps_raw_le hinit
                  have hc'_le := (chainFrom_wire_le hkdf st.chain (some vn) hch').1
                  have hc'_val : ValidChainParams chain'.params := by
                    obtain ⟨_, hsrc⟩ := chainFrom_wire_le hkdf st.chain (some vn) hch'
                    rcases hsrc with ⟨cpb, hch, hp⟩ | ⟨vnpb, hv_eq, hp⟩
                    · exact hst_val.2 cpb hch chain'.params hp
                    · cases hv_eq; exact hst_val.1 vn hvn chain'.params hp
                  rw [pure_bind_except] at hst5
                  refine ⟨{ inner := inner', versionNegotiation := none, chain := some chain'.intoPb },
                    ⟨⟨(by intro _ hnone; cases hnone), ?_⟩, by simp; omega, ?_⟩, hst5⟩
                  · intro ch hch p hp; cases hch; cases hp; exact hc'_val
                  · intro pb hpb _ _
                    have : rawV1State pb ≤ 424 := by dsimp only at hpb; subst hpb; exact hinit_le
                    omega)
        with ⟨statePb, ⟨hstPb_val, hstPb_ch, hstPb_in⟩, h3⟩
      cases hinner : statePb.inner with
      | none =>
        rw [hinner] at h3; have hinj := Except.ok.inj h3; subst hinj; simp
      | some pb =>
        rw [hinner] at h3; dsimp only [] at h3
        rcases except_bind_eq_ok h3 with ⟨sckaMsg, _, h4⟩; rcases except_bind_eq_ok h4 with ⟨st0', hfrom, h5⟩
        rcases except_bind_eq_ok h5 with ⟨⟨key, st1⟩, hrecv_st, h6⟩
        unfold spqrDeps liftStatesResult at hfrom; dsimp only [] at hfrom
        cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
        | error se => rw [hs0] at hfrom; cases se <;> contradiction
        | ok st0 =>
          have hfrom' := hfrom; rw [hs0] at hfrom'; have hst0_eq := Except.ok.inj hfrom'; subst hst0_eq
          rcases States.from_pb_raw_le hs0 with ⟨hst0_raw, hst0_pts⟩
          have hpb_le := hstPb_in pb hinner st0 hs0
          unfold spqrDeps at hrecv_st; dsimp only [] at hrecv_st; cases hr0 : st0.recv K sckaMsg with
          | error se => rw [hr0] at hrecv_st; cases se <;> contradiction
          | ok rOut =>
            have hrecv' := hrecv_st; rw [hr0] at hrecv'; have hst1_eq := (Prod.mk.inj (Except.ok.inj hrecv')).2; subst hst1_eq
            have hst1_raw := (States.recv_raw_le_tight hst0_pts hr0).1
            dsimp only [] at h6; split at h6 <;> [contradiction; skip]
            rcases except_bind_eq_ok h6 with ⟨chain0, hc0, h7⟩; rw [SpqrApiResult.ofError_eq_ok] at hc0
            have hc0_le := (chainFrom_wire_le hkdf statePb.chain statePb.versionNegotiation hc0).1
            have hc0_val : ValidChainParams chain0.params := validChainParams_of_chainFrom hstPb_val hc0
            have htail : ∀ (chain1 : Chain),
                chainWireCore chain1.intoPb ≤ chainWireCore chain0.intoPb + 294 →
                ValidChainParams chain1.params →
                (do
                  let __x_1 ← SpqrApiResult.ofChainResult (Chain.recvKey hkdf chain1 (msg.epoch - 1#64) msg.index)
                  Except.ok ({
                    state := (spqrDeps F K).encodeState {
                      inner := some ((spqrDeps F K).statesIntoPb rOut.state),
                      versionNegotiation := none, chain := some __x_1.1.intoPb },
                    key := if List.isEmpty __x_1.2 = true then none else some __x_1.2 } : Recv)) = .ok out →
                out.state.length ≤ (Proto.encodeState st).length + 80000 := by
              intro chain1 hc1_le hc1_val h8; rcases except_bind_eq_ok h8 with ⟨⟨chain2, msgKey⟩, hc2, h9⟩
              rw [SpqrApiResult.ofChainResult_eq_ok] at hc2; have hinj := Except.ok.inj h9; rw [← hinj]
              obtain ⟨hc2_le, _⟩ := Chain.recvKey_wire_le hkdf chain1 (msg.epoch - 1#64) msg.index hc1_val hc2
              dsimp only [spqrDeps]; rw [encodeState_length_eq, encodeState_length_eq st]
              have hch_low := chainWireCore_le_encodeOpt st.chain
              have hch_up := encodeOpt_chain_le_chainWireCore (some chain2.intoPb)
              have hin_up := pqInner_encode_length_le (.v1 rOut.state.into_pb)
              have hvn_none : (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 none).length = 0 := rfl
              cases hin : st.inner <;>
                simp only [hin, pbToPqRatchetState, Option.map, hvn_none, optRaw_some, rawPqInner] at hpb_le hch_up hin_up ⊢ <;>
                omega
            cases key with
            | none => dsimp only [] at h7; rw [pure_bind_except] at h7; exact htail chain0 (by omega) hc0_val h7
            | some es =>
              dsimp only [] at h7; rcases except_bind_eq_ok h7 with ⟨chain1, hc1, h8⟩
              rw [SpqrApiResult.ofChainPanic_eq_ok] at hc1
              obtain ⟨hadd, hp1⟩ := Chain.addEpoch_wire_le hkdf chain0 es hc1
              exact htail chain1 hadd (hp1 ▸ hc0_val) h8

theorem spqrV1_send_validState_length_le_tight (F : ShaCompress) (K : MlKem)
    (s : Bytes) (tape : Bytes) (s' : Bytes) (salt : Salt) (msg : Bytes)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F K).send s tape = some (s', salt, msg)) :
    ValidState s' ∧ s'.length ≤ s.length + 8000 := by
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hsend : (send (spqrDeps F K) (spqrHkdfWith F) s tape).1 with
  | error _ => rw [hsend] at h; contradiction
  | ok out =>
    rw [hsend] at h; dsimp only [] at h; cases hsalt : messageKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only [] at h; have hinj := (Prod.mk.inj (Option.some.inj h)).1; subst hinj
      exact send_validState_length_le_tight F K (spqrHkdfWith F) s tape out hval hlen hsend

theorem spqrV1_recv_validState_length_le_tight (F : ShaCompress) (K : MlKem)
    (s msg : Bytes) (s' : Bytes) (salt : Salt)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F K).recv s msg = .ok (s', salt)) :
    ValidState s' ∧ s'.length ≤ s.length + 80000 := by
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) s msg with
  | error e => rw [hrecv] at h; cases e <;> contradiction
  | ok out =>
    rw [hrecv] at h; dsimp only [] at h; cases hsalt : recvKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only [] at h
      have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
      exact recv_validState_length_le_tight F K (spqrHkdfWith F) s msg out hval hlen hrecv

end TightSpqrGrowth

/-! ## Whisper-receive step properties -/

section WhisperProps

open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)
open CryptoVerification.LibsignalTripleRatchet.Seeds (tryDecryptFromRecord_preserves)
open CryptoVerification.LibsignalSpqrV1 (spqrV1 spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1.Top.StateSize (ValidState spqrV1_recv_validState_length_le)

@[local simp] private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := rfl

@[local simp] private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

@[local simp] private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] private theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

@[local simp] private theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl

@[local simp] private theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

@[local simp] private theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r) s = (r, s) := by
  cases r <;> rfl

@[local simp] private theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

@[local simp] private theorem exec_map {σ α β : Type} (f : α → β) (m : Mut σ α) (s : σ) :
    Mut.exec (f <$> m) s =
      match Mut.exec m s with
      | (.ok a, s') => (.ok (f a), s')
      | (.error e, s') => (.error e, s') := by
  rw [map_eq_bind_pure_comp]
  simp only [exec_bind, Function.comp_apply, exec_pure]

@[local simp] private theorem exec_onRatchet {PQ α : Type} (m : Mut RatchetState α)
    (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      ((Mut.exec m t.ratchet).1, { t with ratchet := (Mut.exec m t.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  simp

private theorem takeSkippedKey_receiverChains_length (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.takeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp [h1, h2, h3]
      · rcases h4 : c.messageKeys[pos]? with _ | key
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

private theorem storeSkippedKey_receiverChains_length (their : PublicKey)
    (key : MessageKeyGenerator) (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · simp [h1, h2]

private theorem setReceiverChainKey_receiverChains_length (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · simp [h1, h2]

private theorem advanceChain_receiverChains_length (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : ℕ) (ck : ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains.length =
      r.receiverChains.length := by
  induction fuel generalizing ck r with
  | zero => rfl
  | succ fuel ih =>
    unfold RatchetState.advanceChain
    split
    · rw [exec_bind]
      have h1 := storeSkippedKey_receiverChains_length their (ck.messageKeys F) r
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨_ | _, r1⟩
      · rw [hs] at h1; exact h1
      · rw [hs] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck.nextChainKey F with _ | ck'
        · exact h1
        · exact (ih ck' r1).trans h1
    · rfl

private theorem consumeMessageKey_receiverChains_length (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    have h1 := takeSkippedKey_receiverChains_length their counter r
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨_ | opt, r1⟩
    · rw [ht] at h1; exact h1
    · rw [ht] at h1; cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    split
    · rfl
    · rw [exec_bind]
      have h1 := advanceChain_receiverChains_length F their counter (counter - ck.index).toNat ck r
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨_ | ck1, r1⟩
      · rw [ha] at h1; exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_receiverChains_length their ck2 r1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨_ | _, r2⟩ <;>
            · rw [hs] at h2; exact h2.trans h1

private theorem dhRatchetStep_ok_receiverChains_length (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : ChainKey)
    (h : Mut.exec (RatchetState.dhRatchetStep C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.length =
      (r.receiverChains.length + 1) - ((r.receiverChains.length + 1) - maxReceiverChains) := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey at h
  simp only [exec_bind, exec_get] at h
  rcases hsc : r.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_modifyGet, exec_liftE] at h
    rcases hrc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
      _ | ⟨newRootKey, receiverChainKey⟩
    · simp [hrc1] at h
    · simp only [hrc1, exec_modify, exec_pure] at h
      rcases hrc2 : rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey with
        _ | ⟨finalRootKey, senderChainKey⟩
      · simp [hrc2] at h
      · simp only [hrc2, Prod.mk.injEq, Except.ok.injEq] at h
        rcases h with ⟨_, rfl⟩
        simp [RatchetState.evictReceiverChains, List.length_drop, List.length_append]

private theorem ensureReceiverChain_ok_some_length (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : ChainKey) (i : ℕ)
    (hidx : r.receiverChains.findIdx? (·.senderRatchetKey == their) = some i)
    (h : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex at h
  simp only [exec_bind, exec_get, hidx, exec_liftE] at h
  rcases hget : r.receiverChains[i]? with _ | c
  · simp [hget] at h
  · rcases hck : c.chainKey with _ | ck'
    · simp [hget, hck] at h
    · simp only [hget, hck, exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      rfl

private theorem ensureReceiverChain_ok_none_length (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : ChainKey)
    (hidx : r.receiverChains.findIdx? (·.senderRatchetKey == their) = none)
    (h : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.length =
      (r.receiverChains.length + 1) - ((r.receiverChains.length + 1) - maxReceiverChains) := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex at h
  simp only [exec_bind, exec_get, hidx, exec_liftE] at h
  exact dhRatchetStep_ok_receiverChains_length C their coins r r1 ck h

private theorem tryDecryptFromRecord_ok_core {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC) (expected : Option Bytes) (msg : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (st st' : SessionState PQ) (pt : Bytes)
    (h : SessionState.tryDecryptFromRecord C spqr expected msg msgType coins st = (.ok pt, st')) :
    st'.pendingPreKey = false ∧
    st'.localIdentity = st.localIdentity ∧
    st'.remoteIdentity = st.remoteIdentity ∧
    (∃ key, spqr.recv st.pqRatchetState msg.pqRatchet = .ok (st'.pqRatchetState, key)) ∧
    ∃ ck r1 mkg r2,
      Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ =
        (.ok ck, r1) ∧
      Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType) r1 =
        (.ok mkg, r2) ∧
      st'.receiverChains = r2.receiverChains := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C spqr expected msg msgType coins) st with
      ⟨_ | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at hd
      · simp only [hrem, exec_bind, exec_modifyGet, exec_get, exec_pure] at hd
        rcases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨_ | pt', tr'⟩
        · simp [hdec] at hd
        · rw [hdec] at hd
          simp only [exec_liftE, exec_modify, Prod.mk.injEq, Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          unfold TripleRatchet.decrypt at hdec
          rw [exec_bind, exec_onRatchet] at hdec
          rcases he : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
              ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ with
            ⟨_ | ck, r1⟩
          · simp [he] at hdec
          · simp only [he, exec_bind, exec_onRatchet] at hdec
            rcases hc : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck
                msg.counter msgType) r1 with ⟨_ | mkg, r2⟩
            · simp [hc] at hdec
            · simp only [hc, exec_get] at hdec
              cases hpan : spqr.recvPanics st.pqRatchetState msg.pqRatchet
              case true => simp [hpan] at hdec
              simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
              rcases hspqr : spqr.recv st.pqRatchetState msg.pqRatchet with
                ⟨_ | _⟩ | ⟨newPqrState, pqrKey⟩
              · simp [hspqr] at hdec
              · simp [hspqr] at hdec
              · simp only [hspqr, exec_pure, exec_bind] at hdec
                split_ifs at hdec
                · simp at hdec
                · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                      (mkg.generateKeys C.F pqrKey).iv msg.ciphertext with _ | pt''
                  · simp [haes] at hdec
                  · simp only [haes] at hdec
                    rcases hdec with ⟨_, rfl⟩
                    exact ⟨rfl, rfl, rfl, ⟨pqrKey, rfl⟩, ck, r1, mkg, r2, rfl, hc, rfl⟩

theorem paramsV1_receive_seeds_chains
    (W : PEParams) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (g : GhostState Bytes) (body : Bytes) (rc : BitVec 256)
    {g' : GhostState Bytes} {t i : ℕ} {pt : Bytes}
    (hrcv : (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F K) idA idB).receive g body rc =
      some (g', t, i, pt))
    (hSeeds : SeedsLen32 g.session)
    (hChains : g.session.receiverChains.length ≤ maxReceiverChains) :
    SeedsLen32 g'.session ∧ g'.session.receiverChains.length ≤ maxReceiverChains := by
  let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F K) idA idB
  change P_v1.receive g body rc = some (g', t, i, pt) at hrcv
  rw [Record.receive_eq_afterRecv] at hrcv
  rcases htf : SignalMessage.tryFrom P_v1.codec body with _ | msg
  · simp [htf] at hrcv
  rw [htf] at hrcv; dsimp only at hrcv
  rcases hd : SessionState.tryDecryptFromRecord P_v1.C P_v1.spqr
      (P_v1.expectedAddrs g.party) msg .whisper rc g.session with ⟨_ | pt', s⟩
  · simp [hd] at hrcv
  rw [hd] at hrcv
  simp only [Option.some.injEq] at hrcv
  have hSeeds' : SeedsLen32 s := by
    have := tryDecryptFromRecord_preserves P_v1.C P_v1.spqr (P_v1.expectedAddrs g.party) msg
      .whisper rc g.session hSeeds
    simpa [hd] using this
  obtain ⟨-, -, -, -, ck, r1, mkg, r2, he, hc, hsrc⟩ := tryDecryptFromRecord_ok_core P_v1.C P_v1.spqr
    (P_v1.expectedAddrs g.party) msg .whisper rc g.session s pt' hd
  have hc_len := consumeMessageKey_receiverChains_length P_v1.C.F msg.senderRatchetKey ck
    msg.counter .whisper r1
  rw [hc] at hc_len
  have hs_r1 : s.receiverChains.length = r1.receiverChains.length := by rw [hsrc, hc_len]
  have hs_le : s.receiverChains.length ≤ maxReceiverChains := by
    rcases hidx : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)
      with _ | j
    · have he_len := ensureReceiverChain_ok_none_length P_v1.C msg.senderRatchetKey rc _ r1 ck hidx he
      rw [hs_r1, he_len]
      omega
    · have he_len := ensureReceiverChain_ok_some_length P_v1.C msg.senderRatchetKey rc _ r1 ck j hidx he
      rw [hs_r1, he_len]
      exact hChains
  have hg' := congrArg Prod.fst hrcv
  dsimp only [GhostState.afterRecv] at hg'
  subst hg'
  exact ⟨hSeeds', hs_le⟩

/-- Accepted `paramsIdsWithSpqr` whisper-receive steps preserve session invariants and grow
`pqRatchetState` by at most `80000` bytes. -/
theorem paramsV1_receive_whisper_props
    (W : PEParams) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (g : GhostState Bytes) (body : Bytes) (rc : BitVec 256)
    {g' : GhostState Bytes} {t i : ℕ} {pt : Bytes}
    (hrcv : (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F K) idA idB).receive g body rc =
      some (g', t, i, pt))
    (hSeeds : SeedsLen32 g.session)
    (hChains : g.session.receiverChains.length ≤ maxReceiverChains)
    (hAl : g.Aligned)
    (hVal : ValidState g.session.pqRatchetState)
    (hpq64 : g.session.pqRatchetState.length < 2 ^ 64) :
    g'.party = g.party ∧
    g'.session.pendingPreKey = false ∧
    g'.session.localIdentity = g.session.localIdentity ∧
    (g'.epoch = g.epoch ∨ g'.epoch = g.epoch + 1) ∧
    (g.session.receiverChains = [] → g'.epoch = g.epoch + 1) ∧
    g'.Aligned ∧
    ValidState g'.session.pqRatchetState ∧
    g'.session.pqRatchetState.length ≤ g.session.pqRatchetState.length + 80000 := by
  have _ := paramsV1_receive_seeds_chains W K idA idB g body rc hrcv hSeeds hChains
  let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F K) idA idB
  change P_v1.receive g body rc = some (g', t, i, pt) at hrcv
  rw [Record.receive_eq_afterRecv] at hrcv
  rcases htf : SignalMessage.tryFrom P_v1.codec body with _ | msg
  · simp [htf] at hrcv
  rw [htf] at hrcv; dsimp only at hrcv
  rcases hd : SessionState.tryDecryptFromRecord P_v1.C P_v1.spqr
      (P_v1.expectedAddrs g.party) msg .whisper rc g.session with ⟨_ | pt', s⟩
  · simp [hd] at hrcv
  rw [hd] at hrcv
  simp only [Option.some.injEq] at hrcv
  obtain ⟨hppk, hloc, -, ⟨key, hspqr⟩, ck, r1, mkg, r2, he, hc, hsrc⟩ :=
    tryDecryptFromRecord_ok_core P_v1.C P_v1.spqr (P_v1.expectedAddrs g.party) msg .whisper
      rc g.session s pt' hd
  have hspqr' : (spqrV1 W.C.F K).recv g.session.pqRatchetState msg.pqRatchet =
      .ok (s.pqRatchetState, key) := hspqr
  obtain ⟨hval', hpq_le⟩ := spqrV1_recv_validState_length_le_tight W.C.F K
    g.session.pqRatchetState msg.pqRatchet s.pqRatchetState key hVal hpq64 hspqr'
  have hc_len := consumeMessageKey_receiverChains_length P_v1.C.F msg.senderRatchetKey ck
    msg.counter .whisper r1
  rw [hc] at hc_len
  have hs_r1 : s.receiverChains.length = r1.receiverChains.length := by rw [hsrc, hc_len]
  have hce : g.chainEpochs.length = g.session.receiverChains.length := hAl
  have hg' := congrArg Prod.fst hrcv
  dsimp only at hg'
  unfold GhostState.afterRecv at hg'
  rcases hidx : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)
    with _ | j
  · have he_len := ensureReceiverChain_ok_none_length P_v1.C msg.senderRatchetKey rc _ r1 ck hidx he
    have hs_len : s.receiverChains.length =
        (g.session.receiverChains.length + 1) -
          ((g.session.receiverChains.length + 1) - maxReceiverChains) := hs_r1.trans he_len
    rw [hidx] at hg'
    dsimp only at hg'
    subst hg'
    refine ⟨rfl, hppk, hloc, Or.inr rfl, fun _ => rfl, ?_, hval', hpq_le⟩
    unfold GhostState.Aligned
    dsimp only
    rw [List.length_drop, List.length_append, List.length_singleton, hce, hs_len]
    omega
  · have he_len := ensureReceiverChain_ok_some_length P_v1.C msg.senderRatchetKey rc _ r1 ck j hidx he
    have hs_len : s.receiverChains.length = g.session.receiverChains.length := hs_r1.trans he_len
    rw [hidx] at hg'
    dsimp only at hg'
    subst hg'
    refine ⟨rfl, hppk, hloc, Or.inl rfl, fun hnil => ?_, ?_, hval', hpq_le⟩
    · rw [hnil] at hidx; simp at hidx
    · unfold GhostState.Aligned
      dsimp only
      rw [List.length_drop, hce, hs_len]
      omega

end WhisperProps

end CryptoVerification.E2E.BhAdapterIjHelpersV1
