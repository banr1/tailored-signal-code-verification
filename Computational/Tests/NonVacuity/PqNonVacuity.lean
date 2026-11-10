/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.MlKemCorrectFacts
public import Computational.Proofs.SpqrV1Sync.TopLog
import all Init.Data.String.Defs
import all Init.Data.Repr
public import LibsignalBinary.Proofs.SignalSession.PqStep
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.LibsignalCli.CliCapsCompleteness
import Computational.Proofs.LibsignalCli.PqFirstMessageSpqr
import Computational.Proofs.LibsignalCli.PqSteadyRefine
import Computational.Proofs.SignalWireRoundTrip
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SignalSession.PqClosure
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.DecoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.EncoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
import ProofLib.SepLogic.WP.StepsCore

/-!
# End-to-End Non-Vacuity of `CliSpecPqxdh`

Constructs a concrete primitive witness `(K0, Q0, C0, W0, X0)` and executes a 5-step PQXDH and
SPQR-V1 conversation from sessionless party directories (`session = none`): Alice `init`, Alice
pre-key `send`, Bob pre-key `recv` (recovering `pt1`), Bob whisper `send`, and Alice whisper `recv`
(clearing `pendingPreKey` and recovering `pt2`).

Consequently, every `run` satisfying `CliSpecPqxdh run X0 W0` exits `0` and writes non-empty
SPQR-V1 session records across all five CLI invocations (`cliSpecPq_forces_full_conversation`), and
no always-rejecting binary satisfies `CliSpecPqxdh` for any `(X, W)` (`not_cliSpecPq_alwaysReject`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalCli.PqNonVacuity.SpqrBounds

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoGames.LibsignalSession (ShaCompress spqrPos)
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawVN rawChain rawV1State)

theorem partyTop_ne_nil {F : ShaCompress} {K : MlKem} {authKey : Bytes} {dir : Direction}
    {secret : Nat → Bytes} {st : St F} {sendEp : Nat} {sendCtr : Nat → Nat}
    {recvSet : Nat → Finset Nat} {bytes : Bytes}
    (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes) :
    bytes ≠ [] := by
  obtain ⟨vn?, ch?, _, hw⟩ := h
  rw [hw.hbytes]
  intro hnil
  have hlen := congrArg List.length hnil
  dsimp only [topBytes, topPb, spqrDeps, pbToPqRatchetState, Proto.encodeState,
    PqRatchetState.encode, PqRatchetState.encodeRaw, PqRatchetState.Inner.encode,
    Proto.encodeMessage] at hlen
  have hk : (Proto.encodeKey 3#32 .lengthDelimited).length = 1 := rfl
  simp only [Option.map_some, List.length_append, List.length_nil, hk] at hlen
  omega

private theorem nv_rawAuth_update (F : ShaCompress) (a : Authenticator) (ep : Epoch) (k : Bytes) :
    CryptoVerification.SpqrV1.Top.StateSize.rawAuth ((spqrAuthApi F).into_pb (a.update F ep k)) = 64 := by
  simp [CryptoVerification.SpqrV1.Top.StateSize.rawAuth, spqrAuthApi, Authenticator.intoPb,
    Authenticator.update, hkdfToVecUnchecked, hkdfToSliceUnchecked]

private theorem nv_rawAuth_authNext (F : ShaCompress) (K : MlKem) (e : Epoch)
    (auth : Authenticator) (s : Seed) (r : EncRand) :
    CryptoVerification.SpqrV1.Top.StateSize.rawAuth
      ((spqrAuthApi F).into_pb (authNext F K e auth s r)) = 64 :=
  nv_rawAuth_update F auth e _

private theorem nv_runT_rawAuth (F : ShaCompress) (K : MlKem) (authKey : Bytes) {e : Epoch}
    {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
    (hr : RunT F K authKey e auth c stA stB toA toB) :
    CryptoVerification.SpqrV1.Top.StateSize.rawAuth ((spqrAuthApi F).into_pb auth) = 64 := by
  induction hr with
  | init => exact nv_rawAuth_update F _ 1#64 authKey
  | sendA _ _ _ _ _ _ _ _ _ ih | sendB _ _ _ _ _ _ _ _ _ ih => exact ih
  | recvA _ _ _ _ _ _ _ ih | recvB _ _ _ _ _ _ _ ih => exact ih
  | advanceA | advanceB => exact nv_rawAuth_authNext F K _ _ _ _

private theorem nv_sum_map_le {α : Type} (l : List α) (f : α → Nat) (B : Nat)
    (h : ∀ x ∈ l, f x ≤ B) : (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_one_mul]
    have := h x List.mem_cons_self
    have := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

private theorem nv_needed_le {len : Nat} (hlen : len ≤ 1152) (j : Nat) :
    CryptoVerification.SpqrV1Sync.Erasure.needed len j ≤ 1200 := by
  unfold CryptoVerification.SpqrV1Sync.Erasure.needed; split <;> omega

private theorem nv_rawPolyEnc_le {msg : Bytes} {enc : PolyEncoder}
    (henc : CryptoVerification.SpqrV1Sync.Erasure.EncInv msg enc) (hlen : msg.length ≤ 1152) :
    CryptoVerification.SpqrV1.Top.StateSize.rawPolyEnc (spqrPolyApi.encoder_into_pb enc) ≤ 38752 := by
  rcases enc with ⟨idx, s⟩
  rcases henc with hpts | ⟨polys, hpolys, hlen16, hcoeff⟩
  · simp only at hpts; subst hpts
    simp only [spqrPolyApi, protoPolyEncoderToPb, PolyEncoder.intoPb,
      CryptoVerification.SpqrV1.Top.StateSize.rawPolyEnc, List.map_nil, List.sum_nil, Nat.add_zero]
    have h1 := nv_sum_map_le
      ((CryptoVerification.SpqrV1Sync.Erasure.msgPoints msg).map
        (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value)))
      (fun b => b.length + 22) 2422 ?_
    · rw [List.length_map, CryptoVerification.SpqrV1Sync.Erasure.EncoderCodec.msgPoints_length] at h1
      omega
    · intro b hb
      rcases List.mem_map.1 hb with ⟨pt, hpt, rfl⟩
      rcases List.mem_map.1 hpt with ⟨j, -, rfl⟩
      rw [CryptoVerification.SpqrV1Sync.Erasure.EncoderCodec.flatMap_u16ToBeBytes_length,
        List.length_map, List.length_range]
      have := nv_needed_le hlen j; omega
  · simp only at hpolys; subst hpolys
    simp only [spqrPolyApi, protoPolyEncoderToPb, PolyEncoder.intoPb,
      CryptoVerification.SpqrV1.Top.StateSize.rawPolyEnc, List.map_nil, List.sum_nil, Nat.zero_add]
    have h1 := nv_sum_map_le (polys.map Poly.serialize) (fun b => b.length + 22) 2422 ?_
    · rw [List.length_map, hlen16] at h1; omega
    · intro b hb
      rcases List.mem_map.1 hb with ⟨p, hp, rfl⟩
      rcases List.getElem_of_mem hp with ⟨j, hj, rfl⟩
      have hcj := (hcoeff j hj).1
      dsimp only [Poly.serialize]
      have hser := CryptoVerification.SpqrV1Sync.Erasure.EncoderCodec.flatMap_u16ToBeBytes_length
        polys[j].coefficients
      have := nv_needed_le hlen j; omega

private theorem nv_sortedSetPt_length_le (s : SortedSetPt)
    (hpw : (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)) :
    s.vec.length ≤ 2 ^ 16 := by
  let l := s.vec.map fun pt => pt.x.value.toNat
  have hnd : l.Nodup := hpw.imp ne_of_lt
  have hsub : l.toFinset ⊆ Finset.range (2 ^ 16) := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨pt, -, rfl⟩ := hx
    exact Finset.mem_range.2 pt.x.value.isLt
  have h1 : l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
  have h2 : l.toFinset.card ≤ (Finset.range (2 ^ 16)).card := Finset.card_le_card hsub
  have h3 : l.length = s.vec.length := List.length_map _
  rw [Finset.card_range] at h2; omega

private theorem nv_rawPolyDec_le {msg : Bytes} {S : Finset Nat} {dec : PolyDecoder}
    (hdec : CryptoVerification.SpqrV1Sync.Erasure.DecInv msg S dec) :
    CryptoVerification.SpqrV1.Top.StateSize.rawPolyDec (spqrPolyApi.decoder_into_pb dec) ≤ 4194656 := by
  simp only [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb,
    CryptoVerification.SpqrV1.Top.StateSize.rawPolyDec]
  have h1 := nv_sum_map_le (dec.pts.map (fun s => s.vec.flatMap Pt.serialize))
    (fun b => b.length + 22) 262166 ?_
  · rw [List.length_map, hdec.len] at h1; omega
  · intro b hb
    rcases List.mem_map.1 hb with ⟨s, hs, rfl⟩
    rcases List.getElem_of_mem hs with ⟨j, hj, rfl⟩
    have := nv_sortedSetPt_length_le dec.pts[j] (hdec.sorted j hj)
    have := CryptoVerification.SpqrV1Sync.Erasure.DecoderCodec.length_flatMap_serialize dec.pts[j].vec
    omega

private theorem nv_esOf_length_le (K : MlKem) (s : Seed) (r : EncRand) :
    (esOf K s r).length ≤ 2080 := by
  rcases h : encOf K s r with _ | ⟨ct1, es, ss⟩ <;> simp [esOf, h]

private theorem nv_c2Msg_length_le (F : ShaCompress) (K : MlKem) (e : Epoch)
    (auth : Authenticator) (s : Seed) (r : EncRand) :
    (c2Msg F K e auth s r).length ≤ 160 := by
  have hct2 : (ct2Of K s r).length ≤ 128 := by
    unfold ct2Of
    cases h : encaps2 K (ekOf K s) (esOf K s r) with
    | ok ct2 => exact le_of_eq (encaps2_ok_length h)
    | error _ => simp
  simp only [c2Msg, List.length_append, Authenticator.length_macCtUnchecked]; omega

private theorem nv_xShape_le (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (hauth : CryptoVerification.SpqrV1.Top.StateSize.rawAuth ((spqrAuthApi F).into_pb auth) = 64)
    (seed? : Option Seed) (x : St F) (hx : XShape F K e auth seed? x) :
    rawV1State x.into_pb ≤ 5000000 := by
  cases seed? with
  | none =>
    subst hx
    simp only [States.into_pb, Chunked.SendEk.KeysUnsampled.into_pb,
      Unchunked.SendEk.KeysUnsampled.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChKeysUnsampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcKeysUnsampled,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth]; decide
  | some s =>
    obtain ⟨enc, henc, rfl⟩ := hx
    have := nv_rawPolyEnc_le henc (by rw [hdrMsg_length]; decide)
    simp only [States.into_pb, Chunked.SendEk.KeysSampled.into_pb,
      Unchunked.SendEk.HeaderSent.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChKeysSampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcHeaderSent,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some,
      hauth, Codec.ekOf_length, Codec.dkOf_length]; omega

private theorem nv_yShape_le (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (hauth : CryptoVerification.SpqrV1.Top.StateSize.rawAuth ((spqrAuthApi F).into_pb auth) = 64)
    (seed? : Option Seed) (y : St F) (hy : YShape F K e auth seed? y) :
    rawV1State y.into_pb ≤ 5000000 := by
  cases seed? with
  | none =>
    subst hy
    have := nv_rawPolyDec_le (Codec.freshDec_decInv 96 (by decide))
    simp only [States.into_pb, Chunked.SendCt.NoHeaderReceived.into_pb,
      Unchunked.SendCt.NoHeaderReceived.into_pb, rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChNoHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcNoHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth]; omega
  | some s =>
    rcases hy with ⟨S, dec, hdec, -, rfl⟩ | rfl
    · have := nv_rawPolyDec_le hdec
      simp only [States.into_pb, Chunked.SendCt.NoHeaderReceived.into_pb,
        Unchunked.SendCt.NoHeaderReceived.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChNoHeaderReceived,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcNoHeaderReceived,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth]; omega
    · have := nv_rawPolyDec_le (Codec.freshDec_decInv 1152 (by decide))
      simp only [States.into_pb, Chunked.SendCt.HeaderReceived.into_pb,
        Unchunked.SendCt.HeaderReceived.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChHeaderReceived,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcHeaderReceived,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, Codec.hdrOf_length]; omega

private theorem nv_xShapeE_le (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins)
    (hauth : CryptoVerification.SpqrV1.Top.StateSize.rawAuth ((spqrAuthApi F).into_pb auth) = 64)
    (x : St F) (hx : XShapeE F K e auth c x) :
    rawV1State x.into_pb ≤ 5000000 := by
  cases c with
  | init => exact nv_xShape_le F K e auth hauth none x hx
  | seed s => exact nv_xShape_le F K e auth hauth (some s) x hx
  | both s r =>
    rcases hx with hx | ⟨enc, S, dec, henc, hdec, -, rfl⟩ | ⟨enc, henc, rfl⟩ |
      ⟨S, dec, hdec, -, rfl⟩ | hx
    · exact nv_xShape_le F K e auth hauth (some s) x hx
    · have := nv_rawPolyEnc_le henc (by rw [Codec.ekOf_length])
      have := nv_rawPolyDec_le hdec
      simp only [States.into_pb, Chunked.SendEk.HeaderSent.into_pb,
        Unchunked.SendEk.EkSent.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChHeaderSent,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcEkSent,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, Codec.dkOf_length]; omega
    · have := nv_rawPolyEnc_le henc (by rw [Codec.ekOf_length])
      have := ct1Of_length_le K s r
      simp only [States.into_pb, Chunked.SendEk.Ct1Received.into_pb,
        Unchunked.SendEk.EkSentCt1Received.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChCt1Received,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcEkSentCt1Received,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, Codec.dkOf_length]; omega
    · have := nv_rawPolyDec_le hdec
      have := ct1Of_length_le K s r
      simp only [States.into_pb, Chunked.SendEk.EkSentCt1Received.into_pb,
        Unchunked.SendEk.EkSentCt1Received.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChEkSentCt1Received,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcEkSentCt1Received,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth, Codec.dkOf_length]; omega
    · exact nv_yShape_le F K (e + 1#64) (authNext F K e auth s r)
        (nv_rawAuth_authNext F K e auth s r) none x hx

private theorem nv_yShapeE_le (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins)
    (hauth : CryptoVerification.SpqrV1.Top.StateSize.rawAuth ((spqrAuthApi F).into_pb auth) = 64)
    (y : St F) (hy : YShapeE F K e auth c y) :
    rawV1State y.into_pb ≤ 5000000 := by
  cases c with
  | init => exact nv_yShape_le F K e auth hauth none y hy
  | seed s => exact nv_yShape_le F K e auth hauth (some s) y hy
  | both s r =>
    have hauth' := nv_rawAuth_authNext F K e auth s r
    have hct1Le := ct1Of_length_le K s r
    have hesLe := nv_esOf_length_le K s r
    rcases hy with ⟨enc, S, dec, henc, hdec, -, rfl⟩ | ⟨enc, henc, rfl⟩ |
      ⟨S, dec, hdec, -, rfl⟩ | ⟨enc, henc, rfl⟩
    · have := nv_rawPolyEnc_le henc (by omega)
      have := nv_rawPolyDec_le hdec
      simp only [States.into_pb, Chunked.SendCt.Ct1Sampled.into_pb,
        Unchunked.SendCt.Ct1Sent.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChCt1Sampled,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcCt1Sent,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth', Codec.hdrOf_length]; omega
    · have := nv_rawPolyEnc_le henc (by omega)
      simp only [States.into_pb, Chunked.SendCt.EkReceivedCt1Sampled.into_pb,
        Unchunked.SendCt.Ct1SentEkReceived.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChEkReceivedCt1Sampled,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcCt1SentEkReceived,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth', Codec.ekOf_length]; omega
    · have := nv_rawPolyDec_le hdec
      simp only [States.into_pb, Chunked.SendCt.Ct1Acknowledged.into_pb,
        Unchunked.SendCt.Ct1Sent.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChCt1Acknowledged,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcCt1Sent,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth', Codec.hdrOf_length]; omega
    · have := nv_c2Msg_length_le F K e auth s r
      have := nv_rawPolyEnc_le henc (by omega)
      simp only [States.into_pb, Chunked.SendCt.Ct2Sampled.into_pb,
        Unchunked.SendCt.Ct2Sent.into_pb, rawV1State,
        CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
        CryptoVerification.SpqrV1.Top.StateSize.rawChCt2Sampled,
        CryptoVerification.SpqrV1.Top.StateSize.rawUcCt2Sent,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some, hauth']; omega

private theorem runT_rawV1State_le_5M (F : ShaCompress) (K : MlKem) (authKey : Bytes) {e : Epoch}
    {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
    (hr : RunT F K authKey e auth c stA stB toA toB) :
    rawV1State stA.into_pb ≤ 5000000 ∧ rawV1State stB.into_pb ≤ 5000000 := by
  have hauth := nv_runT_rawAuth F K authKey hr
  have hsync := runT_inSync F K authKey hr
  rcases hs : ekSide e with _ | _
  · have he := (inSync_of_a hs).1 hsync
    exact ⟨nv_xShapeE_le F K e auth c hauth stA he.hx, nv_yShapeE_le F K e auth c hauth stB he.hy⟩
  · have he := (inSync_of_b hs).1 hsync
    exact ⟨nv_yShapeE_le F K e auth c hauth stA he.hy, nv_xShapeE_le F K e auth c hauth stB he.hx⟩

theorem topInv_state_bounds (F : ShaCompress) (K : MlKem) (k : BitVec 256)
    (s : CryptoGames.LibsignalSM.Corr.SpqrGameState Bytes)
    (g : CryptoVerification.SpqrV1Sync.TopLog.Ghost F)
    (h : CryptoVerification.SpqrV1Sync.TopLog.TopInv F K k s g)
    (hlen : s.sent.length ≤ 2) (P : CryptoGames.Party) :
    (s.st P).1 ≠ [] ∧ (s.st P).1.length < 2 ^ 28 := by
  obtain ⟨sE, hpt, hla⟩ := h.hparty P
  refine ⟨partyTop_ne_nil hpt, ?_⟩
  obtain ⟨vn?, ch?, chE, hw⟩ := hpt
  have htop := topBytes_length_le F K (g.st P) vn? ch?
  rw [← hw.hbytes] at htop
  have hauth : (CryptoVerification.SpqrV1Sync.TopLog.authOf k).length = 32 := by
    simp [CryptoVerification.SpqrV1Sync.TopLog.authOf, CryptoGames.HMAC.keyToBytes32]
  have hvn : optRaw rawVN vn? ≤ 32 := by
    rcases hw.hvn with rfl | rfl
    · exact Nat.zero_le _
    · exact le_of_eq hauth
  have he_pos := CryptoVerification.SpqrV1Sync.TopLog.runT_epoch_pos h.hrun
  have hcur_both := CryptoVerification.SpqrV1Sync.TopLog.inSync_chainCur F K g.e g.auth g.c
    (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
    (runT_inSync F K (CryptoVerification.SpqrV1Sync.TopLog.authOf k) h.hrun) he_pos
  have hep_le := h.epoch_le
  have hcur : chainCur (g.st P) ≤ 3 := by
    cases P with
    | A => rcases hcur_both.1 with hA | ⟨hA, -⟩ <;> omega
    | B => rcases hcur_both.2 with hB | ⟨hB, -⟩ <;> omega
  obtain ⟨_, _, hlaQ⟩ := h.hparty P.other
  have hlogQ := h.hlogSent P.other
  have hsup_le : ∀ e, (g.recvSet P e).sup id ≤ 2 := by
    intro e
    refine Finset.sup_le fun i hi => ?_
    have hrec_i : (e + 1, i) ∈ CryptoVerification.SpqrV1Sync.TopLog.posList (s.st P).2.recvd :=
      (hla.hrecvd (e + 1) i).mpr ⟨by omega, hi⟩
    have hsent_i := h.hdeliv P (e + 1, i) hrec_i
    have hi_le : 1 ≤ i ∧ i ≤ g.sendCtr P.other e := by
      have := (hlaQ.hsent (e + 1) i).mp hsent_i
      exact ⟨this.2.1, this.2.2⟩
    by_contra hgt
    dsimp only [id] at hgt
    have hm1 := (hlaQ.hsent (e + 1) 1).mpr ⟨by omega, by omega, by change 1 ≤ g.sendCtr P.other e; omega⟩
    have hm2 := (hlaQ.hsent (e + 1) 2).mpr ⟨by omega, by omega, by change 2 ≤ g.sendCtr P.other e; omega⟩
    have hm3 := (hlaQ.hsent (e + 1) 3).mpr ⟨by omega, by omega, by change 3 ≤ g.sendCtr P.other e; omega⟩
    have hps_len : (CryptoVerification.SpqrV1Sync.TopLog.posList (s.st P.other).2.sent).length ≤ 2 := by
      dsimp only [CryptoVerification.SpqrV1Sync.TopLog.posList]
      have := List.length_filterMap_le spqrPos (s.st P.other).2.sent; omega
    rcases hps : CryptoVerification.SpqrV1Sync.TopLog.posList (s.st P.other).2.sent with
      _ | ⟨⟨a1, b1⟩, _ | ⟨⟨a2, b2⟩, _ | _⟩⟩
    · simp only [hps, List.not_mem_nil] at hm1
    · simp only [hps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm1 hm2; omega
    · simp only [hps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm1 hm2 hm3; omega
    · simp only [hps, List.length_cons] at hps_len; omega
  have hsum_le : ∑ e ∈ Finset.range (chainCur (g.st P) + 1),
      (264 + 36 * (g.recvSet P e).sup id) ≤ 1344 := by
    have h1 : ∑ e ∈ Finset.range (chainCur (g.st P) + 1),
        (264 + 36 * (g.recvSet P e).sup id) ≤
        ∑ _e ∈ Finset.range (chainCur (g.st P) + 1), 336 :=
      Finset.sum_le_sum fun e _ => by have := hsup_le e; omega
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1; omega
  have hch : optRaw rawChain (ch?.map Chain.intoPb) ≤ 1376 := by
    rcases hw.hch with rfl | ⟨rfl, -, -⟩
    · have hc := chainOk_rawChain_le F (CryptoVerification.SpqrV1Sync.TopLog.authOf k)
        (CryptoVerification.SpqrV1Sync.TopLog.partyDir P) g.secret (g.sendCtr P) (g.recvSet P)
        chE hw.hok hw.hsendPrev
      simp only [Option.map_some, CryptoVerification.SpqrV1.Top.StateSize.optRaw_some]
      rw [hw.hcur] at hc; omega
    · exact Nat.zero_le _
  have hraw := runT_rawV1State_le_5M F K (CryptoVerification.SpqrV1Sync.TopLog.authOf k) h.hrun
  have hbraid : rawV1State (g.st P).into_pb ≤ 5000000 := by
    cases P <;> [exact hraw.1; exact hraw.2]
  omega

private theorem nv_encodeVarintLoop_len_le : ∀ (fuel : Nat) (a : BitVec 64),
    (encodeVarintLoop fuel a).length ≤ fuel
  | 0, _ => by simp [encodeVarintLoop]
  | fuel + 1, a => by
    simp only [encodeVarintLoop]; split
    · simp
    · simp only [List.length_cons]; have := nv_encodeVarintLoop_len_le fuel (a >>> 7); omega

private theorem nv_sent_msg_len_le {F : ShaCompress} {K : MlKem} {k : BitVec 256}
    {s : CryptoGames.LibsignalSM.Corr.SpqrGameState Bytes}
    {g : CryptoVerification.SpqrV1Sync.TopLog.Ghost F}
    (h : CryptoVerification.SpqrV1Sync.TopLog.TopInv F K k s g)
    (j : Nat) (Q : CryptoGames.Party) (msg : Bytes) (salt : CryptoGames.HKDF.Salt)
    (hj : s.sent[j]? = some (Q, msg, salt)) :
    msg.length ≤ 64 := by
  obtain ⟨m, idx, -, rfl, -⟩ := h.hsent j Q msg salt hj
  have he1 := nv_encodeVarintLoop_len_le MAX_VARINT_BYTES_LEN m.epoch
  have he2 := nv_encodeVarintLoop_len_le MAX_VARINT_BYTES_LEN (idx.zeroExtend 64)
  rcases m with ⟨ep, p⟩
  cases p with
  | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
    have he3 := nv_encodeVarintLoop_len_le MAX_VARINT_BYTES_LEN
      ((spqrPolyApi.chunkIndex c).zeroExtend 64)
    simp only [Message.serialize, encode_chunk, encode_varint, MAX_VARINT_BYTES_LEN,
      List.length_append, List.length_cons, List.length_nil, List.Vector.toList_length] at he1 he2 he3 ⊢
    omega
  | none | ct1Ack _ =>
    simp only [Message.serialize, encode_varint, MAX_VARINT_BYTES_LEN,
      List.length_append, List.length_cons, List.length_nil] at he1 he2 ⊢
    omega

private theorem nv_init_a_ok (F : ShaCompress) (k : BitVec 256) :
    ∃ stA, States.init_a spqrPolyApi (spqrAuthApi F)
      (CryptoVerification.SpqrV1Sync.TopLog.authOf k) = .ok stA := by
  unfold States.init_a Chunked.SendEk.KeysUnsampled.new Unchunked.SendEk.KeysUnsampled.new
  simp only [spqrAuthApi, Authenticator.new]
  exact ⟨_, rfl⟩

private theorem nv_init_b_ok (F : ShaCompress) (k : BitVec 256) :
    ∃ stB, States.init_b spqrPolyApi (spqrAuthApi F)
      (CryptoVerification.SpqrV1Sync.TopLog.authOf k) = .ok stB := by
  unfold States.init_b Chunked.SendCt.NoHeaderReceived.new Unchunked.SendCt.NoHeaderReceived.new
  simp only [spqrAuthApi, Authenticator.new, spqrPolyApi, PolyDecoder.new]
  exact ⟨_, rfl⟩

private theorem nv_recvPanics_eq_false_of_ok (F : ShaCompress) (K : MlKem)
    (st : Bytes × CryptoGames.LibsignalSession.SpqrLog) (msg : Bytes)
    (st' : Bytes × CryptoGames.LibsignalSession.SpqrLog) (salt : CryptoGames.HKDF.Salt)
    (h : (spqrV1SessionUniformCoins F K).withLog.recv st msg = .ok (st', salt)) :
    (spqrV1SessionUniformCoins F K).withLog.recvPanics st msg = false := by
  simp only [CryptoGames.LibsignalSession.Spqr.withLog, spqrV1SessionUniformCoins, spqrV1_eq, toSpqrModel,
    recvPanicsB] at h ⊢
  cases hr : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) st.1 msg with
  | ok _ => rfl
  | error e =>
    cases e with
    | err _ => rfl
    | panic _ => rw [hr] at h; cases h

private theorem spqrTwoMsg_roundtrip_of_honestFail (F : ShaCompress) (K : MlKem)
    (hhonest : ∀ (s : Seed) (r : EncRand), K.honestExchangeFails s r = false) (pqr0 : BitVec 256) :
    (spqrV1Session F K).init .a2b pqr0 ≠ [] ∧
    ((spqrV1Session F K).init .a2b pqr0).length < 2 ^ 28 ∧
    (spqrV1Session F K).init .b2a pqr0 ≠ [] ∧
    ((spqrV1Session F K).init .b2a pqr0).length < 2 ^ 28 ∧
    ∃ stA1 salt1 pqMsg1 stB1 stB2 salt2 pqMsg2 stA2,
      (spqrV1Session F K).send ((spqrV1Session F K).init .a2b pqr0) (coinBytes 0#512) =
        some (stA1, salt1, pqMsg1) ∧
      (spqrV1Session F K).recv ((spqrV1Session F K).init .b2a pqr0) pqMsg1 = .ok (stB1, salt1) ∧
      (spqrV1Session F K).send stB1 (coinBytes 0#512) = some (stB2, salt2, pqMsg2) ∧
      (spqrV1Session F K).recv stA1 pqMsg2 = .ok (stA2, salt2) ∧
      stA1 ≠ [] ∧ stA1.length < 2 ^ 28 ∧
      stB1 ≠ [] ∧ stB1.length < 2 ^ 28 ∧
      stB2 ≠ [] ∧ stB2.length < 2 ^ 28 ∧
      stA2 ≠ [] ∧ stA2.length < 2 ^ 28 ∧
      pqMsg1.length ≤ 64 ∧ pqMsg2.length ≤ 64 := by
  obtain ⟨stA0', hstA0_def⟩ : ∃ x, (spqrV1Session F K).init .a2b pqr0 = x := ⟨_, rfl⟩
  obtain ⟨stB0', hstB0_def⟩ : ∃ x, (spqrV1Session F K).init .b2a pqr0 = x := ⟨_, rfl⟩
  obtain ⟨bA, hbA⟩ := nv_init_a_ok F pqr0
  obtain ⟨bB, hbB⟩ := nv_init_b_ok F pqr0
  have hkem : ∀ g P r, CryptoVerification.SpqrV1Sync.TopLog.KemGood F K g P r :=
    fun _ _ _ _ s r' _ _ => kemOk_of_honestFail K s r' (hhonest s r')
  obtain ⟨s0, hs0_def⟩ : ∃ s0 : CryptoGames.LibsignalSM.Corr.SpqrGameState Bytes,
      ⟨fun P => (spqrV1SessionUniformCoins F K).withLog.init (CryptoGames.LibsignalSM.Corr.spqrDir P) pqr0,
        [], false⟩ = s0 := ⟨_, rfl⟩
  obtain ⟨g0, hg0_def⟩ : ∃ g0,
      CryptoVerification.SpqrV1Sync.TopLog.initGhost F pqr0 bA bB = g0 := ⟨_, rfl⟩
  have h0 : CryptoVerification.SpqrV1Sync.TopLog.FifoAll F K pqr0 s0 g0 := by
    rw [← hs0_def, ← hg0_def]
    exact CryptoVerification.SpqrV1Sync.TopLog.fifoAll_init F K pqr0 bA bB hbA hbB
  have hs0_sent : s0.sent = [] := by rw [← hs0_def]
  have hs0_stA : s0.st .A = (stA0', ⟨[], []⟩) := by
    rw [← hs0_def]
    dsimp only [CryptoGames.LibsignalSession.Spqr.withLog, CryptoGames.LibsignalSM.Corr.spqrDir]
    rw [spqrV1SessionB_init, ← spqrV1Session_init, hstA0_def]
    rfl
  have hs0_stB : s0.st .B = (stB0', ⟨[], []⟩) := by
    rw [← hs0_def]
    dsimp only [CryptoGames.LibsignalSession.Spqr.withLog, CryptoGames.LibsignalSM.Corr.spqrDir]
    rw [spqrV1SessionB_init, ← spqrV1Session_init, hstB0_def]
    rfl
  have hb0A := topInv_state_bounds F K pqr0 s0 g0 h0.htop (by rw [hs0_sent]; simp) .A
  have hb0B := topInv_state_bounds F K pqr0 s0 g0 h0.htop (by rw [hs0_sent]; simp) .B
  obtain ⟨hsucc1, h1'⟩ := CryptoVerification.SpqrV1Sync.TopLog.fifoAll_send F K pqr0 2
    (by decide) s0 g0 h0 (by rw [hs0_sent]; simp) .A 0#512 (hkem _ _ _)
  obtain ⟨stA1, salt1, pqMsg1, hSendA, hs1_step⟩ :=
    CryptoVerification.SpqrV1Sync.TopLog.spqrSendStep_succ (spqrV1SessionUniformCoins F K) s0 .A 0#512 hsucc1
  obtain ⟨s1, hs1_def⟩ : ∃ s1,
      (CryptoGames.LibsignalSM.Corr.spqrSendStep (spqrV1SessionUniformCoins F K) s0 .A 0#512).2 = s1 :=
    ⟨_, rfl⟩
  obtain ⟨g1, hg1_def⟩ : ∃ g1,
      CryptoVerification.SpqrV1Sync.TopLog.ghostSend F K g0 .A 0#512 = g1 := ⟨_, rfl⟩
  have h1 : CryptoVerification.SpqrV1Sync.TopLog.FifoAll F K pqr0 s1 g1 := by
    rwa [← hs1_def, ← hg1_def]
  have hs1_eq : s1 =
      { s0 with st := Function.update s0.st .A
                  (stA1, { (s0.st .A).2 with sent := pqMsg1 :: (s0.st .A).2.sent })
                sent := s0.sent ++ [(.A, pqMsg1, salt1)] } := hs1_def.symm.trans hs1_step
  have hs1_sent : s1.sent = [(.A, pqMsg1, salt1)] := by rw [hs1_eq, hs0_sent]; rfl
  have hs1_stA : s1.st .A = (stA1, ⟨[pqMsg1], []⟩) := by
    rw [hs1_eq]; dsimp only; rw [Function.update_self, hs0_stA]
  have hs1_stB : s1.st .B = (stB0', ⟨[], []⟩) := by
    rw [hs1_eq]; dsimp only
    rw [Function.update_of_ne (by decide : CryptoGames.Party.B ≠ .A), hs0_stB]
  have hs1_len : s1.sent.length ≤ 2 := by rw [hs1_sent]; simp
  have hb1A := topInv_state_bounds F K pqr0 s1 g1 h1.htop hs1_len .A
  have hpq1 : pqMsg1.length ≤ 64 :=
    nv_sent_msg_len_le h1.htop 0 .A pqMsg1 salt1 (by rw [hs1_sent]; rfl)
  have hj0 : CryptoVerification.SpqrV1Sync.TopLog.fifoNext s1 .B = some 0 := by
    unfold CryptoVerification.SpqrV1Sync.TopLog.fifoNext
      CryptoVerification.SpqrV1Sync.TopLog.sendIdx
    rw [hs1_sent, hs1_stB]; rfl
  obtain ⟨pqMsg1', salt1', hjs1, hwin1⟩ := CryptoVerification.SpqrV1Sync.TopLog.fifo_window
    F K pqr0 s1 g1 h1 (by rw [hs1_sent]; simp) .B 0 hj0
  have hjs1_eq : (CryptoGames.Party.A, pqMsg1', salt1') = (.A, pqMsg1, salt1) := by
    have h := hjs1; rw [hs1_sent] at h; exact Option.some.inj h.symm
  obtain ⟨-, rfl, rfl⟩ := hjs1_eq
  obtain ⟨stB1_log, hRecvB_log, -, -⟩ := CryptoVerification.SpqrV1Sync.TopLog.deliver_inWindow
    F K pqr0 2 (by decide) s1 g1 h1.htop hs1_len .B 0 pqMsg1 salt1 hjs1 hwin1
  obtain ⟨_, h2'⟩ := CryptoVerification.SpqrV1Sync.TopLog.fifoAll_deliver
    F K pqr0 2 (by decide) s1 g1 h1 hs1_len .B 0 hj0
  obtain ⟨s2, hs2_def⟩ : ∃ s2,
      (CryptoGames.LibsignalSM.Corr.spqrDeliverStep (spqrV1SessionUniformCoins F K) s1 .B 0 true).2 = s2 :=
    ⟨_, rfl⟩
  obtain ⟨g2, hg2_def⟩ : ∃ g2,
      CryptoVerification.SpqrV1Sync.TopLog.ghostDeliver F K g1 .B 0 = g2 := ⟨_, rfl⟩
  have h2 : CryptoVerification.SpqrV1Sync.TopLog.FifoAll F K pqr0 s2 g2 := by
    rwa [← hs2_def, ← hg2_def]
  have hs2_eq : s2 = { s1 with st := Function.update s1.st .B stB1_log } := by
    rw [← hs2_def, CryptoVerification.SpqrV1Sync.TopLog.spqrDeliverStep_accept
      (spqrV1SessionUniformCoins F K) s1 .B 0 pqMsg1 salt1 stB1_log h1.htop.hwin hjs1 hRecvB_log
      (nv_recvPanics_eq_false_of_ok F K (s1.st .B) pqMsg1 stB1_log salt1 hRecvB_log)]
  obtain ⟨hRecvB, -⟩ := CryptoVerification.SpqrV1Sync.TopLog.withLog_recv_ok
    (spqrV1SessionUniformCoins F K) (s1.st .B) pqMsg1 stB1_log salt1 hRecvB_log
  have hs2_sent : s2.sent = [(.A, pqMsg1, salt1)] := by rw [hs2_eq, hs1_sent]
  have hs2_stA : s2.st .A = (stA1, ⟨[pqMsg1], []⟩) := by
    rw [hs2_eq]; dsimp only
    rw [Function.update_of_ne (by decide : CryptoGames.Party.A ≠ .B), hs1_stA]
  have hs2_stB : (s2.st .B).1 = stB1_log.1 := by rw [hs2_eq]; dsimp only; rw [Function.update_self]
  have hs2_len : s2.sent.length ≤ 2 := by rw [hs2_sent]; simp
  have hb2B := topInv_state_bounds F K pqr0 s2 g2 h2.htop hs2_len .B
  obtain ⟨hsucc2, h3'⟩ := CryptoVerification.SpqrV1Sync.TopLog.fifoAll_send F K pqr0 2
    (by decide) s2 g2 h2 hs2_len .B 0#512 (hkem _ _ _)
  obtain ⟨stB2, salt2, pqMsg2, hSendB, hs3_step⟩ :=
    CryptoVerification.SpqrV1Sync.TopLog.spqrSendStep_succ (spqrV1SessionUniformCoins F K) s2 .B 0#512 hsucc2
  obtain ⟨s3, hs3_def⟩ : ∃ s3,
      (CryptoGames.LibsignalSM.Corr.spqrSendStep (spqrV1SessionUniformCoins F K) s2 .B 0#512).2 = s3 :=
    ⟨_, rfl⟩
  obtain ⟨g3, hg3_def⟩ : ∃ g3,
      CryptoVerification.SpqrV1Sync.TopLog.ghostSend F K g2 .B 0#512 = g3 := ⟨_, rfl⟩
  have h3 : CryptoVerification.SpqrV1Sync.TopLog.FifoAll F K pqr0 s3 g3 := by
    rwa [← hs3_def, ← hg3_def]
  have hs3_eq : s3 =
      { s2 with st := Function.update s2.st .B
                  (stB2, { (s2.st .B).2 with sent := pqMsg2 :: (s2.st .B).2.sent })
                sent := s2.sent ++ [(.B, pqMsg2, salt2)] } := hs3_def.symm.trans hs3_step
  have hs3_sent : s3.sent = [(.A, pqMsg1, salt1), (.B, pqMsg2, salt2)] := by
    rw [hs3_eq, hs2_sent]; rfl
  have hs3_stA : s3.st .A = (stA1, ⟨[pqMsg1], []⟩) := by
    rw [hs3_eq]; dsimp only
    rw [Function.update_of_ne (by decide : CryptoGames.Party.A ≠ .B), hs2_stA]
  have hs3_stB : (s3.st .B).1 = stB2 := by rw [hs3_eq]; dsimp only; rw [Function.update_self]
  have hs3_len : s3.sent.length ≤ 2 := by rw [hs3_sent]; simp
  have hb3B := topInv_state_bounds F K pqr0 s3 g3 h3.htop hs3_len .B
  have hpq2 : pqMsg2.length ≤ 64 :=
    nv_sent_msg_len_le h3.htop 1 .B pqMsg2 salt2 (by rw [hs3_sent]; rfl)
  have hj1 : CryptoVerification.SpqrV1Sync.TopLog.fifoNext s3 .A = some 1 := by
    unfold CryptoVerification.SpqrV1Sync.TopLog.fifoNext
      CryptoVerification.SpqrV1Sync.TopLog.sendIdx
    rw [hs3_sent, hs3_stA]; rfl
  obtain ⟨pqMsg2', salt2', hjs2, hwin2⟩ := CryptoVerification.SpqrV1Sync.TopLog.fifo_window
    F K pqr0 s3 g3 h3 (by rw [hs3_sent]; simp) .A 1 hj1
  have hjs2_eq : (CryptoGames.Party.B, pqMsg2', salt2') = (.B, pqMsg2, salt2) := by
    have h := hjs2; rw [hs3_sent] at h; exact Option.some.inj h.symm
  obtain ⟨-, rfl, rfl⟩ := hjs2_eq
  obtain ⟨stA2_log, hRecvA_log, -, -⟩ := CryptoVerification.SpqrV1Sync.TopLog.deliver_inWindow
    F K pqr0 2 (by decide) s3 g3 h3.htop hs3_len .A 1 pqMsg2 salt2 hjs2 hwin2
  obtain ⟨_, h4'⟩ := CryptoVerification.SpqrV1Sync.TopLog.fifoAll_deliver
    F K pqr0 2 (by decide) s3 g3 h3 hs3_len .A 1 hj1
  obtain ⟨s4, hs4_def⟩ : ∃ s4,
      (CryptoGames.LibsignalSM.Corr.spqrDeliverStep (spqrV1SessionUniformCoins F K) s3 .A 1 true).2 = s4 :=
    ⟨_, rfl⟩
  obtain ⟨g4, hg4_def⟩ : ∃ g4,
      CryptoVerification.SpqrV1Sync.TopLog.ghostDeliver F K g3 .A 1 = g4 := ⟨_, rfl⟩
  have h4 : CryptoVerification.SpqrV1Sync.TopLog.FifoAll F K pqr0 s4 g4 := by
    rwa [← hs4_def, ← hg4_def]
  have hs4_eq : s4 = { s3 with st := Function.update s3.st .A stA2_log } := by
    rw [← hs4_def, CryptoVerification.SpqrV1Sync.TopLog.spqrDeliverStep_accept
      (spqrV1SessionUniformCoins F K) s3 .A 1 pqMsg2 salt2 stA2_log h3.htop.hwin hjs2 hRecvA_log
      (nv_recvPanics_eq_false_of_ok F K (s3.st .A) pqMsg2 stA2_log salt2 hRecvA_log)]
  obtain ⟨hRecvA, -⟩ := CryptoVerification.SpqrV1Sync.TopLog.withLog_recv_ok
    (spqrV1SessionUniformCoins F K) (s3.st .A) pqMsg2 stA2_log salt2 hRecvA_log
  have hs4_sent : s4.sent = [(.A, pqMsg1, salt1), (.B, pqMsg2, salt2)] := by
    rw [hs4_eq, hs3_sent]
  have hs4_stA : (s4.st .A).1 = stA2_log.1 := by rw [hs4_eq]; dsimp only; rw [Function.update_self]
  have hs4_len : s4.sent.length ≤ 2 := by rw [hs4_sent]; simp
  have hb4A := topInv_state_bounds F K pqr0 s4 g4 h4.htop hs4_len .A
  have hs0A1 : (s0.st .A).1 = stA0' := by rw [hs0_stA]
  have hs0B1 : (s0.st .B).1 = stB0' := by rw [hs0_stB]
  have hs1A1 : (s1.st .A).1 = stA1 := by rw [hs1_stA]
  have hs1B1 : (s1.st .B).1 = stB0' := by rw [hs1_stB]
  have hs3A1 : (s3.st .A).1 = stA1 := by rw [hs3_stA]
  rw [hs0A1, spqrV1SessionB_send] at hSendA
  rw [hs0A1] at hb0A
  rw [hs0B1] at hb0B
  rw [hs1A1] at hb1A
  rw [hs1B1, spqrV1SessionB_recv] at hRecvB
  rw [hs2_stB, spqrV1SessionB_send] at hSendB
  rw [hs2_stB] at hb2B
  rw [hs3_stB] at hb3B
  rw [hs3A1, spqrV1SessionB_recv] at hRecvA
  rw [hs4_stA] at hb4A
  rw [hstA0_def, hstB0_def]
  exact ⟨hb0A.1, hb0A.2, hb0B.1, hb0B.2,
    stA1, salt1, pqMsg1, stB1_log.1, stB2, salt2, pqMsg2, stA2_log.1,
    hSendA, hRecvB, hSendB, hRecvA,
    hb1A.1, hb1A.2, hb2B.1, hb2B.2, hb3B.1, hb3B.2, hb4A.1, hb4A.2, hpq1, hpq2⟩

/-- Two-message SPQR V1 round-trip under `MlKem.ideal` with non-empty `< 2 ^ 28`-byte states and
`≤ 64`-byte wire tokens at each step. -/
theorem spqrTwoMsg_roundtrip (F : ShaCompress) (pqr0 : BitVec 256) :
    (spqrV1Session F MlKem.ideal).init .a2b pqr0 ≠ [] ∧
    ((spqrV1Session F MlKem.ideal).init .a2b pqr0).length < 2 ^ 28 ∧
    (spqrV1Session F MlKem.ideal).init .b2a pqr0 ≠ [] ∧
    ((spqrV1Session F MlKem.ideal).init .b2a pqr0).length < 2 ^ 28 ∧
    ∃ stA1 salt1 pqMsg1 stB1 stB2 salt2 pqMsg2 stA2,
      (spqrV1Session F MlKem.ideal).send
        ((spqrV1Session F MlKem.ideal).init .a2b pqr0) (coinBytes 0#512) =
        some (stA1, salt1, pqMsg1) ∧
      (spqrV1Session F MlKem.ideal).recv
        ((spqrV1Session F MlKem.ideal).init .b2a pqr0) pqMsg1 = .ok (stB1, salt1) ∧
      (spqrV1Session F MlKem.ideal).send stB1 (coinBytes 0#512) =
        some (stB2, salt2, pqMsg2) ∧
      (spqrV1Session F MlKem.ideal).recv stA1 pqMsg2 = .ok (stA2, salt2) ∧
      stA1 ≠ [] ∧ stA1.length < 2 ^ 28 ∧
      stB1 ≠ [] ∧ stB1.length < 2 ^ 28 ∧
      stB2 ≠ [] ∧ stB2.length < 2 ^ 28 ∧
      stA2 ≠ [] ∧ stA2.length < 2 ^ 28 ∧
      pqMsg1.length ≤ 64 ∧ pqMsg2.length ≤ 64 :=
  spqrTwoMsg_roundtrip_of_honestFail F MlKem.ideal MlKem.ideal_honestFail pqr0

/-- Existential form of `spqrTwoMsg_roundtrip` with opaque initial states `stA0` and `stB0` so
callers do not unfold `spqrV1Init`. -/
theorem spqrTwoMsg_roundtrip_exists (F : ShaCompress) (K : MlKem) (hK : K = MlKem.ideal)
    (S : CryptoGames.LibsignalSession.Spqr (List (BitVec 8)) (List (BitVec 8)))
    (hS : S = spqrV1Session F K)
    (coins : List (BitVec 8)) (hcoins : coins = coinBytes 0#512) (pqr0 : BitVec 256) :
    ∃ stA0 stB0 stA1 salt1 pqMsg1 stB1 stB2 salt2 pqMsg2 stA2,
      S.init .a2b pqr0 = stA0 ∧
      S.init .b2a pqr0 = stB0 ∧
      stA0 ≠ [] ∧ stA0.length < 2 ^ 28 ∧
      stB0 ≠ [] ∧ stB0.length < 2 ^ 28 ∧
      S.send stA0 coins = some (stA1, salt1, pqMsg1) ∧
      S.recv stB0 pqMsg1 = .ok (stB1, salt1) ∧
      S.send stB1 coins = some (stB2, salt2, pqMsg2) ∧
      S.recv stA1 pqMsg2 = .ok (stA2, salt2) ∧
      stA1 ≠ [] ∧ stA1.length < 2 ^ 28 ∧
      stB1 ≠ [] ∧ stB1.length < 2 ^ 28 ∧
      stB2 ≠ [] ∧ stB2.length < 2 ^ 28 ∧
      stA2 ≠ [] ∧ stA2.length < 2 ^ 28 ∧
      pqMsg1.length ≤ 64 ∧ pqMsg2.length ≤ 64 := by
  subst hK; subst hS; subst hcoins
  obtain ⟨h1, h2, h3, h4, stA1, salt1, pqMsg1, stB1, stB2, salt2, pqMsg2, stA2, rest⟩ :=
    spqrTwoMsg_roundtrip F pqr0
  exact ⟨_, _, stA1, salt1, pqMsg1, stB1, stB2, salt2, pqMsg2, stA2, rfl, rfl, h1, h2, h3, h4,
    rest⟩

end CryptoVerification.LibsignalCli.PqNonVacuity.SpqrBounds

namespace CryptoVerification.LibsignalCli.PqNonVacuity

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.SignalSession
open CryptoVerification.LibsignalProtoCodec

def K0 : LibsignalSpqrV1.MlKem := LibsignalSpqrV1.MlKem.ideal

/-- `PqxdhPrims` witness whose Kyber1024 `encaps` places the 32 coin bytes at the start of the
1568-byte ciphertext for exact `decaps` recovery, and whose Ed25519 hooks accept the zero
signature. -/
def Q0 : PqxdhPrims where
  F512 := fun st _ => st
  montToEd := fun _ _ => some (List.Vector.replicate 160 0#8)
  compress := fun _ => List.Vector.replicate 32 0#8
  edNeg := fun p => p
  isTorsionFree := fun _ => true
  dsmb := fun _ _ _ => List.Vector.replicate 160 0#8
  scalarMod := fun _ => List.Vector.replicate 32 0#8
  scalarWide := fun _ => List.Vector.replicate 32 0#8
  encaps := fun _ coins =>
    (⟨coins.toList ++ List.replicate 1536 0#8, by
      simp only [List.length_append, List.Vector.toList_length, List.length_replicate]⟩, coins)
  decaps := fun _ ct =>
    ⟨ct.toList.take 32, by simp only [List.length_take, List.Vector.toList_length]; omega⟩
  K := K0

/-- `Crypto` witness with identity block cipher, constant non-zero DH output `1#8 :: 0^31`, and
`pubKey` equal to byte `0` of the scalar padded with 31 zero bytes. -/
def C0 : Crypto where
  F := fun st _ => st
  E := fun _ blk => blk
  D := fun _ blk => blk
  X := fun _ _ => ⟨1#8 :: List.replicate 31 0#8, rfl⟩
  pubKey := fun sk => ⟨sk.get 0 :: List.replicate 31 0#8, rfl⟩

def W0 : PEParams where
  C := C0
  Q := Q0

def X0 : UnreachedPqxdhPrimitives where
  sigPkGen := fun a => vecU8 (C0.pubKey (Ratchet.clampScalar (u8Vec 32 a)))
  sigSign := fun _ _ _ => List.replicate 64 0
  scalarMul := fun _ _ => List.replicate 32 0
  scalarAdd := fun _ _ => List.replicate 32 0
  kemKeyGen := fun _ => (List.replicate 1568 0, List.replicate 3168 0)
  pow8 := fun p => p
  isValidDhTriple := fun _ _ _ => true

theorem c0_dh_comm (a b : List.Vector (BitVec 8) 32) :
    W0.C.X (Ratchet.clampScalar a) (W0.C.pubKey (Ratchet.clampScalar b)) =
      W0.C.X (Ratchet.clampScalar b) (W0.C.pubKey (Ratchet.clampScalar a)) := rfl

theorem c0_dh_ne_zero (a b : List.Vector (BitVec 8) 32) :
    W0.C.X (Ratchet.clampScalar a) (W0.C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8 := by
  intro h
  have h0 := congrArg (fun v => v.toList.head?) h
  simp [W0, C0, List.Vector.replicate, List.Vector.toList] at h0

theorem c0_aes_roundtrip (k : CBC.AesKey) (m : CBC.Block) :
    W0.C.D k (W0.C.E k m) = m := rfl

theorem q0_kyber_roundtrip (sk : List.Vector (BitVec 8) 3168)
    (pk : List.Vector (BitVec 8) 1568) (coins : List.Vector (BitVec 8) 32) :
    W0.Q.decaps sk (W0.Q.encaps pk coins).1 = (W0.Q.encaps pk coins).2 := by
  apply List.Vector.eq
  simp only [W0, Q0, List.Vector.toList_mk, List.take_left' coins.toList_length]

/-- 16-byte UUID parsed from `partyAddressName .A`. -/
def uuidA : List.Vector (BitVec 8) 16 :=
  ⟨[0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8,
    0x9a#8, 0x0b#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8], rfl⟩

/-- 16-byte UUID parsed from `partyAddressName .B`. -/
def uuidB : List.Vector (BitVec 8) 16 :=
  ⟨[0x5d#8, 0x3e#8, 0x2f#8, 0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8,
    0x8e#8, 0x0f#8, 0xa1#8, 0xb2#8, 0xc3#8, 0xd4#8, 0xe5#8, 0xf6#8], rfl⟩

theorem uuidTryParse_nameE_distinct :
    ∃ uA uB,
      LibsignalTripleRatchetRepr.uuidTryParse (LibsignalTripleRatchetRepr.utf8 (partyAddressName .A)) =
        some uA ∧
      LibsignalTripleRatchetRepr.uuidTryParse (LibsignalTripleRatchetRepr.utf8 (partyAddressName .B)) =
        some uB ∧
      uA ≠ uB ∧
      LibsignalTripleRatchetRepr.serviceIdParse LibsignalTripleRatchetRepr.uuidTryParse
        (LibsignalTripleRatchetRepr.utf8 (partyAddressName .A)) ≠
      LibsignalTripleRatchetRepr.serviceIdParse LibsignalTripleRatchetRepr.uuidTryParse
        (LibsignalTripleRatchetRepr.utf8 (partyAddressName .B)) :=
  ⟨uuidA, uuidB, by decide +kernel, by decide +kernel, by decide, by decide +kernel⟩

private theorem vecU8_replicate_zero (n : Nat) :
    vecU8 (List.Vector.replicate n 0#8) = List.replicate n 0 := by
  simp [vecU8, toU8, List.Vector.replicate, List.Vector.toList]

private theorem vecU8_length {n : Nat} (v : List.Vector (BitVec 8) n) :
    (vecU8 v).length = n := by
  simp only [vecU8, toU8, List.length_map, List.Vector.toList_length]

private theorem toU8_ofU8 (bs : List UInt8) : toU8 (ofU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih => simp only [toU8, ofU8, List.map_cons] at *; rw [ih]

private theorem ofU8_toU8 (bs : Bytes) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih => simp only [toU8, ofU8, List.map_cons] at *; rw [ih]

private theorem u8Vec_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    u8Vec n (vecU8 v) = v := by
  apply List.Vector.eq
  rcases v with ⟨l, hl⟩
  simp [u8Vec, vecU8, ofU8_toU8, fitVec, List.Vector.toList, hl]

private theorem vecU8_u8Vec_of_length {n : Nat} (xs : List UInt8) (h : xs.length = n) :
    vecU8 (u8Vec n xs) = xs := by
  have hlen : (ofU8 xs).length = n := by simp [ofU8, h]
  simp [vecU8, u8Vec, fitVec, List.Vector.toList, hlen, toU8_ofU8]

theorem w0_isCanonical (sk : List.Vector (BitVec 8) 32) :
    SignalPqxdh.isCanonicalRef (modelPrims X0 W0) (vecU8 (W0.C.pubKey sk)) = true := by
  have hv : vecU8 (W0.C.pubKey sk) = UInt8.ofBitVec (sk.get 0) :: List.replicate 31 0 := by
    simp [W0, C0, vecU8, toU8]
  rw [hv]
  unfold SignalPqxdh.isCanonicalRef SignalPqxdh.scalarIsInRange
  have hlen : (UInt8.ofBitVec (sk.get 0) :: List.replicate 31 (0 : UInt8)).length = 32 := rfl
  have hget : (UInt8.ofBitVec (sk.get 0) :: List.replicate 31 (0 : UInt8)).getD 31 0 = 0 := rfl
  simp only [hlen, hget]
  have h1 : ((32 : Nat) == 32) = true := rfl
  have h2 : (((0 : UInt8) &&& 0x80) == 0) = true := rfl
  have h3 : (((0 : UInt8) &&& 0x7F) == 0x7F) = false := rfl
  simp only [h1, h2, h3, Bool.and_false, Bool.not_false, Bool.and_self, ↓reduceIte,
    modelPrims, blockLevelPrims, W0, Q0]
  rfl

theorem w0_sigVerify_zero (pk m : List UInt8) (hpk : pk.length = 32) :
    (modelPrims X0 W0).sigVerify pk m (List.replicate 64 0) = true := by
  change SignalPqxdh.xeddsaVerifyRef (modelPrims X0 W0) pk m (List.replicate 64 0) = true
  unfold SignalPqxdh.xeddsaVerifyRef
  rw [hpk]
  have hcond : (((32 : Nat) == 32 && (List.replicate 64 (0 : UInt8)).length == 64 &&
      ((List.replicate 64 (0 : UInt8)).getD 63 0 &&& 0x60) == 0)) = true := rfl
  rw [hcond]; simp only [↓reduceIte]
  have hm2e : ∀ sb, (modelPrims X0 W0).montToEd pk sb =
      some (vecU8 (List.Vector.replicate 160 0#8)) := fun _ => rfl
  rw [hm2e]; dsimp only
  have htake : (List.replicate 64 (0 : UInt8)).take 32 = List.replicate 32 0 := rfl
  have hcmp : ∀ p, (modelPrims X0 W0).compress p = List.replicate 32 0 :=
    fun _ => vecU8_replicate_zero 32
  rw [htake, hcmp]; decide

def aliceMe : LocalIdentity := ⟨⟨8#8 :: List.replicate 31 0#8, rfl⟩, 1#32⟩
def bobMe : LocalIdentity := ⟨⟨16#8 :: List.replicate 31 0#8, rfl⟩, 2#32⟩

def spkId0 : BitVec 32 := 10#32
def opkId0 : BitVec 32 := 20#32
def kpkId0 : BitVec 32 := 30#32

def spkPriv0 : List.Vector (BitVec 8) 32 := List.Vector.replicate 32 0#8
def opkPriv0 : List.Vector (BitVec 8) 32 := ⟨24#8 :: List.replicate 31 0#8, rfl⟩
def sigZero64 : List.Vector (BitVec 8) 64 := List.Vector.replicate 64 0#8
def kpkPub0 : List.Vector (BitVec 8) 1568 := List.Vector.replicate 1568 0#8
def kpkSec0 : List.Vector (BitVec 8) 3168 := List.Vector.replicate 3168 0#8

def spkRec0 : PqSignedKey := { priv := spkPriv0, sig := sigZero64, timestamp := 0#64 }
def kpkRec0 : PqKyberKey := { pub := kpkPub0, sec := kpkSec0, sig := sigZero64, timestamp := 0#64 }

def keysB0 : ResponderPreKeySecrets :=
  { spkId := spkId0, spkPriv := spkPriv0, kpkId := kpkId0, kpkPub := kpkPub0,
    kpkSec := kpkSec0, opk := some (opkId0, opkPriv0) }

def bundleB0 : PreKeyBundleFields := honestBundle W0.C bobMe keysB0 sigZero64 sigZero64

def tape0 : List.Vector (BitVec 8) initiateTapeLen := List.Vector.replicate initiateTapeLen 0#8

def coins0 : List.Vector (BitVec 8) 64 :=
  ⟨LibsignalSpqrV1.coinBytes 0#512, LibsignalSpqrV1.coinBytes_length 0#512⟩

def idKeyA : IdentityKey := ⟨(keyPairOf W0.C aliceMe.idPriv).publicKey⟩
def idKeyB : IdentityKey := ⟨(keyPairOf W0.C bobMe.idPriv).publicKey⟩

theorem bundleB0_sigsOk : bundleB0.signaturesVerify X0 W0 = true := by
  unfold PreKeyBundleFields.signaturesVerify
  have hsig : vecU8 sigZero64 = List.replicate 64 0 := vecU8_replicate_zero 64
  have hpk : (vecU8 bundleB0.idPub).length = 32 := vecU8_length _
  change ((modelPrims X0 W0).sigVerify (vecU8 bundleB0.idPub) _ (vecU8 sigZero64) &&
      (modelPrims X0 W0).sigVerify (vecU8 bundleB0.idPub) _ (vecU8 sigZero64)) = true
  rw [hsig, w0_sigVerify_zero _ _ hpk, w0_sigVerify_zero _ _ hpk]; rfl

def aliceDir0 : PqParty :=
  { party := .A, me := aliceMe, peerId := some idKeyB, session := none,
    signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }

def bobDir0 : PqParty :=
  { party := .B, me := bobMe, peerId := some idKeyA, session := none,
    signed := [(spkId0, spkRec0)], oneTime := [(opkId0, some opkPriv0)],
    kyberOneTime := [], kyberLastResort := [(kpkId0, kpkRec0, [])] }

private theorem encodeVarintAux_len_le : ∀ (fuel : Nat) (v : BitVec 64),
    (encodeVarintAux fuel v).length ≤ fuel
  | 0, _ => by simp [encodeVarintAux]
  | fuel + 1, v => by
    simp only [encodeVarintAux]; split
    · simp
    · simp only [List.length_cons]; have := encodeVarintAux_len_le fuel (v >>> 7); omega

private theorem encodeVarint_len_bounds (v : BitVec 64) :
    1 ≤ (encodeVarint v).length ∧ (encodeVarint v).length ≤ 10 := by
  refine ⟨?_, encodeVarintAux_len_le 10 v⟩
  unfold encodeVarint encodeVarintAux; split <;> simp

private theorem encodeKey_len_bounds (tag : Nat) (wt : WireType) :
    1 ≤ (encodeKey tag wt).length ∧ (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_len_bounds _

private theorem lenField_len_bounds (tag : Nat) (payload : Bytes) :
    1 ≤ (lenField tag payload).length ∧ (lenField tag payload).length ≤ 20 + payload.length := by
  have hk := encodeKey_len_bounds tag .lengthDelimited
  have hv := encodeVarint_len_bounds (BitVec.ofNat 64 payload.length)
  simp only [lenField, List.length_append]; omega

private theorem lenField_le_of_le (tag : Nat) {payload : Bytes} {B : Nat} (h : payload.length ≤ B) :
    (lenField tag payload).length ≤ 20 + B := by
  have := (lenField_len_bounds tag payload).2; omega

private theorem bytesField_len_le (tag : Nat) (v : Bytes) :
    (bytesField tag v).length ≤ 20 + v.length := by
  unfold bytesField; split <;> [simp; exact (lenField_len_bounds tag v).2]

private theorem uint32Field_len_le (tag : Nat) (v : BitVec 32) :
    (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field; split
  · simp
  · have := (encodeKey_len_bounds tag .varint).2
    have := (encodeVarint_len_bounds (v.setWidth 64)).2
    simp only [List.length_append]; omega

private theorem uint64FieldX_len_le (tag : Nat) (v : BitVec 64) :
    (uint64FieldX tag v).length ≤ 20 := by
  unfold uint64FieldX; split
  · simp
  · have := (encodeKey_len_bounds tag .varint).2
    have := (encodeVarint_len_bounds v).2
    simp only [List.length_append]; omega

private theorem int32FieldX_len_le (tag : Nat) (v : BitVec 32) :
    (int32FieldX tag v).length ≤ 20 := by
  unfold int32FieldX; split
  · simp
  · have := (encodeKey_len_bounds tag .varint).2
    have := (encodeVarint_len_bounds (v.signExtend 64)).2
    simp only [List.length_append]; omega

private theorem optUint32FieldX_len_le (tag : Nat) (o : Option (BitVec 32)) :
    (optUint32FieldX tag o).length ≤ 20 := by
  cases o with
  | none => simp [optUint32FieldX]
  | some v =>
    have := (encodeKey_len_bounds tag .varint).2
    have := (encodeVarint_len_bounds (v.setWidth 64)).2
    simp only [optUint32FieldX, List.length_append]; omega

private theorem encodeBytesField_opt_len_le (tag : Nat) (o : Option Bytes) :
    (encodeBytesField tag o).length ≤ 20 + (o.getD []).length := by
  cases o with
  | none => simp [encodeBytesField]
  | some v =>
    have := (encodeKey_len_bounds tag .lengthDelimited).2
    have := (encodeVarint_len_bounds (BitVec.ofNat 64 v.length)).2
    simp only [encodeBytesField, Option.getD_some, List.length_append]; omega

private theorem encodeUint32Field_opt_len_le (tag : Nat) (o : Option (BitVec 32)) :
    (encodeUint32Field tag o).length ≤ 20 := by
  cases o with
  | none => simp [encodeUint32Field]
  | some v =>
    have := (encodeKey_len_bounds tag .varint).2
    have := (encodeVarint_len_bounds (BitVec.zeroExtend 64 v)).2
    simp only [encodeUint32Field, List.length_append]; omega

private theorem encodeBytes3_len_le (tag : Nat) (v : Bytes) :
    (RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold RecordCodecs.encodeProto3BytesField; split
  · simp
  · simpa using encodeBytesField_opt_len_le tag (some v)

private theorem encodeUint32_3_len_le (tag : Nat) (v : BitVec 32) :
    (RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold RecordCodecs.encodeProto3Uint32Field; split
  · simp
  · exact encodeUint32Field_opt_len_le tag (some v)

private theorem encodeFixed64_3_len_le (tag : Nat) (v : BitVec 64) :
    (RecordCodecs.encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold RecordCodecs.encodeProto3Fixed64Field; split
  · simp
  · have := (encodeKey_len_bounds tag .sixtyFourBit).2
    simp only [List.length_append, RecordCodecs.le64Bytes, List.length_cons,
      List.length_nil]; omega

private theorem djbKey_len (v : List.Vector (BitVec 8) 32) : (djbKey v).length = 33 := by
  simp [djbKey, List.Vector.toList_length]

private theorem kyberKey_len (v : List.Vector (BitVec 8) 1568) : (kyberKey v).length = 1569 := by
  simp [kyberKey, List.Vector.toList_length]

private theorem identityKeyPair_encode_len_lt (W : PEParams) (me : LocalIdentity) :
    (RecordCodecs.IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C me.idPriv).publicKey.bytes, me.idPriv.toList⟩).length < 2 ^ 31 := by
  unfold RecordCodecs.IdentityKeyPairStructure.encode
  have h1 := encodeBytes3_len_le 1 (djbKey (keyPairOf W.C me.idPriv).publicKey.bytes)
  have h2 := encodeBytes3_len_le 2 me.idPriv.toList
  rw [djbKey_len] at h1; rw [List.Vector.toList_length] at h2
  simp only [List.length_append]; omega

private theorem signedRecordBytes_len_lt (C : Crypto) (id : BitVec 32) (k : PqSignedKey) :
    (signedRecordBytes C id k).length < 2 ^ 31 := by
  unfold signedRecordBytes RecordCodecs.SignedPreKeyRecordStructure.encode
  have h1 := encodeUint32_3_len_le 1 id
  have h2 := encodeBytes3_len_le 2 (djbKey (keyPairOf C k.priv).publicKey.bytes)
  have h3 := encodeBytes3_len_le 3 k.priv.toList
  have h4 := encodeBytes3_len_le 4 k.sig.toList
  have h5 := encodeFixed64_3_len_le 5 k.timestamp
  rw [djbKey_len] at h2; rw [List.Vector.toList_length] at h3 h4
  simp only [List.length_append]; omega

private theorem oneTimeRecordBytes_len_lt (C : Crypto) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    (oneTimeRecordBytes C id sk).length < 2 ^ 31 := by
  unfold oneTimeRecordBytes RecordCodecs.PreKeyRecordStructure.encode
  have h1 := encodeUint32_3_len_le 1 id
  have h2 := encodeBytes3_len_le 2 (djbKey (keyPairOf C sk).publicKey.bytes)
  have h3 := encodeBytes3_len_le 3 sk.toList
  rw [djbKey_len] at h2; rw [List.Vector.toList_length] at h3
  simp only [List.length_append]; omega

private theorem kyberRecordBytes_len_lt (id : BitVec 32) (k : PqKyberKey) :
    (kyberRecordBytes id k).length < 2 ^ 31 := by
  unfold kyberRecordBytes RecordCodecs.SignedPreKeyRecordStructure.encode
  have h1 := encodeUint32_3_len_le 1 id
  have h2 := encodeBytes3_len_le 2 (kyberKey k.pub)
  have h3 := encodeBytes3_len_le 3 (0x08#8 :: k.sec.toList)
  have h4 := encodeBytes3_len_le 4 k.sig.toList
  have h5 := encodeFixed64_3_len_le 5 k.timestamp
  rw [kyberKey_len] at h2
  simp only [List.length_cons, List.Vector.toList_length] at h3
  rw [List.Vector.toList_length] at h4
  simp only [List.length_append]; omega

theorem encodeRecordX_ne_nil (E : Party → RecordExtras) (g : GhostState Bytes) :
    encodeRecordUnderExtras E g ≠ [] := by
  intro h
  have h1 := (lenField_len_bounds 1 (encStateUnderExtras (E g.party) g.session)).1
  change 1 ≤ (encodeRecordUnderExtras E g).length at h1
  rw [h] at h1; simp at h1

private theorem encChainKey_len_le (ck : ChainKey) : (encChainKey ck).length ≤ 72 := by
  unfold encChainKey
  have h1 := uint32Field_len_le 1 ck.index
  have h2 := bytesField_len_le 2 (HMAC.keyToBytes32 ck.key)
  have hk : (HMAC.keyToBytes32 ck.key).length = 32 := rfl
  rw [hk] at h2
  simp only [List.length_append]; omega

private theorem encReceiverChain_emptyMk_len_le (c : ReceiverChain) (hm : c.messageKeys = []) :
    (lenField 7 (encReceiverChain c)).length ≤ 165 := by
  refine lenField_le_of_le 7 (B := 145) ?_
  unfold encReceiverChain
  rw [hm]
  have h1 := bytesField_len_le 1 c.senderRatchetKey.serialize
  have hs : c.senderRatchetKey.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  rw [hs] at h1
  have h2 : (msgField 3 (c.chainKey.map encChainKey)).length ≤ 92 := by
    cases c.chainKey with
    | none => simp [msgField]
    | some ck =>
      simp only [Option.map_some, msgField]
      exact lenField_le_of_le 3 (encChainKey_len_le ck)
  simp only [List.map_nil, List.flatten_nil, List.append_nil, List.length_append]; omega

theorem encodeRecordX_length_lt_of_bounds (x : RecordExtras) (g : GhostState Bytes)
    (hpq : g.session.pqRatchetState.length < 2 ^ 28)
    (hrc : g.session.receiverChains.length ≤ 2)
    (hmk : ∀ c ∈ g.session.receiverChains, c.messageKeys = [])
    (habk : x.aliceBaseKey.length ≤ 64)
    (hkyb : ∀ k, x.kyber = some k → k.ciphertext.length ≤ 1600) :
    (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := by
  have hbody : (encStateUnderExtras x g.session).length ≤ 2 ^ 28 + 3000 := by
    unfold encStateUnderExtras
    have h1 := uint32Field_len_le 1 g.session.sessionVersion
    have h2 := bytesField_len_le 2 g.session.localIdentity.serialize
    have hlid : g.session.localIdentity.serialize.length = 33 := by
      simp [IdentityKey.serialize, PublicKey.serialize, List.Vector.toList_length]
    rw [hlid] at h2
    have h3 : (bytesField 3 ((g.session.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤
        53 := by
      cases g.session.remoteIdentity with
      | none =>
        have := bytesField_len_le 3 []
        simp only [Option.map_none, Option.getD_none, List.length_nil] at this ⊢; omega
      | some rid =>
        have h := bytesField_len_le 3 rid.serialize
        have hrid : rid.serialize.length = 33 := by
          simp [IdentityKey.serialize, PublicKey.serialize, List.Vector.toList_length]
        rw [hrid] at h; simpa using h
    have h4 := bytesField_len_le 4 (HMAC.keyToBytes32 g.session.rootKey)
    have hrk : (HMAC.keyToBytes32 g.session.rootKey).length = 32 := rfl
    rw [hrk] at h4
    have h5 := uint32Field_len_le 5 g.session.previousCounter
    have h6 : (msgField 6 (g.session.senderChain.map encSenderChain)).length ≤ 217 := by
      cases g.session.senderChain with
      | none => simp [msgField]
      | some sc =>
        simp only [Option.map_some, msgField]
        refine lenField_le_of_le 6 (B := 197) ?_
        unfold encSenderChain msgField
        have hs1 := bytesField_len_le 1 sc.ratchetKey.publicKey.serialize
        have hser : sc.ratchetKey.publicKey.serialize.length = 33 := by
          simp [PublicKey.serialize, List.Vector.toList_length]
        rw [hser] at hs1
        have hs2 := bytesField_len_le 2 sc.ratchetKey.privateKey.bytes.toList
        rw [List.Vector.toList_length] at hs2
        have hs3 := lenField_le_of_le 3 (encChainKey_len_le sc.chainKey)
        simp only [List.length_append]; omega
    have h7 : ((g.session.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten).length ≤
        330 := by
      rcases hrc_list : g.session.receiverChains with _ | ⟨c1, _ | ⟨c2, _ | ⟨_, _⟩⟩⟩
      · simp
      · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
        have := encReceiverChain_emptyMk_len_le c1 (hmk c1 (by simp [hrc_list])); omega
      · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.length_append]
        have := encReceiverChain_emptyMk_len_le c1 (hmk c1 (by simp [hrc_list]))
        have := encReceiverChain_emptyMk_len_le c2 (hmk c2 (by simp [hrc_list])); omega
      · rw [hrc_list] at hrc; simp at hrc
    have h9 : (msgField 9 (if g.session.pendingPreKey then some (encPendingPreKeyX x.pending)
        else none)).length ≤ 133 := by
      split
      · simp only [msgField]
        refine lenField_le_of_le 9 (B := 113) ?_
        unfold encPendingPreKeyX
        have hp1 := optUint32FieldX_len_le 1 x.pending.preKeyId
        have hp2 := bytesField_len_le 2 x.pending.baseKey.serialize
        have hbk : x.pending.baseKey.serialize.length = 33 := by
          simp [PublicKey.serialize, List.Vector.toList_length]
        rw [hbk] at hp2
        have hp3 := int32FieldX_len_le 3 x.pending.signedPreKeyId
        have hp4 := uint64FieldX_len_le 4 x.pending.timestamp
        simp only [List.length_append]; omega
      · simp [msgField]
    have h10 := uint32Field_len_le 10 x.remoteRegistrationId
    have h11 := uint32Field_len_le 11 x.localRegistrationId
    have h13 := bytesField_len_le 13 x.aliceBaseKey
    have h14 : (msgField 14 (if g.session.pendingPreKey then x.kyber.map encPendingKyberX
        else none)).length ≤ 1660 := by
      split
      · cases hxk : x.kyber with
        | none => simp [msgField]
        | some k =>
          simp only [Option.map_some, msgField]
          refine lenField_le_of_le 14 (B := 1640) ?_
          unfold encPendingKyberX
          have hk1 := uint32Field_len_le 1 k.preKeyId
          have hk2 := bytesField_len_le 2 k.ciphertext
          have hkc := hkyb k hxk
          simp only [List.length_append]; omega
      · simp [msgField]
    have h15 := bytesField_len_le 15 g.session.pqRatchetState
    simp only [List.length_append]; omega
  have houter := lenField_le_of_le 1 hbody
  change (encodeRecordUnderExtras (fun _ => x) g).length ≤ _ at houter
  omega

theorem wfPq_aliceDir0 : PqxdhPartyInSpecDomain W0 aliceDir0 := by
  have hcap := (Computational.Proofs.LibsignalCli.CliCapsCompleteness.honest_party_and_bundle_files_le_fileCap
    (W := W0) (st := aliceDir0) (b := bundleB0) (dir := bundleDir)
    (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)).2
  refine ⟨by simp [aliceDir0], fun f hf => ?_, by decide, by decide, by decide, by decide⟩
  have hle := hcap f.1 f.2 hf
  have hlt : fileCapBytes < 2 ^ 31 := by decide
  exact ⟨Nat.lt_of_le_of_lt hle hlt, fun _ => hle⟩

theorem wfPq_bobDir0 : PqxdhPartyInSpecDomain W0 bobDir0 := by
  have hcap := (Computational.Proofs.LibsignalCli.CliCapsCompleteness.honest_party_and_bundle_files_le_fileCap
    (W := W0) (st := bobDir0) (b := bundleB0) (dir := bundleDir) (fun _ _ h => nomatch h)
    (by intro i k seen h; simp [bobDir0] at h; rcases h with ⟨-, -, rfl⟩; simp)).2
  refine ⟨by simp [bobDir0], fun f hf => ?_, by decide, by decide, by decide, by decide⟩
  have hle := hcap f.1 f.2 hf
  have hlt : fileCapBytes < 2 ^ 31 := by decide
  exact ⟨Nat.lt_of_le_of_lt hle hlt, fun _ => hle⟩

private theorem w0_kemEncaps (pk : List.Vector (BitVec 8) 1568)
    (coins : List.Vector (BitVec 8) 32) :
    (modelPrims X0 W0).kemEncaps (vecU8 pk) (vecU8 coins) =
      some (vecU8 (W0.Q.encaps pk coins).2, vecU8 (W0.Q.encaps pk coins).1) := by
  dsimp only [modelPrims, blockLevelPrims]
  have hpk : ((vecU8 pk).length == SignalPqxdh.kyberPkLen) = true := by
    rw [vecU8_length]; rfl
  rw [ite_eq_left hpk]
  simp only [SignalPqxdh.kyberPkLen, u8Vec_vecU8]

private theorem w0_kemDecaps_encaps (sk : List.Vector (BitVec 8) 3168)
    (pk : List.Vector (BitVec 8) 1568) (coins : List.Vector (BitVec 8) 32) :
    (modelPrims X0 W0).kemDecaps (vecU8 sk)
      (vecU8 (u8Vec 1568 (vecU8 (W0.Q.encaps pk coins).1))) =
      some (vecU8 (W0.Q.encaps pk coins).2) := by
  dsimp only [modelPrims, blockLevelPrims]
  have hct : ((vecU8 (u8Vec 1568 (vecU8 (W0.Q.encaps pk coins).1))).length ==
      SignalPqxdh.kyberCtLen) = true := by
    rw [vecU8_length]; rfl
  rw [ite_eq_left hct]
  simp only [SignalPqxdh.kyberCtLen, u8Vec_vecU8, q0_kyber_roundtrip]

theorem initiateKeys_acceptKeys_W0 :
    ∃ dk hdr,
      SignalPqxdh.Model.initiateKeys (modelPrims X0 W0)
        (initiateInput W0 aliceMe bundleB0 tape0) = some (dk, hdr) ∧
      hdr.ekAPk.length = 32 ∧
      hdr.kemCt.length = 1568 ∧
      ∀ (innerBytes : Bytes),
        let m : PreKeyMessageFields :=
          { regId := aliceMe.regId
            opkId := some opkId0
            spkId := spkId0
            kpkId := kpkId0
            kyberCt := u8Vec 1568 hdr.kemCt
            baseKey := u8Vec 32 hdr.ekAPk
            idPub := (keyPairOf W0.C aliceMe.idPriv).publicKey.bytes
            inner := innerBytes }
        SignalPqxdh.Model.acceptKeys (modelPrims X0 W0) (acceptInput W0 bobMe keysB0 m) =
          some dk := by
  obtain ⟨i, hi_def⟩ : ∃ x, initiateInput W0 aliceMe bundleB0 tape0 = x := ⟨_, rfl⟩
  obtain ⟨coinsK, hcoinsK⟩ : ∃ x, initiateKemCoins tape0 = x := ⟨_, rfl⟩
  obtain ⟨ss0, hss0⟩ : ∃ x, vecU8 (W0.Q.encaps kpkPub0 coinsK).2 = x := ⟨_, rfl⟩
  obtain ⟨kemCt0, hkemCt0⟩ : ∃ x, vecU8 (W0.Q.encaps kpkPub0 coinsK).1 = x := ⟨_, rfl⟩
  obtain ⟨dh0, hdh0⟩ : ∃ x, vecU8 ⟨1#8 :: List.replicate 31 0#8, rfl⟩ = x := ⟨_, rfl⟩
  obtain ⟨dk0, hdk0⟩ :
      ∃ x, (modelPrims X0 W0).hkdfDerive96
        (SignalPqxdh.buildSecrets dh0 dh0 dh0 (some dh0) ss0) = x := ⟨_, rfl⟩
  obtain ⟨ekAPk0, hekAPk0⟩ : ∃ x, (modelPrims X0 W0).x25519Base i.ekASk = x := ⟨_, rfl⟩
  have htp : i.trustedPeer = true := by rw [← hi_def]; rfl
  have hpkB : i.bundle.ikB.length = 32 := by
    have h : i.bundle.ikB = vecU8 bundleB0.idPub := by rw [← hi_def]; rfl
    rw [h]; exact vecU8_length _
  have hsig1 : (modelPrims X0 W0).sigVerify i.bundle.ikB (SignalPqxdh.encodeEC i.bundle.spkB)
      i.bundle.spkSig = true := by
    have hspk : i.bundle.spkSig = List.replicate 64 0 := by
      have h : i.bundle.spkSig = vecU8 sigZero64 := by rw [← hi_def]; rfl
      rw [h]; exact vecU8_replicate_zero 64
    rw [hspk]; exact w0_sigVerify_zero _ _ hpkB
  have hsig2 : (modelPrims X0 W0).sigVerify i.bundle.ikB (SignalPqxdh.encodeKEM i.bundle.pqspkB)
      i.bundle.pqspkSig = true := by
    have hpq : i.bundle.pqspkSig = List.replicate 64 0 := by
      have h : i.bundle.pqspkSig = vecU8 sigZero64 := by rw [← hi_def]; rfl
      rw [h]; exact vecU8_replicate_zero 64
    rw [hpq]; exact w0_sigVerify_zero _ _ hpkB
  have hEncaps : (modelPrims X0 W0).kemEncaps i.bundle.pqspkB i.kemCoins = some (ss0, kemCt0) := by
    have hpqB : i.bundle.pqspkB = vecU8 kpkPub0 := by rw [← hi_def]; rfl
    have hkc : i.kemCoins = vecU8 coinsK := by rw [← hi_def, ← hcoinsK]; rfl
    rw [hpqB, hkc, ← hss0, ← hkemCt0]
    exact w0_kemEncaps kpkPub0 coinsK
  have hdh : ∀ a b, (modelPrims X0 W0).x25519 a b = dh0 := fun _ _ => hdh0
  have hdh_nz : (dh0 != List.replicate 32 0) = true := by rw [← hdh0]; decide
  have hopk_i : i.bundle.opkB?.map (fun (_, opkPk) => (modelPrims X0 W0).x25519 i.ekASk opkPk) =
      some dh0 := by
    have hopkB : i.bundle.opkB? = some (20, vecU8 (keyPairOf W0.C opkPriv0).publicKey.bytes) := by
      rw [← hi_def]; rfl
    rw [hopkB]; dsimp only [Option.map]; rw [hdh]
  have hdh4_nz : SignalPqxdh.dhOptNonZero (some dh0) = true := hdh_nz
  let hdr0 : SignalPqxdh.HandshakeHdr :=
    { ikAPk := i.ikAPk
      ekAPk := ekAPk0
      spkId := i.bundle.spkId
      opkId? := i.bundle.opkB?.map Prod.fst
      pqspkId := i.bundle.pqspkId
      kemCt := kemCt0 }
  have hInit : SignalPqxdh.Model.initiateKeys (modelPrims X0 W0) i = some (dk0, hdr0) := by
    unfold SignalPqxdh.Model.initiateKeys
    rw [htp, hsig1, hsig2, hEncaps, hopk_i, hekAPk0]
    dsimp only [bind, Option.bind, pure, _root_.guard]
    simp only [hdh, hdh_nz, hdh4_nz, ↓reduceIte, hdk0]
    rfl
  have hek_len : hdr0.ekAPk.length = 32 := by
    dsimp only [hdr0]
    rw [← hekAPk0]
    exact vecU8_length _
  have hct_len : hdr0.kemCt.length = 1568 := by
    dsimp only [hdr0]
    rw [← hkemCt0]
    exact vecU8_length _
  refine ⟨dk0, hdr0, hi_def ▸ hInit, hek_len, hct_len, fun innerBytes => ?_⟩
  intro m
  obtain ⟨acc, hacc_def⟩ : ∃ x, acceptInput W0 bobMe keysB0 m = x := ⟨_, rfl⟩
  have htpA : acc.trustedPeer = true := by rw [← hacc_def]; rfl
  have hrepA : acc.replayOk = true := by rw [← hacc_def]; rfl
  have hik_len : (acc.hdr.ikAPk.length == 32) = true := by
    have h : acc.hdr.ikAPk = vecU8 (keyPairOf W0.C aliceMe.idPriv).publicKey.bytes := by
      rw [← hacc_def]; rfl
    rw [h, vecU8_length]; rfl
  have hekA_len : (acc.hdr.ekAPk.length == 32) = true := by
    have h : acc.hdr.ekAPk = vecU8 (u8Vec 32 ekAPk0) := by rw [← hacc_def]; rfl
    rw [h, vecU8_length]; rfl
  have hkem_len : (acc.hdr.kemCt.length == SignalPqxdh.kyberCtLen) = true := by
    have h : acc.hdr.kemCt = vecU8 (u8Vec 1568 kemCt0) := by rw [← hacc_def]; rfl
    rw [h, vecU8_length]; rfl
  have hcanon : (modelPrims X0 W0).isCanonical acc.hdr.ekAPk = true := by
    have h1 : acc.hdr.ekAPk = vecU8 (u8Vec 32 ekAPk0) := by rw [← hacc_def]; rfl
    have h2 : ekAPk0 = vecU8 (W0.C.pubKey (Ratchet.clampScalar (u8Vec 32 i.ekASk))) :=
      hekAPk0.symm
    rw [h1, h2, u8Vec_vecU8]
    exact w0_isCanonical _
  have hopkId : acc.hdr.opkId? = some 20 := by rw [← hacc_def]; rfl
  obtain ⟨opkSk0, hopkSk⟩ : ∃ s, acc.opkBSk? = some s := by rw [← hacc_def]; exact ⟨_, rfl⟩
  have hDecaps : (modelPrims X0 W0).kemDecaps acc.pqspkBSk acc.hdr.kemCt = some ss0 := by
    have h1 : acc.pqspkBSk = vecU8 kpkSec0 := by rw [← hacc_def]; rfl
    have h2 : acc.hdr.kemCt = vecU8 (u8Vec 1568 kemCt0) := by rw [← hacc_def]; rfl
    rw [h1, h2, ← hkemCt0, ← hss0]
    exact w0_kemDecaps_encaps kpkSec0 kpkPub0 coinsK
  rw [hacc_def]
  unfold SignalPqxdh.Model.acceptKeys
  rw [htpA, hrepA, hik_len, hekA_len, hkem_len, hcanon, hopkId, hopkSk, hDecaps]
  dsimp only [bind, Option.bind, pure, _root_.guard]
  simp only [hdh, hdh_nz, hdh4_nz, ↓reduceIte, hdk0]

private theorem aesCbcDecrypt_w0 (key : CBC.AesKey) (iv : CBC.Block) (pt : Bytes) :
    aesCbcDecrypt W0.C.D key iv (aesCbcEncrypt W0.C.E key iv pt) = some pt :=
  CryptoGames.LibsignalSM.Proofs.Correctness.aesCbcDecrypt_aesCbcEncrypt c0_aes_roundtrip key iv pt

private theorem aesCbcDecrypt_w0_twoBytes (key : CBC.AesKey) (iv : CBC.Block)
    (b0 b1 : BitVec 8) :
    aesCbcDecrypt W0.C.D key iv (aesCbcEncrypt W0.C.E key iv [b0, b1]) = some [b0, b1] :=
  aesCbcDecrypt_w0 key iv [b0, b1]

section EndToEnd

open CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.SignalSession.FirstMessage

def pt1 : Bytes := [0x41#8, 0x31#8]
def pt2 : Bytes := [0x42#8, 0x32#8]

/-- All-ones receive coins: clamping sets byte `0` to `0xf8 ≠ 0x00`, so Bob's fresh ratchet public
key differs from `spkPriv0`'s public key and Alice's receive takes `dhRatchetStep`. -/
def rcB0 : BitVec 256 := BitVec.allOnes 256
def rcA0 : BitVec 256 := 0#256

private theorem foldl_dir_entries_of_not_mem (fs : Arm64.FsState) (prefs : List Arm64.FsPath)
    (target : Arm64.FsPath) (h : target ∉ prefs) :
    (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries target =
      fs.entries target := by
  induction prefs generalizing fs with
  | nil => rfl
  | cons pref rest ih =>
    have hne : target ≠ pref := fun heq => h (heq ▸ List.mem_cons_self ..)
    have hrest : target ∉ rest := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [List.foldl_cons]
    rw [ih _ hrest]
    simp [Arm64.FsState.setEntry, hne]

private theorem filesFold_entries_of_disjoint (suf : List (String × Bytes)) (fs : Arm64.FsState)
    (target : Arm64.FsPath)
    (h : ∀ q ∈ suf.map Prod.fst,
      target ≠ Arm64.normalizePath q ∧
        target ∉ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath q)).dropLast) :
    (filesFold suf fs).entries target = fs.entries target := by
  induction suf generalizing fs with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨q, b⟩
    have hq := h q (List.mem_cons_self ..)
    have hrest : ∀ q' ∈ rest.map Prod.fst,
        target ≠ Arm64.normalizePath q' ∧
          target ∉ (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath q')).dropLast :=
      fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    simp only [filesFold, List.foldl_cons]
    change (filesFold rest _).entries target = fs.entries target
    rw [ih _ hrest]
    simp only [Arm64.FsState.setFile, Arm64.FsState.setEntry, beq_eq_false_iff_ne.mpr hq.1,
      Bool.false_eq_true, ↓reduceIte]
    exact foldl_dir_entries_of_not_mem fs _ target hq.2

private theorem filesOf_lookup (pre suf : List (String × Bytes)) (p : String) (bs : Bytes)
    (hp_stdio : Arm64.normalizePath p ∉ stdioPaths.map Arm64.normalizePath)
    (hp_ne : (Arm64.normalizePath p).isEmpty = false)
    (hsuf : ∀ q ∈ suf.map Prod.fst,
      Arm64.normalizePath p ≠ Arm64.normalizePath q ∧
        Arm64.normalizePath p ∉
          (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath q)).dropLast) :
    filesOf (pre ++ (p, bs) :: suf) p = some bs := by
  unfold filesOf fsView
  simp only [hp_stdio, ↓reduceIte, Arm64.FsState.files, Arm64.FsState.getEntry, hp_ne,
    Bool.false_eq_true]
  rw [initFsState_entries { files := pre ++ (p, bs) :: suf } (Arm64.normalizePath p) hp_stdio]
  have hsplit : filesFold (pre ++ (p, bs) :: suf) (dirsFold [] {}) =
      filesFold suf (filesFold [(p, bs)] (filesFold pre (dirsFold [] {}))) := by
    simp only [filesFold, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hsplit, filesFold_entries_of_disjoint suf _ _ hsuf]
  simp [filesFold, Arm64.FsState.setFile, Arm64.FsState.setEntry]

private theorem list_reassoc_alice {α : Type} (pre a b : List α) (x : α) :
    pre ++ (a ++ b ++ [x]) = (pre ++ a ++ b) ++ x :: [] := by
  simp [List.append_assoc]

private theorem list_reassoc_bob {α : Type} (pre a b : List α) (x : α) (c d e : List α) :
    pre ++ (a ++ b ++ [x] ++ c ++ d ++ e) = (pre ++ a ++ b) ++ x :: (c ++ d ++ e) := by
  simp [List.append_assoc]

private theorem filesOf_alice_session (pre : List (String × Bytes)) (st : PqParty)
    (x : RecordExtras) (g : GhostState Bytes)
    (hp : st.party = .A) (hsess : st.session = some (x, g))
    (hsig : st.signed = []) (hot : st.oneTime = [])
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort = []) :
    filesOf (pre ++ encodeDir W0 st) (sessionFile (partyAddress .B)) =
      some (encodeRecordUnderExtras (fun _ => x) g) := by
  unfold encodeDir
  rw [hp, hsess, hsig, hot, hkot, hklr]
  simp only [Party.other, List.map_nil, List.flatten_nil, List.append_nil]
  rw [list_reassoc_alice]
  exact filesOf_lookup _ [] (sessionFile (partyAddress .B)) _ (by decide +kernel) (by decide +kernel)
    (by simp)

private theorem filesOf_bob_session (pre : List (String × Bytes)) (st : PqParty)
    (x : RecordExtras) (g : GhostState Bytes)
    (sk : PqSignedKey) (ot : Option (List.Vector (BitVec 8) 32))
    (kk : PqKyberKey) (seen : List (BitVec 32 × List.Vector (BitVec 8) 32))
    (hp : st.party = .B) (hsess : st.session = some (x, g))
    (hsig : st.signed = [(spkId0, sk)]) (hot : st.oneTime = [(opkId0, ot)])
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort = [(kpkId0, kk, seen)]) :
    filesOf (pre ++ encodeDir W0 st) (sessionFile (partyAddress .A)) =
      some (encodeRecordUnderExtras (fun _ => x) g) := by
  unfold encodeDir
  rw [hp, hsess, hsig, hot, hkot, hklr]
  simp only [Party.other, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  rw [list_reassoc_bob]
  apply filesOf_lookup
  · decide +kernel
  · decide +kernel
  · dsimp only [List.cons_append, List.nil_append, List.map, Prod.fst]
    decide +kernel

private theorem toList_ne_zero32 {v : List.Vector (BitVec 8) 32}
    (h : v ≠ List.Vector.replicate 32 0#8) :
    v.toList ≠ List.replicate 32 0#8 := by
  intro heq
  apply h
  apply List.Vector.eq
  rw [heq]
  simp [List.Vector.replicate, List.Vector.toList]

private theorem rootCreateChain_w0 (rk : RootKey) (a b : List.Vector (BitVec 8) 32) :
    rootCreateChain W0.C rk ⟨W0.C.pubKey (Ratchet.clampScalar b)⟩ ⟨Ratchet.clampScalar a⟩ =
      .ok (let p := Ratchet.rootKdf W0.C.F rk
             (W0.C.X (Ratchet.clampScalar a) (W0.C.pubKey (Ratchet.clampScalar b))).toList
           (p.1, ⟨p.2, 0#32⟩)) := by
  dsimp only [rootCreateChain, Ratchet.createChain]
  rw [clampScalar_idem]
  have hne := toList_ne_zero32 (c0_dh_ne_zero a b)
  simp only [hne, ↓reduceIte]
  rfl

private theorem spkPub_beq_ephB_false :
    ((⟨(keyPairOf W0.C spkPriv0).publicKey.bytes⟩ : PublicKey) ==
      (KeyPair.generate W0.C rcB0).publicKey) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq
  have h0 := congrArg (fun k : PublicKey => k.bytes.toList.head?) heq
  have hl : (⟨(keyPairOf W0.C spkPriv0).publicKey.bytes⟩ : PublicKey).bytes.toList.head? =
      some ((Ratchet.clampScalar spkPriv0).get 0) := rfl
  have hr : (KeyPair.generate W0.C rcB0).publicKey.bytes.toList.head? =
      some ((Ratchet.clampScalar (Ratchet.keyToBytesVec32 rcB0)).get 0) := rfl
  rw [hl, hr] at h0
  injection h0 with h0
  rw [clampScalar_get, clampScalar_get] at h0
  simp only [↓reduceIte, keyVec_get, spkPriv0, rcB0] at h0
  have hs : (List.Vector.replicate 32 0#8).get 0 = 0#8 := rfl
  rw [hs] at h0
  revert h0
  decide

private theorem aesCbcEncrypt_len_le (E : CBC.AesKey → CBC.Block → CBC.Block)
    (key : CBC.AesKey) (iv : CBC.Block) (pt : Bytes) :
    (aesCbcEncrypt E key iv pt).length ≤ pt.length + 16 := by
  have hlen : (aesCbcEncrypt E key iv pt).length = 16 * CBC.nBlocks pt.length := by
    dsimp only [aesCbcEncrypt, CBC.cbcPkcs7EncryptOnly, CipherScheme.enc]
    rw [List.length_flatMap]
    have h16 : ∀ b : CBC.Block, (CBC.blockToBytesLE b).length = 16 := fun _ => by
      simp [CBC.blockToBytesLE]
    simp [h16, List.sum_replicate, Nat.mul_comm]
  rw [hlen, CBC.nBlocks]
  omega

private theorem addrsE_len {uuidParse : LibsignalTripleRatchetRepr.UuidParser} {s r : Party}
    {a : Bytes} (h : serializedPartyAddresses uuidParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : LibsignalTripleRatchetRepr.serviceIdParse uuidParse
      (LibsignalTripleRatchetRepr.utf8 (partyAddressName s)) with
  | none => simp [hs, bind] at h
  | some sidS =>
    cases hr : LibsignalTripleRatchetRepr.serviceIdParse uuidParse
        (LibsignalTripleRatchetRepr.utf8 (partyAddressName r)) with
    | none => simp [hs, hr, bind] at h
    | some sidR =>
      simp only [hs, hr, bind, Option.bind, pure] at h
      injection h with h
      subst h
      simp [LibsignalTripleRatchetRepr.addrBytes, List.Vector.toList_length]

private theorem addrsOpt_ok_bound (addrs : Option Bytes)
    (h : addrs = none ∨ ∃ s r, addrs = serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse s r) :
    ∀ a, addrs = some a → a.length ≤ 36 := by
  intro a ha
  rcases h with rfl | ⟨s, r, rfl⟩
  · cases ha
  · exact Nat.le_of_eq (addrsE_len ha)

private theorem signalWireShort_of_bounds (rk : PublicKey) (addrs : Option Bytes)
    (haddrs : ∀ a, addrs = some a → a.length ≤ 36)
    (E : CBC.AesKey → CBC.Block → CBC.Block) (key : CBC.AesKey) (iv : CBC.Block)
    (pt pqMsg : Bytes) (hpt : pt.length ≤ 64) (hpq : pqMsg.length ≤ 64) :
    SignalWireShort ⟨currentVersion, rk, 0#32, 0#32, pqMsg, addrs⟩
      (aesCbcEncrypt E key iv pt) := by
  refine ⟨rfl, by unfold rustLenBound; dsimp only; omega, ?_, ?_⟩
  · intro a ha
    have := haddrs a ha
    unfold rustLenBound; omega
  · have := aesCbcEncrypt_len_le E key iv pt
    unfold rustLenBound; omega

private theorem signalMessage_new_len_le (F : ShaCompress) (macKey : BitVec 256)
    (addrs : Option Bytes) (haddrs : ∀ a, addrs = some a → a.length ≤ 36)
    (rk : PublicKey) (cnt prevCnt : BitVec 32)
    (E : CBC.AesKey → CBC.Block → CBC.Block) (key : CBC.AesKey) (iv : CBC.Block)
    (pt : Bytes) (sId rId : IdentityKey) (pqMsg : Bytes)
    (hpt : pt.length ≤ 64) (hpq : pqMsg.length ≤ 64) :
    (SignalMessage.new F protoSignalCodec currentVersion macKey addrs rk cnt prevCnt
      (aesCbcEncrypt E key iv pt) sId rId pqMsg).serialized.length ≤ 350 := by
  dsimp only [SignalMessage.new]
  rw [List.length_append, computeMac_length]
  dsimp only [serializeContent, protoSignalCodec, encode]
  have h1 := encodeBytesField_opt_len_le 1 (some rk.serialize)
  have hrk : rk.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  simp only [Option.getD_some, hrk] at h1
  have h2 := encodeUint32Field_opt_len_le 2 (some cnt)
  have h3 := encodeUint32Field_opt_len_le 3 (some prevCnt)
  have h4 := encodeBytesField_opt_len_le 4 (some (aesCbcEncrypt E key iv pt))
  have hct := aesCbcEncrypt_len_le E key iv pt
  simp only [Option.getD_some] at h4
  have h5 := encodeBytesField_opt_len_le 5 (if pqMsg.isEmpty then none else some pqMsg)
  have h5' : ((if pqMsg.isEmpty then none else some pqMsg).getD []).length ≤ 64 := by
    split <;> simp_all
  have h6 := encodeBytesField_opt_len_le 6 addrs
  have h6' : (addrs.getD []).length ≤ 36 := by
    cases h : addrs with
    | none => simp
    | some a => simpa using haddrs a h
  simp only [List.length_cons, List.length_append, macLength]
  omega

private theorem addrsOk_refl (a : Option Bytes) : LibsignalAead.addressCheckPasses a a = true := by
  cases a <;> simp [LibsignalAead.addressCheckPasses]

private theorem addrsOk_none (e : Option Bytes) : LibsignalAead.addressCheckPasses none e = true := by
  simp [LibsignalAead.addressCheckPasses]

private theorem hlr_of_nil {p : PqParty} (h : p.kyberLastResort = []) :
    lastResortUses p < 2 ^ 25 := by
  unfold lastResortUses; rw [h]; decide

private theorem session_rec_bound {s : Option (RecordExtras × GhostState Bytes)}
    {x0 : RecordExtras} {g0 : GhostState Bytes}
    (hs0 : s = some (x0, g0))
    (hb : (encodeRecordUnderExtras (fun _ => x0) g0).length < 2 ^ 31) :
    ∀ x g, s = some (x, g) → (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := by
  rintro x g hs
  rw [hs0] at hs
  cases hs
  exact hb

private theorem rc1_bounds {g : GhostState Bytes} {pk : PublicKey} {ck : Option ChainKey}
    (h : g.session.receiverChains = [⟨pk, ck, []⟩]) :
    g.session.receiverChains.length ≤ 2 ∧
      ∀ c ∈ g.session.receiverChains, c.messageKeys = [] := by
  rw [h]; simp

private theorem rc2_bounds {g : GhostState Bytes} {pk1 pk2 : PublicKey}
    {ck1 ck2 : Option ChainKey}
    (h : g.session.receiverChains = [⟨pk1, ck1, []⟩, ⟨pk2, ck2, []⟩]) :
    g.session.receiverChains.length ≤ 2 ∧
      ∀ c ∈ g.session.receiverChains, c.messageKeys = [] := by
  rw [h]; simp

set_option maxRecDepth 8192 in
/-- Executes the 5-step PQXDH and SPQR-V1 model conversation on `(X0, W0)` from
`(aliceDir0, bobDir0)` and preserves `PqxdhPartyInSpecDomain W0` at every step. -/
theorem pqConversation_5steps :
    ∃ (aliceDir1 aliceDir2 aliceDir3 bobDir1 bobDir2 : PqParty)
      (m1 : PreKeyMessageFields) (c2 : Bytes)
      (xA xB : RecordExtras) (gA0 gA1 gA2 gB1 gB2 : GhostState Bytes),
      PqxdhPartyInSpecDomain W0 aliceDir0 ∧ PqxdhPartyInSpecDomain W0 bobDir0 ∧
      PqxdhPartyInSpecDomain W0 aliceDir1 ∧ PqxdhPartyInSpecDomain W0 aliceDir2 ∧ PqxdhPartyInSpecDomain W0 aliceDir3 ∧
      PqxdhPartyInSpecDomain W0 bobDir1 ∧ PqxdhPartyInSpecDomain W0 bobDir2 ∧
      aliceDir1.session = some (xA, gA0) ∧ gA0.session.pqRatchetState ≠ [] ∧
      aliceDir2.session = some (xA, gA1) ∧ gA1.session.pqRatchetState ≠ [] ∧
      bobDir1.session = some (xB, gB1) ∧ gB1.session.pqRatchetState ≠ [] ∧
      bobDir2.session = some (xB, gB2) ∧ gB2.session.pqRatchetState ≠ [] ∧
      aliceDir3.session = some (xA, gA2) ∧ gA2.session.pqRatchetState ≠ [] ∧
      gA2.session.pendingPreKey = false ∧
      bobDir1.oneTime = [(opkId0, none)] ∧
      bobDir1.kyberLastResort = [(kpkId0, kpkRec0, [(spkId0, m1.baseKey)])] ∧
      m1.inner.length + 2048 < 2 ^ 32 ∧
      c2.length < 2 ^ 32 ∧
      pqInitModel X0 W0 aliceDir0 bundleB0 tape0 = some (some (aliceDir1, [])) ∧
      pqSendModel W0 aliceDir1 pt1 coins0.toList =
        some (some (aliceDir2, wirePrekey :: m1.bytes)) ∧
      pqRecvPrekeyModel X0 W0 bobDir0 m1 rcB0 = some (some (bobDir1, pt1)) ∧
      pqSendModel W0 bobDir1 pt2 coins0.toList =
        some (some (bobDir2, wireWhisper :: c2)) ∧
      c2 = ((pqxdhSessionParams W0).send gB1 pt2 coins0.toList).2 ∧
      pqRecvWhisperModel W0 aliceDir2 c2 rcA0 = some (some (aliceDir3, pt2)) ∧
      (∀ pre, filesOf (pre ++ encodeDir W0 aliceDir1) (sessionFile (partyAddress .B)) =
        some (encodeRecordUnderExtras (fun _ => xA) gA0)) ∧
      (∀ pre, filesOf (pre ++ encodeDir W0 aliceDir2) (sessionFile (partyAddress .B)) =
        some (encodeRecordUnderExtras (fun _ => xA) gA1)) ∧
      (∀ pre, filesOf (pre ++ encodeDir W0 bobDir1) (sessionFile (partyAddress .A)) =
        some (encodeRecordUnderExtras (fun _ => xB) gB1)) ∧
      (∀ pre, filesOf (pre ++ encodeDir W0 bobDir2) (sessionFile (partyAddress .A)) =
        some (encodeRecordUnderExtras (fun _ => xB) gB2)) ∧
      (∀ pre, filesOf (pre ++ encodeDir W0 aliceDir3) (sessionFile (partyAddress .B)) =
        some (encodeRecordUnderExtras (fun _ => xA) gA2)) := by
  obtain ⟨dk0, hdr0, hIK, hek_len, hct_len, hAccAll⟩ := initiateKeys_acceptKeys_W0
  obtain ⟨rk0, hrk0⟩ : ∃ x, HKDF.bytesToKey32 (ofU8 dk0.rootKey) = x := ⟨_, rfl⟩
  obtain ⟨ck0, hck0⟩ : ∃ x, HKDF.bytesToKey32 (ofU8 dk0.chainKey) = x := ⟨_, rfl⟩
  obtain ⟨pqr0, hpqr0⟩ : ∃ x, HKDF.bytesToKey32 (ofU8 dk0.pqrKey) = x := ⟨_, rfl⟩
  obtain ⟨coinsA, hcoinsA⟩ :
      ∃ x, HKDF.bytesToKey32 ((tape0.toList.drop 160).take 32) = x := ⟨_, rfl⟩
  obtain ⟨stA0, stB0, stA1, salt1, pqMsg1, stB1, stB2, salt2, pqMsg2, stA2,
    hstA0, hstB0, hstA0_ne, -, -, -,
    hSpqrSend1, hSpqrRecv1, hSpqrSend2, hSpqrRecv2,
    hstA1_ne, -, hstB1_ne, -, hstB2_ne, -, hstA2_ne, -,
    hpq1_le, hpq2_le⟩ :=
    SpqrBounds.spqrTwoMsg_roundtrip_exists W0.C.F W0.Q.K rfl (pqxdhSpqrSession W0) rfl coins0.toList rfl pqr0
  -- Bind ratchet keys opaquely so SHA-256 and HKDF do not unfold.
  obtain ⟨ephA, hephA⟩ : ∃ x, KeyPair.generate W0.C coinsA = x := ⟨_, rfl⟩
  obtain ⟨ephB, hephB⟩ : ∃ x, KeyPair.generate W0.C rcB0 = x := ⟨_, rfl⟩
  obtain ⟨ephA2, hephA2⟩ : ∃ x, KeyPair.generate W0.C rcA0 = x := ⟨_, rfl⟩
  obtain ⟨pA, hpA⟩ : ∃ x, Ratchet.rootKdf W0.C.F rk0
      (W0.C.X (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA))
        (W0.C.pubKey (Ratchet.clampScalar spkPriv0))).toList = x := ⟨_, rfl⟩
  obtain ⟨pB, hpB⟩ : ∃ x, Ratchet.rootKdf W0.C.F pA.1
      (W0.C.X (Ratchet.clampScalar (Ratchet.keyToBytesVec32 rcB0))
        (W0.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA)))).toList = x := ⟨_, rfl⟩
  obtain ⟨pA2, hpA2⟩ : ∃ x, Ratchet.rootKdf W0.C.F pB.1
      (W0.C.X (Ratchet.clampScalar (Ratchet.keyToBytesVec32 rcA0))
        (W0.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 rcB0)))).toList = x := ⟨_, rfl⟩
  obtain ⟨nextCkA, hnextCkA⟩ :
      ∃ x, HKDF.bytesToKey32 (Ratchet.chainHmac W0.C.F pA.2 Ratchet.chainKeySeed) = x := ⟨_, rfl⟩
  obtain ⟨nextCkB, hnextCkB⟩ :
      ∃ x, HKDF.bytesToKey32 (Ratchet.chainHmac W0.C.F pB.2 Ratchet.chainKeySeed) = x := ⟨_, rfl⟩
  obtain ⟨mk1, hmk1⟩ :
      ∃ x, ((⟨pA.2, 0#32⟩ : ChainKey).messageKeys W0.C.F).generateKeys W0.C.F salt1 = x := ⟨_, rfl⟩
  obtain ⟨mk2, hmk2⟩ :
      ∃ x, ((⟨pB.2, 0#32⟩ : ChainKey).messageKeys W0.C.F).generateKeys W0.C.F salt2 = x := ⟨_, rfl⟩
  obtain ⟨ctext1, hctext1⟩ :
      ∃ x, aesCbcEncrypt W0.C.E mk1.cipherKey mk1.iv pt1 = x := ⟨_, rfl⟩
  obtain ⟨ctext2, hctext2⟩ :
      ∃ x, aesCbcEncrypt W0.C.E mk2.cipherKey mk2.iv pt2 = x := ⟨_, rfl⟩
  obtain ⟨spkPubKey, hspkPubKey⟩ :
      ∃ x : PublicKey, ⟨(keyPairOf W0.C spkPriv0).publicKey.bytes⟩ = x := ⟨_, rfl⟩
  have hbundle_idPub : (⟨⟨bundleB0.idPub⟩⟩ : IdentityKey) = idKeyB := rfl
  have hbundle_spkPub : (⟨bundleB0.spkPub⟩ : PublicKey) = spkPubKey := hspkPubKey
  let xA : RecordExtras :=
    initiatorRecordExtras aliceMe bundleB0 ⟨u8Vec 32 hdr0.ekAPk⟩ (u8Vec 1568 hdr0.kemCt)
  let sA0 : SessionState Bytes :=
    (((SessionState.new currentVersion idKeyA idKeyB pA.1
      stA0).addReceiverChain spkPubKey ⟨ck0, 0#32⟩).setSenderChain
      ephA ⟨pA.2, 0#32⟩).setUnacknowledgedPreKeyMessage
  let gA0 : GhostState Bytes := ⟨.A, sA0, 0, [0]⟩
  let aliceDir1 : PqParty := { aliceDir0 with peerId := some idKeyB, session := some (xA, gA0) }
  have hInitSess :
      initializeInitiatorSession W0.C (pqxdhSpqrSession W0) idKeyA idKeyB spkPubKey rk0 ck0 pqr0 coinsA =
      .ok (((SessionState.new currentVersion idKeyA idKeyB pA.1
        stA0).addReceiverChain spkPubKey ⟨ck0, 0#32⟩).setSenderChain
        ephA ⟨pA.2, 0#32⟩) := by
    unfold initializeInitiatorSession
    rw [hephA, hstA0]
    have hrc : rootCreateChain W0.C rk0 spkPubKey ephA.privateKey = .ok (pA.1, ⟨pA.2, 0#32⟩) := by
      rw [← hspkPubKey, ← hephA]
      dsimp only [keyPairOf, KeyPair.generate]
      rw [rootCreateChain_w0 rk0 (Ratchet.keyToBytesVec32 coinsA) spkPriv0, hpA]
    dsimp only [bind, Except.bind, pure, Except.pure]
    rw [hrc]
    rfl
  have hIS : initiateState X0 W0 .A aliceMe bundleB0 tape0 = some (xA, gA0) := by
    unfold initiateState
    rw [hIK]
    dsimp only
    rw [hrk0, hck0, hpqr0, hcoinsA, hbundle_idPub, hbundle_spkPub]
    change (match initializeInitiatorSession W0.C (pqxdhSpqrSession W0) idKeyA idKeyB spkPubKey
        rk0 ck0 pqr0 coinsA with
      | .error _ => none
      | .ok st => some (xA, ⟨.A, st.setUnacknowledgedPreKeyMessage, 0, [0]⟩)) = some (xA, gA0)
    rw [hInitSess]
  have hStep1 : pqInitModel X0 W0 aliceDir0 bundleB0 tape0 = some (some (aliceDir1, [])) := by
    unfold pqInitModel
    have htr : aliceDir0.trusts idKeyB = true := by simp [aliceDir0, PqParty.trusts]
    rw [hbundle_idPub, htr]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change (match initiateState X0 W0 .A aliceMe bundleB0 tape0 with
      | none => some none
      | some (x, g) => some (some ({ aliceDir0 with peerId := some idKeyB, session := some (x, g) },
          []))) = some (some (aliceDir1, []))
    rw [hIS]
  let addrsAB := serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B
  obtain ⟨msg1, hmsg1⟩ : ∃ x, SignalMessage.new W0.C.F protoSignalCodec currentVersion mk1.macKey
      addrsAB ephA.publicKey 0#32 0 ctext1 idKeyA idKeyB pqMsg1 = x := ⟨_, rfl⟩
  let sA1 : SessionState Bytes :=
    { (((SessionState.new currentVersion idKeyA idKeyB pA.1
        stA0).addReceiverChain spkPubKey ⟨ck0, 0#32⟩).setSenderChain
        ephA ⟨nextCkA, 1#32⟩).setUnacknowledgedPreKeyMessage
      with pqRatchetState := stA1 }
  let gA1 : GhostState Bytes := ⟨.A, sA1, 0, [0]⟩
  let m1 : PreKeyMessageFields :=
    { regId := aliceMe.regId
      opkId := some opkId0
      spkId := spkId0
      kpkId := kpkId0
      kyberCt := u8Vec 1568 hdr0.kemCt
      baseKey := u8Vec 32 hdr0.ekAPk
      idPub := (keyPairOf W0.C aliceMe.idPriv).publicKey.bytes
      inner := msg1.serialized }
  let aliceDir2 : PqParty := { aliceDir1 with peerId := some idKeyB, session := some (xA, gA1) }
  have hEnc1 :
      SessionState.messageEncrypt W0.C protoSignalCodec (pqxdhSpqrSession W0)
        ((pqxdhSessionParams W0).sendAddrs .A) pt1 coins0.toList sA0 = (.ok msg1, sA1) := by
    have hPan := spqrPq_sendPanics_false_of_send_some W0 stA0 coins0.toList hSpqrSend1
    have hFrom : Mut.exec OutgoingTripleRatchet.fromSessionState sA0 =
        (.ok ⟨ephA, ⟨pA.2, 0#32⟩, 0, stA0, currentVersion, idKeyA, idKeyB⟩,
         { sA0 with pqRatchetState := [] }) := rfl
    have hNext : (⟨pA.2, 0#32⟩ : ChainKey).nextChainKey W0.C.F = .ok ⟨nextCkA, 1#32⟩ := by
      rw [← hnextCkA]; rfl
    unfold SessionState.messageEncrypt
    rw [hFrom]
    dsimp only [OutgoingTripleRatchet.encrypt, SessionState.encryptAddresses, sA0,
      SessionState.setUnacknowledgedPreKeyMessage, SessionState.setSenderChain,
      SessionState.addReceiverChain, SessionState.new, Params.sendAddrs, pqxdhSessionParams,
      Mut.exec, ExceptT.run, StateT.run, Id.run,
      monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
      ExceptT.lift, Functor.map, StateT.map,
      bind, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, Pure.pure, ExceptT.pure, StateT.bind, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, liftE]
    simp only [↓reduceIte, hPan, Bool.false_eq_true]
    rw [hSpqrSend1]
    dsimp only
    rw [hmk1, hctext1, hmsg1, hNext]
    rfl
  have hStep2 :
      pqSendModel W0 aliceDir1 pt1 coins0.toList =
        some (some (aliceDir2, wirePrekey :: m1.bytes)) := by
    unfold pqSendModel
    change (match SessionState.messageEncrypt W0.C protoSignalCodec (pqxdhSpqrSession W0)
          ((pqxdhSessionParams W0).sendAddrs .A) pt1 coins0.toList sA0 with
      | (.ok msg, s) => _
      | (.error .panic, _) => none
      | (.error _, _) => some none) = _
    rw [hEnc1]
    have hrem : sA0.remoteIdentity = some idKeyB := rfl
    have htr : aliceDir1.trusts idKeyB = true := by simp [aliceDir1, PqParty.trusts]
    have hpend : sA0.pendingPreKey = true := rfl
    rw [hrem]
    dsimp only
    rw [htr, hpend]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hm1_len : m1.inner.length + 2048 < 2 ^ 32 := by
    change msg1.serialized.length + 2048 < 2 ^ 32
    rw [← hmsg1, ← hctext1]
    have hle := signalMessage_new_len_le W0.C.F mk1.macKey addrsAB
      (addrsOpt_ok_bound _ (Or.inr ⟨.A, .B, rfl⟩)) ephA.publicKey 0#32 0
      W0.C.E mk1.cipherKey mk1.iv pt1 idKeyA idKeyB pqMsg1 (by decide) hpq1_le
    omega
  have htf1 : SignalMessage.tryFrom protoSignalCodec m1.inner = .ok msg1 := by
    change SignalMessage.tryFrom protoSignalCodec msg1.serialized = .ok msg1
    rw [← hmsg1, ← hctext1]
    apply tryFrom_new
    exact CryptoVerification.LibsignalSession.signalRoundTripShort_proto _ _
      (signalWireShort_of_bounds ephA.publicKey addrsAB
        (addrsOpt_ok_bound _ (Or.inr ⟨.A, .B, rfl⟩))
        W0.C.E mk1.cipherKey mk1.iv pt1 pqMsg1 (by decide) hpq1_le)
  have hAcc : SignalPqxdh.Model.acceptKeys (modelPrims X0 W0) (acceptInput W0 bobMe keysB0 m1) =
      some dk0 := hAccAll msg1.serialized
  let xB : RecordExtras := responderRecordExtras bobMe m1
  let sB1 : SessionState Bytes :=
    { sessionVersion := 4#32
      localIdentity := idKeyB
      remoteIdentity := some idKeyA
      rootKey := pB.1
      previousCounter := 0#32
      senderChain := some ⟨ephB, ⟨pB.2, 0#32⟩⟩
      receiverChains := [⟨ephA.publicKey, some ⟨nextCkA, 1#32⟩, []⟩]
      pendingPreKey := false
      pqRatchetState := stB1 }
  let gB1 : GhostState Bytes := ⟨.B, sB1, 1, [1]⟩
  let bobDir1 : PqParty :=
    { party := .B
      me := bobMe
      peerId := some idKeyA
      session := some (xB, gB1)
      signed := [(spkId0, spkRec0)]
      oneTime := [(opkId0, none)]
      kyberOneTime := []
      kyberLastResort := [(kpkId0, kpkRec0, [(spkId0, m1.baseKey)])] }
  have hRecvState1 :
      recvPrekeyState X0 W0 .B bobMe keysB0 m1 rcB0 = some (some (xB, gB1, pt1)) := by
    unfold recvPrekeyState
    rw [htf1]
    have hids : ¬ (m1.spkId ≠ keysB0.spkId ∨ m1.kpkId ≠ keysB0.kpkId) := by
      rintro (h | h) <;> exact h rfl
    simp only [hids, ↓reduceIte]
    rw [hAcc]
    dsimp only
    rw [hrk0, hck0, hpqr0]
    let st0 : SessionState Bytes :=
      initializeRecipientSession (pqxdhSpqrSession W0) idKeyB idKeyA (keyPairOf W0.C spkPriv0) rk0 ck0 pqr0
    have hsrk1 : msg1.senderRatchetKey = ephA.publicKey := by rw [← hmsg1]; rfl
    have hrc1 : rootCreateChain W0.C rk0 ephA.publicKey
        (keyPairOf W0.C spkPriv0).privateKey = .ok (pA.1, ⟨pA.2, 0#32⟩) := by
      rw [← hephA]
      dsimp only [KeyPair.generate, keyPairOf]
      rw [rootCreateChain_w0 rk0 spkPriv0 (Ratchet.keyToBytesVec32 coinsA),
        c0_dh_comm spkPriv0 (Ratchet.keyToBytesVec32 coinsA), hpA]
    have hrc2 : rootCreateChain W0.C pA.1 ephA.publicKey ephB.privateKey =
        .ok (pB.1, ⟨pB.2, 0#32⟩) := by
      rw [← hephA, ← hephB]
      dsimp only [KeyPair.generate]
      rw [rootCreateChain_w0 pA.1 (Ratchet.keyToBytesVec32 rcB0) (Ratchet.keyToBytesVec32 coinsA), hpB]
    have hmac1 : msg1.verifyMacWithAddresses W0.C.F ((pqxdhSessionParams W0).expectedAddrs .B)
        idKeyA idKeyB mk1.macKey = true := by
      rw [← hmsg1]
      exact verifyMacWithAddresses_new W0.C.F protoSignalCodec currentVersion mk1.macKey
        addrsAB addrsAB ephA.publicKey 0#32 0 ctext1 idKeyA idKeyB pqMsg1 (addrsOk_refl _)
    have hcbc1 : aesCbcDecrypt W0.C.D mk1.cipherKey mk1.iv msg1.ciphertext = some pt1 := by
      have hct : msg1.ciphertext = ctext1 := by rw [← hmsg1]; rfl
      rw [hct, ← hctext1]
      exact aesCbcDecrypt_w0 mk1.cipherKey mk1.iv pt1
    have hver1 : ¬ (st0.version.toNat ≠ msg1.messageVersion.toNat) := by
      rw [← hmsg1]; intro h; exact h rfl
    have hcnt1 : ¬ (msg1.counter < (0#32 : BitVec 32)) := by
      have hc : msg1.counter = 0#32 := by rw [← hmsg1]; rfl
      rw [hc]; decide
    have hsub1 : (msg1.counter - 0#32).toNat = 0 := by
      have hc : msg1.counter = 0#32 := by rw [← hmsg1]; rfl
      rw [hc]; decide
    have hnextA : (⟨pA.2, 0#32⟩ : ChainKey).nextChainKey W0.C.F = .ok ⟨nextCkA, 1#32⟩ := by
      rw [← hnextCkA]; rfl
    have hPan1 := spqrPq_recvPanics_false_of_recv_ok W0 stB0 pqMsg1 hSpqrRecv1
    change (match SessionState.tryDecryptFromRecord W0.C (pqxdhSpqrSession W0)
          ((pqxdhSessionParams W0).expectedAddrs .B) msg1 .preKey rcB0 st0 with
      | (.ok pt, st) => some (some (xB, ⟨.B, st, 1, [1]⟩, pt))
      | (.error .panic, _) => none
      | (.error _, _) => some none) = some (some (xB, gB1, pt1))
    unfold SessionState.tryDecryptFromRecord
    simp only [hver1, ↓reduceIte]
    dsimp only [st0, initializeRecipientSession]
    rw [hstB0]
    dsimp only [SessionState.tryDecryptWithState, TripleRatchet.fromSessionState,
      SessionState.takeRatchetState, SessionState.takePqRatchetState,
      TripleRatchet.decrypt, TripleRatchet.onRatchet, zoom,
      RatchetState.ensureReceiverChain, RatchetState.findReceiverChainKey,
      RatchetState.findReceiverChainIndex, List.findIdx?, List.findIdx?.go,
      RatchetState.dhRatchetStep, RatchetState.takeRootKey,
      RatchetState.evictReceiverChains, maxReceiverChains,
      RatchetState.consumeMessageKey, RatchetState.advanceChain,
      RatchetState.setReceiverChainKey,
      SessionState.new, SessionState.setSenderChain,
      Mut.exec, ExceptT.run, StateT.run, Id.run,
      monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
      ExceptT.lift, Functor.map, StateT.map,
      bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, get, getThe, MonadStateOf.get,
      StateT.get, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, liftE]
    rw [hsrk1, hrc1]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
    rw [hephB, hrc2]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
      List.nil_append, List.length_singleton]
    have hdrop1 : (1 - 5 : Nat) = 0 := rfl
    simp only [hdrop1, List.drop_zero, hcnt1, hsub1, maxForwardJumps, Nat.not_lt_zero,
      RatchetState.advanceChain, ↓reduceIte]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
    rw [hnextA]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
      List.findIdx?.go]
    simp only [beq_self_eq_true, ↓reduceIte]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
      List.getElem?_cons_zero, List.set]
    have hpqField1 : msg1.pqRatchet = pqMsg1 := by rw [← hmsg1]; rfl
    rw [hpqField1]
    simp only [hPan1, Bool.false_eq_true, ↓reduceIte]
    rw [hSpqrRecv1]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]
    rw [hmk1, hmac1, hcbc1]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hStep3 : pqRecvPrekeyModel X0 W0 bobDir0 m1 rcB0 = some (some (bobDir1, pt1)) := by
    unfold pqRecvPrekeyModel
    rw [htf1]
    dsimp only
    have hidA : (⟨⟨m1.idPub⟩⟩ : IdentityKey) = idKeyA := rfl
    have htrB : bobDir0.trusts idKeyA = true := by simp [bobDir0, PqParty.trusts]
    have hkeysB : preKeysNamedBy bobDir0 m1 = some keysB0 := by
      dsimp only [preKeysNamedBy, bobDir0, m1, spkRec0, kpkRec0, keysB0, List.lookup, Option.map]
      have h1 : (spkId0 == spkId0) = true := rfl
      have h2 : (kpkId0 == kpkId0) = true := rfl
      have h3 : (opkId0 == opkId0) = true := rfl
      simp only [h1, h2, h3]
    have hmarkB : markKyberUsed bobDir0 m1 =
        some { bobDir0 with
          kyberLastResort := [(kpkId0, kpkRec0, [(spkId0, m1.baseKey)])] } := by
      dsimp only [markKyberUsed, bobDir0, m1, List.lookup, List.map]
      have h1 : (kpkId0 == kpkId0) = true := rfl
      have h2 : ¬ (37 * ([] : List (BitVec 32 × List.Vector (BitVec 8) 32)).length > fileCapBytes) := by
        decide
      simp only [h1, h2, false_or, List.not_mem_nil, ↓reduceIte, List.nil_append]
    rw [hidA, htrB]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change (match preKeysNamedBy bobDir0 m1 with
      | none => some none
      | some k =>
        match recvPrekeyState X0 W0 .B bobMe k m1 rcB0 with
        | none => none
        | some none => some none
        | some (some (x, g, pt)) =>
          match markKyberUsed bobDir0 m1 with
          | none => some none
          | some st1 =>
            some (some ({ removeOpk st1 m1 with peerId := some idKeyA, session := some (x, g) },
              pt))) = some (some (bobDir1, pt1))
    rw [hkeysB]; dsimp only
    rw [hRecvState1]; dsimp only
    rw [hmarkB]
    dsimp only [removeOpk, m1, bobDir0, List.map]
    simp only [↓reduceIte]
    rfl
  obtain ⟨msg2, hmsg2⟩ : ∃ x, SignalMessage.new W0.C.F protoSignalCodec currentVersion mk2.macKey
      none ephB.publicKey 0#32 0 ctext2 idKeyB idKeyA pqMsg2 = x := ⟨_, rfl⟩
  let sB2 : SessionState Bytes :=
    { sB1 with senderChain := some ⟨ephB, ⟨nextCkB, 1#32⟩⟩, pqRatchetState := stB2 }
  let gB2 : GhostState Bytes := ⟨.B, sB2, 1, [1]⟩
  let bobDir2 : PqParty := { bobDir1 with peerId := some idKeyA, session := some (xB, gB2) }
  let c2 : Bytes := msg2.serialized
  have hEnc2 :
      SessionState.messageEncrypt W0.C protoSignalCodec (pqxdhSpqrSession W0)
        ((pqxdhSessionParams W0).sendAddrs .B) pt2 coins0.toList sB1 = (.ok msg2, sB2) := by
    have hPan := spqrPq_sendPanics_false_of_send_some W0 stB1 coins0.toList hSpqrSend2
    have hFrom : Mut.exec OutgoingTripleRatchet.fromSessionState sB1 =
        (.ok ⟨ephB, ⟨pB.2, 0#32⟩, 0, stB1, currentVersion, idKeyB, idKeyA⟩,
         { sB1 with pqRatchetState := [] }) := rfl
    have hNextB : (⟨pB.2, 0#32⟩ : ChainKey).nextChainKey W0.C.F = .ok ⟨nextCkB, 1#32⟩ := by
      rw [← hnextCkB]; rfl
    unfold SessionState.messageEncrypt
    rw [hFrom]
    dsimp only [OutgoingTripleRatchet.encrypt, SessionState.encryptAddresses, sB1,
      Mut.exec, ExceptT.run, StateT.run, Id.run,
      monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
      ExceptT.lift, Functor.map, StateT.map,
      bind, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, Pure.pure, ExceptT.pure, StateT.bind, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, liftE]
    simp only [Bool.false_eq_true, ↓reduceIte, hPan]
    rw [hSpqrSend2]
    dsimp only
    rw [hmk2, hctext2, hmsg2, hNextB]
    rfl
  have hStep4 :
      pqSendModel W0 bobDir1 pt2 coins0.toList =
        some (some (bobDir2, wireWhisper :: c2)) := by
    unfold pqSendModel
    change (match SessionState.messageEncrypt W0.C protoSignalCodec (pqxdhSpqrSession W0)
          ((pqxdhSessionParams W0).sendAddrs .B) pt2 coins0.toList sB1 with
      | (.ok msg, s) => _
      | (.error .panic, _) => none
      | (.error _, _) => some none) = _
    rw [hEnc2]
    have hrem : sB1.remoteIdentity = some idKeyA := rfl
    have htr : bobDir1.trusts idKeyA = true := by simp [bobDir1, PqParty.trusts]
    have hpend : sB1.pendingPreKey = false := rfl
    rw [hrem]
    dsimp only
    rw [htr, hpend]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hSteady4 :=
    (pqCliSteadyRefinesSM_proof W0 bobDir1 xB gB1 rfl rfl).1 pt2 coins0.toList bobDir2
      (wireWhisper :: c2) hStep4
  obtain ⟨_, _, _, hwire2_eq⟩ := hSteady4
  have hc2_sm : c2 = ((pqxdhSessionParams W0).send gB1 pt2 coins0.toList).2 :=
    List.cons.inj hwire2_eq |>.2
  have hc2_len : c2.length < 2 ^ 32 := by
    change msg2.serialized.length < 2 ^ 32
    rw [← hmsg2, ← hctext2]
    have hle := signalMessage_new_len_le W0.C.F mk2.macKey none
      (addrsOpt_ok_bound _ (Or.inl rfl)) ephB.publicKey 0#32 0
      W0.C.E mk2.cipherKey mk2.iv pt2 idKeyB idKeyA pqMsg2 (by decide) hpq2_le
    omega
  have htf2 : SignalMessage.tryFrom protoSignalCodec c2 = .ok msg2 := by
    change SignalMessage.tryFrom protoSignalCodec msg2.serialized = .ok msg2
    rw [← hmsg2, ← hctext2]
    apply tryFrom_new
    exact CryptoVerification.LibsignalSession.signalRoundTripShort_proto _ _
      (signalWireShort_of_bounds ephB.publicKey none
        (addrsOpt_ok_bound _ (Or.inl rfl))
        W0.C.E mk2.cipherKey mk2.iv pt2 pqMsg2 (by decide) hpq2_le)
  let sA2 : SessionState Bytes :=
    { sessionVersion := 4#32
      localIdentity := idKeyA
      remoteIdentity := some idKeyB
      rootKey := pA2.1
      previousCounter := 0#32
      senderChain := some ⟨ephA2, ⟨pA2.2, 0#32⟩⟩
      receiverChains :=
        [⟨spkPubKey, some ⟨ck0, 0#32⟩, []⟩,
         ⟨ephB.publicKey, some ⟨nextCkB, 1#32⟩, []⟩]
      pendingPreKey := false
      pqRatchetState := stA2 }
  let gA2 : GhostState Bytes := ⟨.A, sA2, 0, [0]⟩
  let aliceDir3 : PqParty := { aliceDir2 with peerId := some idKeyB, session := some (xA, gA2) }
  have hDec2 :
      SessionState.tryDecryptFromRecord W0.C (pqxdhSpqrSession W0) ((pqxdhSessionParams W0).expectedAddrs .A)
        msg2 .whisper rcA0 sA1 = (.ok pt2, sA2) := by
    have hver2 : ¬ (sA1.version.toNat ≠ msg2.messageVersion.toNat) := by
      rw [← hmsg2]; intro h; exact h rfl
    have hsrk2 : msg2.senderRatchetKey = ephB.publicKey := by rw [← hmsg2]; rfl
    have hneq_pk : (spkPubKey == ephB.publicKey) = false := by
      rw [← hspkPubKey, ← hephB]
      exact spkPub_beq_ephB_false
    have hrcA1 : rootCreateChain W0.C pA.1 ephB.publicKey ephA.privateKey =
        .ok (pB.1, ⟨pB.2, 0#32⟩) := by
      rw [← hephB, ← hephA]
      dsimp only [KeyPair.generate]
      rw [rootCreateChain_w0 pA.1 (Ratchet.keyToBytesVec32 coinsA) (Ratchet.keyToBytesVec32 rcB0),
        c0_dh_comm (Ratchet.keyToBytesVec32 coinsA) (Ratchet.keyToBytesVec32 rcB0), hpB]
    have hrcA2 : rootCreateChain W0.C pB.1 ephB.publicKey ephA2.privateKey =
        .ok (pA2.1, ⟨pA2.2, 0#32⟩) := by
      rw [← hephB, ← hephA2]
      dsimp only [KeyPair.generate]
      rw [rootCreateChain_w0 pB.1 (Ratchet.keyToBytesVec32 rcA0) (Ratchet.keyToBytesVec32 rcB0), hpA2]
    have hcnt2 : ¬ (msg2.counter < (0#32 : BitVec 32)) := by
      have hc : msg2.counter = 0#32 := by rw [← hmsg2]; rfl
      rw [hc]; decide
    have hsub2 : (msg2.counter - 0#32).toNat = 0 := by
      have hc : msg2.counter = 0#32 := by rw [← hmsg2]; rfl
      rw [hc]; decide
    have hNextB : (⟨pB.2, 0#32⟩ : ChainKey).nextChainKey W0.C.F = .ok ⟨nextCkB, 1#32⟩ := by
      rw [← hnextCkB]; rfl
    have hPan2 := spqrPq_recvPanics_false_of_recv_ok W0 stA1 pqMsg2 hSpqrRecv2
    have hmac2 : msg2.verifyMacWithAddresses W0.C.F ((pqxdhSessionParams W0).expectedAddrs .A)
        idKeyB idKeyA mk2.macKey = true := by
      rw [← hmsg2]
      exact verifyMacWithAddresses_new W0.C.F protoSignalCodec currentVersion mk2.macKey
        none ((pqxdhSessionParams W0).expectedAddrs .A) ephB.publicKey 0#32 0 ctext2 idKeyB idKeyA
        pqMsg2 (addrsOk_none _)
    have hcbc2 : aesCbcDecrypt W0.C.D mk2.cipherKey mk2.iv msg2.ciphertext = some pt2 := by
      have hct : msg2.ciphertext = ctext2 := by rw [← hmsg2]; rfl
      rw [hct, ← hctext2]
      exact aesCbcDecrypt_w0 mk2.cipherKey mk2.iv pt2
    unfold SessionState.tryDecryptFromRecord
    simp only [hver2, ↓reduceIte]
    dsimp only [sA1, SessionState.setUnacknowledgedPreKeyMessage, SessionState.setSenderChain,
      SessionState.addReceiverChain, SessionState.new, maxReceiverChains,
      List.nil_append, List.length_singleton]
    have hlt5 : ¬ (5 < 1) := by decide
    simp only [hlt5, ↓reduceIte]
    dsimp only [SessionState.tryDecryptWithState, TripleRatchet.fromSessionState,
      SessionState.takeRatchetState, SessionState.takePqRatchetState,
      TripleRatchet.decrypt, TripleRatchet.onRatchet, zoom,
      RatchetState.ensureReceiverChain, RatchetState.findReceiverChainKey,
      RatchetState.findReceiverChainIndex, List.findIdx?, List.findIdx?.go,
      RatchetState.dhRatchetStep, RatchetState.takeRootKey,
      RatchetState.evictReceiverChains, maxReceiverChains,
      RatchetState.consumeMessageKey, RatchetState.advanceChain,
      RatchetState.setReceiverChainKey,
      Mut.exec, ExceptT.run, StateT.run, Id.run,
      monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
      ExceptT.lift, Functor.map, StateT.map,
      bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, get, getThe, MonadStateOf.get,
      StateT.get, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, liftE]
    rw [hsrk2]
    simp only [hneq_pk, Bool.false_eq_true, ↓reduceIte]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
    rw [hrcA1]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
    rw [hephA2, hrcA2]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
      List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    have hdrop2 : (2 - 5 : Nat) = 0 := rfl
    simp only [hdrop2, List.drop_zero, hcnt2, hsub2, maxForwardJumps, Nat.not_lt_zero,
      RatchetState.advanceChain, ↓reduceIte]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
    rw [hNextB]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
      List.findIdx?.go]
    simp only [hneq_pk, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
      List.getElem?_cons_succ, List.getElem?_cons_zero, List.set]
    have hpqField2 : msg2.pqRatchet = pqMsg2 := by rw [← hmsg2]; rfl
    rw [hpqField2]
    simp only [hPan2, Bool.false_eq_true, ↓reduceIte]
    rw [hSpqrRecv2]
    dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
      get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      TripleRatchet.applyToSessionState, SessionState.clearUnacknowledgedPreKeyMessage]
    rw [hmk2, hmac2, hcbc2]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hStep5 : pqRecvWhisperModel W0 aliceDir2 c2 rcA0 = some (some (aliceDir3, pt2)) := by
    unfold pqRecvWhisperModel
    change (match SignalMessage.tryFrom protoSignalCodec c2 with
      | .error _ => some none
      | .ok msg => pqxdhSessionDecryptModel W0 aliceDir2 xA gA1 msg .whisper rcA0) = _
    rw [htf2]
    unfold pqxdhSessionDecryptModel
    change (match SessionState.tryDecryptFromRecord W0.C (pqxdhSpqrSession W0)
          ((pqxdhSessionParams W0).expectedAddrs .A) msg2 .whisper rcA0 sA1 with
      | (.ok pt, s) => _
      | (.error .panic, _) => none
      | (.error _, _) => some none) = _
    rw [hDec2]
    dsimp only
    have hrem : sA2.remoteIdentity = some idKeyB := rfl
    have htr : aliceDir2.trusts idKeyB = true := by simp [aliceDir2, PqParty.trusts]
    rw [hrem]
    dsimp only
    rw [htr]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  have habk_xA : xA.aliceBaseKey.length ≤ 64 := by
    dsimp only [xA, initiatorRecordExtras]
    simp [PublicKey.serialize, List.Vector.toList_length]
  have hkyb_xA : ∀ k, xA.kyber = some k → k.ciphertext.length ≤ 1600 := by
    intro k hk
    dsimp only [xA, initiatorRecordExtras] at hk
    injection hk with hk
    subst hk
    simp [kyberKey_len]
  have habk_xB : xB.aliceBaseKey.length ≤ 64 := by
    dsimp only [xB, responderRecordExtras]
    rw [djbKey_len]; omega
  have hkyb_xB : ∀ k, xB.kyber = some k → k.ciphertext.length ≤ 1600 := by
    intro k hk; cases hk
  have ht_eq : ∀ {a b : Bytes},
      CryptoVerification.SpqrV1Sync.SendTotal.TopStateTight W0.C.F W0.Q.K a → a = b →
      CryptoVerification.SpqrV1Sync.SendTotal.TopStateTight W0.C.F W0.Q.K b := by
    rintro _ _ ha rfl; exact ha
  have htA0 := ht_eq (CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_init W0.C.F W0.Q.K .a2b pqr0) hstA0
  have htB0 := ht_eq (CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_init W0.C.F W0.Q.K .b2a pqr0) hstB0
  have htA1 := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_send W0.C.F W0.Q.K htA0 hSpqrSend1
  have htB1 := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_recv W0.C.F W0.Q.K htB0 hSpqrRecv1
  have htB2 := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_send W0.C.F W0.Q.K htB1 hSpqrSend2
  have htA2 := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_recv W0.C.F W0.Q.K htA1 hSpqrRecv2
  have hstA0_le := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_length_le W0.C.F W0.Q.K htA0
  have hstA1_le := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_length_le W0.C.F W0.Q.K htA1
  have hstB1_le := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_length_le W0.C.F W0.Q.K htB1
  have hstB2_le := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_length_le W0.C.F W0.Q.K htB2
  have hstA2_le := CryptoVerification.SpqrV1Sync.SendTotal.topStateTight_length_le W0.C.F W0.Q.K htA2
  have hrec_cap : ∀ (x : RecordExtras) (g : GhostState Bytes),
      g.session.pqRatchetState.length ≤ 286196 →
      g.session.receiverChains.length ≤ 2 →
      (∀ c ∈ g.session.receiverChains, c.messageKeys = []) →
      x.aliceBaseKey.length ≤ 64 →
      (∀ k, x.kyber = some k → k.ciphertext.length ≤ 1600) →
      (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes := by
    intro x g hpq_le hrc hmk habk hkyb
    have hbody : (encStateUnderExtras x g.session).length ≤ 286196 + 3000 := by
      unfold encStateUnderExtras
      have h1 := uint32Field_len_le 1 g.session.sessionVersion
      have h2 := bytesField_len_le 2 g.session.localIdentity.serialize
      have hlid : g.session.localIdentity.serialize.length = 33 := by
        simp [IdentityKey.serialize, PublicKey.serialize, List.Vector.toList_length]
      rw [hlid] at h2
      have h3 : (bytesField 3 ((g.session.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤
          53 := by
        cases g.session.remoteIdentity with
        | none =>
          have := bytesField_len_le 3 []
          simp only [Option.map_none, Option.getD_none, List.length_nil] at this ⊢; omega
        | some rid =>
          have h := bytesField_len_le 3 rid.serialize
          have hrid : rid.serialize.length = 33 := by
            simp [IdentityKey.serialize, PublicKey.serialize, List.Vector.toList_length]
          rw [hrid] at h; simpa using h
      have h4 := bytesField_len_le 4 (HMAC.keyToBytes32 g.session.rootKey)
      have hrk : (HMAC.keyToBytes32 g.session.rootKey).length = 32 := rfl
      rw [hrk] at h4
      have h5 := uint32Field_len_le 5 g.session.previousCounter
      have h6 : (msgField 6 (g.session.senderChain.map encSenderChain)).length ≤ 217 := by
        cases g.session.senderChain with
        | none => simp [msgField]
        | some sc =>
          simp only [Option.map_some, msgField]
          refine lenField_le_of_le 6 (B := 197) ?_
          unfold encSenderChain msgField
          have hs1 := bytesField_len_le 1 sc.ratchetKey.publicKey.serialize
          have hser : sc.ratchetKey.publicKey.serialize.length = 33 := by
            simp [PublicKey.serialize, List.Vector.toList_length]
          rw [hser] at hs1
          have hs2 := bytesField_len_le 2 sc.ratchetKey.privateKey.bytes.toList
          rw [List.Vector.toList_length] at hs2
          have hs3 := lenField_le_of_le 3 (encChainKey_len_le sc.chainKey)
          simp only [List.length_append]; omega
      have h7 : ((g.session.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten).length ≤
          330 := by
        rcases hrc_list : g.session.receiverChains with _ | ⟨c1, _ | ⟨c2, _ | ⟨_, _⟩⟩⟩
        · simp
        · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
          have := encReceiverChain_emptyMk_len_le c1 (hmk c1 (by simp [hrc_list])); omega
        · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.length_append]
          have := encReceiverChain_emptyMk_len_le c1 (hmk c1 (by simp [hrc_list]))
          have := encReceiverChain_emptyMk_len_le c2 (hmk c2 (by simp [hrc_list])); omega
        · rw [hrc_list] at hrc; simp at hrc
      have h9 : (msgField 9 (if g.session.pendingPreKey then some (encPendingPreKeyX x.pending)
          else none)).length ≤ 133 := by
        split
        · simp only [msgField]
          refine lenField_le_of_le 9 (B := 113) ?_
          unfold encPendingPreKeyX
          have hp1 := optUint32FieldX_len_le 1 x.pending.preKeyId
          have hp2 := bytesField_len_le 2 x.pending.baseKey.serialize
          have hbk : x.pending.baseKey.serialize.length = 33 := by
            simp [PublicKey.serialize, List.Vector.toList_length]
          rw [hbk] at hp2
          have hp3 := int32FieldX_len_le 3 x.pending.signedPreKeyId
          have hp4 := uint64FieldX_len_le 4 x.pending.timestamp
          simp only [List.length_append]; omega
        · simp [msgField]
      have h10 := uint32Field_len_le 10 x.remoteRegistrationId
      have h11 := uint32Field_len_le 11 x.localRegistrationId
      have h13 := bytesField_len_le 13 x.aliceBaseKey
      have h14 : (msgField 14 (if g.session.pendingPreKey then x.kyber.map encPendingKyberX
          else none)).length ≤ 1660 := by
        split
        · cases hxk : x.kyber with
          | none => simp [msgField]
          | some k =>
            simp only [Option.map_some, msgField]
            refine lenField_le_of_le 14 (B := 1640) ?_
            unfold encPendingKyberX
            have hk1 := uint32Field_len_le 1 k.preKeyId
            have hk2 := bytesField_len_le 2 k.ciphertext
            have hkc := hkyb k hxk
            simp only [List.length_append]; omega
        · simp [msgField]
      have h15 := bytesField_len_le 15 g.session.pqRatchetState
      simp only [List.length_append]; omega
    have houter := lenField_le_of_le 1 hbody
    change (encodeRecordUnderExtras (fun _ => x) g).length ≤ _ at houter
    unfold fileCapBytes
    omega
  have session_rec_cap : ∀ {s : Option (RecordExtras × GhostState Bytes)}
      {x0 : RecordExtras} {g0 : GhostState Bytes},
      s = some (x0, g0) →
      (encodeRecordUnderExtras (fun _ => x0) g0).length ≤ fileCapBytes →
      ∀ x g, s = some (x, g) → (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes := by
    rintro s x0 g0 hs0 hb x g hs; rw [hs0] at hs; cases hs; exact hb
  have hwf_A1 : PqxdhPartyInSpecDomain W0 aliceDir1 :=
    wfPq_step X0 W0 aliceDir0 aliceDir1 wfPq_aliceDir0
      (.init bundleB0 tape0 aliceDir1 [] rfl hStep1) (hlr_of_nil rfl)
      (session_rec_cap rfl (hrec_cap xA gA0 hstA0_le
        (rc1_bounds rfl).1 (rc1_bounds rfl).2 habk_xA hkyb_xA))
  have hwf_A2 : PqxdhPartyInSpecDomain W0 aliceDir2 :=
    wfPq_step X0 W0 aliceDir1 aliceDir2 hwf_A1
      (.send pt1 coins0 aliceDir2 _ (by decide) hStep2) (hlr_of_nil rfl)
      (session_rec_cap rfl (hrec_cap xA gA1 hstA1_le
        (rc1_bounds rfl).1 (rc1_bounds rfl).2 habk_xA hkyb_xA))
  have hlr_B1 : lastResortUses bobDir1 < 2 ^ 25 := by
    simp only [lastResortUses, bobDir1, List.map_cons, List.map_nil, List.length_singleton,
      List.sum_cons, List.sum_nil]
    decide
  have hwf_B1 : PqxdhPartyInSpecDomain W0 bobDir1 :=
    wfPq_step X0 W0 bobDir0 bobDir1 wfPq_bobDir0
      (.recvPrekey m1 rcB0 bobDir1 pt1 hm1_len (by intro _ _ h; cases h) hStep3) hlr_B1
      (session_rec_cap rfl (hrec_cap xB gB1 hstB1_le
        (rc1_bounds rfl).1 (rc1_bounds rfl).2 habk_xB hkyb_xB))
  have hwf_B2 : PqxdhPartyInSpecDomain W0 bobDir2 :=
    wfPq_step X0 W0 bobDir1 bobDir2 hwf_B1
      (.send pt2 coins0 bobDir2 _ (by decide) hStep4) hlr_B1
      (session_rec_cap rfl (hrec_cap xB gB2 hstB2_le
        (rc1_bounds rfl).1 (rc1_bounds rfl).2 habk_xB hkyb_xB))
  have hwf_A3 : PqxdhPartyInSpecDomain W0 aliceDir3 :=
    wfPq_step X0 W0 aliceDir2 aliceDir3 hwf_A2
      (.recvWhisper c2 rcA0 aliceDir3 pt2 hc2_len hStep5) (hlr_of_nil rfl)
      (session_rec_cap rfl (hrec_cap xA gA2 hstA2_le
        (rc2_bounds rfl).1 (rc2_bounds rfl).2 habk_xA hkyb_xA))
  exact ⟨aliceDir1, aliceDir2, aliceDir3, bobDir1, bobDir2, m1, c2,
    xA, xB, gA0, gA1, gA2, gB1, gB2,
    wfPq_aliceDir0, wfPq_bobDir0, hwf_A1, hwf_A2, hwf_A3, hwf_B1, hwf_B2,
    rfl, hstA0_ne, rfl, hstA1_ne, rfl, hstB1_ne, rfl, hstB2_ne, rfl, hstA2_ne,
    rfl, rfl, rfl, hm1_len, hc2_len,
    hStep1, hStep2, hStep3, hStep4, hc2_sm, hStep5,
    fun pre => filesOf_alice_session pre aliceDir1 xA gA0 rfl rfl rfl rfl rfl rfl,
    fun pre => filesOf_alice_session pre aliceDir2 xA gA1 rfl rfl rfl rfl rfl rfl,
    fun pre => filesOf_bob_session pre bobDir1 xB gB1 spkRec0 none kpkRec0
      [(spkId0, m1.baseKey)] rfl rfl rfl rfl rfl rfl,
    fun pre => filesOf_bob_session pre bobDir2 xB gB2 spkRec0 none kpkRec0
      [(spkId0, m1.baseKey)] rfl rfl rfl rfl rfl rfl,
    fun pre => filesOf_alice_session pre aliceDir3 xA gA2 rfl rfl rfl rfl rfl rfl⟩

/-- Every `run : CliRun` satisfying `CliSpecPqxdh run X0 W0` exits `0` across all five steps of
the `(aliceDir0, bobDir0)` conversation, writes non-empty SPQR-V1 session records, and outputs
`wire1`, `pt1`, `wire2`, and `pt2`. -/
theorem cliSpecPq_forces_full_conversation :
    aliceDir0.session = none ∧ bobDir0.session = none ∧
    ∃ (aliceDir1 aliceDir2 bobDir1 : PqParty)
      (wire1 wire2 : Bytes)
      (recA1 recA2 recB1 recB2 recA3 : Bytes),
      wire1.head? = some wirePrekey ∧
      wire2.head? = some wireWhisper ∧
      recA1 ≠ [] ∧ recA2 ≠ [] ∧ recB1 ≠ [] ∧ recB2 ≠ [] ∧ recA3 ≠ [] ∧
      ∀ (run : CliRun), CliSpecPqxdh run X0 W0 →
        (∃ fs1,
          run (pqInitInputs W0 aliceDir0 bundleB0 tape0) = some (.exited 0 [] fs1) ∧
          fs1 (sessionFile (partyAddress .B)) = some recA1) ∧
        (∃ fs2,
          run (pqSendInputs W0 aliceDir1 pt1 coins0) = some (.exited 0 wire1 fs2) ∧
          fs2 (sessionFile (partyAddress .B)) = some recA2) ∧
        (∃ fs3,
          run (pqRecvInputs W0 bobDir0 wire1 rcB0) = some (.exited 0 pt1 fs3) ∧
          fs3 (sessionFile (partyAddress .A)) = some recB1) ∧
        (∃ fs4,
          run (pqSendInputs W0 bobDir1 pt2 coins0) = some (.exited 0 wire2 fs4) ∧
          fs4 (sessionFile (partyAddress .A)) = some recB2) ∧
        (∃ fs5,
          run (pqRecvInputs W0 aliceDir2 wire2 rcA0) = some (.exited 0 pt2 fs5) ∧
          fs5 (sessionFile (partyAddress .B)) = some recA3) := by
  obtain ⟨aliceDir1, aliceDir2, _, bobDir1, _, m1, c2,
    xA, xB, gA0, gA1, gA2, gB1, gB2,
    hwfA0, hwfB0, hwfA1, hwfA2, _, hwfB1, _,
    _, _, _, _, _, _, _, _, _, _,
    _, _, _, hm1_len, hc2_len,
    hStep1, hStep2, hStep3, hStep4, _, hStep5,
    hfsA1, hfsA2, hfsB1, hfsB2, hfsA3⟩ := pqConversation_5steps
  refine ⟨rfl, rfl, aliceDir1, aliceDir2, bobDir1,
    wirePrekey :: m1.bytes, wireWhisper :: c2,
    encodeRecordUnderExtras (fun _ => xA) gA0, encodeRecordUnderExtras (fun _ => xA) gA1,
    encodeRecordUnderExtras (fun _ => xB) gB1, encodeRecordUnderExtras (fun _ => xB) gB2,
    encodeRecordUnderExtras (fun _ => xA) gA2,
    rfl, rfl,
    encodeRecordX_ne_nil _ gA0, encodeRecordX_ne_nil _ gA1,
    encodeRecordX_ne_nil _ gB1, encodeRecordX_ne_nil _ gB2,
    encodeRecordX_ne_nil _ gA2,
    fun run hSpec => ?_⟩
  have hw1 : ¬ (wirePrekey :: m1.bytes).length > stdinCapBytes :=
    Nat.not_lt.mpr
      (Computational.Proofs.LibsignalCli.CliCapsCompleteness.honest_send_ciphertext_le_stdinCap
        (fun x g hs => let ⟨⟨g₀, hR, _, hgs⟩, _⟩ := hwfA1.1 x g hs; ⟨g₀, hR, hgs⟩)
        (by decide) hStep2).2
  have hw2 : ¬ (wireWhisper :: c2).length > stdinCapBytes :=
    Nat.not_lt.mpr
      (Computational.Proofs.LibsignalCli.CliCapsCompleteness.honest_send_ciphertext_le_stdinCap
        (fun x g hs => let ⟨⟨g₀, hR, _, hgs⟩, _⟩ := hwfB1.1 x g hs; ⟨g₀, hR, hgs⟩)
        (by decide) hStep4).2
  have hpt1_sc : ¬ pt1.length > stdinCapBytes := by decide
  have hpt1_mp : ¬ pt1.length > maxPlaintextBytes := by decide
  have hpt2_sc : ¬ pt2.length > stdinCapBytes := by decide
  have hpt2_mp : ¬ pt2.length > maxPlaintextBytes := by decide
  have h1 := (hSpec aliceDir0 hwfA0).1 bundleB0 tape0 rfl
  rw [hStep1] at h1
  dsimp only [pqxdhExpectedOutcome, Option.map, observe] at h1
  have h2 := (hSpec aliceDir1 hwfA1).2.1 pt1 coins0 (by decide)
  simp only [hpt1_sc, hpt1_mp, ↓reduceIte, hStep2, pqxdhExpectedOutcome, Option.map, observe] at h2
  have h3 := (hSpec bobDir0 hwfB0).2.2.2.1 m1 rcB0 hm1_len (by intro _ _ h; cases h)
  simp only [hw1, ↓reduceIte, hStep3, pqxdhExpectedOutcome, Option.map, observe] at h3
  have h4 := (hSpec bobDir1 hwfB1).2.1 pt2 coins0 (by decide)
  simp only [hpt2_sc, hpt2_mp, ↓reduceIte, hStep4, pqxdhExpectedOutcome, Option.map, observe] at h4
  have h5 := (hSpec aliceDir2 hwfA2).2.2.1 c2 rcA0 hc2_len
  simp only [hw2, ↓reduceIte, hStep5, pqxdhExpectedOutcome, Option.map, observe] at h5
  exact ⟨⟨_, h1, hfsA1 _⟩, ⟨_, h2, hfsA2 _⟩, ⟨_, h3, hfsB1 _⟩,
    ⟨_, h4, hfsB2 _⟩, ⟨_, h5, hfsA3 _⟩⟩

theorem not_cliSpecPq_neverExitZero (run : CliRun)
    (hno0 : ∀ inp out fs, run inp ≠ some (.exited 0 out fs)) :
    ¬ CliSpecPqxdh run X0 W0 := by
  intro hSpec
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hAll⟩ :=
    cliSpecPq_forces_full_conversation
  obtain ⟨⟨fs1, h1, _⟩, _⟩ := hAll run hSpec
  exact hno0 _ _ fs1 h1

/-- The constant exit-`1` implementation does not satisfy `CliSpecPqxdh` for any `(X, W)`. -/
theorem not_cliSpecPq_alwaysReject :
    ¬ ∃ X W, CliSpecPqxdh (fun _ => some (.exited 1 [] (fun _ => none))) X W := by
  rintro ⟨X, W, hSpec⟩
  let st0 : PqParty :=
    { party := .A, me := aliceMe, peerId := none, session := none,
      signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }
  have hwf0 : PqxdhPartyInSpecDomain W st0 := by
    have hcap := (Computational.Proofs.LibsignalCli.CliCapsCompleteness.honest_party_and_bundle_files_le_fileCap
      (W := W) (st := st0) (b := bundleB0) (dir := bundleDir)
      (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)).2
    refine ⟨by simp [st0], fun f hf => ?_, by decide, by decide, by decide, by decide⟩
    have hle := hcap f.1 f.2 hf
    have hlt : fileCapBytes < 2 ^ 31 := by decide
    exact ⟨Nat.lt_of_le_of_lt hle hlt, fun _ => hle⟩
  have hnil_sc : ¬ ([] : List (BitVec 8)).length > stdinCapBytes := by decide
  have hrej := (hSpec st0 hwf0).2.2.2.2 [] 0#256 (by decide) (by decide) (by decide)
  simp only [hnil_sc, ↓reduceIte] at hrej
  injection hrej with hrej
  injection hrej with _ _ hfs
  have hcoins := congrFun hfs coinsFile
  have hlookup :
      filesOf (pqRecvInputs W st0 [] 0#256).files coinsFile = some (HMAC.keyToBytes32 0#256) := by
    dsimp only [pqRecvInputs, pqInputs]
    rw [List.append_nil]
    exact filesOf_lookup (encodeDir W st0) [] coinsFile (HMAC.keyToBytes32 0#256)
      (by decide +kernel) (by decide +kernel) (by simp)
  rw [hlookup] at hcoins
  nomatch hcoins

end EndToEnd

end CryptoVerification.LibsignalCli.PqNonVacuity
