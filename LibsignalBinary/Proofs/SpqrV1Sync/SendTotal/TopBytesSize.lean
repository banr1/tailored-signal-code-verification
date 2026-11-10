/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.SizeDefs

set_option autoImplicit false

/-!
# Top-Level Serialized State Size Bound

Proves `TopSizeStmt` (`bytes.length < 2 ^ 64`) for any `TopAdv F K n bytes` state with `n < 2 ^ 32`,
combining at most `n + 1` chain links (each bounded via `RecvSmall` and `SendPrevNil`), `BSizeStmt`
(`rawV1State ≤ 2 ^ 40`), and protobuf framing bounds.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoGames.LibsignalSession (ShaCompress)

open CryptoVerification.SpqrV1.Top.StateSize (
  encodeKey_length_le encodeVarint_length_le
  optRaw rawVN rawChain rawChainEpoch rawEpochDir
  rawAuth rawPolyEnc rawPolyDec
  rawUcKeysUnsampled rawUcHeaderSent rawUcEkSent rawUcEkSentCt1Received
  rawUcNoHeaderReceived rawUcHeaderReceived rawUcCt1Sent rawUcCt1SentEkReceived rawUcCt2Sent
  rawChKeysUnsampled rawChKeysSampled rawChHeaderSent rawChCt1Received rawChEkSentCt1Received
  rawChNoHeaderReceived rawChHeaderReceived rawChCt1Sampled rawChEkReceivedCt1Sampled
  rawChCt1Acknowledged rawChCt2Sampled rawInnerState rawV1State)

theorem tsz_link_le (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (hsp : SendPrevNil ch)
    (hsmall : RecvSmall ch) (l : ChainEpoch) (hmem : l ∈ ch.links) :
    rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb + 200 ≤ 2 ^ 20 + 264 := by
  obtain ⟨i, hi_lt, rfl⟩ := List.getElem_of_mem hmem
  have hi_opt : ch.links[i]? = some ch.links[i] := List.getElem?_eq_getElem hi_lt
  have hi_bd : i < ch.currentEpoch.toNat - (ch.sendEpoch.toNat - 1) + 1 := by
    have := h.hlen; omega
  let e := (ch.sendEpoch.toNat - 1) + i
  have he_lo : ch.sendEpoch.toNat - 1 ≤ e := Nat.le_add_right _ _
  have he_hi : e ≤ ch.currentEpoch.toNat := by
    have := h.hsend_le; omega
  have he_sub : e - (ch.sendEpoch.toNat - 1) = i := Nat.add_sub_cancel_left _ _
  obtain ⟨l_r, hl_r, hrecv⟩ := h.hrecvDir e he_lo he_hi
  rw [he_sub, hi_opt] at hl_r
  cases hl_r
  have hrecv_next : ch.links[i].recv.next.length = 32 := by
    rw [hrecv.hnext]
    exact length_nextAt F _ (length_seedAt F authKey secret dir.switch e) _
  have hrecv_prev : ch.links[i].recv.prev.data.length < 2 ^ 20 := hsmall _ hmem
  have hsend_prev : ch.links[i].send.prev.data = [] := hsp _ hmem
  have hsend_next : ch.links[i].send.next.length ≤ 32 := by
    by_cases h0 : i = 0 ∧ 1 ≤ ch.sendEpoch.toNat
    · rcases h0 with ⟨rfl, h1⟩
      have hnil := h.hsendOld ch.links[0] h1 hi_opt
      simp [hnil]
    · have he_send : ch.sendEpoch.toNat ≤ e := by omega
      obtain ⟨l_s, hl_s, hsend⟩ := h.hsendDir e he_send he_hi
      rw [he_sub, hi_opt] at hl_s
      cases hl_s
      rw [hsend.hnext, length_nextAt F _ (length_seedAt F authKey secret dir e) _]
  simp only [rawEpochDir, ChainEpochDirection.intoPb, hsend_prev, List.length_nil, hrecv_next]
  omega

private theorem tsz_chainCur_le_phiB {F : ShaCompress} (st : St F) : chainCur st ≤ phiB st := by
  cases st <;> simp [chainCur, phiB, keyedB, freshB]

private theorem tsz_sum_map_le {α : Type} (xs : List α) (f : α → Nat) (c : Nat)
    (h : ∀ x ∈ xs, f x ≤ c) : (xs.map f).sum ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    calc f x + (xs.map f).sum ≤ c + xs.length * c := Nat.add_le_add hx hxs
      _ = (xs.length + 1) * c := by rw [Nat.succ_mul, Nat.add_comm]

private theorem tsz_len_uint32 (t : BitVec 32) (v : BitVec 32) :
    (Proto.encodeUint32Field t v).length ≤ 22 := by
  unfold Proto.encodeUint32Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le t .varint
    have h2 := encodeVarint_length_le (v.zeroExtend 64)
    omega

private theorem tsz_len_uint64 (t : BitVec 32) (v : BitVec 64) :
    (Proto.encodeUint64Field t v).length ≤ 22 := by
  unfold Proto.encodeUint64Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le t .varint
    have h2 := encodeVarint_length_le v
    omega

private theorem tsz_len_int32 (t : BitVec 32) (v : BitVec 32) :
    (Proto.encodeInt32Field t v).length ≤ 22 := by
  unfold Proto.encodeInt32Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le t .varint
    have h2 := encodeVarint_length_le (v.signExtend 64)
    omega

private theorem tsz_len_bool (t : BitVec 32) (v : Bool) :
    (Proto.encodeBoolField t v).length ≤ 12 := by
  unfold Proto.encodeBoolField
  split
  · simp only [List.length_append, List.length_singleton]
    have h1 := encodeKey_length_le t .varint
    omega
  · simp

private theorem tsz_len_bytesUncond (t : BitVec 32) (v : Bytes) :
    (Proto.encodeBytesUncond t v).length ≤ v.length + 22 := by
  unfold Proto.encodeBytesUncond
  simp only [List.length_append]
  have h1 := encodeKey_length_le t .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 v.length)
  omega

private theorem tsz_len_bytes (t : BitVec 32) (v : Bytes) :
    (Proto.encodeBytesField t v).length ≤ v.length + 22 := by
  unfold Proto.encodeBytesField
  split
  · simp
  · exact tsz_len_bytesUncond t v

private theorem tsz_len_repBytes (t : BitVec 32) (vs : List Bytes) :
    (Proto.encodeRepeatedBytes t vs).length ≤ (vs.map (fun v => v.length + 22)).sum := by
  unfold Proto.encodeRepeatedBytes
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldr_cons, List.length_append, List.map_cons, List.sum_cons]
    have hv := tsz_len_bytesUncond t v
    omega

private theorem tsz_len_msg {M : Type} (enc : M → Bytes) (t : BitVec 32) (m : M) :
    (Proto.encodeMessage enc t m).length ≤ (enc m).length + 22 := by
  unfold Proto.encodeMessage
  simp only [List.length_append]
  have h1 := encodeKey_length_le t .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 (enc m).length)
  omega

private theorem tsz_len_optMsg {M : Type} (enc : M → Bytes) (f : M → Nat) (c : Nat)
    (hf : ∀ m, (enc m).length ≤ f m + c) (t : BitVec 32) (opt : Option M) :
    (Proto.encodeOptMessage enc t opt).length ≤ optRaw f opt + (c + 22) := by
  cases opt with
  | none => simp [Proto.encodeOptMessage, optRaw]
  | some m =>
    simp only [Proto.encodeOptMessage, optRaw]
    have hm := tsz_len_msg enc t m
    have hfm := hf m
    omega

private theorem tsz_len_repMsg {M : Type} (enc : M → Bytes) (f : M → Nat)
    (hf : ∀ m, (enc m).length + 22 ≤ f m) (t : BitVec 32) (ms : List M) :
    (Proto.encodeRepeatedMessage enc t ms).length ≤ (ms.map f).sum := by
  unfold Proto.encodeRepeatedMessage
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.foldr_cons, List.length_append, List.map_cons, List.sum_cons]
    have hm := tsz_len_msg enc t m
    have hfm := hf m
    omega

private theorem tsz_len_auth (a : ProtoAuthenticator) :
    (ProtoAuthenticator.encodeRaw a).length ≤ rawAuth a + 44 := by
  simp only [ProtoAuthenticator.encodeRaw, List.length_append, rawAuth]
  have h1 := tsz_len_bytes 1#32 a.rootKey
  have h2 := tsz_len_bytes 2#32 a.macKey
  omega

private theorem tsz_len_polyEnc (pe : PolynomialEncoder) :
    (PolynomialEncoder.encodeRaw pe).length ≤ rawPolyEnc pe + 22 := by
  simp only [PolynomialEncoder.encodeRaw, List.length_append, rawPolyEnc]
  have h1 := tsz_len_uint32 1#32 pe.idx
  have h2 := tsz_len_repBytes 2#32 pe.pts
  have h3 := tsz_len_repBytes 3#32 pe.polys
  omega

private theorem tsz_len_polyDec (pd : PolynomialDecoder) :
    (PolynomialDecoder.encodeRaw pd).length ≤ rawPolyDec pd + 56 := by
  simp only [PolynomialDecoder.encodeRaw, List.length_append, rawPolyDec]
  have h1 := tsz_len_uint32 1#32 pd.ptsNeeded
  have h2 := tsz_len_uint32 2#32 pd.polys
  have h3 := tsz_len_repBytes 3#32 pd.pts
  have h4 := tsz_len_bool 4#32 pd.isComplete
  omega

private theorem tsz_len_chainParams (cp : ChainParamsPB) :
    (ChainParamsPB.encodeRaw cp).length ≤ (fun _ => 0) cp + 44 := by
  simp only [ChainParamsPB.encodeRaw, List.length_append]
  have h1 := tsz_len_uint32 1#32 cp.maxJump
  have h2 := tsz_len_uint32 2#32 cp.maxOooKeys
  omega

private theorem tsz_len_vn (vn : VersionNegotiationPB) :
    (VersionNegotiationPB.encodeRaw vn).length ≤ rawVN vn + 132 := by
  simp only [VersionNegotiationPB.encodeRaw, List.length_append, rawVN]
  have h1 := tsz_len_bytes 1#32 vn.authKey
  have h2 := tsz_len_int32 2#32 vn.direction
  have h3 := tsz_len_int32 3#32 vn.minVersion
  have h4 := tsz_len_optMsg ChainParamsPB.encodeRaw (fun _ => 0) 44 tsz_len_chainParams 4#32 vn.chainParams
  have h4' : optRaw (fun _ => 0) vn.chainParams = 0 := by cases vn.chainParams <;> rfl
  omega

private theorem tsz_len_epochDir (ed : EpochDirectionPB) :
    (EpochDirectionPB.encodeRaw ed).length ≤ rawEpochDir ed + 66 := by
  simp only [EpochDirectionPB.encodeRaw, List.length_append, rawEpochDir]
  have h1 := tsz_len_uint32 1#32 ed.ctr
  have h2 := tsz_len_bytes 2#32 ed.next
  have h3 := tsz_len_bytes 3#32 ed.prev
  omega

private theorem tsz_len_chainEpoch (ep : ChainEpochPB) :
    (ChainEpochPB.encodeRaw ep).length + 22 ≤ rawChainEpoch ep + 200 := by
  simp only [ChainEpochPB.encodeRaw, List.length_append, rawChainEpoch]
  have h1 := tsz_len_optMsg EpochDirectionPB.encodeRaw rawEpochDir 66 tsz_len_epochDir 1#32 ep.send
  have h2 := tsz_len_optMsg EpochDirectionPB.encodeRaw rawEpochDir 66 tsz_len_epochDir 2#32 ep.recv
  omega

private theorem tsz_len_chain (ch : ChainPB) :
    (ChainPB.encodeRaw ch).length ≤ rawChain ch + 154 := by
  simp only [ChainPB.encodeRaw, List.length_append, rawChain]
  have h1 := tsz_len_int32 1#32 ch.direction
  have h2 := tsz_len_uint64 2#32 ch.currentEpoch
  have h3 := tsz_len_repMsg ChainEpochPB.encodeRaw (fun ep => rawChainEpoch ep + 200) tsz_len_chainEpoch 3#32 ch.links
  have h4 := tsz_len_bytes 4#32 ch.nextRoot
  have h5 := tsz_len_uint64 5#32 ch.sendEpoch
  have h6 := tsz_len_optMsg ChainParamsPB.encodeRaw (fun _ => 0) 44 tsz_len_chainParams 6#32 ch.params
  have h6' : optRaw (fun _ => 0) ch.params = 0 := by cases ch.params <;> rfl
  omega

private theorem tsz_len_ucKeysUnsampled (m : V1State.Unchunked.KeysUnsampled) :
    (V1State.Unchunked.KeysUnsampled.encodeRaw m).length ≤ rawUcKeysUnsampled m + 88 := by
  simp only [V1State.Unchunked.KeysUnsampled.encodeRaw, List.length_append, rawUcKeysUnsampled]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  omega

private theorem tsz_len_ucHeaderSent (m : V1State.Unchunked.HeaderSent) :
    (V1State.Unchunked.HeaderSent.encodeRaw m).length ≤ rawUcHeaderSent m + 132 := by
  simp only [V1State.Unchunked.HeaderSent.encodeRaw, List.length_append, rawUcHeaderSent]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  have h3 := tsz_len_bytes 3#32 m.ek
  have h4 := tsz_len_bytes 4#32 m.dk
  omega

private theorem tsz_len_ucEkSent (m : V1State.Unchunked.EkSent) :
    (V1State.Unchunked.EkSent.encodeRaw m).length ≤ rawUcEkSent m + 110 := by
  simp only [V1State.Unchunked.EkSent.encodeRaw, List.length_append, rawUcEkSent]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  have h3 := tsz_len_bytes 3#32 m.dk
  omega

private theorem tsz_len_ucEkSentCt1Received (m : V1State.Unchunked.EkSentCt1Received) :
    (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length ≤ rawUcEkSentCt1Received m + 132 := by
  simp only [V1State.Unchunked.EkSentCt1Received.encodeRaw, List.length_append, rawUcEkSentCt1Received]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  have h3 := tsz_len_bytes 3#32 m.dk
  have h4 := tsz_len_bytes 4#32 m.ct1
  omega

private theorem tsz_len_ucNoHeaderReceived (m : V1State.Unchunked.NoHeaderReceived) :
    (V1State.Unchunked.NoHeaderReceived.encodeRaw m).length ≤ rawUcNoHeaderReceived m + 88 := by
  simp only [V1State.Unchunked.NoHeaderReceived.encodeRaw, List.length_append, rawUcNoHeaderReceived]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  omega

private theorem tsz_len_ucHeaderReceived (m : V1State.Unchunked.HeaderReceived) :
    (V1State.Unchunked.HeaderReceived.encodeRaw m).length ≤ rawUcHeaderReceived m + 110 := by
  simp only [V1State.Unchunked.HeaderReceived.encodeRaw, List.length_append, rawUcHeaderReceived]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  have h3 := tsz_len_bytes 3#32 m.hdr
  omega

private theorem tsz_len_ucCt1Sent (m : V1State.Unchunked.Ct1Sent) :
    (V1State.Unchunked.Ct1Sent.encodeRaw m).length ≤ rawUcCt1Sent m + 154 := by
  simp only [V1State.Unchunked.Ct1Sent.encodeRaw, List.length_append, rawUcCt1Sent]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  have h3 := tsz_len_bytes 3#32 m.hdr
  have h4 := tsz_len_bytes 4#32 m.es
  have h5 := tsz_len_bytes 5#32 m.ct1
  omega

private theorem tsz_len_ucCt1SentEkReceived (m : V1State.Unchunked.Ct1SentEkReceived) :
    (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m).length ≤ rawUcCt1SentEkReceived m + 154 := by
  simp only [V1State.Unchunked.Ct1SentEkReceived.encodeRaw, List.length_append, rawUcCt1SentEkReceived]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  have h3 := tsz_len_bytes 3#32 m.es
  have h4 := tsz_len_bytes 4#32 m.ek
  have h5 := tsz_len_bytes 5#32 m.ct1
  omega

private theorem tsz_len_ucCt2Sent (m : V1State.Unchunked.Ct2Sent) :
    (V1State.Unchunked.Ct2Sent.encodeRaw m).length ≤ rawUcCt2Sent m + 88 := by
  simp only [V1State.Unchunked.Ct2Sent.encodeRaw, List.length_append, rawUcCt2Sent]
  have h1 := tsz_len_uint64 1#32 m.epoch
  have h2 := tsz_len_optMsg ProtoAuthenticator.encodeRaw rawAuth 44 tsz_len_auth 2#32 m.auth
  omega

private theorem tsz_len_innerState (is : V1State.InnerState) :
    (V1State.InnerState.encode is).length ≤ rawInnerState is + 320 := by
  cases is with
  | keysUnsampled v =>
    have hm := tsz_len_msg V1State.Chunked.KeysUnsampled.encodeRaw 1#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.KeysUnsampled.encodeRaw rawUcKeysUnsampled 88
      tsz_len_ucKeysUnsampled 1#32 v.uc
    simp only [V1State.InnerState.encode, V1State.Chunked.KeysUnsampled.encodeRaw,
      rawInnerState, rawChKeysUnsampled] at hm ⊢
    omega
  | keysSampled v =>
    have hm := tsz_len_msg V1State.Chunked.KeysSampled.encodeRaw 2#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.HeaderSent.encodeRaw rawUcHeaderSent 132
      tsz_len_ucHeaderSent 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialEncoder.encodeRaw rawPolyEnc 22 tsz_len_polyEnc 2#32 v.sendingHdr
    simp only [V1State.InnerState.encode, V1State.Chunked.KeysSampled.encodeRaw,
      List.length_append, rawInnerState, rawChKeysSampled] at hm ⊢
    omega
  | headerSent v =>
    have hm := tsz_len_msg V1State.Chunked.HeaderSent.encodeRaw 3#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.EkSent.encodeRaw rawUcEkSent 110
      tsz_len_ucEkSent 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialEncoder.encodeRaw rawPolyEnc 22 tsz_len_polyEnc 2#32 v.sendingEk
    have h3 := tsz_len_optMsg PolynomialDecoder.encodeRaw rawPolyDec 56 tsz_len_polyDec 3#32 v.receivingCt1
    simp only [V1State.InnerState.encode, V1State.Chunked.HeaderSent.encodeRaw,
      List.length_append, rawInnerState, rawChHeaderSent] at hm ⊢
    omega
  | ct1Received v =>
    have hm := tsz_len_msg V1State.Chunked.Ct1Received.encodeRaw 4#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received 132
      tsz_len_ucEkSentCt1Received 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialEncoder.encodeRaw rawPolyEnc 22 tsz_len_polyEnc 2#32 v.sendingEk
    simp only [V1State.InnerState.encode, V1State.Chunked.Ct1Received.encodeRaw,
      List.length_append, rawInnerState, rawChCt1Received] at hm ⊢
    omega
  | ekSentCt1Received v =>
    have hm := tsz_len_msg V1State.Chunked.EkSentCt1Received.encodeRaw 5#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received 132
      tsz_len_ucEkSentCt1Received 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialDecoder.encodeRaw rawPolyDec 56 tsz_len_polyDec 3#32 v.receivingCt2
    simp only [V1State.InnerState.encode, V1State.Chunked.EkSentCt1Received.encodeRaw,
      List.length_append, rawInnerState, rawChEkSentCt1Received] at hm ⊢
    omega
  | noHeaderReceived v =>
    have hm := tsz_len_msg V1State.Chunked.NoHeaderReceived.encodeRaw 6#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.NoHeaderReceived.encodeRaw rawUcNoHeaderReceived 88
      tsz_len_ucNoHeaderReceived 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialDecoder.encodeRaw rawPolyDec 56 tsz_len_polyDec 2#32 v.receivingHdr
    simp only [V1State.InnerState.encode, V1State.Chunked.NoHeaderReceived.encodeRaw,
      List.length_append, rawInnerState, rawChNoHeaderReceived] at hm ⊢
    omega
  | headerReceived v =>
    have hm := tsz_len_msg V1State.Chunked.HeaderReceived.encodeRaw 7#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.HeaderReceived.encodeRaw rawUcHeaderReceived 110
      tsz_len_ucHeaderReceived 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialDecoder.encodeRaw rawPolyDec 56 tsz_len_polyDec 2#32 v.receivingEk
    simp only [V1State.InnerState.encode, V1State.Chunked.HeaderReceived.encodeRaw,
      List.length_append, rawInnerState, rawChHeaderReceived] at hm ⊢
    omega
  | ct1Sampled v =>
    have hm := tsz_len_msg V1State.Chunked.Ct1Sampled.encodeRaw 8#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent 154
      tsz_len_ucCt1Sent 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialEncoder.encodeRaw rawPolyEnc 22 tsz_len_polyEnc 2#32 v.sendingCt1
    have h3 := tsz_len_optMsg PolynomialDecoder.encodeRaw rawPolyDec 56 tsz_len_polyDec 3#32 v.receivingEk
    simp only [V1State.InnerState.encode, V1State.Chunked.Ct1Sampled.encodeRaw,
      List.length_append, rawInnerState, rawChCt1Sampled] at hm ⊢
    omega
  | ekReceivedCt1Sampled v =>
    have hm := tsz_len_msg V1State.Chunked.EkReceivedCt1Sampled.encodeRaw 9#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.Ct1SentEkReceived.encodeRaw rawUcCt1SentEkReceived 154
      tsz_len_ucCt1SentEkReceived 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialEncoder.encodeRaw rawPolyEnc 22 tsz_len_polyEnc 2#32 v.sendingCt1
    simp only [V1State.InnerState.encode, V1State.Chunked.EkReceivedCt1Sampled.encodeRaw,
      List.length_append, rawInnerState, rawChEkReceivedCt1Sampled] at hm ⊢
    omega
  | ct1Acknowledged v =>
    have hm := tsz_len_msg V1State.Chunked.Ct1Acknowledged.encodeRaw 10#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent 154
      tsz_len_ucCt1Sent 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialDecoder.encodeRaw rawPolyDec 56 tsz_len_polyDec 2#32 v.receivingEk
    simp only [V1State.InnerState.encode, V1State.Chunked.Ct1Acknowledged.encodeRaw,
      List.length_append, rawInnerState, rawChCt1Acknowledged] at hm ⊢
    omega
  | ct2Sampled v =>
    have hm := tsz_len_msg V1State.Chunked.Ct2Sampled.encodeRaw 11#32 v
    have h1 := tsz_len_optMsg V1State.Unchunked.Ct2Sent.encodeRaw rawUcCt2Sent 88
      tsz_len_ucCt2Sent 1#32 v.uc
    have h2 := tsz_len_optMsg PolynomialEncoder.encodeRaw rawPolyEnc 22 tsz_len_polyEnc 2#32 v.sendingCt2
    simp only [V1State.InnerState.encode, V1State.Chunked.Ct2Sampled.encodeRaw,
      List.length_append, rawInnerState, rawChCt2Sampled] at hm ⊢
    omega

private theorem tsz_len_v1State (v : V1State) :
    (V1State.encodeRaw v).length ≤ rawV1State v + 320 := by
  simp only [V1State.encodeRaw, rawV1State]
  cases v.innerState with
  | none => simp [optRaw]
  | some is =>
    simp only [optRaw]
    exact tsz_len_innerState is

private theorem tsz_topBytes_length_le (F : ShaCompress) (K : MlKem) (st : St F)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) :
    (topBytes F K st vn? ch?).length ≤
      optRaw rawVN vn? + optRaw rawChain (ch?.map Chain.intoPb) + rawV1State st.into_pb + 752 := by
  simp only [topBytes, spqrDeps, topPb, pbToPqRatchetState, Proto.encodeState,
    PqRatchetState.encode, PqRatchetState.encodeRaw, Option.map_some,
    PqRatchetState.Inner.encode, List.length_append]
  have h1 := tsz_len_optMsg VersionNegotiationPB.encodeRaw rawVN 132 tsz_len_vn 1#32 vn?
  have h2 := tsz_len_optMsg ChainPB.encodeRaw rawChain 154 tsz_len_chain 2#32 (ch?.map Chain.intoPb)
  have h3 := tsz_len_msg V1State.encodeRaw 3#32 st.into_pb
  have h4 := tsz_len_v1State st.into_pb
  omega

theorem st_topSize (F : ShaCompress) (K : MlKem) (hBS : BSizeStmt F) : TopSizeStmt F K := by
  rintro n bytes ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ hn
  have htb := tsz_topBytes_length_le F K st vn? ch?
  rw [← hw.htop.hbytes] at htb
  have hvn_le : optRaw rawVN vn? ≤ 32 := by
    rcases hw.htop.hvn with rfl | rfl
    · simp [optRaw]
    · simp [optRaw, vnOf, rawVN, hw.hauth]
  have hbraid_le : rawV1State st.into_pb ≤ 2 ^ 40 := hBS st hw.hbok
  have hch_le : optRaw rawChain (ch?.map Chain.intoPb) ≤ 2 ^ 32 * (2 ^ 20 + 264) + 32 := by
    rcases hw.htop.hch with rfl | ⟨rfl, _, _⟩
    · simp only [Option.map_some, optRaw, rawChain, Chain.intoPb, List.map_map]
      have hroot_le : chE.nextRoot.length ≤ 32 := by
        rw [hw.htop.hok.hroot]
        exact List.length_take_le _ _
      have hsum_le :
          (chE.links.map
              ((fun ep => rawChainEpoch ep + 200) ∘
                fun link => { send := some link.send.intoPb, recv := some link.recv.intoPb })).sum ≤
            chE.links.length * (2 ^ 20 + 264) := by
        apply tsz_sum_map_le
        intro l hl
        simp only [Function.comp_apply, rawChainEpoch, optRaw]
        exact tsz_link_le F authKey dir secret sendCtr recvSet chE
          hw.htop.hok hw.htop.hsendPrev hw.hsmall l hl
      have hlinks_len : chE.links.length ≤ 2 ^ 32 := by
        have hlen := hw.htop.hok.hlen
        have hcur := hw.htop.hcur
        have hcphi := tsz_chainCur_le_phiB st
        have hphi := hw.hphi
        omega
      have hmul : chE.links.length * (2 ^ 20 + 264) ≤ 2 ^ 32 * (2 ^ 20 + 264) :=
        Nat.mul_le_mul_right _ hlinks_len
      omega
    · simp [optRaw]
  omega

end CryptoVerification.SpqrV1Sync.SendTotal
