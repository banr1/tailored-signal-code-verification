/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

/-!
# CT-Side Braid Well-Formedness Under Adversarial Receives

Proves that `States.recv` preserves `BOk` on all six CT-side braid variants (`st_bRecvCt`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoGames.LibsignalSession (ShaCompress)

private theorem brct_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem brct_ofPanic_ok {α : Type} {x : Except StatesPanic α} {v : α}
    (h : StatesResult.ofPanic x = .ok v) : x = .ok v := by
  cases x with
  | error p => cases h
  | ok a =>
    dsimp only [StatesResult.ofPanic, Except.mapError] at h
    cases h
    rfl

private theorem brct_addChunk_res {d d' : PolyDecoder} {c : Chunk}
    (h : StatesResult.ofPanic (spqrPolyApi.add_chunk d c) = .ok d') :
    d.addChunk c = .ok d' := by
  cases ha : d.addChunk c with
  | error p =>
    rw [show spqrPolyApi.add_chunk d c = .error p.toSpqrPanic by
      simp [spqrPolyApi, ha, Except.mapError]] at h
    cases h
  | ok v =>
    rw [show spqrPolyApi.add_chunk d c = .ok v by
      simp [spqrPolyApi, ha, Except.mapError]] at h
    dsimp only [StatesResult.ofPanic, Except.mapError] at h
    cases h
    rfl

private theorem brct_decodedMessage_res {d : PolyDecoder} {out : Option Bytes}
    (h : StatesResult.ofPanic (spqrPolyApi.decoded_message d) = .ok out) :
    d.decodedMessage = .ok out := by
  cases hd : d.decodedMessage with
  | error p =>
    rw [show spqrPolyApi.decoded_message d = .error p.toSpqrPanic by
      simp [spqrPolyApi, hd, Except.mapError]] at h
    cases h
  | ok v =>
    rw [show spqrPolyApi.decoded_message d = .ok v by
      simp [spqrPolyApi, hd, Except.mapError]] at h
    dsimp only [StatesResult.ofPanic, Except.mapError] at h
    cases h
    rfl

private theorem brct_decoder_new_res (hDF : DecFreshStmt) (len : ℕ) (heven : len % 2 = 0)
    {res : Except EncodingError PolyDecoder} {d : PolyDecoder}
    (h1 : StatesResult.ofPanic (spqrPolyApi.decoder_new len) = .ok res)
    (h2 : res = .ok d) : DecWF (len / 2) d := by
  rcases hDF len heven with ⟨d0, hd0, hwf⟩
  rw [show spqrPolyApi.decoder_new len = .ok (.ok d0) by
    simp [spqrPolyApi, hd0, Except.mapError]] at h1
  dsimp only [StatesResult.ofPanic, Except.mapError] at h1
  cases h1
  cases h2
  exact hwf

private theorem brct_expectEncodeBytes (hEN : EncNewStmt) (site : String) (msg : Bytes)
    (heven : msg.length % 2 = 0) (hle : msg.length ≤ 2 ^ 20) {e : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok e) : EncWF msg.length e := by
  rcases hEN msg heven hle with ⟨e0, he0, hwf⟩
  dsimp only [expectEncodeBytes, spqrPolyApi, Bind.bind, Except.bind, Except.mapError] at h
  rw [he0] at h
  cases h
  exact hwf

private theorem brct_encaps2_len (K : MlKem) (ek es ct2 : Bytes)
    (h : encaps2 K ek es = .ok ct2) : ct2.length = 128 := by
  unfold encaps2 at h
  rcases brct_bind_ok h with ⟨maybeFix, _, h1⟩
  cases hb1 : bytesToVector? ENCAPSULATION_STATE_SIZE (maybeFix.getD es) <;>
    cases hb2 : bytesToVector? ENCAPSULATION_KEY_SIZE ek <;>
    simp only [hb1, hb2] at h1 <;>
    cases h1
  exact List.Vector.toList_length _

private theorem brct_macCt_len (F : ShaCompress) (a : Authenticator) (ep : Epoch) (ct mac : Bytes)
    (h : (liftM ((spqrAuthApi F).mac_ct a ep ct) : Except StatesPanic Bytes) = .ok mac) :
    mac.length = 32 := by
  dsimp only [spqrAuthApi, Authenticator.macCt] at h
  split at h
  · cases h
    exact Authenticator.length_macCtUnchecked F a ep ct
  · cases h

private theorem brct_send_ct2 (F : ShaCompress) (K : MlKem) (hEN : EncNewStmt)
    (u : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) (hauth : AuthOk u.auth)
    {u' : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)} {ct2 mac : Bytes} {enc : PolyEncoder}
    (hs : u.send_ct2 K = .ok (u', ct2, mac))
    (he : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc) :
    AuthOk u'.auth ∧ EncWF 160 enc := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at hs
  rcases brct_bind_ok hs with ⟨ct2_0, hct2, hs1⟩
  rcases brct_bind_ok hs1 with ⟨mac_0, hmac, hs2⟩
  cases hs2
  have hlen_ct2 : ct2.length = 128 := brct_encaps2_len K u.ek u.es ct2 hct2
  have hlen_mac : mac.length = 32 := brct_macCt_len F u.auth u.epoch (u.ct1 ++ ct2) mac hmac
  have hlen_full : (ct2 ++ mac).length = 160 := by
    rw [List.length_append, hlen_ct2, hlen_mac]
  have henc : EncWF (ct2 ++ mac).length enc :=
    brct_expectEncodeBytes hEN _ (ct2 ++ mac) (by omega) (by omega) he
  rw [hlen_full] at henc
  exact ⟨hauth, henc⟩

private theorem brct_uc_recv_ek (F : ShaCompress) (K : MlKem)
    (u : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (hauth : AuthOk u.auth)
    (huc : Codec.UcOk.ctCt1Sent u) (ep : Epoch) (ek : Bytes)
    (hek_len : ek.length = ENCAPSULATION_KEY_SIZE)
    {u' : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    (h : u.recv_ek K ep ek = .ok u') :
    AuthOk u'.auth ∧ Codec.UcOk.ctCt1SentEkReceived u' := by
  unfold Unchunked.SendCt.Ct1Sent.recv_ek at h
  split at h
  · cases h
  · split at h
    · cases h
      exact ⟨hauth, ⟨huc.2.1, huc.2.2, hek_len⟩⟩
    · cases h

/-- Any successful `States.recv` on a CT-side state (`isEkSide st = false`) preserves `BOk`. -/
theorem st_bRecvCt (F : ShaCompress) (K : MlKem) (hDF : DecFreshStmt) (hDA : DecAddStmt)
    (hDM : DecMsgStmt) (hEN : EncNewStmt) : BRecvCtStmt F K := by
  intro st st' m key hek hbok hrecv
  cases st with
  | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _ | ekSentCt1Received _ =>
    cases hek
  | noHeaderReceived state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases hlt : m.epoch < state.epoch
      · simp only [hlt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
      · simp only [hlt, ↓reduceIte] at hrecv
        cases hp : m.payload with
        | hdr chunk =>
          rw [hp] at hrecv
          rcases brct_bind_ok hrecv with ⟨res, hrc, hout⟩
          unfold Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at hrc
          by_cases hne : (m.epoch != state.uc.epoch) = true
          · rw [hne] at hrc; cases hrc
          · simp only [Bool.not_eq_true] at hne
            rw [hne] at hrc
            rcases brct_bind_ok hrc with ⟨d1, hd1, hrc1⟩
            rcases brct_bind_ok hrc1 with ⟨decoded?, hdm, hrc2⟩
            rcases hbok with ⟨hauth, hdec⟩
            have hwf1 : DecWF 48 d1 :=
              hDA 48 state.receiving_hdr d1 chunk hdec (brct_addChunk_res hd1)
            cases decoded? with
            | none =>
              cases hrc2
              cases hout
              exact ⟨hauth, hwf1⟩
            | some hdrFull =>
              by_cases hlen : hdrFull.length < HEADER_SIZE
              · simp only [hlen, ↓reduceIte] at hrc2; cases hrc2
              · simp only [hlen, ↓reduceIte] at hrc2
                rcases brct_bind_ok hrc2 with ⟨receivingEkRes, hdnew, hrc3⟩
                rcases brct_bind_ok hrc3 with ⟨uc, huc, hrc4⟩
                cases receivingEkRes with
                | error _ => cases hrc4
                | ok receivingEk =>
                  cases hrc4
                  cases hout
                  have hwf_ek : DecWF 576 receivingEk :=
                    brct_decoder_new_res hDF ENCAPSULATION_KEY_SIZE (by decide) hdnew rfl
                  have hfull_len : hdrFull.length = 96 :=
                    hDM 48 d1 hdrFull hwf1 (brct_decodedMessage_res hdm)
                  unfold Unchunked.SendCt.NoHeaderReceived.recv_header at huc
                  by_cases hne2 : (m.epoch != state.uc.epoch) = true
                  · rw [hne2] at huc; cases huc
                  · simp only [Bool.not_eq_true] at hne2
                    rw [hne2] at huc
                    rcases brct_bind_ok huc with ⟨verifyRes, _, huc2⟩
                    cases verifyRes with
                    | error _ => cases huc2
                    | ok _ =>
                      cases huc2
                      have hhdr_len : (hdrFull.take HEADER_SIZE).length = HEADER_SIZE := by
                        simp [HEADER_SIZE, hfull_len]
                      exact ⟨hauth, hhdr_len, hwf_ek⟩
        | none | ek _ | ekCt1Ack _ | ct1Ack _ | ct1 _ | ct2 _ =>
          rw [hp] at hrecv; cases hrecv; exact hbok
  | headerReceived state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
  | ct1Sampled state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases hlt : m.epoch < state.epoch
      · simp only [hlt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
      · simp only [hlt, ↓reduceIte] at hrecv
        split at hrecv
        · cases hrecv; exact hbok
        · rename_i chunk ack _
          rcases brct_bind_ok hrecv with ⟨res, hrc, hout⟩
          unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk at hrc
          rcases brct_bind_ok hrc with ⟨d1, hd1, hrc1⟩
          rcases brct_bind_ok hrc1 with ⟨decoded?, hdm, hrc2⟩
          rcases hbok with ⟨hauth, huc, henc, hdec⟩
          have hwf1 : DecWF 576 d1 :=
            hDA 576 state.receiving_ek d1 chunk hdec (brct_addChunk_res hd1)
          cases decoded? with
          | none =>
            cases ack with
            | true =>
              cases hrc2; cases hout
              exact ⟨hauth, huc, hwf1⟩
            | false =>
              cases hrc2; cases hout
              exact ⟨hauth, huc, henc, hwf1⟩
          | some decoded =>
            rcases brct_bind_ok hrc2 with ⟨uc1, huc1, hrc3⟩
            have hek_len : decoded.length = ENCAPSULATION_KEY_SIZE :=
              hDM 576 d1 decoded hwf1 (brct_decodedMessage_res hdm)
            rcases brct_uc_recv_ek F K state.uc hauth huc m.epoch decoded hek_len huc1 with
              ⟨hauth1, huc1_ok⟩
            cases ack with
            | false =>
              cases hrc3; cases hout
              exact ⟨hauth1, huc1_ok, henc⟩
            | true =>
              rcases brct_bind_ok hrc3 with ⟨⟨uc2, ct2, mac⟩, hsct2, hrc4⟩
              rcases brct_bind_ok hrc4 with ⟨sendingCt2, henc2, hrc5⟩
              cases hrc5; cases hout
              exact brct_send_ct2 F K hEN uc1 hauth1
                (brct_ofPanic_ok hsct2) (brct_ofPanic_ok henc2)
  | ekReceivedCt1Sampled state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases hlt : m.epoch < state.epoch
      · simp only [hlt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
      · simp only [hlt, ↓reduceIte] at hrecv
        suffices hack_step :
            (do
              let s' ← StatesResult.ofPanic (state.recv_ct1_ack K m.epoch)
              (.ok { key := none, state := .ct2Sampled s' } : StatesResult (V1Recv spqrPolyApi (spqrAuthApi F)))) =
                .ok { key := key, state := st' } → BOk st' by
          cases hp : m.payload with
          | ct1Ack b =>
            cases b with
            | false => rw [hp] at hrecv; cases hrecv; exact hbok
            | true => rw [hp] at hrecv; exact hack_step hrecv
          | ekCt1Ack _ => rw [hp] at hrecv; exact hack_step hrecv
          | none | hdr _ | ek _ | ct1 _ | ct2 _ =>
            rw [hp] at hrecv; cases hrecv; exact hbok
        intro hdo
        rcases brct_bind_ok hdo with ⟨s', hs', hout⟩
        cases hout
        have hrc := brct_ofPanic_ok hs'
        unfold Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at hrc
        by_cases hne : (m.epoch != state.uc.epoch) = true
        · rw [hne] at hrc; cases hrc
        · simp only [Bool.not_eq_true] at hne
          rw [hne] at hrc
          rcases brct_bind_ok hrc with ⟨⟨uc2, ct2, mac⟩, hsct2, hrc2⟩
          rcases brct_bind_ok hrc2 with ⟨sendingCt2, henc2, hrc3⟩
          cases hrc3
          exact brct_send_ct2 F K hEN state.uc hbok.1 hsct2 henc2
  | ct1Acknowledged state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases hlt : m.epoch < state.epoch
      · simp only [hlt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
      · simp only [hlt, ↓reduceIte] at hrecv
        split at hrecv
        · cases hrecv; exact hbok
        · rename_i chunk _
          rcases brct_bind_ok hrecv with ⟨res, hrc, hout⟩
          unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at hrc
          rcases brct_bind_ok hrc with ⟨d1, hd1, hrc1⟩
          rcases brct_bind_ok hrc1 with ⟨decoded?, hdm, hrc2⟩
          rcases hbok with ⟨hauth, huc, hdec⟩
          have hwf1 : DecWF 576 d1 :=
            hDA 576 state.receiving_ek d1 chunk hdec (brct_addChunk_res hd1)
          cases decoded? with
          | none =>
            cases hrc2; cases hout
            exact ⟨hauth, huc, hwf1⟩
          | some decoded =>
            rcases brct_bind_ok hrc2 with ⟨uc1, huc1, hrc3⟩
            rcases brct_bind_ok hrc3 with ⟨⟨uc2, ct2, mac⟩, hsct2, hrc4⟩
            rcases brct_bind_ok hrc4 with ⟨sendingCt2, henc2, hrc5⟩
            cases hrc5; cases hout
            have hek_len : decoded.length = ENCAPSULATION_KEY_SIZE :=
              hDM 576 d1 decoded hwf1 (brct_decodedMessage_res hdm)
            rcases brct_uc_recv_ek F K state.uc hauth huc m.epoch decoded hek_len huc1 with
              ⟨hauth1, _⟩
            exact brct_send_ct2 F K hEN uc1 hauth1
              (brct_ofPanic_ok hsct2) (brct_ofPanic_ok henc2)
  | ct2Sampled state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases heq : (m.epoch == state.epoch + 1#64) = true
      · rw [heq] at hrecv
        rcases brct_bind_ok hrecv with ⟨s', hs', hout⟩
        cases hout
        have hrc := brct_ofPanic_ok hs'
        unfold Chunked.SendCt.Ct2Sampled.recv_next_epoch at hrc
        rcases brct_bind_ok hrc with ⟨uc, huc, hrc2⟩
        cases hrc2
        unfold Unchunked.SendCt.Ct2Sent.recv_next_epoch at huc
        split at huc
        · cases huc
        · change (if (state.uc.epoch + 1#64 != m.epoch) = true then _ else _) = _ at huc
          split at huc
          · cases huc
          · cases huc
            exact hbok.1
      · simp only [Bool.not_eq_true] at heq
        rw [heq] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv; exact hbok

end CryptoVerification.SpqrV1Sync.SendTotal
