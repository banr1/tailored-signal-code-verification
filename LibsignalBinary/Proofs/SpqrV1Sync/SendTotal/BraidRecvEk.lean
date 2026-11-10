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
# EK-Side Braid Well-Formedness Under Adversarial Receives

Proves that `States.recv` preserves `BOk` on all five EK-side braid variants (`st_bRecvEk`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoGames.LibsignalSession (ShaCompress)

private theorem brek_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem brek_ofPanic_ok {α : Type} {x : Except StatesPanic α} {v : α}
    (h : StatesResult.ofPanic x = .ok v) : x = .ok v := by
  cases x with
  | error p => cases h
  | ok a =>
    dsimp only [StatesResult.ofPanic, Except.mapError] at h
    cases h
    rfl

private theorem brek_expectDecoderNew (hDF : DecFreshStmt) (site : String) (len : ℕ)
    (heven : len % 2 = 0) {d : PolyDecoder}
    (h : expectDecoderNew spqrPolyApi site len = .ok d) : DecWF (len / 2) d := by
  rcases hDF len heven with ⟨d0, hd0, hwf⟩
  dsimp only [expectDecoderNew, spqrPolyApi, Bind.bind, Except.bind, Except.mapError] at h
  rw [hd0] at h
  cases h
  exact hwf

private theorem brek_expectEncodeBytes (hEN : EncNewStmt) (site : String) (msg : Bytes)
    (heven : msg.length % 2 = 0) (hle : msg.length ≤ 2 ^ 20) {e : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok e) : EncWF msg.length e := by
  rcases hEN msg heven hle with ⟨e0, he0, hwf⟩
  dsimp only [expectEncodeBytes, spqrPolyApi, Bind.bind, Except.bind, Except.mapError] at h
  rw [he0] at h
  cases h
  exact hwf

private theorem brek_addChunk_lift {d d' : PolyDecoder} {c : Chunk}
    (h : (liftM (spqrPolyApi.add_chunk d c) : Except StatesPanic PolyDecoder) = .ok d') :
    d.addChunk c = .ok d' := by
  cases ha : d.addChunk c with
  | error p =>
    rw [show spqrPolyApi.add_chunk d c = .error p.toSpqrPanic by
      simp [spqrPolyApi, ha, Except.mapError]] at h
    cases h
  | ok v =>
    rw [show spqrPolyApi.add_chunk d c = .ok v by
      simp [spqrPolyApi, ha, Except.mapError]] at h
    cases h
    rfl

private theorem brek_addChunk_res {d d' : PolyDecoder} {c : Chunk}
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

private theorem brek_decodedMessage_lift {d : PolyDecoder} {out : Option Bytes}
    (h : (liftM (spqrPolyApi.decoded_message d) : Except StatesPanic (Option Bytes)) = .ok out) :
    d.decodedMessage = .ok out := by
  cases hd : d.decodedMessage with
  | error p =>
    rw [show spqrPolyApi.decoded_message d = .error p.toSpqrPanic by
      simp [spqrPolyApi, hd, Except.mapError]] at h
    cases h
  | ok v =>
    rw [show spqrPolyApi.decoded_message d = .ok v by
      simp [spqrPolyApi, hd, Except.mapError]] at h
    cases h
    rfl

private theorem brek_authOk_update (F : ShaCompress) (a : Authenticator) (ep : Epoch)
    (k : Bytes) : AuthOk (a.update F ep k) := by
  simp [AuthOk, Authenticator.update, hkdfToVecUnchecked, hkdfToSliceUnchecked]

private theorem brek_uc_recv_ct2 (F : ShaCompress) (K : MlKem)
    (u : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (ct2 mac : Bytes)
    {u' : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F)} {sec : EpochSecret}
    (h : u.recv_ct2 K ct2 mac = .ok (u', sec)) : AuthOk u'.auth := by
  unfold Unchunked.SendEk.EkSentCt1Received.recv_ct2 at h
  rcases brek_bind_ok h with ⟨ss0, _, h1⟩
  rcases brek_bind_ok h1 with ⟨ss, _, h2⟩
  rcases brek_bind_ok h2 with ⟨auth, hauth_step, h3⟩
  dsimp only [StatesResult.ofPanic, spqrAuthApi, Except.mapError] at hauth_step
  cases hauth_step
  rcases brek_bind_ok h3 with ⟨verifyRes, _, h4⟩
  cases verifyRes with
  | error _ => cases h4
  | ok u0 =>
    cases u0
    by_cases hov : (u.epoch == BitVec.allOnes 64) = true
    · change (if (u.epoch == BitVec.allOnes 64) = true then _ else _) = _ at h4
      rw [hov] at h4
      cases h4
    · simp only [Bool.not_eq_true] at hov
      change (if (u.epoch == BitVec.allOnes 64) = true then _ else _) = _ at h4
      rw [hov] at h4
      cases h4
      exact brek_authOk_update F u.auth u.epoch ss

/-- Any successful `States.recv` on an EK-side state (`isEkSide st = true`) preserves `BOk`. -/
theorem st_bRecvEk (F : ShaCompress) (K : MlKem) (hDF : DecFreshStmt) (hDA : DecAddStmt)
    (hDM : DecMsgStmt) (hEN : EncNewStmt) : BRecvEkStmt F K := by
  intro st st' m key hek hbok hrecv
  cases st with
  | noHeaderReceived _ | headerReceived _ | ct1Sampled _
  | ekReceivedCt1Sampled _ | ct1Acknowledged _ | ct2Sampled _ =>
    cases hek
  | keysUnsampled state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      cases hrecv
      exact hbok
  | keysSampled state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases hlt : m.epoch < state.epoch
      · simp only [hlt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
      · simp only [hlt, ↓reduceIte] at hrecv
        cases hp : m.payload with
        | ct1 chunk =>
          rw [hp] at hrecv
          rcases brek_bind_ok hrecv with ⟨s', hs', hout⟩
          cases hout
          have hrc := brek_ofPanic_ok hs'
          unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at hrc
          by_cases hne : (m.epoch != state.uc.epoch) = true
          · rw [hne] at hrc; cases hrc
          · simp only [Bool.not_eq_true] at hne
            rw [hne] at hrc
            rcases brek_bind_ok hrc with ⟨d0, hd0, hrc1⟩
            rcases brek_bind_ok hrc1 with ⟨d1, hd1, hrc2⟩
            rcases brek_bind_ok hrc2 with ⟨sendingEk, henc, hrc3⟩
            cases hrc3
            rcases hbok with ⟨hauth, ⟨hdk, hek_len⟩, _⟩
            have hwf0 : DecWF 480 d0 :=
              brek_expectDecoderNew hDF _ CIPHERTEXT1_SIZE (by decide) hd0
            have hwf1 : DecWF 480 d1 := hDA 480 d0 d1 chunk hwf0 (brek_addChunk_lift hd1)
            have henc_wf : EncWF 1152 sendingEk := by
              have hlen_ek : state.uc.send_ek.2.length = 1152 := hek_len
              have hw := brek_expectEncodeBytes hEN _ state.uc.send_ek.2
                (by omega) (by omega) henc
              rwa [hlen_ek] at hw
            exact ⟨hauth, hdk, henc_wf, hwf1⟩
        | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct2 _ =>
          rw [hp] at hrecv; cases hrecv; exact hbok
  | headerSent state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases hlt : m.epoch < state.epoch
      · simp only [hlt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
      · simp only [hlt, ↓reduceIte] at hrecv
        cases hp : m.payload with
        | ct1 chunk =>
          rw [hp] at hrecv
          rcases brek_bind_ok hrecv with ⟨res, hres, hout⟩
          have hrc := brek_ofPanic_ok hres
          unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk at hrc
          by_cases hne : (m.epoch != state.uc.epoch) = true
          · rw [hne] at hrc; cases hrc
          · simp only [Bool.not_eq_true] at hne
            rw [hne] at hrc
            rcases brek_bind_ok hrc with ⟨d1, hd1, hrc1⟩
            rcases brek_bind_ok hrc1 with ⟨decoded?, hdm, hrc2⟩
            rcases hbok with ⟨hauth, hdk, henc, hdec⟩
            have hwf1 : DecWF 480 d1 := hDA 480 state.receiving_ct1 d1 chunk hdec (brek_addChunk_lift hd1)
            cases decoded? with
            | none =>
              cases hrc2
              cases hout
              exact ⟨hauth, hdk, henc, hwf1⟩
            | some decoded =>
              rcases brek_bind_ok hrc2 with ⟨uc, huc, hrc3⟩
              cases hrc3
              cases hout
              have hlen_ct1 : decoded.length = CIPHERTEXT1_SIZE :=
                hDM 480 d1 decoded hwf1 (brek_decodedMessage_lift hdm)
              unfold Unchunked.SendEk.EkSent.recv_ct1 at huc
              by_cases hne2 : (m.epoch != state.uc.epoch) = true
              · rw [hne2] at huc; cases huc
              · simp only [Bool.not_eq_true] at hne2
                rw [hne2] at huc
                cases huc
                exact ⟨hauth, ⟨hdk, hlen_ct1⟩, henc⟩
        | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct2 _ =>
          rw [hp] at hrecv; cases hrecv; exact hbok
  | ct1Received state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases hlt : m.epoch < state.epoch
      · simp only [hlt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
      · simp only [hlt, ↓reduceIte] at hrecv
        cases hp : m.payload with
        | ct2 chunk =>
          rw [hp] at hrecv
          rcases brek_bind_ok hrecv with ⟨s', hs', hout⟩
          cases hout
          have hrc := brek_ofPanic_ok hs'
          unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk at hrc
          by_cases hne : (m.epoch != state.uc.epoch) = true
          · rw [hne] at hrc; cases hrc
          · simp only [Bool.not_eq_true] at hne
            rw [hne] at hrc
            rcases brek_bind_ok hrc with ⟨d0, hd0, hrc1⟩
            rcases brek_bind_ok hrc1 with ⟨d1, hd1, hrc2⟩
            cases hrc2
            rcases hbok with ⟨hauth, huc, _⟩
            have hwf0 : DecWF 80 d0 :=
              brek_expectDecoderNew hDF _ (CIPHERTEXT2_SIZE + AUTHENTICATOR_MACSIZE) (by decide) hd0
            have hwf1 : DecWF 80 d1 := hDA 80 d0 d1 chunk hwf0 (brek_addChunk_lift hd1)
            exact ⟨hauth, huc, hwf1⟩
        | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct1 _ =>
          rw [hp] at hrecv; cases hrecv; exact hbok
  | ekSentCt1Received state =>
    unfold States.recv at hrecv
    by_cases hgt : m.epoch > state.epoch
    · simp only [hgt, ↓reduceIte] at hrecv; cases hrecv
    · simp only [hgt, ↓reduceIte] at hrecv
      by_cases hlt : m.epoch < state.epoch
      · simp only [hlt, ↓reduceIte] at hrecv; cases hrecv; exact hbok
      · simp only [hlt, ↓reduceIte] at hrecv
        cases hp : m.payload with
        | ct2 chunk =>
          rw [hp] at hrecv
          rcases brek_bind_ok hrecv with ⟨res, hrc, hout⟩
          unfold Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at hrc
          by_cases hne : (m.epoch != state.uc.epoch) = true
          · rw [hne] at hrc; cases hrc
          · simp only [Bool.not_eq_true] at hne
            rw [hne] at hrc
            rcases brek_bind_ok hrc with ⟨d1, hd1, hrc1⟩
            rcases brek_bind_ok hrc1 with ⟨decoded?, _, hrc2⟩
            rcases hbok with ⟨hauth, huc, hdec⟩
            have hwf1 : DecWF 80 d1 :=
              hDA 80 state.receiving_ct2 d1 chunk hdec (brek_addChunk_res hd1)
            cases decoded? with
            | none =>
              cases hrc2
              cases hout
              exact ⟨hauth, huc, hwf1⟩
            | some ct2Full =>
              by_cases hlen : ct2Full.length < CIPHERTEXT2_SIZE
              · simp only [hlen, ↓reduceIte] at hrc2; cases hrc2
              · simp only [hlen, ↓reduceIte] at hrc2
                rcases brek_bind_ok hrc2 with ⟨⟨uc, sec⟩, huc_step, hrc3⟩
                rcases brek_bind_ok hrc3 with ⟨receivingHdr, hdhdr, hrc4⟩
                cases hrc4
                cases hout
                have hauth' : AuthOk uc.auth := brek_uc_recv_ct2 F K state.uc _ _ huc_step
                have hwf_hdr : DecWF 48 receivingHdr :=
                  brek_expectDecoderNew hDF _ (HEADER_SIZE + AUTHENTICATOR_MACSIZE) (by decide)
                    (brek_ofPanic_ok hdhdr)
                exact ⟨hauth', hwf_hdr⟩
        | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct1 _ =>
          rw [hp] at hrecv; cases hrecv; exact hbok

end CryptoVerification.SpqrV1Sync.SendTotal
