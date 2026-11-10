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

set_option autoImplicit false

/-!
# Braid Well-Formedness Under Sends

Proves that `States.send` preserves `BOk` across all eleven braid state variants (`st_bSendClosed`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoGames.LibsignalSession (ShaCompress)

private theorem bsc_bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem bsc_ofPanic_ok {α : Type} {r : Except StatesPanic α} {v : α}
    (h : StatesResult.ofPanic r = .ok v) : r = .ok v := by
  cases r with
  | error _ => cases h
  | ok a => simpa [StatesResult.ofPanic] using h

private theorem bsc_lift_ok {α : Type} {r : Except SpqrPanic α} {v : α}
    (h : (liftM r : Except StatesPanic α) = .ok v) : r = .ok v := by
  cases r with
  | error _ => cases h
  | ok a =>
    have hv : a = v := by
      simpa [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic] using h
    exact congrArg Except.ok hv

private theorem bsc_authOk_update (F : ShaCompress) (a : Authenticator) (ep : Epoch) (k : Bytes) :
    AuthOk (a.update F ep k) := by
  unfold AuthOk Authenticator.update hkdfToVecUnchecked hkdfToSliceUnchecked
  simp [length_hkdfExpand]

private theorem bsc_nextChunk_wf (hEX : EncNextStmt) {len : ℕ} {e e' : PolyEncoder} {c : Chunk}
    (hwf : EncWF len e) (hle : len ≤ 2 ^ 20)
    (h : (liftM (spqrPolyApi.next_chunk e) : Except StatesPanic (PolyEncoder × Chunk)) =
      .ok (e', c)) :
    EncWF len e' := by
  have h' := bsc_lift_ok h
  obtain ⟨e1, c1, hnc, hwf1⟩ := hEX len e hwf hle
  simp only [spqrPolyApi, hnc, Except.mapError, Except.ok.injEq, Prod.mk.injEq] at h'
  rcases h' with ⟨rfl, rfl⟩
  exact hwf1

private theorem bsc_expectEncode_wf (hEN : EncNewStmt) {site : String} {msg : Bytes}
    {e : PolyEncoder} (heven : msg.length % 2 = 0) (hle : msg.length ≤ 2 ^ 20)
    (h : expectEncodeBytes spqrPolyApi site msg = .ok e) : EncWF msg.length e := by
  obtain ⟨e1, henc, hwf1⟩ := hEN msg heven hle
  simp only [expectEncodeBytes, spqrPolyApi, henc, Except.mapError, Bind.bind, Except.bind,
    liftM, monadLift, MonadLift.monadLift, liftSpqrPanic, Except.ok.injEq] at h
  subst h
  exact hwf1

private theorem bsc_generate_lengths (K : MlKem) (tape tape' : Bytes) (keys : Keys)
    (h : generate K tape = .ok (keys, tape')) :
    keys.hdr.length = 64 ∧ keys.ek.length = ENCAPSULATION_KEY_SIZE ∧
      keys.dk.length = DECAPSULATION_KEY_SIZE := by
  unfold generate at h
  cases hb : bytesToVector? KEY_GENERATION_SEED_SIZE (tape.take KEY_GENERATION_SEED_SIZE) with
  | none => simp [hb] at h
  | some seed =>
    simp only [hb, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    simp [ENCAPSULATION_KEY_SIZE, DECAPSULATION_KEY_SIZE]

private theorem bsc_encaps1_lengths (K : MlKem) (hdr tape tape' ct1 es ss : Bytes)
    (h : encaps1 K hdr tape = .ok ((ct1, es, ss), tape')) :
    ct1.length = CIPHERTEXT1_SIZE ∧ es.length = ENCAPSULATION_STATE_SIZE := by
  unfold encaps1 at h
  cases hb : bytesToVector? SHARED_SECRET_SIZE (tape.take SHARED_SECRET_SIZE) with
  | none => simp [hb] at h
  | some rand =>
    simp only [hb] at h
    cases he : K.encaps1 hdr rand with
    | none => simp [he] at h
    | some v =>
      rcases v with ⟨ct1V, esV, ssV⟩
      simp only [he, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨⟨rfl, rfl, rfl⟩, _⟩
      simp [CIPHERTEXT1_SIZE, ENCAPSULATION_STATE_SIZE]

private theorem bsc_macHdr_length (F : ShaCompress) (a : Authenticator) (ep : Epoch)
    (hdr mac : Bytes)
    (h : (liftM ((spqrAuthApi F).mac_hdr a ep hdr) : Except StatesPanic Mac) = .ok mac) :
    mac.length = 32 := by
  have h' := bsc_lift_ok h
  simp only [spqrAuthApi, Authenticator.macHdr] at h'
  split_ifs at h'
  simp only [Except.ok.injEq] at h'
  subst h'
  exact Authenticator.length_macHdrUnchecked F a ep hdr

/-- Any successful `States.send` preserves `BOk`. -/
theorem st_bSendClosed (F : ShaCompress) (K : MlKem) (hEN : EncNewStmt) (hEX : EncNextStmt) :
    BSendClosedStmt F K := by
  intro st st' tape tape' m key hbok hsend
  cases st with
  | keysUnsampled s =>
    simp only [States.send] at hsend
    obtain ⟨⟨s', chunk, t'⟩, hp, hret⟩ := bsc_bind_ok hsend
    simp only [Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hret
    rcases hret with ⟨⟨_, _, rfl⟩, _⟩
    have hp' := bsc_ofPanic_ok hp
    unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk at hp'
    obtain ⟨⟨uc, toSend, mac, t1⟩, hsh, hp1⟩ := bsc_bind_ok hp'
    obtain ⟨e0, henc, hp2⟩ := bsc_bind_ok hp1
    obtain ⟨⟨e1, c1⟩, hnc, hp3⟩ := bsc_bind_ok hp2
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp3
    rcases hp3 with ⟨rfl, _, _⟩
    unfold Unchunked.SendEk.KeysUnsampled.send_header at hsh
    obtain ⟨⟨keys, t0⟩, hgen, hsh1⟩ := bsc_bind_ok hsh
    obtain ⟨mac0, hmac, hsh2⟩ := bsc_bind_ok hsh1
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsh2
    rcases hsh2 with ⟨rfl, rfl, rfl, _⟩
    obtain ⟨hhdr, hek, hdk⟩ := bsc_generate_lengths K tape t0 keys hgen
    have hmacLen : mac0.length = 32 := bsc_macHdr_length F s.uc.auth s.uc.epoch keys.hdr mac0 hmac
    have hfull : (keys.hdr ++ mac0).length = 96 := by simp [hhdr, hmacLen]
    have he0 : EncWF 96 e0 := by
      have hw := bsc_expectEncode_wf hEN (by rw [hfull]) (by rw [hfull]; decide) henc
      rwa [hfull] at hw
    exact ⟨hbok, ⟨hdk, hek⟩, bsc_nextChunk_wf hEX he0 (by decide) hnc⟩
  | keysSampled s =>
    rcases hbok with ⟨hauth, huc, henc⟩
    simp only [States.send] at hsend
    obtain ⟨⟨s', chunk⟩, hp, hret⟩ := bsc_bind_ok hsend
    simp only [Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hret
    rcases hret with ⟨⟨_, _, rfl⟩, _⟩
    have hp' := bsc_ofPanic_ok hp
    unfold Chunked.SendEk.KeysSampled.send_hdr_chunk at hp'
    obtain ⟨⟨e1, c1⟩, hnc, hp1⟩ := bsc_bind_ok hp'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp1
    rcases hp1 with ⟨rfl, _⟩
    exact ⟨hauth, huc, bsc_nextChunk_wf hEX henc (by decide) hnc⟩
  | headerSent s =>
    rcases hbok with ⟨hauth, huc, henc, hdec⟩
    simp only [States.send] at hsend
    obtain ⟨⟨s', chunk⟩, hp, hret⟩ := bsc_bind_ok hsend
    simp only [Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hret
    rcases hret with ⟨⟨_, _, rfl⟩, _⟩
    have hp' := bsc_ofPanic_ok hp
    unfold Chunked.SendEk.HeaderSent.send_ek_chunk at hp'
    obtain ⟨⟨e1, c1⟩, hnc, hp1⟩ := bsc_bind_ok hp'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp1
    rcases hp1 with ⟨rfl, _⟩
    exact ⟨hauth, huc, bsc_nextChunk_wf hEX henc (by decide) hnc, hdec⟩
  | ct1Received s =>
    rcases hbok with ⟨hauth, huc, henc⟩
    simp only [States.send] at hsend
    obtain ⟨⟨s', chunk⟩, hp, hret⟩ := bsc_bind_ok hsend
    simp only [Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hret
    rcases hret with ⟨⟨_, _, rfl⟩, _⟩
    have hp' := bsc_ofPanic_ok hp
    unfold Chunked.SendEk.Ct1Received.send_ek_chunk at hp'
    obtain ⟨⟨e1, c1⟩, hnc, hp1⟩ := bsc_bind_ok hp'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp1
    rcases hp1 with ⟨rfl, _⟩
    exact ⟨hauth, huc, bsc_nextChunk_wf hEX henc (by decide) hnc⟩
  | ekSentCt1Received s =>
    simp only [States.send, Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hsend
    rcases hsend with ⟨⟨_, _, rfl⟩, _⟩
    exact hbok
  | noHeaderReceived s =>
    simp only [States.send, Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hsend
    rcases hsend with ⟨⟨_, _, rfl⟩, _⟩
    exact hbok
  | headerReceived s =>
    rcases hbok with ⟨_, huc, hdec⟩
    simp only [States.send] at hsend
    obtain ⟨⟨s', chunk, esec, t'⟩, hp, hret⟩ := bsc_bind_ok hsend
    simp only [Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hret
    rcases hret with ⟨⟨_, _, rfl⟩, _⟩
    have hp' := bsc_ofPanic_ok hp
    unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk at hp'
    obtain ⟨⟨uc, ct1, esec0, t1⟩, hsc, hp1⟩ := bsc_bind_ok hp'
    obtain ⟨e0, henc, hp2⟩ := bsc_bind_ok hp1
    obtain ⟨⟨e1, c1⟩, hnc, hp3⟩ := bsc_bind_ok hp2
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp3
    rcases hp3 with ⟨rfl, _, _, _⟩
    unfold Unchunked.SendCt.HeaderReceived.send_ct1 at hsc
    obtain ⟨⟨⟨ct1_0, es_0, ss_0⟩, t0⟩, henc1, hsc1⟩ := bsc_bind_ok hsc
    obtain ⟨sec, _, hsc2⟩ := bsc_bind_ok hsc1
    obtain ⟨auth', hupd, hsc3⟩ := bsc_bind_ok hsc2
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsc3
    rcases hsc3 with ⟨rfl, rfl, _, _⟩
    have hupd' := bsc_lift_ok hupd
    dsimp only [spqrAuthApi] at auth' hupd'
    cases hupd'
    obtain ⟨hct1, hes⟩ := bsc_encaps1_lengths K s.uc.hdr tape t0 ct1_0 es_0 ss_0 henc1
    have hct1_960 : ct1_0.length = 960 := by simpa [CIPHERTEXT1_SIZE] using hct1
    have he0 : EncWF 960 e0 := by
      have hw := bsc_expectEncode_wf hEN (by rw [hct1_960]) (by rw [hct1_960]; decide) henc
      rwa [hct1_960] at hw
    exact ⟨bsc_authOk_update F s.uc.auth s.uc.epoch sec, ⟨huc, hes, hct1⟩,
      bsc_nextChunk_wf hEX he0 (by decide) hnc, hdec⟩
  | ct1Sampled s =>
    rcases hbok with ⟨hauth, huc, henc, hdec⟩
    simp only [States.send] at hsend
    obtain ⟨⟨s', chunk⟩, hp, hret⟩ := bsc_bind_ok hsend
    simp only [Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hret
    rcases hret with ⟨⟨_, _, rfl⟩, _⟩
    have hp' := bsc_ofPanic_ok hp
    unfold Chunked.SendCt.Ct1Sampled.send_ct1_chunk at hp'
    obtain ⟨⟨e1, c1⟩, hnc, hp1⟩ := bsc_bind_ok hp'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp1
    rcases hp1 with ⟨rfl, _⟩
    exact ⟨hauth, huc, bsc_nextChunk_wf hEX henc (by decide) hnc, hdec⟩
  | ekReceivedCt1Sampled s =>
    rcases hbok with ⟨hauth, huc, henc⟩
    simp only [States.send] at hsend
    obtain ⟨⟨s', chunk⟩, hp, hret⟩ := bsc_bind_ok hsend
    simp only [Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hret
    rcases hret with ⟨⟨_, _, rfl⟩, _⟩
    have hp' := bsc_ofPanic_ok hp
    unfold Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk at hp'
    obtain ⟨⟨e1, c1⟩, hnc, hp1⟩ := bsc_bind_ok hp'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp1
    rcases hp1 with ⟨rfl, _⟩
    exact ⟨hauth, huc, bsc_nextChunk_wf hEX henc (by decide) hnc⟩
  | ct1Acknowledged s =>
    simp only [States.send, Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hsend
    rcases hsend with ⟨⟨_, _, rfl⟩, _⟩
    exact hbok
  | ct2Sampled s =>
    rcases hbok with ⟨hauth, henc⟩
    simp only [States.send] at hsend
    obtain ⟨⟨s', chunk⟩, hp, hret⟩ := bsc_bind_ok hsend
    simp only [Except.ok.injEq, Prod.mk.injEq, V1Send.mk.injEq] at hret
    rcases hret with ⟨⟨_, _, rfl⟩, _⟩
    have hp' := bsc_ofPanic_ok hp
    unfold Chunked.SendCt.Ct2Sampled.send_ct2_chunk at hp'
    obtain ⟨⟨e1, c1⟩, hnc, hp1⟩ := bsc_bind_ok hp'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp1
    rcases hp1 with ⟨rfl, _⟩
    exact ⟨hauth, bsc_nextChunk_wf hEX henc (by decide) hnc⟩

end CryptoVerification.SpqrV1Sync.SendTotal
