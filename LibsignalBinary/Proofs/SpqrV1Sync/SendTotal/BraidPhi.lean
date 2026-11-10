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
# Braid Send Potential Bounds

Proves that `States.send` increases the braid potential `phiB` by at most `1` and `States.recv`
never increases `phiB` (`st_bPhi`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoGames.LibsignalSession (ShaCompress)

private theorem bphi_except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem bphi_ofPanic_ok {α : Type} {x : Except StatesPanic α} {a : α}
    (h : StatesResult.ofPanic x = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok v => cases h; rfl

private theorem bphi_toNat_add_one_of_ne_allOnes {e : BitVec 64}
    (hne : (e == BitVec.allOnes 64) = false) :
    (e + 1#64).toNat = e.toNat + 1 := by
  have hne' : e ≠ BitVec.allOnes 64 := by
    intro heq
    subst heq
    simp at hne
  have hlt : e.toNat < 2 ^ 64 - 1 := by
    have hbd := e.isLt
    have hall : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := by decide
    have hval_ne : e.toNat ≠ 2 ^ 64 - 1 := by
      intro h0
      apply hne'
      exact BitVec.eq_of_toNat_eq (by omega)
    omega
  rw [BitVec.toNat_add]
  change (e.toNat + 1) % 2 ^ 64 = e.toNat + 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem bphi_send_epoch {F : ShaCompress} {K : MlKem}
    {st st' : St F} {tape tape' : Bytes} {m : Msg} {key : Option EpochSecret}
    (h : st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape')) :
    st'.epoch = st.epoch := by
  cases st with
  | keysUnsampled s =>
    simp only [States.send] at h
    obtain ⟨⟨s', chunk, t'⟩, hp, hok⟩ := bphi_except_bind_ok h
    cases hok
    have hp' := bphi_ofPanic_ok hp
    simp only [Chunked.SendEk.KeysUnsampled.send_hdr_chunk] at hp'
    obtain ⟨⟨uc, toSend, mac, _⟩, hsh, hp2⟩ := bphi_except_bind_ok hp'
    obtain ⟨enc, _, hp3⟩ := bphi_except_bind_ok hp2
    obtain ⟨⟨enc', _⟩, _, hp4⟩ := bphi_except_bind_ok hp3
    cases hp4
    simp only [Unchunked.SendEk.KeysUnsampled.send_header] at hsh
    obtain ⟨⟨keys, _⟩, _, hsh2⟩ := bphi_except_bind_ok hsh
    obtain ⟨_, _, hsh3⟩ := bphi_except_bind_ok hsh2
    cases hsh3
    rfl
  | keysSampled s =>
    simp only [States.send] at h
    obtain ⟨⟨s', _⟩, hp, hok⟩ := bphi_except_bind_ok h
    cases hok
    have hp' := bphi_ofPanic_ok hp
    simp only [Chunked.SendEk.KeysSampled.send_hdr_chunk] at hp'
    obtain ⟨⟨_, _⟩, _, hp2⟩ := bphi_except_bind_ok hp'
    cases hp2
    rfl
  | headerSent s =>
    simp only [States.send] at h
    obtain ⟨⟨s', _⟩, hp, hok⟩ := bphi_except_bind_ok h
    cases hok
    have hp' := bphi_ofPanic_ok hp
    simp only [Chunked.SendEk.HeaderSent.send_ek_chunk] at hp'
    obtain ⟨⟨_, _⟩, _, hp2⟩ := bphi_except_bind_ok hp'
    cases hp2
    rfl
  | ct1Received s =>
    simp only [States.send] at h
    obtain ⟨⟨s', _⟩, hp, hok⟩ := bphi_except_bind_ok h
    cases hok
    have hp' := bphi_ofPanic_ok hp
    simp only [Chunked.SendEk.Ct1Received.send_ek_chunk] at hp'
    obtain ⟨⟨_, _⟩, _, hp2⟩ := bphi_except_bind_ok hp'
    cases hp2
    rfl
  | ekSentCt1Received s =>
    simp only [States.send] at h
    cases h
    rfl
  | noHeaderReceived s =>
    simp only [States.send] at h
    cases h
    rfl
  | headerReceived s =>
    simp only [States.send] at h
    obtain ⟨⟨s', _, _, _⟩, hp, hok⟩ := bphi_except_bind_ok h
    cases hok
    have hp' := bphi_ofPanic_ok hp
    simp only [Chunked.SendCt.HeaderReceived.send_ct1_chunk] at hp'
    obtain ⟨⟨uc, _, _, _⟩, hsc, hp2⟩ := bphi_except_bind_ok hp'
    obtain ⟨_, _, hp3⟩ := bphi_except_bind_ok hp2
    obtain ⟨⟨_, _⟩, _, hp4⟩ := bphi_except_bind_ok hp3
    cases hp4
    simp only [Unchunked.SendCt.HeaderReceived.send_ct1] at hsc
    obtain ⟨⟨⟨_, _, _⟩, _⟩, _, hsc2⟩ := bphi_except_bind_ok hsc
    obtain ⟨_, _, hsc3⟩ := bphi_except_bind_ok hsc2
    obtain ⟨_, _, hsc4⟩ := bphi_except_bind_ok hsc3
    cases hsc4
    rfl
  | ct1Sampled s =>
    simp only [States.send] at h
    obtain ⟨⟨s', _⟩, hp, hok⟩ := bphi_except_bind_ok h
    cases hok
    have hp' := bphi_ofPanic_ok hp
    simp only [Chunked.SendCt.Ct1Sampled.send_ct1_chunk] at hp'
    obtain ⟨⟨_, _⟩, _, hp2⟩ := bphi_except_bind_ok hp'
    cases hp2
    rfl
  | ekReceivedCt1Sampled s =>
    simp only [States.send] at h
    obtain ⟨⟨s', _⟩, hp, hok⟩ := bphi_except_bind_ok h
    cases hok
    have hp' := bphi_ofPanic_ok hp
    simp only [Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk] at hp'
    obtain ⟨⟨_, _⟩, _, hp2⟩ := bphi_except_bind_ok hp'
    cases hp2
    rfl
  | ct1Acknowledged s =>
    simp only [States.send] at h
    cases h
    rfl
  | ct2Sampled s =>
    simp only [States.send] at h
    obtain ⟨⟨s', _⟩, hp, hok⟩ := bphi_except_bind_ok h
    cases hok
    have hp' := bphi_ofPanic_ok hp
    simp only [Chunked.SendCt.Ct2Sampled.send_ct2_chunk] at hp'
    obtain ⟨⟨_, _⟩, _, hp2⟩ := bphi_except_bind_ok hp'
    cases hp2
    rfl

private theorem bphi_recv_ct1_epoch {Au : AuthApi} {s : Unchunked.SendEk.EkSent Au}
    {ep : Epoch} {ct1 : Ciphertext1} {uc : Unchunked.SendEk.EkSentCt1Received Au}
    (h : s.recv_ct1 ep ct1 = .ok uc) : uc.epoch = s.epoch := by
  unfold Unchunked.SendEk.EkSent.recv_ct1 at h
  split at h
  · cases h
  · cases h; rfl

private theorem bphi_recv_ct2_epoch {K : MlKem} {Au : AuthApi}
    {s : Unchunked.SendEk.EkSentCt1Received Au} {ct2 : Ciphertext2} {mac : Mac}
    {uc : Unchunked.SendCt.NoHeaderReceived Au} {sec : EpochSecret}
    (h : s.recv_ct2 K ct2 mac = .ok (uc, sec)) :
    uc.epoch.toNat = s.epoch.toNat + 1 := by
  unfold Unchunked.SendEk.EkSentCt1Received.recv_ct2 at h
  obtain ⟨_, _, h1⟩ := bphi_except_bind_ok h
  obtain ⟨_, _, h2⟩ := bphi_except_bind_ok h1
  obtain ⟨_, _, h3⟩ := bphi_except_bind_ok h2
  obtain ⟨vr, _, h4⟩ := bphi_except_bind_ok h3
  cases vr with
  | error _ => cases h4
  | ok u =>
    dsimp only at h4
    cases hall : (s.epoch == BitVec.allOnes 64)
    · rw [hall] at h4
      simp only [Bool.false_eq_true, ↓reduceIte] at h4
      cases h4
      exact bphi_toNat_add_one_of_ne_allOnes hall
    · rw [hall] at h4
      simp only [↓reduceIte] at h4
      cases h4

private theorem bphi_recv_header_epoch {Au : AuthApi} {s : Unchunked.SendCt.NoHeaderReceived Au}
    {ep : Epoch} {hdr : Header} {mac : Mac} {uc : Unchunked.SendCt.HeaderReceived Au}
    (h : s.recv_header ep hdr mac = .ok uc) : uc.epoch = s.epoch := by
  unfold Unchunked.SendCt.NoHeaderReceived.recv_header at h
  split at h
  · cases h
  · obtain ⟨vr, _, h2⟩ := bphi_except_bind_ok h
    cases vr with
    | error _ => cases h2
    | ok _ => cases h2; rfl

private theorem bphi_recv_ek_epoch {K : MlKem} {Au : AuthApi} {s : Unchunked.SendCt.Ct1Sent Au}
    {ep : Epoch} {ek : EncapsulationKey} {uc : Unchunked.SendCt.Ct1SentEkReceived Au}
    (h : s.recv_ek K ep ek = .ok uc) : uc.epoch = s.epoch := by
  unfold Unchunked.SendCt.Ct1Sent.recv_ek at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

private theorem bphi_send_ct2_epoch {K : MlKem} {Au : AuthApi}
    {s : Unchunked.SendCt.Ct1SentEkReceived Au} {uc : Unchunked.SendCt.Ct2Sent Au}
    {ct2 : Ciphertext2} {mac : Mac}
    (h : s.send_ct2 K = .ok (uc, ct2, mac)) : uc.epoch = s.epoch := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at h
  obtain ⟨_, _, h1⟩ := bphi_except_bind_ok h
  obtain ⟨_, _, h2⟩ := bphi_except_bind_ok h1
  cases h2
  rfl

private theorem bphi_recv_next_epoch_toNat {Au : AuthApi} {s : Unchunked.SendCt.Ct2Sent Au}
    {ep : Epoch} {uc : Unchunked.SendEk.KeysUnsampled Au}
    (h : s.recv_next_epoch ep = .ok uc) : uc.epoch.toNat = s.epoch.toNat + 1 := by
  unfold Unchunked.SendCt.Ct2Sent.recv_next_epoch at h
  cases hall : (s.epoch == BitVec.allOnes 64)
  · rw [hall] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · cases h
      exact bphi_toNat_add_one_of_ne_allOnes hall
  · rw [hall] at h
    simp only [↓reduceIte] at h
    cases h

private theorem bphi_ct1Sampled_recv_ek_le {F : ShaCompress} {K : MlKem}
    {s : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)}
    {ep : Epoch} {chunk : spqrPolyApi.Chunk} {ack : Bool}
    {res : Chunked.SendCt.Ct1SampledRecvChunk spqrPolyApi (spqrAuthApi F)}
    (hrc : s.recv_ek_chunk K ep chunk ack = .ok res) :
    phiB (match res with
      | .stillReceivingStillSending s' => .ct1Sampled s'
      | .stillReceiving s' => .ct1Acknowledged s'
      | .stillSending s' => .ekReceivedCt1Sampled s'
      | .done s' => .ct2Sampled s') ≤ phiB (.ct1Sampled s) := by
  unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk at hrc
  obtain ⟨_, _, hrc1⟩ := bphi_except_bind_ok hrc
  obtain ⟨dec?, _, hrc2⟩ := bphi_except_bind_ok hrc1
  cases dec? with
  | none =>
    cases ack <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrc2 <;>
      cases hrc2 <;>
      simp [phiB, freshB, States.epoch, Chunked.SendCt.Ct1Sampled.epoch,
        Chunked.SendCt.Ct1Acknowledged.epoch]
  | some dec =>
    dsimp only at hrc2
    obtain ⟨uc, hrek, hrc3⟩ := bphi_except_bind_ok hrc2
    have hep1 := bphi_recv_ek_epoch hrek
    cases ack with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hrc3
      cases hrc3
      simp [phiB, freshB, States.epoch, Chunked.SendCt.EkReceivedCt1Sampled.epoch,
        Chunked.SendCt.Ct1Sampled.epoch, hep1]
    | true =>
      simp only [↓reduceIte] at hrc3
      obtain ⟨⟨uc2, _, _⟩, hsct2, hrc4⟩ := bphi_except_bind_ok hrc3
      obtain ⟨_, _, hrc5⟩ := bphi_except_bind_ok hrc4
      cases hrc5
      have hep2 := bphi_send_ct2_epoch (bphi_ofPanic_ok hsct2)
      simp [phiB, freshB, States.epoch, Chunked.SendCt.Ct2Sampled.epoch,
        Chunked.SendCt.Ct1Sampled.epoch, hep2, hep1]

private theorem bphi_ct1Ack_recv_ek_le {F : ShaCompress} {K : MlKem}
    {s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    {ep : Epoch} {chunk : spqrPolyApi.Chunk}
    {res : Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)}
    (hrc : s.recv_ek_chunk K ep chunk = .ok res) :
    phiB (match res with
      | .stillReceiving s' => .ct1Acknowledged s'
      | .done s' => .ct2Sampled s') ≤ phiB (.ct1Acknowledged s) := by
  unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at hrc
  obtain ⟨_, _, hrc1⟩ := bphi_except_bind_ok hrc
  obtain ⟨dec?, _, hrc2⟩ := bphi_except_bind_ok hrc1
  cases dec? with
  | none =>
    cases hrc2
    exact le_rfl
  | some dec =>
    dsimp only at hrc2
    obtain ⟨uc, hrek, hrc3⟩ := bphi_except_bind_ok hrc2
    obtain ⟨⟨uc2, _, _⟩, hsct2, hrc4⟩ := bphi_except_bind_ok hrc3
    obtain ⟨_, _, hrc5⟩ := bphi_except_bind_ok hrc4
    cases hrc5
    have hep1 := bphi_recv_ek_epoch hrek
    have hep2 := bphi_send_ct2_epoch (bphi_ofPanic_ok hsct2)
    simp [phiB, freshB, States.epoch, Chunked.SendCt.Ct2Sampled.epoch,
      Chunked.SendCt.Ct1Acknowledged.epoch, hep2, hep1]

private theorem bphi_ekRecvCt1Sampled_ack_le {F : ShaCompress} {K : MlKem}
    {s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)}
    {ep : Epoch} {s' : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)}
    (hp' : s.recv_ct1_ack K ep = .ok s') :
    phiB (.ct2Sampled s') ≤ phiB (.ekReceivedCt1Sampled s) := by
  unfold Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at hp'
  split at hp'
  · cases hp'
  · obtain ⟨⟨uc2, _, _⟩, hsct2, hp2⟩ := bphi_except_bind_ok hp'
    obtain ⟨_, _, hp3⟩ := bphi_except_bind_ok hp2
    cases hp3
    have hep := bphi_send_ct2_epoch hsct2
    simp [phiB, freshB, States.epoch, Chunked.SendCt.Ct2Sampled.epoch,
      Chunked.SendCt.EkReceivedCt1Sampled.epoch, hep]

private theorem bphi_recv_le {F : ShaCompress} {K : MlKem}
    {st st' : St F} {m : Msg} {key : Option EpochSecret}
    (h : st.recv K m = .ok { key := key, state := st' }) :
    phiB st' ≤ phiB st := by
  rcases m with ⟨ep, payload⟩
  cases st with
  | keysUnsampled s =>
    simp only [States.recv] at h
    split at h <;> cases h
    exact le_rfl
  | keysSampled s =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_rfl
      · cases payload <;> try (cases h; exact le_rfl)
        rename_i chunk
        obtain ⟨s', hp, hok⟩ := bphi_except_bind_ok h
        cases hok
        have hp' := bphi_ofPanic_ok hp
        unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at hp'
        split at hp'
        · cases hp'
        · obtain ⟨_, _, hp1⟩ := bphi_except_bind_ok hp'
          obtain ⟨_, _, hp2⟩ := bphi_except_bind_ok hp1
          obtain ⟨_, _, hp3⟩ := bphi_except_bind_ok hp2
          cases hp3
          simp [phiB, freshB, States.epoch, Chunked.SendEk.HeaderSent.epoch,
            Chunked.SendEk.KeysSampled.epoch]
  | headerSent s =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_rfl
      · cases payload <;> try (cases h; exact le_rfl)
        rename_i chunk
        obtain ⟨res, hp, hok⟩ := bphi_except_bind_ok h
        have hp' := bphi_ofPanic_ok hp
        unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk at hp'
        split at hp'
        · cases hp'
        · obtain ⟨_, _, hp1⟩ := bphi_except_bind_ok hp'
          obtain ⟨dec?, _, hp2⟩ := bphi_except_bind_ok hp1
          cases dec? with
          | none =>
            cases hp2
            cases hok
            exact le_rfl
          | some dec =>
            dsimp only at hp2
            obtain ⟨uc, hrc, hp3⟩ := bphi_except_bind_ok hp2
            cases hp3
            cases hok
            have hep := bphi_recv_ct1_epoch hrc
            simp [phiB, freshB, States.epoch, Chunked.SendEk.Ct1Received.epoch,
              Chunked.SendEk.HeaderSent.epoch, hep]
  | ct1Received s =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_rfl
      · cases payload <;> try (cases h; exact le_rfl)
        rename_i chunk
        obtain ⟨s', hp, hok⟩ := bphi_except_bind_ok h
        cases hok
        have hp' := bphi_ofPanic_ok hp
        unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk at hp'
        split at hp'
        · cases hp'
        · obtain ⟨_, _, hp1⟩ := bphi_except_bind_ok hp'
          obtain ⟨_, _, hp2⟩ := bphi_except_bind_ok hp1
          cases hp2
          simp [phiB, freshB, States.epoch, Chunked.SendEk.EkSentCt1Received.epoch,
            Chunked.SendEk.Ct1Received.epoch]
  | ekSentCt1Received s =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_rfl
      · cases payload <;> try (cases h; exact le_rfl)
        rename_i chunk
        obtain ⟨res, hrc, hok⟩ := bphi_except_bind_ok h
        unfold Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at hrc
        split at hrc
        · cases hrc
        · obtain ⟨_, _, hrc1⟩ := bphi_except_bind_ok hrc
          obtain ⟨dec?, _, hrc2⟩ := bphi_except_bind_ok hrc1
          cases dec? with
          | none =>
            cases hrc2
            cases hok
            exact le_rfl
          | some ct2Full =>
            dsimp only at hrc2
            split at hrc2
            · cases hrc2
            · obtain ⟨⟨uc, sec⟩, hct2, hrc3⟩ := bphi_except_bind_ok hrc2
              obtain ⟨_, _, hrc4⟩ := bphi_except_bind_ok hrc3
              cases hrc4
              cases hok
              have hep := bphi_recv_ct2_epoch hct2
              simp only [phiB, freshB, Bool.false_eq_true, ↓reduceIte, States.epoch,
                Chunked.SendCt.NoHeaderReceived.epoch, Chunked.SendEk.EkSentCt1Received.epoch, hep]
              omega
  | noHeaderReceived s =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_rfl
      · cases payload <;> try (cases h; exact le_rfl)
        rename_i chunk
        obtain ⟨res, hrc, hok⟩ := bphi_except_bind_ok h
        unfold Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at hrc
        split at hrc
        · cases hrc
        · obtain ⟨_, _, hrc1⟩ := bphi_except_bind_ok hrc
          obtain ⟨dec?, _, hrc2⟩ := bphi_except_bind_ok hrc1
          cases dec? with
          | none =>
            cases hrc2
            cases hok
            exact le_rfl
          | some hdrFull =>
            dsimp only at hrc2
            split at hrc2
            · cases hrc2
            · obtain ⟨ekRes, _, hrc3⟩ := bphi_except_bind_ok hrc2
              obtain ⟨uc, hrh, hrc4⟩ := bphi_except_bind_ok hrc3
              cases ekRes with
              | error _ => cases hrc4
              | ok _ =>
                cases hrc4
                cases hok
                have hep := bphi_recv_header_epoch hrh
                simp [phiB, freshB, States.epoch, Chunked.SendCt.HeaderReceived.epoch,
                  Chunked.SendCt.NoHeaderReceived.epoch, hep]
  | headerReceived s =>
    simp only [States.recv] at h
    split at h <;> cases h
    exact le_rfl
  | ct1Sampled s =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_rfl
      · cases payload <;> try (cases h; exact le_rfl)
        · obtain ⟨res, hrc, hok⟩ := bphi_except_bind_ok h
          have hle := bphi_ct1Sampled_recv_ek_le hrc
          cases res <;> cases hok <;> exact hle
        · obtain ⟨res, hrc, hok⟩ := bphi_except_bind_ok h
          have hle := bphi_ct1Sampled_recv_ek_le hrc
          cases res <;> cases hok <;> exact hle
  | ekReceivedCt1Sampled s =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_rfl
      · cases payload <;> try (cases h; exact le_rfl)
        · obtain ⟨s', hp, hok⟩ := bphi_except_bind_ok h
          cases hok
          exact bphi_ekRecvCt1Sampled_ack_le (bphi_ofPanic_ok hp)
        · rename_i b
          cases b
          · cases h; exact le_rfl
          · obtain ⟨s', hp, hok⟩ := bphi_except_bind_ok h
            cases hok
            exact bphi_ekRecvCt1Sampled_ack_le (bphi_ofPanic_ok hp)
  | ct1Acknowledged s =>
    simp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_rfl
      · cases payload <;> try (cases h; exact le_rfl)
        · obtain ⟨res, hrc, hok⟩ := bphi_except_bind_ok h
          have hle := bphi_ct1Ack_recv_ek_le hrc
          cases res <;> cases hok <;> exact hle
        · obtain ⟨res, hrc, hok⟩ := bphi_except_bind_ok h
          have hle := bphi_ct1Ack_recv_ek_le hrc
          cases res <;> cases hok <;> exact hle
  | ct2Sampled s =>
    simp only [States.recv] at h
    split at h
    · split at h
      · obtain ⟨s', hp, hok⟩ := bphi_except_bind_ok h
        cases hok
        have hp' := bphi_ofPanic_ok hp
        unfold Chunked.SendCt.Ct2Sampled.recv_next_epoch at hp'
        obtain ⟨uc, hrn, hp2⟩ := bphi_except_bind_ok hp'
        cases hp2
        have hep := bphi_recv_next_epoch_toNat hrn
        simp only [phiB, freshB, Bool.false_eq_true, ↓reduceIte, States.epoch,
          Chunked.SendEk.KeysUnsampled.epoch, Chunked.SendCt.Ct2Sampled.epoch, hep]
        omega
      · cases h
    · cases h
      exact le_rfl

/-- `States.send` increments `phiB` by at most `1`, and `States.recv` does not increase `phiB`. -/
theorem st_bPhi (F : ShaCompress) (K : MlKem) : BPhiStmt F K := by
  refine ⟨?_, ?_⟩
  · intro st st' tape tape' m key hsend
    have hep := bphi_send_epoch hsend
    simp only [phiB, hep]
    cases freshB st <;> cases freshB st' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · intro st st' m key hrecv
    exact bphi_recv_le hrecv

end CryptoVerification.SpqrV1Sync.SendTotal
