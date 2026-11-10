/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.SmDir
public import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
public import LibsignalBinary.Proofs.E2E.RecordX.BridgeCommon
public import LibsignalBinary.Proofs.E2E.RecordX.Length

/-!
# SPQR-Off Session-Record and SM-Directory File Cap Bounds

Proves that every reachable SPQR-off session state `Reach (spqrOffSessionParams C) g` has empty
post-quantum ratchet state (`g.session.pqRatchetState = []`) and encodes within `fileCapBytes`
(`2 ^ 21` B), together with file-cap bounds on `dirOfE`, `smSendInputs`, `smRecvInputs`,
`smSendModel`, and `smRecvModel`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Reach.SmSessionCap

open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto GhostState SessionState SignalMessage IdentityKey PublicKey)
open CryptoVerification.E2E
  (Bytes spqrOffSessionParams Reach encodeRecord sendModelSpqrOff recvModelSpqrOff
   partyAddressName partyIdentityKey RecordExtras seedRecordExtras encodeRecordUnderExtras
   FixedIdRecordExtras)
open CryptoVerification.SignalSession
  (fileCapBytes dirOfE smInputs smSendInputs smRecvInputs smWrites smSendModel smRecvModel
   partyAddress textBytes)
open CryptoVerification.E2E.Reach
  (reach_pqRatchetState_eq_nil reach_encodeRecord_length_lt_20
   sessionInv_of_send_ok sessionInv_of_recv_ok encodeRecord_length_lt_20_of_sessionInv)
open CryptoVerification.E2E.RecordX (encodeRecordX_extrasSeed reach_encodeRecordX_length_lt_21)

/-- Every `Reach (spqrOffSessionParams C)` state has an empty SPQR ratchet state (`0` bytes). -/
theorem reach_pqRatchetState_nil (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    g.session.pqRatchetState = [] :=
  reach_pqRatchetState_eq_nil C hg

/-- Every reachable SPQR-off session record `encodeRecord g` encodes to at most `2 ^ 21` bytes. -/
theorem reach_encodeRecord_length_le_sessionCap (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (encodeRecord g).length ≤ 2 ^ 21 :=
  Nat.le_of_lt (Nat.lt_trans (reach_encodeRecord_length_lt_20 C hg) (by decide))

theorem reach_encodeRecord_length_le_fileCapBytes (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (encodeRecord g).length ≤ fileCapBytes := by
  change (encodeRecord g).length ≤ 2 ^ 21
  exact reach_encodeRecord_length_le_sessionCap C hg

theorem reach_encodeRecordUnderExtras_seed_length_le_sessionCap (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) :
    (encodeRecordUnderExtras seedRecordExtras g).length ≤ 2 ^ 21 := by
  rw [encodeRecordX_extrasSeed]
  exact reach_encodeRecord_length_le_sessionCap C hg

/-- Under any `FixedIdRecordExtras` map `E`, `encodeRecordUnderExtras E g` on a reachable SPQR-off
state `Reach (spqrOffSessionParams C) g` is strictly below `2 ^ 21` (`≤ fileCapBytes`). -/
theorem reach_encodeRecordUnderExtras_fixedId_length_le_fileCapBytes (C : Crypto)
    (E : Party → RecordExtras) (hE : ∀ P, FixedIdRecordExtras (E P))
    {g : GhostState Bytes} (hg : Reach (spqrOffSessionParams C) g) :
    (encodeRecordUnderExtras E g).length ≤ fileCapBytes := by
  have hlt : (encodeRecordUnderExtras E g).length < 2 ^ 21 :=
    reach_encodeRecordX_length_lt_21 C E
      (fun P => (hE P).2.2.2.2.2.2)
      (fun P k hk => ((hE P).2.2.2.2.2.1 k hk).2) hg
  unfold fileCapBytes
  exact Nat.le_of_lt hlt

private theorem identityKey_serialize_len_33 (ik : IdentityKey) :
    ik.serialize.length = 33 := by
  simp [IdentityKey.serialize, PublicKey.serialize]

private theorem byteArray_loop_len (bs : ByteArray) (i : Nat) (acc : List UInt8) (hi : i ≤ bs.size) :
    (ByteArray.toList.loop bs i acc).length = acc.length + (bs.size - i) := by
  unfold ByteArray.toList.loop
  split
  · rw [byteArray_loop_len bs (i + 1) _ (by omega)]; simp; omega
  · simp; omega
termination_by bs.size - i
decreasing_by
  have : i < bs.size := ‹_›; omega

private theorem partyAddress_textBytes_le_fileCap (P : Party) :
    (textBytes (partyAddress P).text).length ≤ fileCapBytes := by
  have h1 : ∀ s : String, (textBytes s).length = s.utf8ByteSize := by
    intro s
    unfold textBytes CryptoVerification.LibsignalTripleRatchetRepr.utf8 ByteArray.toList
    rw [List.length_map, byteArray_loop_len _ 0 [] (Nat.zero_le _), String.toUTF8_eq_toByteArray]
    have hsz : s.toByteArray.size = s.utf8ByteSize := String.size_toByteArray
    simp [hsz]
  rw [h1]
  have hn : (partyAddressName P).utf8ByteSize ≤ 64 := by cases P <;> decide
  have hd : ".".utf8ByteSize = 1 := by decide
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hc := Char.utf8Size_le_four (Nat.digitChar 1)
  simp only [CryptoVerification.SignalSession.Address.text, partyAddress, ht1,
    String.utf8ByteSize_append, String.utf8ByteSize_singleton, fileCapBytes]
  omega

/-- Every file in `dirOfE P rec` (`address`, `identities/<peer>`, `sessions/<peer>`) is at most
`fileCapBytes` whenever `rec.length ≤ fileCapBytes`. -/
theorem dirOfE_files_le_fileCapBytes (P : Party) {rec : List (BitVec 8)}
    (hrec : rec.length ≤ fileCapBytes) :
    ∀ p bs, (p, bs) ∈ dirOfE P rec → bs.length ≤ fileCapBytes := by
  intro p bs hmem
  unfold dirOfE at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact partyAddress_textBytes_le_fileCap P
  · rw [identityKey_serialize_len_33]; unfold fileCapBytes; omega
  · exact hrec

/-- Every input file in `(smSendInputs g m).files` for reachable `g` has byte length
`≤ fileCapBytes` (`2 ^ 21`). -/
theorem smSendInputs_files_le_fileCapBytes (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) (m : List (BitVec 8)) :
    ∀ p bs, (p, bs) ∈ (smSendInputs g m).files → bs.length ≤ fileCapBytes := by
  intro p bs hmem
  unfold smSendInputs smInputs at hmem
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with hdir | ⟨-, rfl⟩
  · exact dirOfE_files_le_fileCapBytes g.party (reach_encodeRecord_length_le_fileCapBytes C hg) p bs hdir
  · simp

/-- Every input file in `(smRecvInputs g c rc).files` for reachable `g` has byte length
`≤ fileCapBytes` (`2 ^ 21`). -/
theorem smRecvInputs_files_le_fileCapBytes (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) (c : List (BitVec 8)) (rc : BitVec 256) :
    ∀ p bs, (p, bs) ∈ (smRecvInputs g c rc).files → bs.length ≤ fileCapBytes := by
  intro p bs hmem
  unfold smRecvInputs smInputs at hmem
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with hdir | ⟨-, rfl⟩
  · exact dirOfE_files_le_fileCapBytes g.party (reach_encodeRecord_length_le_fileCapBytes C hg) p bs hdir
  · have h32 : (keyToBytes32 rc).length = 32 := by simp [keyToBytes32]
    unfold fileCapBytes; omega

private theorem smWrites_files_le_fileCapBytes (P : Party) {rec : List (BitVec 8)}
    (hrec : rec.length ≤ fileCapBytes) :
    ∀ p bs, (p, bs) ∈ smWrites P rec → bs.length ≤ fileCapBytes := by
  intro p bs hmem
  unfold smWrites at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rw [identityKey_serialize_len_33]; unfold fileCapBytes; omega
  · exact hrec

/-- Every post-call file written by `smSendModel C g m` on reachable `g` has byte length
`≤ fileCapBytes` (`2 ^ 21`). -/
theorem smSendModel_writes_le_fileCapBytes (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) (m : List (BitVec 8))
    {writes : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : smSendModel C g m = some (some (writes, out))) :
    ∀ p bs, (p, bs) ∈ writes → bs.length ≤ fileCapBytes := by
  unfold smSendModel sendModelSpqrOff at h
  rcases hme : SessionState.messageEncrypt (spqrOffSessionParams C).C
      (spqrOffSessionParams C).codec (spqrOffSessionParams C).spqr
      ((spqrOffSessionParams C).sendAddrs g.party) m () g.session with ⟨res, s⟩
  rw [hme] at h
  rcases res with err | msg
  · cases err <;> simp at h
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, -⟩
    have hinv := sessionInv_of_send_ok C m () msg s hg hme
    have hlt := encodeRecord_length_lt_20_of_sessionInv C hinv
    have hle : (encodeRecord { g with session := s }).length ≤ fileCapBytes := by
      unfold fileCapBytes; omega
    exact smWrites_files_le_fileCapBytes g.party hle

/-- Every post-call file written by `smRecvModel C g c rc` on reachable `g` has byte length
`≤ fileCapBytes` (`2 ^ 21`). -/
theorem smRecvModel_writes_le_fileCapBytes (C : Crypto) {g : GhostState Bytes}
    (hg : Reach (spqrOffSessionParams C) g) (c : List (BitVec 8)) (rc : BitVec 256)
    {writes : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : smRecvModel C g c rc = some (some (writes, out))) :
    ∀ p bs, (p, bs) ∈ writes → bs.length ≤ fileCapBytes := by
  unfold smRecvModel recvModelSpqrOff at h
  rcases hparse : SignalMessage.tryFrom (spqrOffSessionParams C).codec c with err | msg
  · simp [hparse] at h
  · rw [hparse] at h
    dsimp only at h
    rcases hdec : SessionState.tryDecryptFromRecord (spqrOffSessionParams C).C
        (spqrOffSessionParams C).spqr ((spqrOffSessionParams C).expectedAddrs g.party)
        msg .whisper rc g.session with ⟨res, s⟩
    rw [hdec] at h
    rcases res with err | pt
    · cases err <;> simp at h
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, -⟩
      have hinv := sessionInv_of_recv_ok C msg rc pt s hg hdec
      have hlt := encodeRecord_length_lt_20_of_sessionInv C hinv
      have hle : (encodeRecord { g with session := s }).length ≤ fileCapBytes := by
        unfold fileCapBytes; omega
      exact smWrites_files_le_fileCapBytes g.party hle

end LibsignalBinary.Proofs.E2E.Reach.SmSessionCap
