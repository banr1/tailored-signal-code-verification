/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-!
# Pre-Key Store Lookups and Consumption Agreement on `pqRecvInputs`

Proves agreement of pre-key store lookups (`pkStoreKeys_pqRecv`), last-resort `.base-keys` chunk
membership, Kyber pre-key marking (`KyberGhost.mark`), and one-time EC pre-key removal
(`removePreKey`) on `runFiles (pqRecvInputs W st c rc)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-! ## Pre-key store reads (`pkStoreKeys_pqRecv`) -/

private theorem keyName_utf8 (id : BitVec 32) : keyName id = utf8 (toString id.toNat) := rfl

private theorem baseKeysName_utf8 (id : BitVec 32) :
    baseKeysName id = utf8 (toString id.toNat ++ ".base-keys") :=
  (utf8_append _ _).symm

private theorem keyName_chars (id : BitVec 32) :
    ∀ ch ∈ (toString id.toNat).toList, ch.toNat < 128 ∧ ch ≠ '/' ∧ ch ≠ '<' := fun _ hch =>
  let p := toString_nat_char_props id.toNat hch
  ⟨p.1, p.2.2⟩

private theorem baseKeys_chars (id : BitVec 32) :
    ∀ ch ∈ (toString id.toNat ++ ".base-keys").toList, ch.toNat < 128 ∧ ch ≠ '/' ∧ ch ≠ '<' := by
  intro ch hch
  rw [String.toList_append] at hch
  rcases List.mem_append.mp hch with h1 | h2
  · exact keyName_chars id ch h1
  · clear id hch; revert ch h2; decide

private theorem keyName_ne (id : BitVec 32) :
    (toString id.toNat).toList ≠ [] ∧ toString id.toNat ≠ "." :=
  ⟨toString_nat_ne_nil id.toNat, toString_nat_ne_dot id.toNat⟩

private theorem baseKeys_ne (id : BitVec 32) :
    (toString id.toNat ++ ".base-keys").toList ≠ [] ∧ toString id.toNat ++ ".base-keys" ≠ "." := by
  refine ⟨?_, ?_⟩
  · intro hnil
    rw [String.toList_append] at hnil
    exact absurd (List.append_eq_nil_iff.mp hnil).2 (by decide)
  · intro hdot
    have hl := congrArg (fun s => s.toList.length) hdot
    rw [String.toList_append, List.length_append] at hl
    have h10 : ".base-keys".toList.length = 10 := by decide
    have h1 : ".".toList.length = 1 := by decide
    omega

theorem getSignedPreKey_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hnd : (st.signed.map Prod.fst).Nodup) (id : BitVec 32) :
    getSignedPreKey cliIo.rd (runFiles (pqRecvInputs W st c rc)) StoresGhost.opened.signed id =
      match List.lookup id st.signed with
      | none => .error ()
      | some k => .ok ⟨⟨id, djbKey (keyPairOf W.C k.priv).publicKey.bytes,
          k.priv.toList, k.sig.toList, k.timestamp⟩⟩ := by
  have hget : StoresGhost.opened.signed.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (keyName id) =
      .ok (match List.lookup id st.signed with
           | none => []
           | some k => signedRecordBytes W.C id k) := by
    change cliRd (runFiles (pqRecvInputs W st c rc))
      (pathOf (utf8 "signed-pre-keys") (keyName id)) = _
    rw [keyName_utf8, cliRd_pqRecv_preKey W st c rc (by decide) (by decide) (by decide)
      (keyName_chars id) (keyName_ne id)
      (by rw [show "signed-pre-keys" ++ "/" ++ toString id.toNat = signedPreKeyFile id from rfl,
          recvBucket_signedPreKey]; omega)]
    rw [show "signed-pre-keys" ++ "/" ++ toString id.toNat = signedPreKeyFile id from rfl]
    simp only [encodeDir_find_at, recvBucket_signedPreKey]
    unfold blockDir6
    rw [find?_map_nodup signedPreKeyFile_inj hnd]
    cases List.lookup id st.signed with
    | none => simp [fileCapBytes]
    | some k => simp [signedRecordBytes_length_le_fileCapBytes W.C id k]
  unfold getSignedPreKey
  rw [hget]
  cases List.lookup id st.signed with
  | none => rfl
  | some k =>
    dsimp only [bind, Except.bind]
    rw [record_nonempty _ (signedRecordBytes_ne_nil W.C id k)]
    have hdec := SignedPreKeyRecordStructure.decode_encode
      ⟨id, djbKey (keyPairOf W.C k.priv).publicKey.bytes, k.priv.toList, k.sig.toList, k.timestamp⟩
      (by simp [djbKey]) (by simp [k.priv.toList_length]) (by simp [k.sig.toList_length])
    simp only [signedRecordBytes, SignedPreKeyRecord.deserialize, hdec]

theorem oneTime_get_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hnd : (st.oneTime.map Prod.fst).Nodup) (id : BitVec 32) :
    StoresGhost.opened.oneTime.get cliIo.rd (runFiles (pqRecvInputs W st c rc)) (keyName id) =
      .ok (match List.lookup id st.oneTime with
           | some (some sk) => oneTimeRecordBytes W.C id sk
           | _ => []) := by
  change cliRd (runFiles (pqRecvInputs W st c rc))
    (pathOf (utf8 "one-time-pre-keys") (keyName id)) = _
  rw [keyName_utf8, cliRd_pqRecv_preKey W st c rc (by decide) (by decide) (by decide)
    (keyName_chars id) (keyName_ne id)
    (by rw [show "one-time-pre-keys" ++ "/" ++ toString id.toNat = oneTimePreKeyFile id from rfl,
        recvBucket_oneTimePreKey]; omega)]
  rw [show "one-time-pre-keys" ++ "/" ++ toString id.toNat = oneTimePreKeyFile id from rfl]
  simp only [encodeDir_find_at, recvBucket_oneTimePreKey]
  rw [show Option.map Prod.snd
      (List.find? (fun x => x.1 == oneTimePreKeyFile id) (blockDir7 W st).reverse) =
      (List.lookup id st.oneTime).map
        (fun k => match k with | some sk => oneTimeRecordBytes W.C id sk | none => []) from
    find?_map_nodup oneTimePreKeyFile_inj hnd
      (fun i k => match k with | some sk => oneTimeRecordBytes W.C i sk | none => []) id]
  cases List.lookup id st.oneTime with
  | none => simp [fileCapBytes]
  | some o =>
    cases o with
    | none => simp [fileCapBytes]
    | some sk => simp [oneTimeRecordBytes_length_le_fileCapBytes W.C id sk]

theorem getPreKey_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hnd : (st.oneTime.map Prod.fst).Nodup) (id : BitVec 32) :
    getPreKey cliIo.rd (runFiles (pqRecvInputs W st c rc)) StoresGhost.opened.oneTime id =
      match List.lookup id st.oneTime with
      | some (some sk) =>
        .ok ⟨⟨id, djbKey (keyPairOf W.C sk).publicKey.bytes, sk.toList⟩⟩
      | _ => .error () := by
  unfold getPreKey
  rw [oneTime_get_pqRecv W st c rc hnd id]
  cases List.lookup id st.oneTime with
  | none => rfl
  | some o =>
    cases o with
    | none => rfl
    | some sk =>
      dsimp only [bind, Except.bind]
      rw [record_nonempty _ (oneTimeRecordBytes_ne_nil W.C id sk)]
      have hdec := PreKeyRecordStructure.decode_encode
        ⟨id, djbKey (keyPairOf W.C sk).publicKey.bytes, sk.toList⟩
        (by simp [djbKey]) (by simp [sk.toList_length])
      simp only [oneTimeRecordBytes, PreKeyRecord.deserialize, hdec]

theorem kyberOneTime_get_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hnd : (st.kyberOneTime.map Prod.fst).Nodup) (id : BitVec 32) :
    StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (keyName id) =
      .ok (match List.lookup id st.kyberOneTime with
           | some (some k) => kyberRecordBytes id k
           | _ => []) := by
  change cliRd (runFiles (pqRecvInputs W st c rc))
    (pathOf (utf8 "one-time-kyber-pre-keys") (keyName id)) = _
  rw [keyName_utf8, cliRd_pqRecv_preKey W st c rc (by decide) (by decide) (by decide)
    (keyName_chars id) (keyName_ne id)
    (by rw [show "one-time-kyber-pre-keys" ++ "/" ++ toString id.toNat =
        oneTimeKyberPreKeyFile id from rfl, recvBucket_oneTimeKyberPreKey]; omega)]
  rw [show "one-time-kyber-pre-keys" ++ "/" ++ toString id.toNat =
      oneTimeKyberPreKeyFile id from rfl]
  simp only [encodeDir_find_at, recvBucket_oneTimeKyberPreKey]
  rw [show Option.map Prod.snd
      (List.find? (fun x => x.1 == oneTimeKyberPreKeyFile id) (blockDir8 st).reverse) =
      (List.lookup id st.kyberOneTime).map
        (fun k => match k with | some k => kyberRecordBytes id k | none => []) from
    find?_map_nodup oneTimeKyberPreKeyFile_inj hnd
      (fun i k => match k with | some k => kyberRecordBytes i k | none => []) id]
  cases List.lookup id st.kyberOneTime with
  | none => simp [fileCapBytes]
  | some o =>
    cases o with
    | none => simp [fileCapBytes]
    | some k => simp [kyberRecordBytes_length_le_fileCapBytes id k]

theorem kyberLastResort_get_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hnd : (st.kyberLastResort.map Prod.fst).Nodup) (id : BitVec 32) :
    StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (keyName id) =
      .ok (match List.lookup id st.kyberLastResort with
           | some (k, _) => kyberRecordBytes id k
           | none => []) := by
  change cliRd (runFiles (pqRecvInputs W st c rc))
    (pathOf (utf8 "last-resort-kyber-pre-keys") (keyName id)) = _
  rw [keyName_utf8, cliRd_pqRecv_preKey W st c rc (by decide) (by decide) (by decide)
    (keyName_chars id) (keyName_ne id)
    (by rw [show "last-resort-kyber-pre-keys" ++ "/" ++ toString id.toNat =
        lastResortKyberPreKeyFile id from rfl, recvBucket_lastResortKyberPreKey]; omega)]
  rw [show "last-resort-kyber-pre-keys" ++ "/" ++ toString id.toNat =
      lastResortKyberPreKeyFile id from rfl]
  simp only [encodeDir_find_at, recvBucket_lastResortKyberPreKey]
  rw [find?_lastResort_rec st hnd id]
  cases List.lookup id st.kyberLastResort with
  | none => simp [fileCapBytes]
  | some p => simp [kyberRecordBytes_length_le_fileCapBytes id p.1]

theorem kyberBaseKeys_get_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hnd : (st.kyberLastResort.map Prod.fst).Nodup) (id : BitVec 32) :
    StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (baseKeysName id) =
      let bs := match List.lookup id st.kyberLastResort with
        | some (_, seen) => baseKeysBytes seen
        | none => []
      if bs.length ≤ fileCapBytes then .ok bs else .error () := by
  change cliRd (runFiles (pqRecvInputs W st c rc))
    (pathOf (utf8 "last-resort-kyber-pre-keys") (baseKeysName id)) = _
  rw [baseKeysName_utf8, cliRd_pqRecv_preKey W st c rc (by decide) (by decide)
    (by decide) (baseKeys_chars id) (baseKeys_ne id)
    (by rw [show "last-resort-kyber-pre-keys" ++ "/" ++ (toString id.toNat ++ ".base-keys") =
        baseKeysFile id by simp [baseKeysFile, String.append_assoc], recvBucket_baseKeysFile];
        omega)]
  rw [show "last-resort-kyber-pre-keys" ++ "/" ++ (toString id.toNat ++ ".base-keys") =
      baseKeysFile id by simp [baseKeysFile, String.append_assoc]]
  simp only [encodeDir_find_at, recvBucket_baseKeysFile]
  rw [find?_lastResort_baseKeys st hnd id]
  cases List.lookup id st.kyberLastResort <;> rfl

def kyberLookup (st : PqParty) (id : BitVec 32) : Option PqKyberKey :=
  match List.lookup id st.kyberOneTime with
  | some (some k) => some k
  | _ => (List.lookup id st.kyberLastResort).map (·.1)

theorem keysFor_eq (st : PqParty) (m : PreKeyMessageFields) :
    preKeysNamedBy st m =
      match List.lookup m.spkId st.signed with
      | none => none
      | some s =>
        match kyberLookup st m.kpkId with
        | none => none
        | some k =>
          (match m.opkId with
           | none => some none
           | some j =>
             match List.lookup j st.oneTime with
             | some (some sk) => some (some (j, sk))
             | _ => none).map fun o =>
            { spkId := m.spkId, spkPriv := s.priv, kpkId := m.kpkId,
              kpkPub := k.pub, kpkSec := k.sec, opk := o } := by
  unfold preKeysNamedBy kyberLookup
  cases List.lookup m.spkId st.signed with
  | none => rfl
  | some s =>
    cases List.lookup m.kpkId st.kyberOneTime with
    | none => rfl
    | some o => cases o <;> rfl

theorem kyberGet_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hnd1 : (st.kyberOneTime.map Prod.fst).Nodup)
    (hnd2 : (st.kyberLastResort.map Prod.fst).Nodup) (id : BitVec 32) :
    StoresGhost.opened.kyber.get cliIo.rd (runFiles (pqRecvInputs W st c rc)) id =
      match kyberLookup st id with
      | some k => .ok ⟨⟨id, kyberKey k.pub, 8#8 :: k.sec.toList, k.sig.toList, k.timestamp⟩⟩
      | none => .error () := by
  unfold KyberGhost.get kyberLookup
  rw [kyberOneTime_get_pqRecv W st c rc hnd1 id, kyberLastResort_get_pqRecv W st c rc hnd2 id]
  have deser_eq : ∀ k : PqKyberKey,
      record KyberPreKeyRecord.deserialize (kyberRecordBytes id k) =
        .ok (some ⟨⟨id, kyberKey k.pub, 8#8 :: k.sec.toList, k.sig.toList, k.timestamp⟩⟩) := by
    intro k
    rw [record_nonempty _ (kyberRecordBytes_ne_nil id k)]
    have hdec := SignedPreKeyRecordStructure.decode_encode
      ⟨id, kyberKey k.pub, 8#8 :: k.sec.toList, k.sig.toList, k.timestamp⟩
      (by simp [kyberKey]) (by simp [k.sec.toList_length]) (by simp [k.sig.toList_length])
    simp only [kyberRecordBytes, KyberPreKeyRecord.deserialize, hdec]
  cases List.lookup id st.kyberOneTime with
  | none =>
    cases List.lookup id st.kyberLastResort with
    | none => rfl
    | some p =>
      dsimp only [bind, Except.bind, pure, Except.pure, Option.map_some]
      rw [deser_eq p.1]; rfl
  | some o =>
    cases o with
    | none =>
      cases List.lookup id st.kyberLastResort with
      | none => rfl
      | some p =>
        dsimp only [bind, Except.bind, pure, Except.pure, Option.map_some]
        rw [deser_eq p.1]; rfl
    | some k =>
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [deser_eq k]

theorem pkStoreKeys_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st) (m : PreKeyMessageFields) :
    pkStoreKeys (runFiles (pqRecvInputs W st c rc)) m = preKeysNamedBy st m := by
  rcases hwf with ⟨_, _, hnd_spk, hnd_opk, hnd_kot, hnd_klr⟩
  rw [keysFor_eq]
  unfold pkStoreKeys
  try dsimp only
  rw [getSignedPreKey_pqRecv W st c rc hnd_spk m.spkId,
    kyberGet_pqRecv W st c rc hnd_kot hnd_klr m.kpkId]
  cases List.lookup m.spkId st.signed with
  | none => rfl
  | some s =>
    cases kyberLookup st m.kpkId with
    | none => rfl
    | some k =>
      try dsimp only
      have hv1 : pkVec? 32 s.priv.toList = some s.priv := pkVec?_toList s.priv
      have hv2 : pkVecTag? 8 1568 (kyberKey k.pub) = some k.pub := pkVecTag?_cons_self 8#8 k.pub
      have hv3 : pkVecTag? 8 3168 (8#8 :: k.sec.toList) = some k.sec :=
        pkVecTag?_cons_self 8#8 k.sec
      rw [hv1, hv2, hv3]
      cases m.opkId with
      | none => rfl
      | some j =>
        try dsimp only
        rw [getPreKey_pqRecv W st c rc hnd_opk j]
        cases List.lookup j st.oneTime with
        | none => rfl
        | some o =>
          cases o with
          | none => rfl
          | some sk =>
            try dsimp only
            rw [pkVec?_toList sk]
            rfl

/-! ## Chunk encoding and pre-key consumption -/

private def chunkOf (p : BitVec 32 × List.Vector (BitVec 8) 32) : List (BitVec 8) :=
  SignalSession.le32 p.1 ++ djbKey p.2

private theorem chunkOf_len (p : BitVec 32 × List.Vector (BitVec 8) 32) :
    (chunkOf p).length = 37 := by
  simp [chunkOf, SignalSession.le32, djbKey]

private theorem chunkOf_inj : Function.Injective chunkOf := by
  rintro ⟨s1, b1⟩ ⟨s2, b2⟩ h
  unfold chunkOf SignalSession.le32 djbKey at h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  rcases h with ⟨e0, e1, e2, e3, _, eb⟩
  have hs : s1 = s2 := by
    rw [← le32_concat_bytes s1, ← le32_concat_bytes s2, e0, e1, e2, e3]
  exact Prod.ext hs (Subtype.ext eb)

private theorem flatten_chunks_len :
    ∀ seen : List (BitVec 32 × List.Vector (BitVec 8) 32),
      (baseKeysBytes seen).length = seen.length * 37
  | [] => rfl
  | p :: rest => by
    change (chunkOf p ++ baseKeysBytes rest).length = (rest.length + 1) * 37
    rw [List.length_append, chunkOf_len, flatten_chunks_len rest]
    omega

private theorem drop_take_chunks :
    ∀ (seen : List (BitVec 32 × List.Vector (BitVec 8) 32)) (idx : Nat) (h : idx < seen.length),
      ((baseKeysBytes seen).drop (idx * 37)).take 37 = chunkOf (seen[idx]'h)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | p :: rest, 0, _ => by
    change ((chunkOf p ++ baseKeysBytes rest).drop 0).take 37 = chunkOf p
    rw [List.drop_zero, List.take_append_of_le_length (Nat.le_of_eq (chunkOf_len p).symm),
      List.take_of_length_le (Nat.le_of_eq (chunkOf_len p))]
  | p :: rest, idx + 1, h => by
    change ((chunkOf p ++ baseKeysBytes rest).drop ((idx + 1) * 37)).take 37 =
      chunkOf (rest[idx]'(Nat.lt_of_succ_lt_succ h))
    rw [List.drop_append, chunkOf_len p, show (idx + 1) * 37 - 37 = idx * 37 by omega]
    have hdrop : (chunkOf p).drop ((idx + 1) * 37) = [] :=
      List.drop_eq_nil_of_le (by rw [chunkOf_len]; omega)
    rw [hdrop, List.nil_append]
    exact drop_take_chunks rest idx (Nat.lt_of_succ_lt_succ h)

theorem hasChunk_baseKeysBytes (seen : List (BitVec 32 × List.Vector (BitVec 8) 32))
    (spkId : BitVec 32) (baseKey : List.Vector (BitVec 8) 32) :
    hasChunk (baseKeysBytes seen) (baseKeyEntry spkId ⟨baseKey⟩) =
      decide ((spkId, baseKey) ∈ seen) := by
  have heq_used : baseKeyEntry spkId ⟨baseKey⟩ = chunkOf (spkId, baseKey) := rfl
  have hulen : (chunkOf (spkId, baseKey)).length = 37 := chunkOf_len _
  unfold hasChunk
  rw [heq_used, hulen, flatten_chunks_len seen, Nat.mul_div_cancel _ (by omega : 0 < 37)]
  cases hmem : decide ((spkId, baseKey) ∈ seen) with
  | true =>
    have hm : (spkId, baseKey) ∈ seen := of_decide_eq_true hmem
    obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hm
    apply List.any_eq_true.mpr
    refine ⟨idx, List.mem_range.mpr hidx, ?_⟩
    rw [drop_take_chunks seen idx hidx, hget]
    exact beq_self_eq_true _
  | false =>
    have hnm : (spkId, baseKey) ∉ seen := of_decide_eq_false hmem
    apply Bool.eq_false_iff.mpr
    intro hany
    obtain ⟨idx, hidx, hbeq⟩ := List.any_eq_true.mp hany
    have hlt : idx < seen.length := List.mem_range.mp hidx
    rw [drop_take_chunks seen idx hlt] at hbeq
    have he := chunkOf_inj (beq_iff_eq.mp hbeq)
    exact hnm (he ▸ List.getElem_mem hlt)

theorem baseKeysBytes_append_single (seen : List (BitVec 32 × List.Vector (BitVec 8) 32))
    (spkId : BitVec 32) (baseKey : List.Vector (BitVec 8) 32) :
    baseKeysBytes (seen ++ [(spkId, baseKey)]) =
      baseKeysBytes seen ++ baseKeyEntry spkId ⟨baseKey⟩ := by
  simp [baseKeysBytes, baseKeyEntry, Cli.le32, SignalSession.le32, PublicKey.serialize, djbKey,
    djbType]

theorem kyberMark_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st) (m : PreKeyMessageFields)
    (hlr_some : List.lookup m.kpkId st.kyberOneTime = none ∨
                List.lookup m.kpkId st.kyberOneTime = some none →
                (List.lookup m.kpkId st.kyberLastResort).isSome) :
    match StoresGhost.opened.kyber.mark cliIo.rd (runFiles (pqRecvInputs W st c rc))
            m.kpkId m.spkId ⟨m.baseKey⟩,
          markKyberUsed st m with
    | (.error _, _), none => True
    | (.ok (), kyber'), some st1 =>
      (∃ k1, List.lookup m.kpkId st.kyberOneTime = some (some k1) ∧
        kyber' = { StoresGhost.opened.kyber with
          oneTime := StoresGhost.opened.kyber.oneTime.put (keyName m.kpkId) [] } ∧
        st1 = { st with kyberOneTime := st.kyberOneTime.map fun (i, k) =>
          if i = m.kpkId then (i, none) else (i, k) }) ∨
      (∃ k2 seen, List.lookup m.kpkId st.kyberLastResort = some (k2, seen) ∧
        (m.spkId, m.baseKey) ∉ seen ∧
        kyber' = { StoresGhost.opened.kyber with
          lastResort := StoresGhost.opened.kyber.lastResort.put (baseKeysName m.kpkId)
            (baseKeysBytes (seen ++ [(m.spkId, m.baseKey)])) } ∧
        st1 = { st with kyberLastResort := st.kyberLastResort.map fun (i, k, s) =>
          if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s) })
    | _, _ => False := by
  rcases hwf with ⟨_, _, _, _, hnd_kot, hnd_klr⟩
  unfold KyberGhost.mark markKyberUsed
  rw [kyberOneTime_get_pqRecv W st c rc hnd_kot m.kpkId,
    kyberBaseKeys_get_pqRecv W st c rc hnd_klr m.kpkId]
  by_cases hkot_some : ∃ k1, List.lookup m.kpkId st.kyberOneTime = some (some k1)
  · obtain ⟨k1, hkot⟩ := hkot_some
    rw [hkot]
    dsimp only
    obtain ⟨b, bs, hcons⟩ := List.exists_cons_of_ne_nil (kyberRecordBytes_ne_nil m.kpkId k1)
    rw [hcons]
    exact Or.inl ⟨k1, rfl, rfl, rfl⟩
  · have hno : List.lookup m.kpkId st.kyberOneTime = none ∨
        List.lookup m.kpkId st.kyberOneTime = some none := by
      cases h : List.lookup m.kpkId st.kyberOneTime with
      | none => exact Or.inl rfl
      | some o =>
        cases o with
        | none => exact Or.inr rfl
        | some k1 => exact absurd ⟨k1, h⟩ hkot_some
    have his := hlr_some hno
    rcases hno with h | h <;> rw [h]
    all_goals
      dsimp only
      cases hlr : List.lookup m.kpkId st.kyberLastResort with
      | none => rw [hlr] at his; simp at his
      | some p =>
        rcases p with ⟨k2, seen⟩
        dsimp only
        by_cases hcap : (baseKeysBytes seen).length ≤ fileCapBytes
        · simp only [hcap, ↓reduceIte]
          have hnotgt : ¬ (37 * seen.length > fileCapBytes) := by
            have hfl := flatten_chunks_len seen
            omega
          have hulen : (baseKeyEntry m.spkId ⟨m.baseKey⟩).length = 37 :=
            chunkOf_len (m.spkId, m.baseKey)
          have hmod : (baseKeysBytes seen).length % (baseKeyEntry m.spkId ⟨m.baseKey⟩).length = 0 := by
            rw [flatten_chunks_len, hulen, Nat.mul_mod_left]
          rw [ite_eq_right (not_not.mpr hmod)]
          by_cases hmem : (m.spkId, m.baseKey) ∈ seen
          · have hc_true :
                hasChunk (baseKeysBytes seen) (baseKeyEntry m.spkId ⟨m.baseKey⟩) = true := by
              rw [hasChunk_baseKeysBytes]; exact decide_eq_true hmem
            have hor : 37 * seen.length > fileCapBytes ∨ (m.spkId, m.baseKey) ∈ seen :=
              Or.inr hmem
            simp only [hc_true, hor, ↓reduceIte]
          · have hc_false :
                hasChunk (baseKeysBytes seen) (baseKeyEntry m.spkId ⟨m.baseKey⟩) = false := by
              rw [hasChunk_baseKeysBytes]; exact decide_eq_false hmem
            have hnor : ¬ (37 * seen.length > fileCapBytes ∨ (m.spkId, m.baseKey) ∈ seen) :=
              fun h => h.elim hnotgt hmem
            simp only [hc_false, Bool.false_eq_true, hnor, ↓reduceIte]
            exact Or.inr ⟨k2, seen, rfl, hmem,
              congrArg (fun bs => { StoresGhost.opened.kyber with
                lastResort := StoresGhost.opened.kyber.lastResort.put (baseKeysName m.kpkId) bs })
                (baseKeysBytes_append_single seen m.spkId m.baseKey).symm, trivial⟩
        · simp only [hcap, ↓reduceIte]
          have hgt : 37 * seen.length > fileCapBytes := by
            have hfl := flatten_chunks_len seen
            omega
          have hor : 37 * seen.length > fileCapBytes ∨ (m.spkId, m.baseKey) ∈ seen := Or.inl hgt
          simp only [hor, ↓reduceIte]

theorem removePreKey_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hnd : (st.oneTime.map Prod.fst).Nodup) {j : BitVec 32}
    {sk : List.Vector (BitVec 8) 32} (hl : List.lookup j st.oneTime = some (some sk)) :
    (removePreKey cliIo.rd (runFiles (pqRecvInputs W st c rc)) StoresGhost.opened.oneTime j).2 =
      StoresGhost.opened.oneTime.put (keyName j) [] := by
  unfold removePreKey
  rw [oneTime_get_pqRecv W st c rc hnd j, hl]
  dsimp only
  obtain ⟨b, bs, hcons⟩ := List.exists_cons_of_ne_nil (oneTimeRecordBytes_ne_nil W.C j sk)
  rw [hcons]

end CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
