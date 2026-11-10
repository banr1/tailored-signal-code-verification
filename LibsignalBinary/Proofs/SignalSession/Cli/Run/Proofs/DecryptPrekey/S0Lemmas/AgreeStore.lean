/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreePaths
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.List.SplitOn.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-!
# Base Store Lookups on `pqRecvInputs`

Proves `runFiles` and `cliRd` lookup lemmas, nodup reverse-lookup helpers, own/peer identity reads,
`loadRec_pqRecv_eq`, and non-emptiness of encoded pre-key records on `runFiles (pqRecvInputs W st c rc)`.
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

/-! ## `runFiles` and `cliRd` lookup on `pqRecvInputs` -/

theorem runFiles_pqRecv_dir (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) {d : String} (hd : d ∈ partyDirs) (hns : '/' ∉ d.toList) :
    runFiles (pqRecvInputs W st c rc) d = some .dir :=
  runFiles_pqRecv_dir_v031 W st c rc hd hns

theorem cliRd_pqRecv_of_bucket (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) {p : List (BitVec 8)} {q : String}
    (hp : pathStr p = q)
    (hb : blockingAncestorF (runFiles (pqRecvInputs W st c rc)) q = none)
    (hq : IsRecvFile q)
    (hpos : 1 ≤ recvBucket q ∧ recvBucket q ≤ 9) :
    cliRd (runFiles (pqRecvInputs W st c rc)) p =
      let bs := (((encodeDir W st).reverse.find? (fun x => x.1 == q)).map Prod.snd).getD []
      if bs.length ≤ fileCapBytes then .ok bs else .error () := by
  unfold cliRd readViewF
  rw [hp, hb]
  dsimp only
  rw [runFiles_pqRecv_isRecvFile W st c rc hq, find?_pqRecv_files W st c rc (by omega)]
  cases (encodeDir W st).reverse.find? (fun x => x.1 == q) with
  | none => simp [fileCapBytes]
  | some pb => by_cases hc : pb.2.length ≤ fileCapBytes <;> simp [hc]

theorem cliRd_pqRecv_preKey (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) {dir sfx : String}
    (hdir_mem : dir ∈ recvParentDirs)
    (hdir_ne : dir.toList ≠ [])
    (hdir_ch : ∀ ch ∈ dir.toList, ch.toNat < 128 ∧ ch ≠ '/' ∧ ch ≠ '<')
    (hsfx_ch : ∀ ch ∈ sfx.toList, ch.toNat < 128 ∧ ch ≠ '/' ∧ ch ≠ '<')
    (hsfx_ne : sfx.toList ≠ [] ∧ sfx ≠ ".")
    (hpos : 1 ≤ recvBucket (dir ++ "/" ++ sfx) ∧ recvBucket (dir ++ "/" ++ sfx) ≤ 9) :
    cliRd (runFiles (pqRecvInputs W st c rc)) (pathOf (utf8 dir) (utf8 sfx)) =
      let bs := (((encodeDir W st).reverse.find?
        (fun x => x.1 == dir ++ "/" ++ sfx)).map Prod.snd).getD []
      if bs.length ≤ fileCapBytes then .ok bs else .error () := by
  have hall_ascii : ∀ ch ∈ (dir ++ "/" ++ sfx).toList, ch.toNat < 128 := by
    intro ch hch
    simp only [String.toList_append, List.mem_append] at hch
    rcases hch with (h | h) | h
    · exact (hdir_ch ch h).1
    · rw [show "/".toList = ['/'] from rfl, List.mem_singleton] at h; subst h; decide
    · exact (hsfx_ch ch h).1
  have hdir_p : dir ∈ partyDirs := (recvParentDirs_props hdir_mem).2.2.2.1
  have hq_rf : IsRecvFile (dir ++ "/" ++ sfx) :=
    Or.inr ⟨dir, sfx, hdir_mem, fun m => (hsfx_ch '/' m).2.1 rfl, hsfx_ne.1, hsfx_ne.2, rfl⟩
  rw [pathOf_utf8_eq hdir_ne]
  exact cliRd_pqRecv_of_bucket W st c rc
    (pathStr_utf8_ascii hall_ascii)
    (blockingAncestorF_dir_sfx
      (fun m => (hdir_ch '/' m).2.1 rfl)
      (fun m => (hsfx_ch '/' m).2.1 rfl)
      (runFiles_pqRecv_dir W st c rc hdir_p (fun m => (hdir_ch '/' m).2.1 rfl)))
    hq_rf hpos

/-! ## Nodup list lookup lemmas -/

theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List (α × β)} {k : α} {v : β}, List.lookup k xs = some v → (k, v) ∈ xs
  | [], _, _, h => nomatch h
  | (a, b) :: rest, k, v, h => by
    unfold List.lookup at h
    cases hka : (k == a)
    · rw [hka] at h; exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)
    · rw [hka] at h; cases h; rw [beq_iff_eq.mp hka]; exact List.mem_cons_self

theorem ne_of_lookup_eq_none {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List (α × β)} {k : α} {p : α × β}, List.lookup k xs = none → p ∈ xs → p.1 ≠ k
  | [], _, _, _, hp => nomatch hp
  | (a, b) :: rest, k, _, h, hp => by
    unfold List.lookup at h
    cases hka : (k == a)
    · rw [hka] at h
      rcases List.mem_cons.mp hp with rfl | hm
      · intro (e : a = k); rw [← e, beq_self_eq_true] at hka; nomatch hka
      · exact ne_of_lookup_eq_none h hm
    · rw [hka] at h; nomatch h

private theorem eq_of_nodup_fst {α β : Type} [DecidableEq α] :
    ∀ {xs : List (α × β)}, (xs.map Prod.fst).Nodup →
      ∀ {k : α} {v1 v2 : β}, (k, v1) ∈ xs → (k, v2) ∈ xs → v1 = v2
  | [], _, _, _, _, h1, _ => nomatch h1
  | (a, b) :: rest, hnd, k, v1, v2, h1, h2 => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases hnd with ⟨hnotmem, hnd'⟩
    rcases List.mem_cons.mp h1 with e1 | m1 <;> rcases List.mem_cons.mp h2 with e2 | m2
    · cases e1; cases e2; rfl
    · cases e1; exact absurd (List.mem_map_of_mem (f := Prod.fst) m2) hnotmem
    · cases e2; exact absurd (List.mem_map_of_mem (f := Prod.fst) m1) hnotmem
    · exact eq_of_nodup_fst hnd' m1 m2

theorem find?_reverse_unique {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)}
    {k : α} {v : β} (hmem : (k, v) ∈ l) (huniq : ∀ x ∈ l, x.1 = k → x.2 = v) :
    l.reverse.find? (fun x => x.1 == k) = some (k, v) := by
  cases hf : l.reverse.find? (fun x => x.1 == k) with
  | none =>
    have hnone := (List.find?_eq_none.mp hf) (k, v) (List.mem_reverse.mpr hmem)
    simp at hnone
  | some p =>
    rcases p with ⟨k', v'⟩
    have hk : k' = k := beq_iff_eq.mp (List.find?_some (p := fun x : α × β => x.1 == k) hf)
    subst hk
    have hm : (k', v') ∈ l := List.mem_reverse.mp (List.mem_of_find?_eq_some hf)
    have hv : v' = v := huniq _ hm rfl
    rw [hv]

theorem find?_map_nodup {α : Type} {f : BitVec 32 → String} (hf : Function.Injective f)
    {xs : List (BitVec 32 × α)} (hnd : (xs.map Prod.fst).Nodup)
    (val : BitVec 32 → α → List (BitVec 8)) (id : BitVec 32) :
    ((xs.map fun (i, a) => (f i, val i a)).reverse.find? (fun x => x.1 == f id)).map Prod.snd =
      (List.lookup id xs).map (val id) := by
  cases hl : List.lookup id xs with
  | none =>
    have hfn : (xs.map fun (i, a) => (f i, val i a)).reverse.find? (fun x => x.1 == f id) =
        none := by
      rw [List.find?_eq_none]
      intro x hx hbeq
      obtain ⟨⟨i, a⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
      exact ne_of_lookup_eq_none hl hm (hf (beq_iff_eq.mp hbeq))
    rw [hfn]; rfl
  | some a0 =>
    have hm0 : (id, a0) ∈ xs := mem_of_lookup_eq_some hl
    have hfn : (xs.map fun (i, a) => (f i, val i a)).reverse.find? (fun x => x.1 == f id) =
        some (f id, val id a0) := by
      refine find?_reverse_unique (List.mem_map_of_mem (f := fun (i, a) => (f i, val i a)) hm0) ?_
      intro x hx heq
      obtain ⟨⟨i, a⟩, hm, rfl⟩ := List.mem_map.mp hx
      have hi : i = id := hf heq
      subst hi
      rw [eq_of_nodup_fst hnd hm hm0]
    rw [hfn]; rfl

theorem find?_lastResort_rec (st : PqParty)
    (hnd : (st.kyberLastResort.map Prod.fst).Nodup) (id : BitVec 32) :
    ((blockDir9 st).reverse.find? (fun x => x.1 == lastResortKyberPreKeyFile id)).map Prod.snd =
      (List.lookup id st.kyberLastResort).map fun p => kyberRecordBytes id p.1 := by
  unfold blockDir9
  cases hl : List.lookup id st.kyberLastResort with
  | none =>
    have hfn : ((st.kyberLastResort.map fun (i, k, seen) =>
        [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
         (baseKeysFile i, baseKeysBytes seen)]).flatten).reverse.find?
        (fun x => x.1 == lastResortKyberPreKeyFile id) = none := by
      rw [List.find?_eq_none]
      intro x hx hbeq
      have heq := beq_iff_eq.mp hbeq
      obtain ⟨l, hml, hmx⟩ := List.mem_flatten.mp (List.mem_reverse.mp hx)
      obtain ⟨⟨i, k, seen⟩, hm, rfl⟩ := List.mem_map.mp hml
      rcases List.mem_cons.mp hmx with rfl | hm2
      · have hi := lastResortKyberPreKeyFile_inj heq
        subst hi
        exact ne_of_lookup_eq_none hl hm rfl
      · rw [List.mem_singleton] at hm2; subst hm2
        exact lastResort_ne_baseKeys id i heq.symm
    rw [hfn]; rfl
  | some p0 =>
    rcases p0 with ⟨k0, seen0⟩
    have hm0 : (id, (k0, seen0)) ∈ st.kyberLastResort := mem_of_lookup_eq_some hl
    have hmem_flat : (lastResortKyberPreKeyFile id, kyberRecordBytes id k0) ∈
        (st.kyberLastResort.map fun (i, k, seen) =>
          [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
           (baseKeysFile i, baseKeysBytes seen)]).flatten :=
      List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hm0, List.mem_cons_self⟩
    have hfn := find?_reverse_unique hmem_flat fun x hx heq => by
      obtain ⟨l, hml, hmx⟩ := List.mem_flatten.mp hx
      obtain ⟨⟨i, k, seen⟩, hm, rfl⟩ := List.mem_map.mp hml
      rcases List.mem_cons.mp hmx with rfl | hm2
      · have hi := lastResortKyberPreKeyFile_inj heq
        subst hi
        have he := eq_of_nodup_fst hnd hm hm0
        cases he; rfl
      · rw [List.mem_singleton] at hm2; subst hm2
        exact absurd heq.symm (lastResort_ne_baseKeys id i)
    rw [hfn]; rfl

theorem find?_lastResort_baseKeys (st : PqParty)
    (hnd : (st.kyberLastResort.map Prod.fst).Nodup) (id : BitVec 32) :
    ((blockDir9 st).reverse.find? (fun x => x.1 == baseKeysFile id)).map Prod.snd =
      (List.lookup id st.kyberLastResort).map fun p => baseKeysBytes p.2 := by
  unfold blockDir9
  cases hl : List.lookup id st.kyberLastResort with
  | none =>
    have hfn : ((st.kyberLastResort.map fun (i, k, seen) =>
        [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
         (baseKeysFile i, baseKeysBytes seen)]).flatten).reverse.find?
        (fun x => x.1 == baseKeysFile id) = none := by
      rw [List.find?_eq_none]
      intro x hx hbeq
      have heq := beq_iff_eq.mp hbeq
      obtain ⟨l, hml, hmx⟩ := List.mem_flatten.mp (List.mem_reverse.mp hx)
      obtain ⟨⟨i, k, seen⟩, hm, rfl⟩ := List.mem_map.mp hml
      rcases List.mem_cons.mp hmx with rfl | hm2
      · exact lastResort_ne_baseKeys i id heq
      · rw [List.mem_singleton] at hm2; subst hm2
        have hi := baseKeysFile_inj heq
        subst hi
        exact ne_of_lookup_eq_none hl hm rfl
    rw [hfn]; rfl
  | some p0 =>
    rcases p0 with ⟨k0, seen0⟩
    have hm0 : (id, (k0, seen0)) ∈ st.kyberLastResort := mem_of_lookup_eq_some hl
    have hmem_flat : (baseKeysFile id, baseKeysBytes seen0) ∈
        (st.kyberLastResort.map fun (i, k, seen) =>
          [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
           (baseKeysFile i, baseKeysBytes seen)]).flatten :=
      List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hm0,
        List.mem_cons_of_mem _ List.mem_cons_self⟩
    have hfn := find?_reverse_unique hmem_flat fun x hx heq => by
      obtain ⟨l, hml, hmx⟩ := List.mem_flatten.mp hx
      obtain ⟨⟨i, k, seen⟩, hm, rfl⟩ := List.mem_map.mp hml
      rcases List.mem_cons.mp hmx with rfl | hm2
      · exact absurd heq (lastResort_ne_baseKeys i id)
      · rw [List.mem_singleton] at hm2; subst hm2
        have hi := baseKeysFile_inj heq
        subst hi
        have he := eq_of_nodup_fst hnd hm hm0
        cases he; rfl
    rw [hfn]; rfl

/-! ## Identity and `loadRec` reads on `pqRecvInputs` -/

theorem encodeDir_find_at (W : PEParams) (st : PqParty) (q : String) :
    (encodeDir W st).reverse.find? (fun x => x.1 == q) =
      match recvBucket q with
      | 1 => (blockDir1 st).reverse.find? (fun x => x.1 == q)
      | 2 => (blockDir2 W st).reverse.find? (fun x => x.1 == q)
      | 3 => (blockDir3 st).reverse.find? (fun x => x.1 == q)
      | 4 => (blockDir4 st).reverse.find? (fun x => x.1 == q)
      | 5 => (blockDir5 st).reverse.find? (fun x => x.1 == q)
      | 6 => (blockDir6 W st).reverse.find? (fun x => x.1 == q)
      | 7 => (blockDir7 W st).reverse.find? (fun x => x.1 == q)
      | 8 => (blockDir8 st).reverse.find? (fun x => x.1 == q)
      | 9 => (blockDir9 st).reverse.find? (fun x => x.1 == q)
      | _ => none := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := bucket_blockDir W st
  rw [encodeDir_blocks]
  exact find?_select_block b1 b2 b3 b4 b5 b6 b7 b8 b9 q

theorem keyPair_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    StoresGhost.opened.identity.keyPair cliIo.rd (runFiles (pqRecvInputs W st c rc)) =
      .ok ⟨⟨(keyPairOf W.C st.me.idPriv).publicKey⟩, ⟨Ratchet.clampScalar st.me.idPriv⟩⟩ := by
  let enc := IdentityKeyPairStructure.encode
    ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩
  have hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (utf8 "identity-key-pair") = .ok enc := by
    change cliRd (runFiles (pqRecvInputs W st c rc)) (utf8 "identity-key-pair") = .ok enc
    rw [cliRd_pqRecv_of_bucket W st c rc
      (pathStr_utf8_ascii (by decide))
      (by unfold blockingAncestorF ancestors pathComps; rfl)
      (Or.inl (by simp [recvRootFiles, identityKeyPairFile]))
      (by rw [show "identity-key-pair" = identityKeyPairFile from rfl, recvBucket_idKeyPair];
          omega)]
    rw [encodeDir_find_at, show recvBucket "identity-key-pair" = 2 from recvBucket_idKeyPair]
    have hcap : enc.length ≤ fileCapBytes :=
      LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.idKeyPair_encode_length_le_fileCapBytes
        W.C st.me.idPriv
    simp [blockDir2, identityKeyPairFile, enc, hcap]
  have hdec := IdentityKeyPairStructure.decode_encode
    ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩
    (by simp [djbKey]) (by simp [st.me.idPriv.toList_length])
  have hik : decodeIdentityKey (djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes) =
      .ok ⟨(keyPairOf W.C st.me.idPriv).publicKey⟩ :=
    decodeIdentityKey_serialize ⟨(keyPairOf W.C st.me.idPriv).publicKey⟩
  have hsk : deserializePrivateKey st.me.idPriv.toList = .ok ⟨Ratchet.clampScalar st.me.idPriv⟩ := by
    simp only [deserializePrivateKey, st.me.idPriv.toList_length, ↓reduceDIte, InitS0.vec_eta]
  unfold IdGhost.keyPair
  rw [hget]
  dsimp only [bind, Except.bind]
  unfold IdentityKeyPair.tryFrom
  rw [hdec]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hik]
  dsimp only
  rw [hsk]

theorem le32_concat_bytes (v : BitVec 32) :
    v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  ext i hi
  have eq_bit : ∀ k, k = i → v.getLsbD k = v[i]'hi := fun _ e => e ▸ rfl
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split_ifs <;> exact eq_bit _ (by omega)

theorem regId_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    StoresGhost.opened.identity.regId cliIo.rd (runFiles (pqRecvInputs W st c rc)) =
      .ok st.me.regId := by
  have hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (utf8 "registration-id") = .ok (SignalSession.le32 st.me.regId) := by
    change cliRd (runFiles (pqRecvInputs W st c rc)) (utf8 "registration-id") =
      .ok (SignalSession.le32 st.me.regId)
    rw [cliRd_pqRecv_of_bucket W st c rc
      (pathStr_utf8_ascii (by decide))
      (by unfold blockingAncestorF ancestors pathComps; rfl)
      (Or.inl (by simp [recvRootFiles, registrationIdFile]))
      (by rw [show "registration-id" = registrationIdFile from rfl, recvBucket_regId]; omega)]
    rw [encodeDir_find_at, show recvBucket "registration-id" = 3 from recvBucket_regId]
    have hcap : (SignalSession.le32 st.me.regId).length ≤ fileCapBytes :=
      LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.le32_length_le_fileCapBytes st.me.regId
    simp [blockDir3, registrationIdFile, hcap]
  unfold IdGhost.regId
  rw [hget]
  simp only [SignalSession.le32, Except.bind, le32_concat_bytes]

theorem idPeer_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    StoresGhost.opened.identity.peer cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (RunRefine.addrValE st.party.other) = .ok st.peerId := by
  have hget : StoresGhost.opened.identity.peers.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (RunRefine.addrValE st.party.other).name =
      .ok (match st.peerId with | some k => k.serialize | none => []) := by
    change cliRd (runFiles (pqRecvInputs W st c rc))
      (pathOf (utf8 "identities") (utf8 (partyAddressName st.party.other))) = _
    rw [cliRd_pqRecv_preKey W st c rc (by decide) (by decide) (by decide)
      (by cases st.party.other <;> decide)
      (by cases st.party.other <;> decide)
      (by rw [show "identities" ++ "/" ++ partyAddressName st.party.other =
          identityFile (partyAddressName st.party.other) from rfl, recvBucket_identityFile]; omega)]
    rw [show "identities" ++ "/" ++ partyAddressName st.party.other =
        identityFile (partyAddressName st.party.other) from rfl,
      encodeDir_find_at, recvBucket_identityFile]
    cases h : st.peerId with
    | none => simp [blockDir4, h, fileCapBytes]
    | some k =>
      have hcap : k.serialize.length ≤ fileCapBytes :=
        LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.identityKey_serialize_length_le_fileCapBytes k
      simp [blockDir4, h, hcap]
  unfold IdGhost.peer
  rw [hget]
  cases st.peerId with
  | none => rfl
  | some k =>
    dsimp only [bind, Except.bind]
    have hser : k.serialize = 5#8 :: k.publicKey.bytes.toList := rfl
    have hdec := decodeIdentityKey_serialize k
    rw [hser] at hdec ⊢
    simp only [record, hdec]

theorem loadRec_pqRecv_eq {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope) (st : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st) :
    Slots.loadRec Scope (runFiles (pqRecvInputs W st c rc))
      (RunRefine.addrValE st.party.other) =
      .ok (st.session.map fun (x, g) =>
        E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) := by
  have htxt : addressText (RunRefine.addrValE st.party.other) =
      utf8 ((partyAddress st.party.other).text) := by
    unfold addressText decimalText RunRefine.addrValE Address.text partyAddress
    have h1 : toString (1 : Nat) = "1" := rfl
    have h1' : toString (1#8).toNat = "1" := rfl
    rw [h1, h1', utf8_append, utf8_append]
  have hget : StoresGhost.opened.sessions.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (addressText (RunRefine.addrValE st.party.other)) =
      .ok (match st.session with
           | some (x, g) => encodeRecordUnderExtras (fun _ => x) g
           | none => []) := by
    change cliRd (runFiles (pqRecvInputs W st c rc))
      (pathOf (utf8 "sessions") (addressText (RunRefine.addrValE st.party.other))) = _
    rw [htxt, cliRd_pqRecv_preKey W st c rc (by decide) (by decide) (by decide)
      (by cases st.party.other <;> decide)
      (by cases st.party.other <;> decide)
      (by rw [show "sessions" ++ "/" ++ (partyAddress st.party.other).text =
          sessionFile (partyAddress st.party.other) from rfl, recvBucket_sessionFile]; omega)]
    rw [show "sessions" ++ "/" ++ (partyAddress st.party.other).text =
        sessionFile (partyAddress st.party.other) from rfl,
      encodeDir_find_at, recvBucket_sessionFile]
    cases h : st.session with
    | none => simp [blockDir5, h, fileCapBytes]
    | some xg =>
      rcases xg with ⟨x, g⟩
      obtain ⟨⟨g₀, hR₀, _, hs₀⟩, _⟩ := hwf.1 x g h
      have hcap : (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes := by
        unfold encodeRecordUnderExtras
        rw [← hs₀]
        exact LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.reachPq_encodeRecordX_length_le_fileCapBytes hR₀
      simp [blockDir5, h, hcap]
  unfold Slots.loadRec
  rw [hget]
  cases hs : st.session with
  | none => rfl
  | some xg =>
    rcases xg with ⟨x, g⟩
    dsimp only [Option.map_some]
    let r0 := E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g
    have henc : encodeRecordUnderExtras (fun _ => x) g = E2E.Record.encodeRecord r0 :=
      E2E.RecordX.encodeRecordX_eq_toRecord (fun _ => x) g
    have hne : E2E.Record.encodeRecord r0 ≠ [] := by
      unfold r0 E2E.Record.toRecord E2E.Record.encodeRecord E2E.Record.msgField
        E2E.Record.lenField
      dsimp only [Option.map_some]
      intro hnil
      exact encodeVarint_ne_nil _ (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hnil).1).1
    obtain ⟨b, bs, hcons⟩ := List.exists_cons_of_ne_nil hne
    rw [henc, hcons]
    dsimp only
    have hsc : Scope r0 := hcov st x g hwf hs
    have hex : ∃ r, E2E.Record.encodeRecord r = b :: bs ∧ Scope r := ⟨r0, hcons, hsc⟩
    simp only [hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    exact congrArg (Except.ok ∘ Option.some) (hinj _ r0 hspec.2 hsc (hspec.1.trans hcons.symm))

/-! ## Non-emptiness and deserialization of encoded pre-key records -/

private theorem encodeBytes3_cons_ne_nil (tag : Nat) (b : BitVec 8) (bs : List (BitVec 8)) :
    encodeProto3BytesField tag (b :: bs) ≠ [] := by
  unfold encodeProto3BytesField encodeBytesField
  simp only [reduceCtorEq, ↓reduceIte]
  intro hnil
  exact List.cons_ne_nil b bs (List.append_eq_nil_iff.mp hnil).2

theorem signedRecordBytes_ne_nil (C : Crypto) (id : BitVec 32) (k : PqSignedKey) :
    signedRecordBytes C id k ≠ [] := by
  unfold signedRecordBytes SignedPreKeyRecordStructure.encode djbKey
  intro hnil
  have h1 := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp
    (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hnil).1).1).1).2
  exact encodeBytes3_cons_ne_nil 2 5#8 _ h1

theorem kyberRecordBytes_ne_nil (id : BitVec 32) (k : PqKyberKey) :
    kyberRecordBytes id k ≠ [] := by
  unfold kyberRecordBytes SignedPreKeyRecordStructure.encode kyberKey
  intro hnil
  have h1 := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp
    (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hnil).1).1).1).2
  exact encodeBytes3_cons_ne_nil 2 8#8 _ h1

theorem oneTimeRecordBytes_ne_nil (C : Crypto) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    oneTimeRecordBytes C id sk ≠ [] := by
  unfold oneTimeRecordBytes PreKeyRecordStructure.encode djbKey
  intro hnil
  have h1 := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hnil).1).2
  exact encodeBytes3_cons_ne_nil 2 5#8 _ h1

theorem record_nonempty {α ε : Type} (dec : List (BitVec 8) → Except ε α)
    {bs : List (BitVec 8)} (hne : bs ≠ []) :
    record dec bs = match dec bs with | .ok a => .ok (some a) | .error _ => .error () := by
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  rfl

end CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
