/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.List.SplitOn.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.InitPaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreePaths
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-!
# Proof of `decPkOk₀_pqRecv` and Wire Helpers

Proves `SignalMessage.tryFrom` serialization preservation, store directory lookup invariants,
identity and session-matching properties, and pre-key file well-formedness to establish
`decPkOk₀_pqRecv` on `runFiles (pqRecvInputs W st c rc)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine

/-! ## Serialization preservation for `SignalMessage.tryFrom` -/

theorem tryFrom_serialized {codec : SignalMessageProtoCodec} {bs : List (BitVec 8)} {i : SignalMessage}
    (hi : SignalMessage.tryFrom codec bs = .ok i) : i.serialized = bs := by
  unfold SignalMessage.tryFrom at hi
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at hi
  split at hi; · cases hi
  split at hi; · cases hi
  split at hi; · cases hi
  split at hi
  · split at hi
    · split at hi
      · cases hi
      · split at hi
        · split at hi
          · injection hi with h
            subst h
            rfl
          · cases hi
        · cases hi
    · cases hi
  · cases hi

/-! ## Decimal `toString` helpers -/

private theorem toString_nat_ascii (n : Nat) : ∀ c ∈ (toString n).toList, c.toNat < 128 :=
  fun _ hc => (toString_nat_char_props n hc).1

private theorem slash_not_mem_toString_nat (n : Nat) : '/' ∉ (toString n).toList :=
  fun hc => (toString_nat_char_props n hc).2.2.1 rfl

private theorem dot_not_mem_toString_nat (n : Nat) : '.' ∉ (toString n).toList :=
  fun hc => (toString_nat_char_props n hc).2.1 rfl

private theorem bitvec32_eq_of_slash {dir : String} {i j : BitVec 32}
    (h : (dir ++ "/") ++ toString j.toNat = dir ++ "/" ++ toString i.toNat) : j = i := by
  have hl := congrArg String.toList h
  simp only [String.toList_append, List.append_assoc] at hl
  have heq : toString j.toNat = toString i.toNat :=
    String.toList_inj.mp (List.append_cancel_left (List.append_cancel_left hl))
  exact BitVec.eq_of_toNat_eq (toString_nat_inj heq)

/-! ## Directory and file lookups on `pqRecvInputs` -/

private theorem find?_reverse_none {l : List (String × List (BitVec 8))} {q : String}
    (h : ∀ x ∈ l, x.1 ≠ q) : l.reverse.find? (fun x => x.1 == q) = none := by
  rw [List.find?_eq_none]
  intro x hx hbeq
  exact h x (List.mem_reverse.mp hx) (beq_iff_eq.mp hbeq)

private theorem find?_reverse_split {pre post : List (String × List (BitVec 8))} {q : String}
    {bs : List (BitVec 8)} (h : ∀ x ∈ post, x.1 ≠ q) :
    (pre ++ (q, bs) :: post).reverse.find? (fun x => x.1 == q) = some (q, bs) := by
  rw [List.reverse_append, List.reverse_cons, List.find?_append, List.find?_append,
    find?_reverse_none h]
  simp only [Option.none_or, List.find?, beq_self_eq_true, Option.some_or]

private theorem mem_files_of_find_some {i : Inputs} {q : String} {pb : String × List (BitVec 8)}
    (hf : i.files.reverse.find? (fun x => x.1 == q) = some pb) :
    pb ∈ i.files ∧ pb.1 = q := by
  have hpb := List.find?_some hf
  exact ⟨List.mem_reverse.mp (List.mem_of_find?_eq_some hf), beq_iff_eq.mp hpb⟩

private theorem subDir_read_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) {dir name : String}
    (hdir : dir ∈ recvParentDirs)
    (hdir_ascii : ∀ ch ∈ dir.toList, ch.toNat < 128)
    (hname_slash : '/' ∉ name.toList)
    (hname_ne : name.toList ≠ []) (hname_ndot : name ≠ ".")
    (hname_ascii : ∀ ch ∈ name.toList, ch.toNat < 128) :
    (DirGhost.new (utf8 dir)).get cliIo.rd (runFiles (pqRecvInputs W st c rc)) (utf8 name) =
      match (pqRecvInputs W st c rc).files.reverse.find?
             (fun x => x.1 == dir ++ "/" ++ name) with
      | some pb => if pb.2.length ≤ fileCapBytes then .ok pb.2 else .error ()
      | none => .ok [] := by
  let q := dir ++ "/" ++ name
  change cliRd (runFiles (pqRecvInputs W st c rc)) (pathOf (utf8 dir) (utf8 name)) = _
  obtain ⟨hdir_slash, hdir_ne, _, hdir_p, _⟩ := recvParentDirs_props hdir
  have hq_ascii : ∀ ch ∈ q.toList, ch.toNat < 128 := by
    intro ch hch
    simp only [q, String.toList_append, List.mem_append] at hch
    rcases hch with (hd | hs) | hn
    · exact hdir_ascii ch hd
    · rw [show "/".toList = ['/'] from rfl, List.mem_singleton] at hs; subst hs; decide
    · exact hname_ascii ch hn
  have hp : pathStr (pathOf (utf8 dir) (utf8 name)) = q := by
    rw [pathOf_utf8_eq hdir_ne, pathStr_utf8_ascii hq_ascii]
  have hb : blockingAncestorF (runFiles (pqRecvInputs W st c rc)) q = none :=
    blockingAncestorF_dir_sfx hdir_slash hname_slash
      (runFiles_pqRecv_dir_v031 W st c rc hdir_p hdir_slash)
  have hq_rf : IsRecvFile q :=
    Or.inr ⟨dir, name, hdir, hname_slash, hname_ne, hname_ndot, rfl⟩
  unfold cliRd readViewF
  rw [hp, hb]
  dsimp only
  rw [runFiles_pqRecv_isRecvFile W st c rc hq_rf]
  cases (pqRecvInputs W st c rc).files.reverse.find? (fun x => x.1 == q) with
  | none => rfl
  | some pb => dsimp only; by_cases hc : pb.2.length ≤ fileCapBytes <;> simp [hc]

/-! ## Canonical `pqPost` tail and prefix classification -/

private def pqPost (W : PEParams) (st : PqParty) (rc : BitVec 256) :
    List (String × List (BitVec 8)) :=
  st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)) ++
  st.oneTime.map (fun (i, k) =>
    (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) =>
    (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
     (baseKeysFile i, baseKeysBytes seen)]).flatten ++
  [(coinsFile, HMAC.keyToBytes32 rc)]

private theorem take16_prefix (p s : String) (h : 16 ≤ p.toList.length) :
    (p ++ s).toList.take 16 = p.toList.take 16 := by
  rw [String.toList_append, List.take_append_of_le_length h]

private theorem take16_slash (dir name : String) (h : 16 ≤ (dir.toList ++ ['/']).length) :
    (dir ++ "/" ++ name).toList.take 16 = (dir.toList ++ ['/']).take 16 := by
  have heq : (dir ++ "/" ++ name).toList = (dir.toList ++ ['/']) ++ name.toList := by
    simp only [String.toList_append, List.append_assoc]
    rfl
  rw [heq, List.take_append_of_le_length h]

private theorem signedPreKeyFile_take16 (i : BitVec 32) :
    (signedPreKeyFile i).toList.take 16 = "signed-pre-keys/".toList :=
  take16_prefix "signed-pre-keys/" _ (by decide)

private theorem oneTimePreKeyFile_take16 (i : BitVec 32) :
    (oneTimePreKeyFile i).toList.take 16 = "one-time-pre-key".toList :=
  take16_prefix "one-time-pre-keys/" _ (by decide)

private theorem oneTimeKyberPreKeyFile_take16 (i : BitVec 32) :
    (oneTimeKyberPreKeyFile i).toList.take 16 = "one-time-kyber-p".toList :=
  take16_prefix "one-time-kyber-pre-keys/" _ (by decide)

private theorem lastResortKyberPreKeyFile_take16 (i : BitVec 32) :
    (lastResortKyberPreKeyFile i).toList.take 16 = "last-resort-kybe".toList :=
  take16_prefix "last-resort-kyber-pre-keys/" _ (by decide)

private theorem baseKeysFile_take16 (i : BitVec 32) :
    (baseKeysFile i).toList.take 16 = "last-resort-kybe".toList := by
  unfold baseKeysFile
  rw [String.append_assoc]
  exact take16_prefix "last-resort-kyber-pre-keys/" _ (by decide)

private theorem pqPost_not_root_or_sess {W : PEParams} {st : PqParty} {rc : BitVec 256}
    {x : String × List (BitVec 8)} (hx : x ∈ pqPost W st rc) :
    x.1 ≠ identityKeyPairFile ∧ ∀ P, x.1 ≠ sessionFile (partyAddress P) := by
  unfold pqPost at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (((h1 | h2) | h3) | h4) | rfl
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp h1
    dsimp only
    have ht := signedPreKeyFile_take16 i
    refine ⟨fun e => ?_, fun P e => ?_⟩
    · rw [e] at ht; exact absurd ht (by dsimp [identityKeyPairFile]; decide)
    · rw [e] at ht; cases P <;> exact absurd ht (by decide)
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp h2
    dsimp only
    have ht := oneTimePreKeyFile_take16 i
    refine ⟨fun e => ?_, fun P e => ?_⟩
    · rw [e] at ht; exact absurd ht (by dsimp [identityKeyPairFile]; decide)
    · rw [e] at ht; cases P <;> exact absurd ht (by decide)
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp h3
    dsimp only
    have ht := oneTimeKyberPreKeyFile_take16 i
    refine ⟨fun e => ?_, fun P e => ?_⟩
    · rw [e] at ht; exact absurd ht (by dsimp [identityKeyPairFile]; decide)
    · rw [e] at ht; cases P <;> exact absurd ht (by decide)
  · obtain ⟨_, hl, hm⟩ := List.mem_flatten.mp h4
    obtain ⟨⟨i, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_cons.mp hm with rfl | hm
    · dsimp only
      have ht := lastResortKyberPreKeyFile_take16 i
      refine ⟨fun e => ?_, fun P e => ?_⟩
      · rw [e] at ht; exact absurd ht (by dsimp [identityKeyPairFile]; decide)
      · rw [e] at ht; cases P <;> exact absurd ht (by decide)
    · rcases List.mem_singleton.mp hm with rfl
      dsimp only
      have ht := baseKeysFile_take16 i
      refine ⟨fun e => ?_, fun P e => ?_⟩
      · rw [e] at ht; exact absurd ht (by dsimp [identityKeyPairFile]; decide)
      · rw [e] at ht; cases P <;> exact absurd ht (by decide)
  · dsimp only
    refine ⟨InitS0.string_ne_of_toList (s1 := coinsFile) (s2 := identityKeyPairFile) (by decide),
      fun P e => ?_⟩
    cases P <;> exact absurd (congrArg String.toList e) (by decide)

/-! ## `keyPairLt_pqRecv` and `idPairDerived_pqRecv` -/

theorem own_get_idKeyPair_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (utf8 "identity-key-pair") = .ok (InitS0.ikBytes W st) := by
  change cliRd (runFiles (pqRecvInputs W st c rc)) (utf8 "identity-key-pair") =
    .ok (InitS0.ikBytes W st)
  have hp : pathStr (utf8 "identity-key-pair") = "identity-key-pair" :=
    pathStr_utf8_ascii (by decide)
  have hb : blockingAncestorF (runFiles (pqRecvInputs W st c rc)) "identity-key-pair" = none := by
    unfold blockingAncestorF ancestors pathComps
    rfl
  have hf : runFiles (pqRecvInputs W st c rc) "identity-key-pair" =
      some (.file (InitS0.ikBytes W st)) := by
    rw [runFiles_pqRecv_isRecvFile W st c rc
      (Or.inl (by simp [recvRootFiles, identityKeyPairFile]))]
    let post :=
      [(registrationIdFile, SignalSession.le32 st.me.regId)] ++
      (match st.peerId with
       | none => []
       | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]) ++
      (match st.session with
       | none => []
       | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]) ++
      pqPost W st rc
    have heq : (pqRecvInputs W st c rc).files =
        [(addressFile, textBytes (partyAddress st.party).text)] ++
          ("identity-key-pair", InitS0.ikBytes W st) :: post := by
      cases h1 : st.peerId <;> cases h2 : st.session <;>
        simp [pqRecvInputs, pqInputs, encodeDir, InitS0.ikBytes, identityKeyPairFile, post, pqPost,
          h1, h2]
      all_goals
        refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ rfl)
        · exact List.map_congr_left fun x _ => by cases x.2 <;> rfl
        · exact List.map_congr_left fun x _ => by cases x.2 <;> rfl
    have hpost : ∀ x ∈ post, x.1 ≠ "identity-key-pair" := by
      intro x hx
      have hx' : x = (registrationIdFile, SignalSession.le32 st.me.regId) ∨
          x ∈ (match st.peerId with
               | none => []
               | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]) ∨
          x ∈ (match st.session with
               | none => []
               | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]) ∨
          x ∈ pqPost W st rc := by
        simpa only [post, List.mem_append, List.mem_singleton, or_assoc] using hx
      rcases hx' with rfl | hp' | hs' | htail
      · exact InitS0.string_ne_of_toList (s1 := registrationIdFile) (s2 := "identity-key-pair")
          (by decide)
      · cases hpid : st.peerId with
        | none => rw [hpid] at hp'; cases hp'
        | some _ =>
          rw [hpid] at hp'; rcases List.mem_singleton.mp hp' with rfl
          dsimp only; cases st.party.other <;> exact InitS0.string_ne_of_toList (by decide)
      · cases hses : st.session with
        | none => rw [hses] at hs'; cases hs'
        | some _ =>
          rw [hses] at hs'; rcases List.mem_singleton.mp hs' with rfl
          dsimp only; cases st.party.other <;> exact InitS0.string_ne_of_toList (by decide)
      · exact (pqPost_not_root_or_sess htail).1
    rw [heq, find?_reverse_split hpost]
    rfl
  have hcap : (InitS0.ikBytes W st).length ≤ fileCapBytes :=
    LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.idKeyPair_encode_length_le_fileCapBytes
      W.C st.me.idPriv
  unfold cliRd readViewF
  rw [hp, hb, hf]
  simp only [hcap, ↓reduceIte]

theorem keyPairLt_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) :
    ∀ bs, StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (utf8 "identity-key-pair") = .ok bs → bs.length < 2 ^ 32 := by
  intro bs hget
  rw [own_get_idKeyPair_pqRecv] at hget
  injection hget with hget
  subst hget
  have hlt : (InitS0.ikBytes W st).length < 2 ^ 31 :=
    (hwf.2.1 (identityKeyPairFile, InitS0.ikBytes W st) (by simp [encodeDir, InitS0.ikBytes])).1
  omega

theorem idPairDerived_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ∀ kp, StoresGhost.opened.identity.keyPair cliIo.rd (runFiles (pqRecvInputs W st c rc)) =
      .ok kp → kp.identityKey.publicKey = (keyPairOf W.C kp.privateKey.bytes).publicKey := by
  intro kp hkp
  unfold IdGhost.keyPair at hkp
  rw [own_get_idKeyPair_pqRecv] at hkp
  dsimp only [Bind.bind, Except.bind] at hkp
  rw [InitS0.tryFrom_ikBytes] at hkp
  injection hkp with hkp
  subst hkp
  simp only [keyPairOf, InitS0.clampScalar_idem]

/-! ## `sessMatch_pqRecv` -/

private theorem addressText_addrValE (P : Party) :
    addressText (addrValE P) = utf8 (partyAddress P).text := by
  unfold addressText decimalText addrValE Address.text partyAddress
  simp only [← utf8_append]
  rfl

private theorem sessGet_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    StoresGhost.opened.sessions.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (addressText (addrValE st.party.other)) =
      match st.session with
      | some (x, g) =>
        if (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes then
          .ok (encodeRecordUnderExtras (fun _ => x) g)
        else .error ()
      | none => .ok [] := by
  rw [addressText_addrValE]
  have hread := subDir_read_pqRecv W st c rc
    (dir := "sessions") (name := (partyAddress st.party.other).text)
    (by decide) (by decide)
    (by cases st.party.other <;> decide)
    (by cases st.party.other <;> decide)
    (by cases st.party.other <;> decide)
    (by cases st.party.other <;> decide)
  have hsf : "sessions" ++ "/" ++ (partyAddress st.party.other).text = sessionFile (partyAddress st.party.other) :=
    rfl
  rw [hsf] at hread
  rw [show StoresGhost.opened.sessions = DirGhost.new (utf8 "sessions") from rfl, hread]
  cases hses : st.session with
  | none =>
    have hnone : (pqRecvInputs W st c rc).files.reverse.find?
        (fun x => x.1 == sessionFile (partyAddress st.party.other)) = none := by
      apply find?_reverse_none
      intro x hx
      have heq_f : (pqRecvInputs W st c rc).files =
          [(addressFile, textBytes (partyAddress st.party).text),
           (identityKeyPairFile, InitS0.ikBytes W st),
           (registrationIdFile, SignalSession.le32 st.me.regId)] ++
          (match st.peerId with
           | none => []
           | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]) ++ pqPost W st rc := by
        cases h1 : st.peerId <;>
          simp [pqRecvInputs, pqInputs, encodeDir, InitS0.ikBytes, h1, hses, pqPost]
        all_goals
          refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ rfl)
          · exact List.map_congr_left fun x _ => by cases x.2 <;> rfl
          · exact List.map_congr_left fun x _ => by cases x.2 <;> rfl
      rw [heq_f] at hx
      have hx' : x ∈ [(addressFile, textBytes (partyAddress st.party).text),
                      (identityKeyPairFile, InitS0.ikBytes W st),
                      (registrationIdFile, SignalSession.le32 st.me.regId)] ∨
          x ∈ (match st.peerId with
               | none => []
               | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]) ∨
          x ∈ pqPost W st rc := by
        simpa only [List.mem_append, or_assoc] using hx
      rcases hx' with hroot | hp | htail
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hroot
        rcases hroot with rfl | rfl | rfl <;>
          (dsimp only; cases st.party.other <;> exact InitS0.string_ne_of_toList (by decide))
      · cases hpid : st.peerId with
        | none => rw [hpid] at hp; cases hp
        | some _ =>
          rw [hpid] at hp; rcases List.mem_singleton.mp hp with rfl
          dsimp only; cases st.party.other <;> exact InitS0.string_ne_of_toList (by decide)
      · exact (pqPost_not_root_or_sess htail).2 st.party.other
    rw [hnone]
  | some xg =>
    rcases xg with ⟨x, g⟩
    have heq_f : (pqRecvInputs W st c rc).files =
        ([(addressFile, textBytes (partyAddress st.party).text),
          (identityKeyPairFile, InitS0.ikBytes W st),
          (registrationIdFile, SignalSession.le32 st.me.regId)] ++
         (match st.peerId with
          | none => []
          | some k => [(identityFile (partyAddressName st.party.other), k.serialize)])) ++
        (sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g) :: pqPost W st rc := by
      cases h1 : st.peerId <;>
        simp [pqRecvInputs, pqInputs, encodeDir, InitS0.ikBytes, h1, hses, pqPost]
      all_goals
        refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ rfl)
        · exact List.map_congr_left fun x _ => by cases x.2 <;> rfl
        · exact List.map_congr_left fun x _ => by cases x.2 <;> rfl
    have hpost : ∀ y ∈ pqPost W st rc, y.1 ≠ sessionFile (partyAddress st.party.other) :=
      fun _ hy => (pqPost_not_root_or_sess hy).2 st.party.other
    rw [heq_f, find?_reverse_split hpost]

theorem sessMatch_pqRecv (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hinj : Slots.EncodeInjOn Scope) (st : PqParty)
    (hcov : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (m : PreKeyMessageFields) (c : List (BitVec 8)) (rc : BitVec 256)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m)
    {r : SessionRecord (List (BitVec 8))}
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hload : Slots.loadRec Scope (runFiles (pqRecvInputs W st c rc))
      (addrValE st.party.other) = .ok (some r))
    (hcur : r.currentSession = some s) :
    s.state.version = 4#32 ∧ s.aliceBaseKey = 5#8 :: m.baseKey.toList := by
  unfold Slots.loadRec at hload
  rw [sessGet_pqRecv] at hload
  cases hses : st.session with
  | none =>
    rw [hses] at hload
    dsimp only at hload
    cases hload
  | some xg =>
    rcases xg with ⟨x, g⟩
    rw [hses] at hload
    dsimp only at hload
    by_cases hcap : (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes
    · simp only [hcap, ↓reduceIte] at hload
      cases henc : encodeRecordUnderExtras (fun _ => x) g with
      | nil =>
        rw [henc] at hload
        dsimp only at hload
        cases hload
      | cons b bs =>
        rw [henc] at hload
        dsimp only at hload
        split at hload
        · next hex =>
          injection hload with hr
          injection hr with hr
          obtain ⟨henc_choose, hS_choose⟩ := Classical.choose_spec hex
          have hr0 : E2E.Record.encodeRecord
              (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) = b :: bs := by
            rw [← E2E.RecordX.encodeRecordX_eq_toRecord, henc]
          have heq_r : r = E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g := by
            rw [← hr]
            exact hinj _ _ hS_choose (hcov x g hses) (henc_choose.trans hr0.symm)
          subst heq_r
          simp only [E2E.Record.toRecord, Option.some.injEq] at hcur
          subst hcur
          obtain ⟨hbk, hver⟩ := hmatch x g hses
          refine ⟨?_, ?_⟩
          · simp [SessionState.version, hver]
          · simpa [E2E.RecordX.extrasOf, E2E.RecordX.toSessionExtras, djbKey] using hbk
        · cases hload
    · simp only [hcap, ↓reduceIte] at hload
      cases hload

/-! ## `preKeysWf` and `baseKeysLt` on `pqRecvInputs` -/

private def pqPre (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  [(addressFile, textBytes (partyAddress st.party).text),
   (identityKeyPairFile, InitS0.ikBytes W st),
   (registrationIdFile, SignalSession.le32 st.me.regId)] ++
  (match st.peerId with
   | none => []
   | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]) ++
  (match st.session with
   | none => []
   | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)])

private theorem not_take16_pre {W : PEParams} {st : PqParty} {x : String × List (BitVec 8)}
    (hx : x ∈ pqPre W st) {t : List Char}
    (ht : t ∈ ["signed-pre-keys/".toList, "one-time-pre-key".toList,
               "one-time-kyber-p".toList, "last-resort-kybe".toList]) :
    x.1.toList.take 16 ≠ t := by
  unfold pqPre at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ht
  rcases hx with ((rfl | rfl | rfl) | hp) | hs
  · rcases ht with rfl | rfl | rfl | rfl <;> (dsimp [addressFile]; decide)
  · rcases ht with rfl | rfl | rfl | rfl <;> (dsimp [identityKeyPairFile]; decide)
  · rcases ht with rfl | rfl | rfl | rfl <;> (dsimp [registrationIdFile]; decide)
  · cases hpid : st.peerId with
    | none => rw [hpid] at hp; cases hp
    | some _ =>
      rw [hpid] at hp; rcases List.mem_singleton.mp hp with rfl
      dsimp only
      cases st.party.other <;>
        (rcases ht with rfl | rfl | rfl | rfl <;> decide)
  · cases hses : st.session with
    | none => rw [hses] at hs; cases hs
    | some _ =>
      rw [hses] at hs; rcases List.mem_singleton.mp hs with rfl
      dsimp only
      cases st.party.other <;>
        (rcases ht with rfl | rfl | rfl | rfl <;> decide)

private theorem split_pqRecv_files (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) {pb : String × List (BitVec 8)} (hmem : pb ∈ (pqRecvInputs W st c rc).files) :
    pb ∈ pqPre W st ∨
    pb ∈ st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)) ∨
    pb ∈ st.oneTime.map (fun (i, k) =>
      (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ∨
    pb ∈ st.kyberOneTime.map (fun (i, k) =>
      (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ∨
    pb ∈ (st.kyberLastResort.map fun (i, k, seen) =>
      [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
       (baseKeysFile i, baseKeysBytes seen)]).flatten ∨
    pb = (coinsFile, HMAC.keyToBytes32 rc) := by
  have heq : (pqRecvInputs W st c rc).files = pqPre W st ++ pqPost W st rc := by
    cases h1 : st.peerId <;> cases h2 : st.session <;>
      simp [pqRecvInputs, pqInputs, encodeDir, InitS0.ikBytes, pqPre, pqPost, h1, h2]
    all_goals
      refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ rfl)
      · exact List.map_congr_left fun x _ => by cases x.2 <;> rfl
      · exact List.map_congr_left fun x _ => by cases x.2 <;> rfl
  rw [heq] at hmem
  rcases List.mem_append.mp hmem with h0 | hpost
  · exact .inl h0
  · unfold pqPost at hpost
    simp only [List.mem_append, List.mem_singleton] at hpost
    rcases hpost with (((h1 | h2) | h3) | h4) | h5
    · exact .inr (.inl h1)
    · exact .inr (.inr (.inl h2))
    · exact .inr (.inr (.inr (.inl h3)))
    · exact .inr (.inr (.inr (.inr (.inl h4))))
    · exact .inr (.inr (.inr (.inr (.inr h5))))

theorem signedWf_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    ∀ i bs, StoresGhost.opened.signed.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (keyName i) = .ok bs → bs = [] ∨ ∃ k, bs = signedRecordBytes W.C i k := by
  intro i bs hget
  have hread := subDir_read_pqRecv W st c rc
    (dir := "signed-pre-keys") (name := toString i.toNat)
    (by decide) (by decide)
    (slash_not_mem_toString_nat i.toNat)
    (toString_nat_ne_nil i.toNat) (toString_nat_ne_dot i.toNat)
    (toString_nat_ascii i.toNat)
  rw [show StoresGhost.opened.signed = DirGhost.new (utf8 "signed-pre-keys") from rfl,
      show keyName i = utf8 (toString i.toNat) from rfl, hread] at hget
  cases hf : (pqRecvInputs W st c rc).files.reverse.find?
      (fun x => x.1 == "signed-pre-keys" ++ "/" ++ toString i.toNat) with
  | none =>
    rw [hf] at hget; injection hget with hget; exact .inl hget.symm
  | some pb =>
    rw [hf] at hget; dsimp only at hget
    by_cases hcap : pb.2.length ≤ fileCapBytes
    · simp only [hcap, ↓reduceIte] at hget; injection hget with hget
      obtain ⟨hmem, hp1⟩ := mem_files_of_find_some hf
      have ht16 : pb.1.toList.take 16 = "signed-pre-keys/".toList := by
        rw [hp1]; exact take16_slash "signed-pre-keys" _ (by decide)
      rcases split_pqRecv_files W st c rc hmem with h0 | h1 | h2 | h3 | h4 | rfl
      · exact absurd ht16 (not_take16_pre h0 (by simp))
      · obtain ⟨⟨j, k⟩, _, rfl⟩ := List.mem_map.mp h1
        dsimp only at hp1 hget
        have hji : j = i := bitvec32_eq_of_slash (dir := "signed-pre-keys") hp1
        subst hji
        exact .inr ⟨k, hget.symm⟩
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h2
        dsimp only at ht16
        rw [oneTimePreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h3
        dsimp only at ht16
        rw [oneTimeKyberPreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨_, hl, hm⟩ := List.mem_flatten.mp h4
        obtain ⟨⟨j, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
        rcases List.mem_cons.mp hm with rfl | hm
        · dsimp only at ht16
          rw [lastResortKyberPreKeyFile_take16] at ht16
          exact absurd ht16 (by decide)
        · rcases List.mem_singleton.mp hm with rfl
          dsimp only at ht16
          rw [baseKeysFile_take16] at ht16
          exact absurd ht16 (by decide)
      · dsimp only at ht16
        exact absurd ht16 (by dsimp [coinsFile]; decide)
    · simp only [hcap, ↓reduceIte] at hget; nomatch hget

theorem oneTimeWf_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    ∀ i bs, StoresGhost.opened.oneTime.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (keyName i) = .ok bs → bs = [] ∨ ∃ sk, bs = oneTimeRecordBytes W.C i sk := by
  intro i bs hget
  have hread := subDir_read_pqRecv W st c rc
    (dir := "one-time-pre-keys") (name := toString i.toNat)
    (by decide) (by decide)
    (slash_not_mem_toString_nat i.toNat)
    (toString_nat_ne_nil i.toNat) (toString_nat_ne_dot i.toNat)
    (toString_nat_ascii i.toNat)
  rw [show StoresGhost.opened.oneTime = DirGhost.new (utf8 "one-time-pre-keys") from rfl,
      show keyName i = utf8 (toString i.toNat) from rfl, hread] at hget
  cases hf : (pqRecvInputs W st c rc).files.reverse.find?
      (fun x => x.1 == "one-time-pre-keys" ++ "/" ++ toString i.toNat) with
  | none =>
    rw [hf] at hget; injection hget with hget; exact .inl hget.symm
  | some pb =>
    rw [hf] at hget; dsimp only at hget
    by_cases hcap : pb.2.length ≤ fileCapBytes
    · simp only [hcap, ↓reduceIte] at hget; injection hget with hget
      obtain ⟨hmem, hp1⟩ := mem_files_of_find_some hf
      have ht16 : pb.1.toList.take 16 = "one-time-pre-key".toList := by
        rw [hp1]; exact take16_slash "one-time-pre-keys" _ (by decide)
      rcases split_pqRecv_files W st c rc hmem with h0 | h1 | h2 | h3 | h4 | rfl
      · exact absurd ht16 (not_take16_pre h0 (by simp))
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h1
        dsimp only at ht16
        rw [signedPreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨⟨j, opt⟩, _, rfl⟩ := List.mem_map.mp h2
        dsimp only at hp1 hget
        have hji : j = i := bitvec32_eq_of_slash (dir := "one-time-pre-keys") hp1
        subst hji
        cases opt with
        | none => exact .inl hget.symm
        | some sk => exact .inr ⟨sk, hget.symm⟩
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h3
        dsimp only at ht16
        rw [oneTimeKyberPreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨_, hl, hm⟩ := List.mem_flatten.mp h4
        obtain ⟨⟨j, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
        rcases List.mem_cons.mp hm with rfl | hm
        · dsimp only at ht16
          rw [lastResortKyberPreKeyFile_take16] at ht16
          exact absurd ht16 (by decide)
        · rcases List.mem_singleton.mp hm with rfl
          dsimp only at ht16
          rw [baseKeysFile_take16] at ht16
          exact absurd ht16 (by decide)
      · dsimp only at ht16
        exact absurd ht16 (by dsimp [coinsFile]; decide)
    · simp only [hcap, ↓reduceIte] at hget; nomatch hget

theorem kyberOneTimeWf_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ∀ i bs, StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (keyName i) = .ok bs → bs = [] ∨ ∃ k, bs = kyberRecordBytes i k := by
  intro i bs hget
  have hread := subDir_read_pqRecv W st c rc
    (dir := "one-time-kyber-pre-keys") (name := toString i.toNat)
    (by decide) (by decide)
    (slash_not_mem_toString_nat i.toNat)
    (toString_nat_ne_nil i.toNat) (toString_nat_ne_dot i.toNat)
    (toString_nat_ascii i.toNat)
  rw [show StoresGhost.opened.kyber.oneTime =
        DirGhost.new (utf8 "one-time-kyber-pre-keys") from rfl,
      show keyName i = utf8 (toString i.toNat) from rfl, hread] at hget
  cases hf : (pqRecvInputs W st c rc).files.reverse.find?
      (fun x => x.1 == "one-time-kyber-pre-keys" ++ "/" ++ toString i.toNat) with
  | none =>
    rw [hf] at hget; injection hget with hget; exact .inl hget.symm
  | some pb =>
    rw [hf] at hget; dsimp only at hget
    by_cases hcap : pb.2.length ≤ fileCapBytes
    · simp only [hcap, ↓reduceIte] at hget; injection hget with hget
      obtain ⟨hmem, hp1⟩ := mem_files_of_find_some hf
      have ht16 : pb.1.toList.take 16 = "one-time-kyber-p".toList := by
        rw [hp1]; exact take16_slash "one-time-kyber-pre-keys" _ (by decide)
      rcases split_pqRecv_files W st c rc hmem with h0 | h1 | h2 | h3 | h4 | rfl
      · exact absurd ht16 (not_take16_pre h0 (by simp))
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h1
        dsimp only at ht16
        rw [signedPreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h2
        dsimp only at ht16
        rw [oneTimePreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨⟨j, opt⟩, _, rfl⟩ := List.mem_map.mp h3
        dsimp only at hp1 hget
        have hji : j = i := bitvec32_eq_of_slash (dir := "one-time-kyber-pre-keys") hp1
        subst hji
        cases opt with
        | none => exact .inl hget.symm
        | some k => exact .inr ⟨k, hget.symm⟩
      · obtain ⟨_, hl, hm⟩ := List.mem_flatten.mp h4
        obtain ⟨⟨j, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
        rcases List.mem_cons.mp hm with rfl | hm
        · dsimp only at ht16
          rw [lastResortKyberPreKeyFile_take16] at ht16
          exact absurd ht16 (by decide)
        · rcases List.mem_singleton.mp hm with rfl
          dsimp only at ht16
          rw [baseKeysFile_take16] at ht16
          exact absurd ht16 (by decide)
      · dsimp only at ht16
        exact absurd ht16 (by dsimp [coinsFile]; decide)
    · simp only [hcap, ↓reduceIte] at hget; nomatch hget

theorem kyberLastResortWf_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ∀ i bs, StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (keyName i) = .ok bs → bs = [] ∨ ∃ k, bs = kyberRecordBytes i k := by
  intro i bs hget
  have hread := subDir_read_pqRecv W st c rc
    (dir := "last-resort-kyber-pre-keys") (name := toString i.toNat)
    (by decide) (by decide)
    (slash_not_mem_toString_nat i.toNat)
    (toString_nat_ne_nil i.toNat) (toString_nat_ne_dot i.toNat)
    (toString_nat_ascii i.toNat)
  rw [show StoresGhost.opened.kyber.lastResort =
        DirGhost.new (utf8 "last-resort-kyber-pre-keys") from rfl,
      show keyName i = utf8 (toString i.toNat) from rfl, hread] at hget
  cases hf : (pqRecvInputs W st c rc).files.reverse.find?
      (fun x => x.1 == "last-resort-kyber-pre-keys" ++ "/" ++ toString i.toNat) with
  | none =>
    rw [hf] at hget; injection hget with hget; exact .inl hget.symm
  | some pb =>
    rw [hf] at hget; dsimp only at hget
    by_cases hcap : pb.2.length ≤ fileCapBytes
    · simp only [hcap, ↓reduceIte] at hget; injection hget with hget
      obtain ⟨hmem, hp1⟩ := mem_files_of_find_some hf
      have ht16 : pb.1.toList.take 16 = "last-resort-kybe".toList := by
        rw [hp1]; exact take16_slash "last-resort-kyber-pre-keys" _ (by decide)
      rcases split_pqRecv_files W st c rc hmem with h0 | h1 | h2 | h3 | h4 | rfl
      · exact absurd ht16 (not_take16_pre h0 (by simp))
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h1
        dsimp only at ht16
        rw [signedPreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h2
        dsimp only at ht16
        rw [oneTimePreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨⟨j, _⟩, _, rfl⟩ := List.mem_map.mp h3
        dsimp only at ht16
        rw [oneTimeKyberPreKeyFile_take16] at ht16
        exact absurd ht16 (by decide)
      · obtain ⟨_, hl, hm⟩ := List.mem_flatten.mp h4
        obtain ⟨⟨j, k, seen⟩, _, rfl⟩ := List.mem_map.mp hl
        rcases List.mem_cons.mp hm with rfl | hm
        · dsimp only at hp1 hget
          have hji : j = i := bitvec32_eq_of_slash (dir := "last-resort-kyber-pre-keys") hp1
          subst hji
          exact .inr ⟨k, hget.symm⟩
        · rcases List.mem_singleton.mp hm with rfl
          dsimp only at hp1
          have hl' := congrArg String.toList hp1
          unfold baseKeysFile at hl'
          simp only [String.toList_append] at hl'
          have hpre : "last-resort-kyber-pre-keys/".toList =
              "last-resort-kyber-pre-keys".toList ++ "/".toList := by decide
          rw [hpre, List.append_assoc, List.append_assoc] at hl'
          have hsuf : (toString j.toNat).toList ++ ".base-keys".toList = (toString i.toNat).toList :=
            List.append_cancel_left (List.append_cancel_left hl')
          have hdot : '.' ∈ (toString j.toNat).toList ++ ".base-keys".toList :=
            List.mem_append_right _ (by decide)
          rw [hsuf] at hdot
          exact absurd hdot (dot_not_mem_toString_nat i.toNat)
      · dsimp only at ht16
        exact absurd ht16 (by dsimp [coinsFile]; decide)
    · simp only [hcap, ↓reduceIte] at hget; nomatch hget

theorem baseKeysLt_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) :
    ∀ i bs, StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
      (baseKeysName i) = .ok bs → bs.length < 2 ^ 32 := by
  intro i bs hget
  have hbname : baseKeysName i = utf8 (toString i.toNat ++ ".base-keys") := by
    unfold baseKeysName keyName decimalText
    rw [utf8_append]
  have hn_slash : '/' ∉ (toString i.toNat ++ ".base-keys").toList := by
    rw [String.toList_append]
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact slash_not_mem_toString_nat i.toNat h1
    · exact absurd h2 (by decide)
  have hn_ne : (toString i.toNat ++ ".base-keys").toList ≠ [] := by
    intro hnil
    rw [String.toList_append] at hnil
    exact absurd (List.append_eq_nil_iff.mp hnil).2 (by decide)
  have hn_ndot : toString i.toNat ++ ".base-keys" ≠ "." := by
    intro hdot
    have hl := congrArg (fun s => s.toList.length) hdot
    rw [String.toList_append, List.length_append] at hl
    have h10 : ".base-keys".toList.length = 10 := by decide
    have h1 : ".".toList.length = 1 := by decide
    omega
  have hb_ascii : ∀ ch ∈ ".base-keys".toList, ch.toNat < 128 := by decide
  have hn_ascii : ∀ ch ∈ (toString i.toNat ++ ".base-keys").toList, ch.toNat < 128 := by
    rw [String.toList_append]
    intro ch hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact toString_nat_ascii i.toNat ch h1
    · exact hb_ascii ch h2
  have hread := subDir_read_pqRecv W st c rc
    (dir := "last-resort-kyber-pre-keys") (name := toString i.toNat ++ ".base-keys")
    (by decide) (by decide) hn_slash hn_ne hn_ndot hn_ascii
  rw [show StoresGhost.opened.kyber.lastResort =
        DirGhost.new (utf8 "last-resort-kyber-pre-keys") from rfl,
      hbname, hread] at hget
  cases hf : (pqRecvInputs W st c rc).files.reverse.find?
      (fun x => x.1 == "last-resort-kyber-pre-keys" ++ "/" ++
        (toString i.toNat ++ ".base-keys")) with
  | none =>
    rw [hf] at hget; injection hget with hget
    subst hget
    decide
  | some pb =>
    rw [hf] at hget; dsimp only at hget
    by_cases hcap : pb.2.length ≤ fileCapBytes
    · simp only [hcap, ↓reduceIte] at hget; injection hget with hget
      subst hget
      obtain ⟨hmem, hp1⟩ := mem_files_of_find_some hf
      simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hdir | hcoins
      · have hlt : pb.2.length < 2 ^ 31 := (hwf.2.1 pb hdir).1
        omega
      · subst hcoins
        have ht : ("last-resort-kyber-pre-keys" ++ "/" ++
            (toString i.toNat ++ ".base-keys")).toList.take 16 = "last-resort-kybe".toList :=
          take16_slash "last-resort-kyber-pre-keys" _ (by decide)
        rw [← hp1] at ht
        dsimp only at ht
        exact absurd ht (by dsimp [coinsFile]; decide)
    · simp only [hcap, ↓reduceIte] at hget; nomatch hget

end CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
