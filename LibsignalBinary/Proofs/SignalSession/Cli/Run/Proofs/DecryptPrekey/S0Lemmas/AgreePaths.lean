/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.List.SplitOn.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.InitPaths
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run

/-!
# Path Buckets, Decimal Injectivity, and Filesystem Lookup Helpers

Establishes injectivity and ASCII character bounds for decimal key identifiers, `utf8` / `pathOf` /
`blockingAncestorF` path lemmas, and an 11-bucket path partition (`recvBucket`) separating all
store directories in `pqRecvInputs` and `encodeDir` for lookup and commit-overwrite proofs.
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

/-! ## Decimal `toString` injectivity and character bounds -/

private def parseDecCore : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => parseDecCore cs (acc * 10 + (c.toNat - 48))

private theorem digitChar_props {r : Nat} (hr : r < 10) :
    (Nat.digitChar r).toNat - 48 = r ∧
    (Nat.digitChar r).toNat < 128 ∧
    Nat.digitChar r ≠ '.' ∧
    Nat.digitChar r ≠ '/' ∧
    Nat.digitChar r ≠ '<' := by
  match r with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | n + 10 => omega

private theorem parseDecCore_toDigitsCore :
    ∀ (fuel n : Nat) (ds : List Char), n < fuel →
      parseDecCore (Nat.toDigitsCore 10 fuel n ds) 0 = parseDecCore ds n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, ds, h => by
    unfold Nat.toDigitsCore
    dsimp only
    have hrem := (digitChar_props (Nat.mod_lt n (by omega))).1
    split
    · next hdiv =>
      simp only [parseDecCore, hrem, Nat.zero_mul, Nat.zero_add]
      have hn : n % 10 = n := Nat.mod_eq_of_lt (by omega)
      rw [hn]
    · next hdiv =>
      have hlt : n / 10 < fuel := by omega
      rw [parseDecCore_toDigitsCore fuel (n / 10) _ hlt]
      simp only [parseDecCore, hrem]
      have hdm : n / 10 * 10 + n % 10 = n := by omega
      rw [hdm]

private theorem mem_toDigitsCore :
    ∀ (fuel n : Nat) (ds : List Char) (c : Char),
      c ∈ Nat.toDigitsCore 10 fuel n ds → c ∈ ds ∨ ∃ r, r < 10 ∧ c = Nat.digitChar r
  | 0, _, ds, _, hc => Or.inl hc
  | fuel + 1, n, ds, c, hc => by
    unfold Nat.toDigitsCore at hc
    dsimp only at hc
    split at hc
    · rcases List.mem_cons.mp hc with rfl | hmem
      · exact Or.inr ⟨n % 10, Nat.mod_lt n (by omega), rfl⟩
      · exact Or.inl hmem
    · rcases mem_toDigitsCore fuel (n / 10) (Nat.digitChar (n % 10) :: ds) c hc with hmem | hex
      · rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact Or.inr ⟨n % 10, Nat.mod_lt n (by omega), rfl⟩
        · exact Or.inl hmem'
      · exact Or.inr hex

theorem toString_nat_toList_eq (n : Nat) : (toString n).toList = Nat.toDigits 10 n := by
  change (Nat.repr n).toList = Nat.toDigits 10 n
  unfold Nat.repr
  exact String.toList_ofList

theorem toString_nat_inj {n m : Nat} (h : toString n = toString m) : n = m := by
  have hl : (toString n).toList = (toString m).toList := congrArg String.toList h
  rw [toString_nat_toList_eq, toString_nat_toList_eq] at hl
  have h1 := parseDecCore_toDigitsCore (n + 1) n [] (Nat.lt_succ_self n)
  have h2 := parseDecCore_toDigitsCore (m + 1) m [] (Nat.lt_succ_self m)
  change parseDecCore (Nat.toDigits 10 n) 0 = n at h1
  change parseDecCore (Nat.toDigits 10 m) 0 = m at h2
  rw [hl] at h1
  exact h1.symm.trans h2

theorem keyId_inj {i j : BitVec 32} (h : toString i.toNat = toString j.toNat) : i = j :=
  BitVec.eq_of_toNat_eq (toString_nat_inj h)

theorem toString_nat_char_props (n : Nat) {c : Char} (hc : c ∈ (toString n).toList) :
    c.toNat < 128 ∧ c ≠ '.' ∧ c ≠ '/' ∧ c ≠ '<' := by
  rw [toString_nat_toList_eq] at hc
  rcases mem_toDigitsCore (n + 1) n [] c hc with hnil | ⟨r, hr, rfl⟩
  · nomatch hnil
  · exact (digitChar_props hr).2

private theorem toDigitsCore_ne_nil :
    ∀ (fuel n : Nat) (ds : List Char), (fuel ≠ 0 ∨ ds ≠ []) →
      Nat.toDigitsCore 10 fuel n ds ≠ []
  | 0, _, _, h => by
    rcases h with h0 | hds
    · exact absurd rfl h0
    · exact hds
  | fuel + 1, n, ds, _ => by
    unfold Nat.toDigitsCore
    dsimp only
    split
    · exact List.cons_ne_nil _ _
    · exact toDigitsCore_ne_nil fuel (n / 10) _ (Or.inr (List.cons_ne_nil _ _))

theorem toString_nat_ne_nil (n : Nat) : (toString n).toList ≠ [] := by
  rw [toString_nat_toList_eq]
  exact toDigitsCore_ne_nil (n + 1) n [] (Or.inl (Nat.succ_ne_zero n))

theorem toString_nat_ne_dot (n : Nat) : toString n ≠ "." := by
  intro h
  have hc : '.' ∈ (toString n).toList := by rw [h]; decide
  exact (toString_nat_char_props n hc).2.1 rfl

theorem append_keyId_inj (pfx sfx : String) {i j : BitVec 32}
    (h : pfx ++ toString i.toNat ++ sfx = pfx ++ toString j.toNat ++ sfx) : i = j := by
  have hl := congrArg String.toList h
  simp only [String.toList_append] at hl
  have hl' := List.append_cancel_left (List.append_cancel_right hl)
  exact keyId_inj (String.toList_inj.mp hl')

theorem signedPreKeyFile_inj : Function.Injective signedPreKeyFile := fun _ _ h =>
  append_keyId_inj "signed-pre-keys/" "" (by simpa [signedPreKeyFile] using h)

theorem oneTimePreKeyFile_inj : Function.Injective oneTimePreKeyFile := fun _ _ h =>
  append_keyId_inj "one-time-pre-keys/" "" (by simpa [oneTimePreKeyFile] using h)

theorem oneTimeKyberPreKeyFile_inj : Function.Injective oneTimeKyberPreKeyFile := fun _ _ h =>
  append_keyId_inj "one-time-kyber-pre-keys/" "" (by simpa [oneTimeKyberPreKeyFile] using h)

theorem lastResortKyberPreKeyFile_inj : Function.Injective lastResortKyberPreKeyFile := fun _ _ h =>
  append_keyId_inj "last-resort-kyber-pre-keys/" ""
    (by simpa [lastResortKyberPreKeyFile] using h)

theorem baseKeysFile_inj : Function.Injective baseKeysFile := fun _ _ h =>
  append_keyId_inj "last-resort-kyber-pre-keys/" ".base-keys" (by simpa [baseKeysFile] using h)

theorem lastResort_ne_baseKeys (i j : BitVec 32) :
    lastResortKyberPreKeyFile i ≠ baseKeysFile j := by
  intro h
  have hdot : '.' ∈ (baseKeysFile j).toList := by
    unfold baseKeysFile
    simp only [String.toList_append, List.mem_append]
    right
    decide
  rw [← h] at hdot
  unfold lastResortKyberPreKeyFile at hdot
  rw [String.toList_append] at hdot
  rcases List.mem_append.mp hdot with hpfx | hdig
  · exact absurd hpfx (by decide)
  · exact (toString_nat_char_props i.toNat hdig).2.1 rfl

/-! ## ASCII `utf8`, `pathOf`, `pathStr`, and `blockingAncestorF` helpers -/

theorem utf8_append (s1 s2 : String) : utf8 (s1 ++ s2) = utf8 s1 ++ utf8 s2 := by
  rw [InitS0.utf8_eq_flatMap, InitS0.utf8_eq_flatMap, InitS0.utf8_eq_flatMap,
    String.toList_append, List.flatMap_append, List.map_append]

private theorem utf8EncodeChar_ascii {c : Char} (hc : c.toNat < 128) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  unfold String.utf8EncodeChar
  simp
  omega

theorem utf8_ascii_bytes {s : String} (hs : ∀ c ∈ s.toList, c.toNat < 128) :
    ∀ b ∈ utf8 s, b.toNat < 128 := by
  rw [InitS0.utf8_eq_flatMap]
  intro b hb
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
  obtain ⟨c, hc, hcu⟩ := List.mem_flatMap.mp hu
  rw [utf8EncodeChar_ascii (hs c hc), List.mem_singleton] at hcu
  subst hcu
  have hlt := hs c hc
  have hu8 : (UInt8.ofNat c.toNat).toNat = c.toNat := Nat.mod_eq_of_lt (by omega : c.toNat < 256)
  rw [hu8, BitVec.toNat_ofNat]
  omega

theorem pathStr_utf8_ascii {s : String} (hs : ∀ c ∈ s.toList, c.toNat < 128) :
    pathStr (utf8 s) = s := by
  apply String.toList_inj.mp
  unfold pathStr
  rw [String.toList_ofList, InitS0.utf8_eq_flatMap, List.map_map]
  have h1 : ∀ cs : List Char, (∀ c ∈ cs, c.toNat < 128) →
      List.map ((fun b : BitVec 8 => Char.ofNat b.toNat) ∘ fun b : UInt8 => BitVec.ofNat 8 b.toNat)
        (cs.flatMap String.utf8EncodeChar) = cs := by
    intro cs hcs
    induction cs with
    | nil => rfl
    | cons c rest ih =>
      have hc := hcs c List.mem_cons_self
      rw [List.flatMap_cons, utf8EncodeChar_ascii hc, List.singleton_append, List.map_cons,
        ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx))]
      congr 1
      dsimp only [Function.comp]
      have hu8 : (UInt8.ofNat c.toNat).toNat = c.toNat := Nat.mod_eq_of_lt (by omega : c.toNat < 256)
      have hmod : (BitVec.ofNat 8 (UInt8.ofNat c.toNat).toNat).toNat = c.toNat := by
        rw [hu8, BitVec.toNat_ofNat]
        omega
      rw [hmod]
      exact Char.ofNat_toNat c
  exact h1 s.toList hs

theorem pathOf_utf8_eq {dir sfx : String} (hdir : dir.toList ≠ []) :
    pathOf (utf8 dir) (utf8 sfx) = utf8 (dir ++ "/" ++ sfx) := by
  have hne : utf8 dir ≠ [] := by
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hdir
    rw [InitS0.utf8_eq_flatMap, hcs, List.flatMap_cons]
    have hce : String.utf8EncodeChar c ≠ [] := by
      unfold String.utf8EncodeChar
      simp
      split_ifs <;> simp
    intro hnil
    exact hce (List.append_eq_nil_iff.mp (List.map_eq_nil_iff.mp hnil)).1
  simp only [pathOf, hne, ↓reduceIte, utf8_append]

private theorem splitOnPPrepend_no_sep :
    ∀ (cs acc : List Char), '/' ∉ cs →
      List.splitOnPPrepend (· == '/') cs acc = [acc.reverse ++ cs]
  | [], acc, _ => by simp [List.splitOnPPrepend]
  | c :: cs, acc, h => by
    have hc : (c == '/') = false := beq_false_of_ne (fun e => h (e ▸ List.mem_cons_self))
    unfold List.splitOnPPrepend
    rw [hc, splitOnPPrepend_no_sep cs (c :: acc) (fun m => h (List.mem_cons_of_mem _ m))]
    simp [List.append_assoc]

private theorem splitOnPPrepend_slash_two {ys : List Char} (hys : '/' ∉ ys) :
    ∀ (xs acc : List Char), '/' ∉ xs →
      List.splitOnPPrepend (· == '/') (xs ++ '/' :: ys) acc = [acc.reverse ++ xs, ys]
  | [], acc, _ => by
    simp only [List.nil_append, List.append_nil]
    unfold List.splitOnPPrepend
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [splitOnPPrepend_no_sep ys [] hys]
    simp
  | x :: rest, acc, hxs => by
    have hx : (x == '/') = false := beq_false_of_ne (fun e => hxs (e ▸ List.mem_cons_self))
    simp only [List.cons_append]
    unfold List.splitOnPPrepend
    rw [hx, splitOnPPrepend_slash_two hys rest (x :: acc) (fun m => hxs (List.mem_cons_of_mem _ m))]
    simp [List.append_assoc]

private theorem splitOn_slash_two {dir sfx : String}
    (hd : '/' ∉ dir.toList) (hs : '/' ∉ sfx.toList) :
    (dir ++ "/" ++ sfx).toList.splitOn '/' = [dir.toList, sfx.toList] := by
  have hl : (dir ++ "/" ++ sfx).toList = dir.toList ++ '/' :: sfx.toList := by
    simp [String.toList_append]
  rw [hl]
  change List.splitOnPPrepend (· == '/') (dir.toList ++ '/' :: sfx.toList) [] = _
  rw [splitOnPPrepend_slash_two hs dir.toList [] hd, List.reverse_nil, List.nil_append]

theorem blockingAncestorF_dir_sfx {F : FsFiles} {dir sfx : String}
    (hd : '/' ∉ dir.toList) (hs : '/' ∉ sfx.toList) (hf : F dir = some .dir) :
    blockingAncestorF F (dir ++ "/" ++ sfx) = none := by
  have hof : String.ofList (dir.toList ++ []) = dir := by
    rw [List.append_nil]; exact String.ofList_toList
  have ha : ancestors (dir ++ "/" ++ sfx) = [dir] := by
    unfold ancestors pathComps
    rw [splitOn_slash_two hd hs]
    exact congrArg List.singleton hof
  unfold blockingAncestorF
  rw [ha, List.find?_cons, hf]
  rfl

/-! ## Path bucket partition (`recvBucket`) -/

def recvBucket (s : String) : Nat :=
  let cs := s.toList
  if cs == "address".toList then 1
  else if cs == "identity-key-pair".toList then 2
  else if cs == "registration-id".toList then 3
  else if cs.take 11 == "identities/".toList then 4
  else if cs.take 9 == "sessions/".toList then 5
  else if cs.take 16 == "signed-pre-keys/".toList then 6
  else if cs.take 18 == "one-time-pre-keys/".toList then 7
  else if cs.take 24 == "one-time-kyber-pre-keys/".toList then 8
  else if cs.take 27 == "last-resort-kyber-pre-keys/".toList then 9
  else if cs == "coins".toList then 10
  else 0

theorem ne_of_recvBucket {s1 s2 : String} (h : recvBucket s1 ≠ recvBucket s2) : s1 ≠ s2 :=
  fun e => h (congrArg recvBucket e)

private theorem take_append_prefix (n : Nat) (p s : String) (hp : p.toList.length = n) :
    (p ++ s).toList.take n = p.toList := by
  rw [String.toList_append, List.take_append_of_le_length (Nat.le_of_eq hp.symm),
    List.take_of_length_le (Nat.le_of_eq hp)]

private theorem ne_toList_of_slash {p s m : String} (hslash : '/' ∈ p.toList)
    (hno : '/' ∉ m.toList) : ((p ++ s).toList == m.toList) = false :=
  beq_false_of_ne fun e => hno (e ▸ String.toList_append ▸ List.mem_append_left _ hslash)

theorem recvBucket_address : recvBucket addressFile = 1 := by decide
theorem recvBucket_idKeyPair : recvBucket identityKeyPairFile = 2 := by decide
theorem recvBucket_regId : recvBucket registrationIdFile = 3 := by decide
theorem recvBucket_coins : recvBucket coinsFile = 10 := by decide

theorem recvBucket_identityFile (s : String) : recvBucket (identityFile s) = 4 := by
  unfold recvBucket identityFile
  dsimp only
  rw [ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    take_append_prefix 11 "identities/" s (by decide)]
  simp

theorem recvBucket_sessionFile (a : Address) : recvBucket (sessionFile a) = 5 := by
  unfold recvBucket sessionFile
  dsimp only
  rw [ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide)]
  have hne4 : (("sessions/" ++ a.text).toList.take 11 == "identities/".toList) = false := by
    apply beq_false_of_ne; intro e
    have h2 := congrArg (List.take 2) e
    rw [List.take_take, show min 2 11 = 2 from rfl, String.toList_append,
      List.take_append_of_le_length (by decide)] at h2
    exact absurd h2 (by decide)
  rw [hne4, take_append_prefix 9 "sessions/" a.text (by decide)]
  simp

private theorem ne_take_of_take2 {p s q : String} {k : Nat} (hk : 2 ≤ k)
    (hp : 2 ≤ p.toList.length) (hne : p.toList.take 2 ≠ q.toList.take 2) :
    ((p ++ s).toList.take k == q.toList) = false := by
  apply beq_false_of_ne; intro e
  have h2 := congrArg (List.take 2) e
  rw [List.take_take, Nat.min_eq_left hk, String.toList_append,
    List.take_append_of_le_length hp] at h2
  exact hne h2

private theorem ne_take_of_take12 {p s q : String} {k : Nat} (hk : 12 ≤ k)
    (hp : 12 ≤ p.toList.length) (hne : p.toList.take 12 ≠ q.toList.take 12) :
    ((p ++ s).toList.take k == q.toList) = false := by
  apply beq_false_of_ne; intro e
  have h12 := congrArg (List.take 12) e
  rw [List.take_take, Nat.min_eq_left hk, String.toList_append,
    List.take_append_of_le_length hp] at h12
  exact hne h12

theorem recvBucket_signedPreKey (i : BitVec 32) : recvBucket (signedPreKeyFile i) = 6 := by
  unfold recvBucket signedPreKeyFile
  dsimp only
  rw [ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    take_append_prefix 16 "signed-pre-keys/" _ (by decide)]
  simp

theorem recvBucket_oneTimePreKey (i : BitVec 32) : recvBucket (oneTimePreKeyFile i) = 7 := by
  unfold recvBucket oneTimePreKeyFile
  dsimp only
  rw [ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    take_append_prefix 18 "one-time-pre-keys/" _ (by decide)]
  simp

theorem recvBucket_oneTimeKyberPreKey (i : BitVec 32) :
    recvBucket (oneTimeKyberPreKeyFile i) = 8 := by
  unfold recvBucket oneTimeKyberPreKeyFile
  dsimp only
  rw [ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take12 (by omega) (by decide) (by decide),
    take_append_prefix 24 "one-time-kyber-pre-keys/" _ (by decide)]
  simp

theorem recvBucket_lastResortSuffix (sfx : String) :
    recvBucket ("last-resort-kyber-pre-keys/" ++ sfx) = 9 := by
  unfold recvBucket
  dsimp only
  rw [ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_toList_of_slash (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    ne_take_of_take2 (by omega) (by decide) (by decide),
    take_append_prefix 27 "last-resort-kyber-pre-keys/" sfx (by decide)]
  simp

theorem recvBucket_lastResortKyberPreKey (i : BitVec 32) :
    recvBucket (lastResortKyberPreKeyFile i) = 9 :=
  recvBucket_lastResortSuffix (toString i.toNat)

theorem recvBucket_baseKeysFile (i : BitVec 32) : recvBucket (baseKeysFile i) = 9 := by
  unfold baseKeysFile
  rw [String.append_assoc]
  exact recvBucket_lastResortSuffix _

theorem recvBucket_partyDirs {d : String} (hd : d ∈ partyDirs) : recvBucket d = 0 := by
  revert d hd
  decide

/-! ## Block decomposition of `encodeDir` and bucket lookup lemmas -/

def blockDir1 (st : PqParty) : List (String × List (BitVec 8)) :=
  [(addressFile, textBytes (partyAddress st.party).text)]

def blockDir2 (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  [(identityKeyPairFile, IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩)]

def blockDir3 (st : PqParty) : List (String × List (BitVec 8)) :=
  [(registrationIdFile, SignalSession.le32 st.me.regId)]

def blockDir4 (st : PqParty) : List (String × List (BitVec 8)) :=
  match st.peerId with
  | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
  | none => []

def blockDir5 (st : PqParty) : List (String × List (BitVec 8)) :=
  match st.session with
  | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
  | none => []

def blockDir6 (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  st.signed.map fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)

def blockDir7 (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  st.oneTime.map fun (i, k) =>
    (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])

def blockDir8 (st : PqParty) : List (String × List (BitVec 8)) :=
  st.kyberOneTime.map fun (i, k) =>
    (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])

def blockDir9 (st : PqParty) : List (String × List (BitVec 8)) :=
  (st.kyberLastResort.map fun (i, k, seen) =>
    [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten

theorem encodeDir_blocks (W : PEParams) (st : PqParty) :
    encodeDir W st =
      blockDir1 st ++ blockDir2 W st ++ blockDir3 st ++ blockDir4 st ++ blockDir5 st ++
        blockDir6 W st ++ blockDir7 W st ++ blockDir8 st ++ blockDir9 st := by
  simp only [encodeDir, blockDir1, blockDir2, blockDir3, blockDir4, blockDir5, blockDir6,
    blockDir7, blockDir8, blockDir9, List.cons_append, List.nil_append, List.append_assoc]
  rfl

theorem bucket_blockDir (W : PEParams) (st : PqParty) :
    (∀ x ∈ blockDir1 st, recvBucket x.1 = 1) ∧
    (∀ x ∈ blockDir2 W st, recvBucket x.1 = 2) ∧
    (∀ x ∈ blockDir3 st, recvBucket x.1 = 3) ∧
    (∀ x ∈ blockDir4 st, recvBucket x.1 = 4) ∧
    (∀ x ∈ blockDir5 st, recvBucket x.1 = 5) ∧
    (∀ x ∈ blockDir6 W st, recvBucket x.1 = 6) ∧
    (∀ x ∈ blockDir7 W st, recvBucket x.1 = 7) ∧
    (∀ x ∈ blockDir8 st, recvBucket x.1 = 8) ∧
    (∀ x ∈ blockDir9 st, recvBucket x.1 = 9) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; unfold blockDir1 at hx; rw [List.mem_singleton] at hx; subst hx
    exact recvBucket_address
  · intro x hx; unfold blockDir2 at hx; rw [List.mem_singleton] at hx; subst hx
    exact recvBucket_idKeyPair
  · intro x hx; unfold blockDir3 at hx; rw [List.mem_singleton] at hx; subst hx
    exact recvBucket_regId
  · intro x hx; unfold blockDir4 at hx
    cases h : st.peerId <;> simp [h] at hx
    subst hx; exact recvBucket_identityFile _
  · intro x hx; unfold blockDir5 at hx
    cases h : st.session <;> simp [h] at hx
    subst hx; exact recvBucket_sessionFile _
  · intro x hx; obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hx
    exact recvBucket_signedPreKey i
  · intro x hx; obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hx
    exact recvBucket_oneTimePreKey i
  · intro x hx; obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp hx
    exact recvBucket_oneTimeKyberPreKey i
  · intro x hx
    obtain ⟨l, hl, hmem⟩ := List.mem_flatten.mp hx
    obtain ⟨⟨i, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_cons.mp hmem with rfl | hmem2
    · exact recvBucket_lastResortKyberPreKey i
    · rw [List.mem_singleton] at hmem2; subst hmem2; exact recvBucket_baseKeysFile i

theorem recvBucket_encodeDir_pos (W : PEParams) (st : PqParty) {x : String × List (BitVec 8)}
    (hx : x ∈ encodeDir W st) : 1 ≤ recvBucket x.1 ∧ recvBucket x.1 ≤ 9 := by
  rw [encodeDir_blocks] at hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := bucket_blockDir W st
  simp only [List.mem_append] at hx
  rcases hx with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
  · have := b1 x h; omega
  · have := b2 x h; omega
  · have := b3 x h; omega
  · have := b4 x h; omega
  · have := b5 x h; omega
  · have := b6 x h; omega
  · have := b7 x h; omega
  · have := b8 x h; omega
  · have := b9 x h; omega

theorem find?_rev_none {l : List (String × List (BitVec 8))} {q : String}
    (h : ∀ x ∈ l, recvBucket x.1 ≠ recvBucket q) :
    l.reverse.find? (fun x => x.1 == q) = none := by
  rw [List.find?_eq_none]
  intro x hx hbeq
  exact ne_of_recvBucket (h x (List.mem_reverse.mp hx)) (beq_iff_eq.mp hbeq)

theorem find?_encodeDir_bucket0 (W : PEParams) (st : PqParty) {q : String}
    (hq : recvBucket q = 0) :
    (encodeDir W st).reverse.find? (fun x => x.1 == q) = none :=
  find?_rev_none fun x hx => by
    have := recvBucket_encodeDir_pos W st hx
    omega

theorem find?_pqRecv_files (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    {q : String} (hq : recvBucket q ≠ 10) :
    (pqRecvInputs W st c rc).files.reverse.find? (fun x => x.1 == q) =
      (encodeDir W st).reverse.find? (fun x => x.1 == q) := by
  have hc : ([(coinsFile, HMAC.keyToBytes32 rc)] : List (String × List (BitVec 8))).reverse.find?
      (fun x => x.1 == q) = none :=
    find?_rev_none fun x hx => by
      rw [List.mem_singleton] at hx; subst hx
      rw [recvBucket_coins]; exact Ne.symm hq
  simp only [pqRecvInputs, pqInputs, List.append_nil, List.reverse_append, List.find?_append,
    hc, Option.none_or]

theorem find?_select_block {b1 b2 b3 b4 b5 b6 b7 b8 b9 : List (String × List (BitVec 8))}
    (hb1 : ∀ x ∈ b1, recvBucket x.1 = 1)
    (hb2 : ∀ x ∈ b2, recvBucket x.1 = 2)
    (hb3 : ∀ x ∈ b3, recvBucket x.1 = 3)
    (hb4 : ∀ x ∈ b4, recvBucket x.1 = 4)
    (hb5 : ∀ x ∈ b5, recvBucket x.1 = 5)
    (hb6 : ∀ x ∈ b6, recvBucket x.1 = 6)
    (hb7 : ∀ x ∈ b7, recvBucket x.1 = 7)
    (hb8 : ∀ x ∈ b8, recvBucket x.1 = 8)
    (hb9 : ∀ x ∈ b9, recvBucket x.1 = 9)
    (q : String) :
    (b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9).reverse.find? (fun x => x.1 == q) =
      match recvBucket q with
      | 1 => b1.reverse.find? (fun x => x.1 == q)
      | 2 => b2.reverse.find? (fun x => x.1 == q)
      | 3 => b3.reverse.find? (fun x => x.1 == q)
      | 4 => b4.reverse.find? (fun x => x.1 == q)
      | 5 => b5.reverse.find? (fun x => x.1 == q)
      | 6 => b6.reverse.find? (fun x => x.1 == q)
      | 7 => b7.reverse.find? (fun x => x.1 == q)
      | 8 => b8.reverse.find? (fun x => x.1 == q)
      | 9 => b9.reverse.find? (fun x => x.1 == q)
      | _ => none := by
  simp only [List.reverse_append, List.find?_append]
  have n1 : recvBucket q ≠ 1 → b1.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb1 x hx]; exact Ne.symm h
  have n2 : recvBucket q ≠ 2 → b2.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb2 x hx]; exact Ne.symm h
  have n3 : recvBucket q ≠ 3 → b3.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb3 x hx]; exact Ne.symm h
  have n4 : recvBucket q ≠ 4 → b4.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb4 x hx]; exact Ne.symm h
  have n5 : recvBucket q ≠ 5 → b5.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb5 x hx]; exact Ne.symm h
  have n6 : recvBucket q ≠ 6 → b6.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb6 x hx]; exact Ne.symm h
  have n7 : recvBucket q ≠ 7 → b7.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb7 x hx]; exact Ne.symm h
  have n8 : recvBucket q ≠ 8 → b8.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb8 x hx]; exact Ne.symm h
  have n9 : recvBucket q ≠ 9 → b9.reverse.find? (fun x => x.1 == q) = none := fun h =>
    find?_rev_none fun x hx => by rw [hb9 x hx]; exact Ne.symm h
  match hb : recvBucket q with
  | 1 => simp [n9 (by omega), n8 (by omega), n7 (by omega), n6 (by omega), n5 (by omega),
      n4 (by omega), n3 (by omega), n2 (by omega)]
  | 2 => simp [n9 (by omega), n8 (by omega), n7 (by omega), n6 (by omega), n5 (by omega),
      n4 (by omega), n3 (by omega), n1 (by omega)]
  | 3 => simp [n9 (by omega), n8 (by omega), n7 (by omega), n6 (by omega), n5 (by omega),
      n4 (by omega), n2 (by omega), n1 (by omega)]
  | 4 => simp [n9 (by omega), n8 (by omega), n7 (by omega), n6 (by omega), n5 (by omega),
      n3 (by omega), n2 (by omega), n1 (by omega)]
  | 5 => simp [n9 (by omega), n8 (by omega), n7 (by omega), n6 (by omega),
      n4 (by omega), n3 (by omega), n2 (by omega), n1 (by omega)]
  | 6 => simp [n9 (by omega), n8 (by omega), n7 (by omega),
      n5 (by omega), n4 (by omega), n3 (by omega), n2 (by omega), n1 (by omega)]
  | 7 => simp [n9 (by omega), n8 (by omega),
      n6 (by omega), n5 (by omega), n4 (by omega), n3 (by omega), n2 (by omega), n1 (by omega)]
  | 8 => simp [n9 (by omega),
      n7 (by omega), n6 (by omega), n5 (by omega), n4 (by omega), n3 (by omega), n2 (by omega),
      n1 (by omega)]
  | 9 => simp [n8 (by omega), n7 (by omega), n6 (by omega), n5 (by omega), n4 (by omega),
      n3 (by omega), n2 (by omega), n1 (by omega)]
  | 0 | _ + 10 =>
    simp [n9 (by omega), n8 (by omega), n7 (by omega), n6 (by omega), n5 (by omega),
      n4 (by omega), n3 (by omega), n2 (by omega), n1 (by omega)]

/-! ## Canonical `IsRecvFile`, `filesFold`, `runFiles`, and `filesOf` lemmas -/

private theorem splitSlash_go_no_slash :
    ∀ (cs cur : List Char), '/' ∉ cs →
      splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by simp [splitSlash.go]
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    have hstep : splitSlash.go cur (c :: cs) = splitSlash.go (c :: cur) cs := by
      rw [splitSlash.go.eq_def]
      split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq
        injection heq with h1 h2
        subst h1 h2
        rfl
    rw [hstep, splitSlash_go_no_slash cs (c :: cur) (fun m => h (List.mem_cons_of_mem _ m))]
    simp [List.reverse_cons, List.append_assoc]

private theorem splitSlash_go_two {cs2 : List Char} (h2 : '/' ∉ cs2) :
    ∀ (cs1 cur : List Char), '/' ∉ cs1 →
      splitSlash.go cur (cs1 ++ '/' :: cs2) =
        [String.ofList (cur.reverse ++ cs1), String.ofList cs2]
  | [], cur, _ => by
    simp only [List.nil_append, List.append_nil, splitSlash.go,
      splitSlash_go_no_slash cs2 [] h2, List.reverse_nil]
  | c :: cs1, cur, h1 => by
    have hc : c ≠ '/' := fun e => h1 (e ▸ List.mem_cons_self)
    simp only [List.cons_append]
    have hstep : splitSlash.go cur (c :: (cs1 ++ '/' :: cs2)) =
        splitSlash.go (c :: cur) (cs1 ++ '/' :: cs2) := by
      rw [splitSlash.go.eq_def]
      split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq
        injection heq with e1 e2
        subst e1 e2
        rfl
    rw [hstep, splitSlash_go_two h2 cs1 (c :: cur) (fun m => h1 (List.mem_cons_of_mem _ m))]
    simp [List.reverse_cons, List.append_assoc]

private theorem seg_filter_ok {s : String} (hne : s.toList ≠ []) (hnd : s ≠ ".") :
    (!s.isEmpty && s != ".") = true := by
  have h1 : s.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    exact hne (congrArg String.toList (String.isEmpty_iff.mp he))
  have h2 : (s != ".") = true := bne_iff_ne.mpr hnd
  rw [h1, h2]
  rfl

theorem normalizePath_dir_sfx {d sfx : String}
    (hd_ns : '/' ∉ d.toList) (hd_ne : d.toList ≠ []) (hd_nd : d ≠ ".")
    (hs_ns : '/' ∉ sfx.toList) (hs_ne : sfx.toList ≠ []) (hs_nd : sfx ≠ ".") :
    normalizePath (d ++ "/" ++ sfx) = [d, sfx] := by
  have hl : (d ++ "/" ++ sfx).toList = d.toList ++ '/' :: sfx.toList := by
    simp [String.toList_append]
  unfold normalizePath splitSlash
  rw [hl, splitSlash_go_two hs_ns d.toList [] hd_ns, List.reverse_nil, List.nil_append,
    String.ofList_toList, String.ofList_toList]
  simp only [List.filter, seg_filter_ok hd_ne hd_nd, seg_filter_ok hs_ne hs_nd]

def recvRootFiles : List String :=
  [addressFile, identityKeyPairFile, registrationIdFile, coinsFile]

def recvParentDirs : List String :=
  ["identities", "sessions", "signed-pre-keys", "one-time-pre-keys",
   "one-time-kyber-pre-keys", "last-resort-kyber-pre-keys"]

def IsRecvFile (p : String) : Prop :=
  p ∈ recvRootFiles ∨
    ∃ d sfx, d ∈ recvParentDirs ∧ '/' ∉ sfx.toList ∧ sfx.toList ≠ [] ∧ sfx ≠ "." ∧
      p = d ++ "/" ++ sfx

theorem recvRootFiles_props {p : String} (hp : p ∈ recvRootFiles) :
    normalizePath p = [p] ∧ p ∉ recvParentDirs ∧ [p] ∉ stdioPaths.map normalizePath ∧
      (dirsFold partyDirs {}).entries [p] = none := by
  revert p hp
  decide

theorem recvParentDirs_props {d : String} (hd : d ∈ recvParentDirs) :
    '/' ∉ d.toList ∧ d.toList ≠ [] ∧ d ≠ "." ∧ d ∈ partyDirs ∧ d ≠ "public" := by
  revert d hd
  decide

theorem isRecvFile_norm_shape {p : String} (hp : IsRecvFile p) :
    (p ∈ recvRootFiles ∧ normalizePath p = [p]) ∨
    ∃ d sfx, d ∈ recvParentDirs ∧ p = d ++ "/" ++ sfx ∧ normalizePath p = [d, sfx] := by
  rcases hp with hr | ⟨d, sfx, hd, hs_ns, hs_ne, hs_nd, rfl⟩
  · exact Or.inl ⟨hr, (recvRootFiles_props hr).1⟩
  · obtain ⟨hd_ns, hd_ne, hd_nd, _, _⟩ := recvParentDirs_props hd
    exact Or.inr ⟨d, sfx, hd, rfl,
      normalizePath_dir_sfx hd_ns hd_ne hd_nd hs_ns hs_ne hs_nd⟩

theorem isRecvFile_norm_inj {p1 p2 : String} (h1 : IsRecvFile p1) (h2 : IsRecvFile p2)
    (heq : normalizePath p1 = normalizePath p2) : p1 = p2 := by
  rcases isRecvFile_norm_shape h1 with ⟨_, hn1⟩ | ⟨d1, s1, _, hp1, hn1⟩ <;>
    rcases isRecvFile_norm_shape h2 with ⟨_, hn2⟩ | ⟨d2, s2, _, hp2, hn2⟩
  · rw [hn1, hn2] at heq; exact List.singleton_injective heq
  · rw [hn1, hn2] at heq; nomatch heq
  · rw [hn1, hn2] at heq; nomatch heq
  · rw [hn1, hn2] at heq
    injection heq with hd hs
    injection hs with hs _
    rw [hp1, hp2, hd, hs]

private def HasParentDirs (fs : FsState) : Prop :=
  ∀ d ∈ recvParentDirs, fs.entries [d] = some .dir

private theorem hasParentDirs_partyDirs : HasParentDirs (dirsFold partyDirs {}) := by
  unfold HasParentDirs
  intro d hd
  revert d hd
  decide

private theorem foldl_setEntry_ne (l : List FsPath) (fs : FsState) (k : FsPath)
    (h : ∀ pref ∈ l, k ≠ pref) :
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k = fs.entries k := by
  induction l generalizing fs with
  | nil => rfl
  | cons pref rest ih =>
    rw [List.foldl_cons, ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have hne : (k == pref) = false := beq_false_of_ne (h pref List.mem_cons_self)
    simp only [FsState.setEntry, hne, Bool.false_eq_true, ↓reduceIte]

private theorem dirsFold_entries_ne (dirs : List String) (fs : FsState) (k : FsPath)
    (h : ∀ dir ∈ dirs, ∀ pref ∈ FsPath.nonEmptyPrefixes (normalizePath dir), k ≠ pref) :
    (dirsFold dirs fs).entries k = fs.entries k := by
  induction dirs generalizing fs with
  | nil => rfl
  | cons dir rest ih =>
    unfold dirsFold
    rw [List.foldl_cons]
    change (dirsFold rest _).entries k = fs.entries k
    rw [ih _ (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    exact foldl_setEntry_ne _ fs k (h dir List.mem_cons_self)

private theorem partyDirs_prefix_shape :
    ∀ dir ∈ partyDirs, ∀ pref ∈ FsPath.nonEmptyPrefixes (normalizePath dir),
      pref.length = 1 ∨ pref.head? = some "public" := by
  intro dir hdir pref hpref
  revert dir hdir pref hpref
  decide

private theorem dirsFold_partyDirs_two_none {d : String} (hd : d ∈ recvParentDirs) (sfx : String) :
    (dirsFold partyDirs {}).entries [d, sfx] = none := by
  have hd_np : d ≠ "public" := (recvParentDirs_props hd).2.2.2.2
  rw [dirsFold_entries_ne partyDirs {} [d, sfx] fun dir hdir pref hpref heq => by
    rcases partyDirs_prefix_shape dir hdir pref hpref with hlen | hhd
    · rw [← heq] at hlen; nomatch hlen
    · rw [← heq, List.head?_cons, Option.some.injEq] at hhd; exact hd_np hhd]
  rfl

private theorem two_not_mem_stdioPaths (d sfx : String) :
    [d, sfx] ∉ stdioPaths.map normalizePath := by
  have hlen : ∀ q ∈ stdioPaths.map normalizePath, q.length = 1 := by
    intro q hq; revert q hq; decide
  intro hm
  have h := hlen [d, sfx] hm
  nomatch h

private theorem filesFold_step_isRecvFile {fs : FsState} (hdirs : HasParentDirs fs)
    {p : String} (bs : List (BitVec 8)) (hp : IsRecvFile p) :
    let fs' := (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))
    HasParentDirs fs' ∧
      ∀ k : FsPath, fs'.entries k =
        if k == normalizePath p then some (.file bs) else fs.entries k := by
  intro fs'
  have hpoint : ∀ k : FsPath, fs'.entries k =
      if k == normalizePath p then some (.file bs) else fs.entries k := by
    intro k
    rcases isRecvFile_norm_shape hp with ⟨_, hn⟩ | ⟨d0, sfx, hd0, _, hn⟩
    · simp only [fs', FsState.setFile, hn, FsPath.nonEmptyPrefixes, List.map_nil,
        List.dropLast, List.foldl_nil, FsState.setEntry]
    · simp only [fs', FsState.setFile, hn, FsPath.nonEmptyPrefixes, List.map_cons,
        List.map_nil, List.dropLast, List.foldl_cons, List.foldl_nil, FsState.setEntry]
      cases hk2 : (k == [d0, sfx]) with
      | true => rfl
      | false =>
        cases hk1 : (k == [d0]) with
        | false => rfl
        | true =>
          rw [beq_iff_eq.mp hk1, hdirs d0 hd0]
          rfl
  refine ⟨fun d hd => ?_, hpoint⟩
  rw [hpoint [d]]
  rcases isRecvFile_norm_shape hp with ⟨hr, hn⟩ | ⟨d0, sfx, _, _, hn⟩
  · have hne : ([d] == [p]) = false :=
      beq_false_of_ne (fun e => (recvRootFiles_props hr).2.1 (List.singleton_injective e ▸ hd))
    rw [hn, hne]
    exact hdirs d hd
  · have hne : ([d] == [d0, sfx]) = false := beq_false_of_ne (by simp)
    rw [hn, hne]
    exact hdirs d hd

private theorem filesFold_isRecvFile_entries {L : List (String × List (BitVec 8))}
    (hL : ∀ x ∈ L, IsRecvFile x.1) {fs : FsState} (hdirs : HasParentDirs fs) :
    HasParentDirs (filesFold L fs) ∧
      ∀ k : FsPath, (filesFold L fs).entries k =
        match L.reverse.find? (fun x => normalizePath x.1 == k) with
        | some pb => some (.file pb.2)
        | none => fs.entries k := by
  induction L generalizing fs with
  | nil => exact ⟨hdirs, fun _ => rfl⟩
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    obtain ⟨hstep_dirs, hstep_eq⟩ :=
      filesFold_step_isRecvFile hdirs bs (hL (p, bs) List.mem_cons_self)
    unfold filesFold
    rw [List.foldl_cons]
    change HasParentDirs (filesFold tl _) ∧ ∀ k, (filesFold tl _).entries k = _
    obtain ⟨hfinal_dirs, hfinal_eq⟩ :=
      ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hstep_dirs
    refine ⟨hfinal_dirs, fun k => ?_⟩
    rw [hfinal_eq k, List.reverse_cons, List.find?_append]
    cases tl.reverse.find? (fun x => normalizePath x.1 == k) with
    | some pb => rfl
    | none =>
      simp only [Option.none_or, List.find?_singleton, hstep_eq k]
      have hsymm : (normalizePath p == k) = (k == normalizePath p) := by
        cases h1 : (normalizePath p == k) <;> cases h2 : (k == normalizePath p)
        · rfl
        · exact absurd (beq_iff_eq.mp h2).symm (beq_eq_false_iff_ne.mp h1)
        · exact absurd (beq_iff_eq.mp h1).symm (beq_eq_false_iff_ne.mp h2)
        · rfl
      rw [hsymm]
      cases (k == normalizePath p) <;> rfl

theorem isRecvFile_keyId {d : String} (hd : d ∈ recvParentDirs) (i : BitVec 32) :
    IsRecvFile (d ++ "/" ++ toString i.toNat) :=
  Or.inr ⟨d, toString i.toNat, hd,
    fun m => (toString_nat_char_props i.toNat m).2.2.1 rfl,
    toString_nat_ne_nil i.toNat, toString_nat_ne_dot i.toNat, rfl⟩

theorem isRecvFile_signedPreKey (i : BitVec 32) : IsRecvFile (signedPreKeyFile i) :=
  isRecvFile_keyId (d := "signed-pre-keys") (by decide) i

theorem isRecvFile_oneTimePreKey (i : BitVec 32) : IsRecvFile (oneTimePreKeyFile i) :=
  isRecvFile_keyId (d := "one-time-pre-keys") (by decide) i

theorem isRecvFile_oneTimeKyberPreKey (i : BitVec 32) : IsRecvFile (oneTimeKyberPreKeyFile i) :=
  isRecvFile_keyId (d := "one-time-kyber-pre-keys") (by decide) i

theorem isRecvFile_lastResortKyberPreKey (i : BitVec 32) :
    IsRecvFile (lastResortKyberPreKeyFile i) :=
  isRecvFile_keyId (d := "last-resort-kyber-pre-keys") (by decide) i

theorem isRecvFile_baseKeysFile (i : BitVec 32) : IsRecvFile (baseKeysFile i) := by
  refine Or.inr ⟨"last-resort-kyber-pre-keys", toString i.toNat ++ ".base-keys", by decide,
    ?_, ?_, ?_, by simp [baseKeysFile, String.append_assoc]⟩
  · intro m
    rw [String.toList_append] at m
    rcases List.mem_append.mp m with h1 | h2
    · exact (toString_nat_char_props i.toNat h1).2.2.1 rfl
    · exact absurd h2 (by decide)
  · intro hnil
    rw [String.toList_append] at hnil
    exact absurd (List.append_eq_nil_iff.mp hnil).2 (by decide)
  · intro hdot
    have hl := congrArg (fun s => s.toList.length) hdot
    rw [String.toList_append, List.length_append] at hl
    have h10 : ".base-keys".toList.length = 10 := by decide
    have h1 : ".".toList.length = 1 := by decide
    omega

theorem isRecvFile_identityFile (P : Party) : IsRecvFile (identityFile (partyAddressName P)) :=
  Or.inr ⟨"identities", partyAddressName P, by decide,
    by cases P <;> decide, by cases P <;> decide, by cases P <;> decide, rfl⟩

theorem isRecvFile_sessionFile (P : Party) : IsRecvFile (sessionFile (partyAddress P)) :=
  Or.inr ⟨"sessions", (partyAddress P).text, by decide,
    by cases P <;> decide, by cases P <;> decide, by cases P <;> decide, rfl⟩

theorem isRecvFile_encodeDir (W : PEParams) (st : PqParty) :
    ∀ x ∈ encodeDir W st, IsRecvFile x.1 := by
  intro x hx
  rw [encodeDir_blocks] at hx
  simp only [List.mem_append] at hx
  rcases hx with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
  · unfold blockDir1 at h; rw [List.mem_singleton] at h; subst h
    exact Or.inl (by simp [recvRootFiles])
  · unfold blockDir2 at h; rw [List.mem_singleton] at h; subst h
    exact Or.inl (by simp [recvRootFiles])
  · unfold blockDir3 at h; rw [List.mem_singleton] at h; subst h
    exact Or.inl (by simp [recvRootFiles])
  · unfold blockDir4 at h
    cases hp : st.peerId <;> simp [hp] at h
    subst h; exact isRecvFile_identityFile _
  · unfold blockDir5 at h
    cases hs : st.session <;> simp [hs] at h
    subst h; exact isRecvFile_sessionFile _
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp h
    exact isRecvFile_signedPreKey i
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp h
    exact isRecvFile_oneTimePreKey i
  · obtain ⟨⟨i, _⟩, _, rfl⟩ := List.mem_map.mp h
    exact isRecvFile_oneTimeKyberPreKey i
  · obtain ⟨l, hl, hmem⟩ := List.mem_flatten.mp h
    obtain ⟨⟨i, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_cons.mp hmem with rfl | hmem2
    · exact isRecvFile_lastResortKyberPreKey i
    · rw [List.mem_singleton] at hmem2; subst hmem2; exact isRecvFile_baseKeysFile i

theorem isRecvFile_pqRecv_files (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ∀ x ∈ (pqRecvInputs W st c rc).files, IsRecvFile x.1 := by
  intro x hx
  simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hx
  rcases hx with henc | rfl
  · exact isRecvFile_encodeDir W st x henc
  · exact Or.inl (by simp [recvRootFiles])

private theorem find?_congr_mem {α : Type} {l : List α} {p1 p2 : α → Bool}
    (h : ∀ x ∈ l, p1 x = p2 x) : l.find? p1 = l.find? p2 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.find?_cons, h hd List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem runFiles_pqRecv_dir_v031 (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) {d : String} (hd : d ∈ partyDirs) (hns : '/' ∉ d.toList) :
    runFiles (pqRecvInputs W st c rc) d = some .dir := by
  have hd_props : normalizePath d = [d] ∧ (normalizePath d).isEmpty = false ∧
      normalizePath d ∉ stdioPaths.map normalizePath ∧ d ∉ recvRootFiles ∧
      (dirsFold partyDirs {}).entries [d] = some .dir := by
    revert d hd hns
    decide
  rcases hd_props with ⟨hn, hne, hstdio, hnroot, hbase⟩
  unfold runFiles
  rw [files_eq_entries, ite_eq_right_iff.mpr (by simp [hne]),
    initFsState_entries (cliInputs (pqRecvInputs W st c rc)) (normalizePath d) hstdio]
  change (filesFold (pqRecvInputs W st c rc).files (dirsFold partyDirs {})).entries
      (normalizePath d) = some .dir
  rw [hn, (filesFold_isRecvFile_entries (isRecvFile_pqRecv_files W st c rc)
      hasParentDirs_partyDirs).2 [d]]
  have hnone : (pqRecvInputs W st c rc).files.reverse.find?
      (fun x => normalizePath x.1 == [d]) = none := by
    rw [List.find?_eq_none]
    intro x hx hbeq
    have heq := beq_iff_eq.mp hbeq
    rcases isRecvFile_norm_shape
        (isRecvFile_pqRecv_files W st c rc x (List.mem_reverse.mp hx)) with
      ⟨hr, hnx⟩ | ⟨_, _, _, _, hnx⟩
    · rw [hnx] at heq; exact hnroot (List.singleton_injective heq ▸ hr)
    · rw [hnx] at heq; nomatch heq
  rw [hnone, hbase]

theorem runFiles_pqRecv_isRecvFile (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) {q : String} (hq : IsRecvFile q) :
    runFiles (pqRecvInputs W st c rc) q =
      ((pqRecvInputs W st c rc).files.reverse.find? (fun x => x.1 == q)).map
        (fun pb => .file pb.2) := by
  have hq_env : (normalizePath q).isEmpty = false ∧
      normalizePath q ∉ stdioPaths.map normalizePath ∧
      (dirsFold partyDirs {}).entries (normalizePath q) = none := by
    rcases isRecvFile_norm_shape hq with ⟨hr, hnq⟩ | ⟨d, sfx, hd, _, hnq⟩
    · obtain ⟨_, _, hstd, hnone⟩ := recvRootFiles_props hr
      rw [hnq]; exact ⟨rfl, hstd, hnone⟩
    · rw [hnq]; exact ⟨rfl, two_not_mem_stdioPaths d sfx, dirsFold_partyDirs_two_none hd sfx⟩
  rcases hq_env with ⟨hne, hstdio, hbase⟩
  unfold runFiles
  rw [files_eq_entries, ite_eq_right_iff.mpr (by simp [hne]),
    initFsState_entries (cliInputs (pqRecvInputs W st c rc)) (normalizePath q) hstdio]
  change (filesFold (pqRecvInputs W st c rc).files (dirsFold partyDirs {})).entries
      (normalizePath q) = _
  rw [(filesFold_isRecvFile_entries (isRecvFile_pqRecv_files W st c rc)
      hasParentDirs_partyDirs).2 (normalizePath q), hbase]
  have hcongr : (pqRecvInputs W st c rc).files.reverse.find?
      (fun x => normalizePath x.1 == normalizePath q) =
      (pqRecvInputs W st c rc).files.reverse.find? (fun x => x.1 == q) := by
    refine find?_congr_mem fun x hx => ?_
    have hx_rf := isRecvFile_pqRecv_files W st c rc x (List.mem_reverse.mp hx)
    cases h1 : (normalizePath x.1 == normalizePath q) <;> cases h2 : (x.1 == q)
    · rfl
    · exact absurd (congrArg normalizePath (beq_iff_eq.mp h2)) (beq_eq_false_iff_ne.mp h1)
    · exact absurd (isRecvFile_norm_inj hx_rf hq (beq_iff_eq.mp h1)) (beq_eq_false_iff_ne.mp h2)
    · rfl
  rw [hcongr]
  cases (pqRecvInputs W st c rc).files.reverse.find? (fun x => x.1 == q) <;> rfl

theorem filesOf_eq_of_isRecvFile {L1 L2 : List (String × List (BitVec 8))}
    (h1 : ∀ x ∈ L1, IsRecvFile x.1) (h2 : ∀ x ∈ L2, IsRecvFile x.1)
    (hfind : ∀ q : String,
      (L1.reverse.find? (fun x => x.1 == q)).map Prod.snd =
      (L2.reverse.find? (fun x => x.1 == q)).map Prod.snd) :
    filesOf L1 = filesOf L2 := by
  have heq1 := (fsView_initFsState { dirs := partyDirs, files := L1 }).symm
  have heq2 := (fsView_initFsState { dirs := partyDirs, files := L2 }).symm
  rw [heq1, heq2]
  funext p
  unfold fsView
  split
  · rfl
  · next hstdio =>
    show fileOfEntry ((Process.initFsState { dirs := partyDirs, files := L1 }).files p) =
      fileOfEntry ((Process.initFsState { dirs := partyDirs, files := L2 }).files p)
    simp only [FsState.files, FsState.getEntry]
    split
    · rfl
    · rw [initFsState_entries { dirs := partyDirs, files := L1 } (normalizePath p) hstdio,
        initFsState_entries { dirs := partyDirs, files := L2 } (normalizePath p) hstdio]
      dsimp only
      rw [(filesFold_isRecvFile_entries h1 hasParentDirs_partyDirs).2 (normalizePath p),
        (filesFold_isRecvFile_entries h2 hasParentDirs_partyDirs).2 (normalizePath p)]
      have hnf : fileOfEntry ((dirsFold partyDirs {}).entries (normalizePath p)) = none :=
        NoFiles.dirsFold_none partyDirs (normalizePath p)
      have heval : ∀ L : List (String × List (BitVec 8)),
          fileOfEntry (match L.reverse.find? (fun x => normalizePath x.1 == normalizePath p) with
            | some pb => some (.file pb.2)
            | none => (dirsFold partyDirs {}).entries (normalizePath p)) =
          (L.reverse.find? (fun x => normalizePath x.1 == normalizePath p)).map Prod.snd := by
        intro L
        cases L.reverse.find? (fun x => normalizePath x.1 == normalizePath p) with
        | some _ => rfl
        | none => exact hnf
      rw [heval L1, heval L2]
      by_cases hex : ∃ q0, IsRecvFile q0 ∧ normalizePath q0 = normalizePath p
      · obtain ⟨q0, hq0, hnorm0⟩ := hex
        rw [← hnorm0]
        have hc1 : L1.reverse.find? (fun x => normalizePath x.1 == normalizePath q0) =
            L1.reverse.find? (fun x => x.1 == q0) := by
          refine find?_congr_mem fun x hx => ?_
          have hx_rf := h1 x (List.mem_reverse.mp hx)
          cases b1 : (normalizePath x.1 == normalizePath q0) <;> cases b2 : (x.1 == q0)
          · rfl
          · exact absurd (congrArg normalizePath (beq_iff_eq.mp b2)) (beq_eq_false_iff_ne.mp b1)
          · exact absurd (isRecvFile_norm_inj hx_rf hq0 (beq_iff_eq.mp b1))
              (beq_eq_false_iff_ne.mp b2)
          · rfl
        have hc2 : L2.reverse.find? (fun x => normalizePath x.1 == normalizePath q0) =
            L2.reverse.find? (fun x => x.1 == q0) := by
          refine find?_congr_mem fun x hx => ?_
          have hx_rf := h2 x (List.mem_reverse.mp hx)
          cases b1 : (normalizePath x.1 == normalizePath q0) <;> cases b2 : (x.1 == q0)
          · rfl
          · exact absurd (congrArg normalizePath (beq_iff_eq.mp b2)) (beq_eq_false_iff_ne.mp b1)
          · exact absurd (isRecvFile_norm_inj hx_rf hq0 (beq_iff_eq.mp b1))
              (beq_eq_false_iff_ne.mp b2)
          · rfl
        rw [hc1, hc2]
        exact hfind q0
      · have hn1 : L1.reverse.find? (fun x => normalizePath x.1 == normalizePath p) = none := by
          rw [List.find?_eq_none]
          intro x hx hbeq
          exact hex ⟨x.1, h1 x (List.mem_reverse.mp hx), beq_iff_eq.mp hbeq⟩
        have hn2 : L2.reverse.find? (fun x => normalizePath x.1 == normalizePath p) = none := by
          rw [List.find?_eq_none]
          intro x hx hbeq
          exact hex ⟨x.1, h2 x (List.mem_reverse.mp hx), beq_iff_eq.mp hbeq⟩
        rw [hn1, hn2]

end CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
