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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreePaths
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Spec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore

/-!
# Commit Writes and Pathwise `filesOf` Overwrite Lemmas

Reduces `namedWrites g'.writes` to canonical `(path, bytes)` entries and rewrites
`filesOf ((pqRecvInputs W st c rc).files ++ ws)` to `filesOf ((pqRecvInputs W st c rc).files ++ encodeDir W st')`
bucket by bucket.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes

/-! ## Bucket-overwrite and single-entry update lemmas for `filesOf` -/

theorem find?_self_double (B : List (String × List (BitVec 8))) (q : String) :
    B.reverse.find? (fun x => x.1 == q) = (B ++ B).reverse.find? (fun x => x.1 == q) := by
  rw [List.reverse_append, List.find?_append]
  cases B.reverse.find? (fun x => x.1 == q) <;> rfl

theorem find?_map_update {α : Type} {f : BitVec 32 → String} (hf : Function.Injective f)
    {xs : List (BitVec 32 × α)} {j : BitVec 32} {a0 : α}
    (hm0 : (j, a0) ∈ xs) (val : BitVec 32 → α → List (BitVec 8))
    (upd : α) (newBytes : List (BitVec 8)) (hupd : val j upd = newBytes) (q : String) :
    let B := xs.map fun (i, a) => (f i, val i a)
    let B' := (xs.map fun (i, a) => if i = j then (i, upd) else (i, a)).map
      fun (i, a) => (f i, val i a)
    (B ++ [(f j, newBytes)]).reverse.find? (fun x => x.1 == q) =
      (B ++ B').reverse.find? (fun x => x.1 == q) := by
  dsimp only
  rw [List.reverse_append, List.find?_append, List.reverse_append, List.find?_append]
  by_cases hq : f j = q
  · subst hq
    have hw : ([(f j, newBytes)] : List (String × List (BitVec 8))).reverse.find?
        (fun x => x.1 == f j) = some (f j, newBytes) := by
      simp
    have hmem_b' : (f j, newBytes) ∈
        (xs.map fun (i, a) => if i = j then (i, upd) else (i, a)).map
          fun (i, a) => (f i, val i a) := by
      have hm1 : (j, upd) ∈ xs.map (fun (i, a) => if i = j then (i, upd) else (i, a)) := by
        have := List.mem_map_of_mem (f := fun (i, a) => if i = j then (i, upd) else (i, a)) hm0
        simpa using this
      exact hupd ▸ List.mem_map_of_mem (f := fun (i, a) => (f i, val i a)) hm1
    have hb' : ((xs.map fun (i, a) => if i = j then (i, upd) else (i, a)).map
        fun (i, a) => (f i, val i a)).reverse.find? (fun x => x.1 == f j) =
        some (f j, newBytes) := by
      refine find?_reverse_unique hmem_b' fun x hx heq => ?_
      obtain ⟨⟨i, a'⟩, hm1, rfl⟩ := List.mem_map.mp hx
      obtain ⟨⟨i0, a1⟩, _, hi0⟩ := List.mem_map.mp hm1
      have hi : i = j := hf heq
      subst hi
      by_cases hij : i0 = i
      · subst hij; simp at hi0; subst hi0; exact hupd
      · simp [hij] at hi0
    rw [hw, hb']
  · have hw : ([(f j, newBytes)] : List (String × List (BitVec 8))).reverse.find?
        (fun x => x.1 == q) = none := by
      simp [beq_false_of_ne hq]
    have hsame : ∀ ys : List (BitVec 32 × α),
        ((ys.map fun (i, a) => if i = j then (i, upd) else (i, a)).map
          fun (i, a) => (f i, val i a)).reverse.find? (fun x => x.1 == q) =
        (ys.map fun (i, a) => (f i, val i a)).reverse.find? (fun x => x.1 == q) := by
      intro ys
      induction ys with
      | nil => rfl
      | cons hd tl ih =>
        rcases hd with ⟨i, a⟩
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte, Bool.false_eq_true, List.map_cons, List.reverse_cons,
            List.find?_append, ih, List.find?_singleton, beq_false_of_ne hq]
        · simp only [hij, ↓reduceIte, List.map_cons, List.reverse_cons, List.find?_append, ih]
    rw [hw, Option.none_or, hsame xs, ← List.find?_append, ← List.reverse_append]
    exact find?_self_double _ q

theorem find?_lr_update {xs : List (BitVec 32 × PqKyberKey ×
      List (BitVec 32 × List.Vector (BitVec 8) 32))}
    {j : BitVec 32} {k0 : PqKyberKey}
    {seen0 seen' : List (BitVec 32 × List.Vector (BitVec 8) 32)}
    (hm0 : (j, (k0, seen0)) ∈ xs) (q : String) :
    let B := (xs.map fun (i, k, s) =>
      [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
       (baseKeysFile i, baseKeysBytes s)]).flatten
    let B' := ((xs.map fun (i, k, s) =>
      if i = j then (i, k, seen') else (i, k, s)).map fun (i, k, s) =>
      [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
       (baseKeysFile i, baseKeysBytes s)]).flatten
    (B ++ [(baseKeysFile j, baseKeysBytes seen')]).reverse.find? (fun x => x.1 == q) =
      (B ++ B').reverse.find? (fun x => x.1 == q) := by
  dsimp only
  rw [List.reverse_append, List.find?_append, List.reverse_append, List.find?_append]
  by_cases hq : baseKeysFile j = q
  · subst hq
    have hw : ([(baseKeysFile j, baseKeysBytes seen')] :
        List (String × List (BitVec 8))).reverse.find?
        (fun x => x.1 == baseKeysFile j) = some (baseKeysFile j, baseKeysBytes seen') := by
      simp
    have hm1 : (j, k0, seen') ∈ xs.map (fun (i, k, s) =>
        if i = j then (i, k, seen') else (i, k, s)) := by
      have := List.mem_map_of_mem
        (f := fun (i, k, s) => if i = j then (i, k, seen') else (i, k, s)) hm0
      simpa using this
    have hmem_b' : (baseKeysFile j, baseKeysBytes seen') ∈
        ((xs.map fun (i, k, s) =>
          if i = j then (i, k, seen') else (i, k, s)).map fun (i, k, s) =>
          [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
           (baseKeysFile i, baseKeysBytes s)]).flatten :=
      List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hm1, List.mem_cons_of_mem _ List.mem_cons_self⟩
    have hb' := find?_reverse_unique hmem_b' fun x hx heq => by
      obtain ⟨l, hml, hmx⟩ := List.mem_flatten.mp hx
      obtain ⟨⟨i, k, s⟩, hm2, rfl⟩ := List.mem_map.mp hml
      rcases List.mem_cons.mp hmx with rfl | hms
      · exact absurd heq (lastResort_ne_baseKeys i j)
      · rw [List.mem_singleton] at hms; subst hms
        have hi := baseKeysFile_inj heq
        subst hi
        obtain ⟨⟨i0, k1, s1⟩, _, hi0⟩ := List.mem_map.mp hm2
        by_cases hij : i0 = i
        · subst hij; simp at hi0; rw [← hi0.2]
        · simp [hij] at hi0
    rw [hw, hb']
  · have hw : ([(baseKeysFile j, baseKeysBytes seen')] :
        List (String × List (BitVec 8))).reverse.find? (fun x => x.1 == q) = none := by
      simp [beq_false_of_ne hq]
    have hsame : ∀ ys : List (BitVec 32 × PqKyberKey ×
          List (BitVec 32 × List.Vector (BitVec 8) 32)),
        (((ys.map fun (i, k, s) =>
          if i = j then (i, k, seen') else (i, k, s)).map fun (i, k, s) =>
          [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
           (baseKeysFile i, baseKeysBytes s)]).flatten).reverse.find? (fun x => x.1 == q) =
        ((ys.map fun (i, k, s) =>
          [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
           (baseKeysFile i, baseKeysBytes s)]).flatten).reverse.find? (fun x => x.1 == q) := by
      intro ys
      induction ys with
      | nil => rfl
      | cons hd tl ih =>
        rcases hd with ⟨i, k, s⟩
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte, Bool.false_eq_true, List.map_cons, List.flatten_cons,
            List.cons_append, List.nil_append, List.reverse_cons, List.find?_append, ih,
            List.find?_singleton, beq_false_of_ne hq]
        · simp only [hij, ↓reduceIte, List.map_cons, List.flatten_cons, List.cons_append,
            List.nil_append, List.reverse_cons, List.find?_append, ih]
    rw [hw, Option.none_or, hsame xs, ← List.find?_append, ← List.reverse_append]
    exact find?_self_double _ q

theorem filesOf_commit_master (W : PEParams) (st st' : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (ws : List (String × List (BitVec 8)))
    {w4 w5 w7 w8 w9 : List (String × List (BitVec 8))}
    (hws : ws = w4 ++ w8 ++ w9 ++ w7 ++ w5)
    (hb4 : ∀ x ∈ w4, recvBucket x.1 = 4)
    (hb5 : ∀ x ∈ w5, recvBucket x.1 = 5)
    (hb7 : ∀ x ∈ w7, recvBucket x.1 = 7)
    (hb8 : ∀ x ∈ w8, recvBucket x.1 = 8)
    (hb9 : ∀ x ∈ w9, recvBucket x.1 = 9)
    (hw7 : ∀ x ∈ w7, IsRecvFile x.1)
    (hw8 : ∀ x ∈ w8, IsRecvFile x.1)
    (hw9 : ∀ x ∈ w9, IsRecvFile x.1)
    (heq1 : blockDir1 st' = blockDir1 st)
    (heq2 : blockDir2 W st' = blockDir2 W st)
    (heq3 : blockDir3 st' = blockDir3 st)
    (heq4 : w4 = blockDir4 st')
    (heq5 : w5 = blockDir5 st')
    (heq6 : blockDir6 W st' = blockDir6 W st)
    (heq7 : ∀ q, (blockDir7 W st ++ w7).reverse.find? (fun x => x.1 == q) =
      (blockDir7 W st ++ blockDir7 W st').reverse.find? (fun x => x.1 == q))
    (heq8 : ∀ q, (blockDir8 st ++ w8).reverse.find? (fun x => x.1 == q) =
      (blockDir8 st ++ blockDir8 st').reverse.find? (fun x => x.1 == q))
    (heq9 : ∀ q, (blockDir9 st ++ w9).reverse.find? (fun x => x.1 == q) =
      (blockDir9 st ++ blockDir9 st').reverse.find? (fun x => x.1 == q)) :
    filesOf ((pqRecvInputs W st c rc).files ++ ws) =
      filesOf ((pqRecvInputs W st c rc).files ++ encodeDir W st') := by
  apply filesOf_eq_of_isRecvFile
  · intro x hx
    simp only [hws, List.mem_append, or_assoc] at hx
    rcases hx with henc | h4 | h8 | h9 | h7 | h5
    · exact isRecvFile_pqRecv_files W st c rc x henc
    · rw [heq4] at h4; exact isRecvFile_encodeDir W st' x (by rw [encodeDir_blocks]; simp [h4])
    · exact hw8 x h8
    · exact hw9 x h9
    · exact hw7 x h7
    · rw [heq5] at h5; exact isRecvFile_encodeDir W st' x (by rw [encodeDir_blocks]; simp [h5])
  · intro x hx
    rcases List.mem_append.mp hx with henc | henc'
    · exact isRecvFile_pqRecv_files W st c rc x henc
    · exact isRecvFile_encodeDir W st' x henc'
  · intro q
    refine congrArg (Option.map Prod.snd) ?_
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := bucket_blockDir W st
    obtain ⟨d1', d2', d3', d4', d5', d6', d7', d8', d9'⟩ := bucket_blockDir W st'
    let nilE : List (String × List (BitVec 8)) := []
    have hws_perm : (w4 ++ w8 ++ w9 ++ w7 ++ w5).reverse.find? (fun x => x.1 == q) =
        (nilE ++ nilE ++ nilE ++ w4 ++ w5 ++ nilE ++ w7 ++ w8 ++ w9).reverse.find?
          (fun x => x.1 == q) := by
      simp only [nilE, List.nil_append, List.reverse_append, List.find?_append]
      have n4 : recvBucket q ≠ 4 → w4.reverse.find? (fun x => x.1 == q) = none := fun h =>
        find?_rev_none fun x hx => by rw [hb4 x hx]; exact Ne.symm h
      have n5 : recvBucket q ≠ 5 → w5.reverse.find? (fun x => x.1 == q) = none := fun h =>
        find?_rev_none fun x hx => by rw [hb5 x hx]; exact Ne.symm h
      have n7 : recvBucket q ≠ 7 → w7.reverse.find? (fun x => x.1 == q) = none := fun h =>
        find?_rev_none fun x hx => by rw [hb7 x hx]; exact Ne.symm h
      have n8 : recvBucket q ≠ 8 → w8.reverse.find? (fun x => x.1 == q) = none := fun h =>
        find?_rev_none fun x hx => by rw [hb8 x hx]; exact Ne.symm h
      have n9 : recvBucket q ≠ 9 → w9.reverse.find? (fun x => x.1 == q) = none := fun h =>
        find?_rev_none fun x hx => by rw [hb9 x hx]; exact Ne.symm h
      match hb : recvBucket q with
      | 4 => simp [n5 (by omega), n7 (by omega), n8 (by omega), n9 (by omega)]
      | 5 => simp [n4 (by omega), n7 (by omega), n8 (by omega), n9 (by omega)]
      | 7 => simp [n4 (by omega), n5 (by omega), n8 (by omega), n9 (by omega)]
      | 8 => simp [n4 (by omega), n5 (by omega), n7 (by omega), n9 (by omega)]
      | 9 => simp [n4 (by omega), n5 (by omega), n7 (by omega), n8 (by omega)]
      | 0 | 1 | 2 | 3 | 6 | _ + 10 =>
        simp [n4 (by omega), n5 (by omega), n7 (by omega), n8 (by omega), n9 (by omega)]
    rw [hws]
    have hlhs : ((pqRecvInputs W st c rc).files ++ (w4 ++ w8 ++ w9 ++ w7 ++ w5)).reverse.find?
        (fun x => x.1 == q) =
        ((nilE ++ nilE ++ nilE ++ w4 ++ w5 ++ nilE ++ w7 ++ w8 ++ w9).reverse.find?
          (fun x => x.1 == q)).or
          ((encodeDir W st ++ [(coinsFile, HMAC.keyToBytes32 rc)]).reverse.find?
            (fun x => x.1 == q)) := by
      simp only [pqRecvInputs, pqInputs, List.append_nil]
      rw [List.reverse_append, List.find?_append, hws_perm]
    have hrhs : ((pqRecvInputs W st c rc).files ++ encodeDir W st').reverse.find?
        (fun x => x.1 == q) =
        ((blockDir1 st' ++ blockDir2 W st' ++ blockDir3 st' ++ blockDir4 st' ++ blockDir5 st' ++
          blockDir6 W st' ++ blockDir7 W st' ++ blockDir8 st' ++ blockDir9 st').reverse.find?
          (fun x => x.1 == q)).or
          ((encodeDir W st ++ [(coinsFile, HMAC.keyToBytes32 rc)]).reverse.find?
            (fun x => x.1 == q)) := by
      simp only [pqRecvInputs, pqInputs, List.append_nil]
      rw [List.reverse_append, List.find?_append, encodeDir_blocks W st']
    have hnilE : ∀ n : Nat, ∀ x ∈ nilE, recvBucket x.1 = n :=
      fun _ _ h => False.elim (List.not_mem_nil h)
    rw [hlhs, hrhs]
    rw [find?_select_block (hnilE 1) (hnilE 2) (hnilE 3) hb4 hb5 (hnilE 6) hb7 hb8 hb9 q,
      find?_select_block d1' d2' d3' d4' d5' d6' d7' d8' d9' q]
    by_cases h10 : recvBucket q = 10
    · rw [h10]; rfl
    · have hc_none : ([(coinsFile, HMAC.keyToBytes32 rc)] :
          List (String × List (BitVec 8))).reverse.find? (fun x => x.1 == q) = none :=
        find?_rev_none fun x hx => by
          rw [List.mem_singleton] at hx; subst hx; rw [recvBucket_coins]; exact Ne.symm h10
      simp only [List.reverse_append, List.find?_append, hc_none, Option.none_or]
      rw [encodeDir_blocks W st, find?_select_block d1 d2 d3 d4 d5 d6 d7 d8 d9 q]
      match hb : recvBucket q with
      | 1 =>
        simp only [nilE, List.reverse_nil, List.find?_nil, Option.none_or, heq1,
          ← List.find?_append, ← List.reverse_append]
        exact find?_self_double _ q
      | 2 =>
        simp only [nilE, List.reverse_nil, List.find?_nil, Option.none_or, heq2,
          ← List.find?_append, ← List.reverse_append]
        exact find?_self_double _ q
      | 3 =>
        simp only [nilE, List.reverse_nil, List.find?_nil, Option.none_or, heq3,
          ← List.find?_append, ← List.reverse_append]
        exact find?_self_double _ q
      | 4 => rw [heq4]; rfl
      | 5 => rw [heq5]; rfl
      | 6 =>
        simp only [nilE, List.reverse_nil, List.find?_nil, Option.none_or, heq6,
          ← List.find?_append, ← List.reverse_append]
        exact find?_self_double _ q
      | 7 =>
        simpa only [List.reverse_append, List.find?_append] using heq7 q
      | 8 =>
        simpa only [List.reverse_append, List.find?_append] using heq8 q
      | 9 =>
        simpa only [List.reverse_append, List.find?_append] using heq9 q
      | 0 => rfl
      | _ + 10 => rfl

/-! ## `namedWrites` evaluation -/

private theorem idPeer_path_eq (P : Party) :
    pathStr (pathOf (utf8 "identities") (RunRefine.addrValE P).name) =
      identityFile (partyAddressName P) ∧
    (∀ bt ∈ pathOf (utf8 "identities") (RunRefine.addrValE P).name, bt.toNat < 128) := by
  have hn : (RunRefine.addrValE P).name = utf8 (partyAddressName P) := rfl
  have hascii : ∀ ch ∈ ("identities" ++ "/" ++ partyAddressName P).toList, ch.toNat < 128 := by
    cases P <;> simp only [String.toList_append, partyAddressName] <;> decide
  rw [hn, pathOf_utf8_eq (by decide)]
  exact ⟨pathStr_utf8_ascii hascii, utf8_ascii_bytes hascii⟩

private theorem sessPeer_path_eq (P : Party) :
    pathStr (pathOf (utf8 "sessions") (addressText (RunRefine.addrValE P))) =
      sessionFile (partyAddress P) ∧
    (∀ bt ∈ pathOf (utf8 "sessions") (addressText (RunRefine.addrValE P)), bt.toNat < 128) := by
  have htxt : addressText (RunRefine.addrValE P) = utf8 ((partyAddress P).text) := by
    unfold addressText decimalText RunRefine.addrValE Address.text partyAddress
    have h1 : toString (1 : Nat) = "1" := rfl
    have h1' : toString (1#8).toNat = "1" := rfl
    rw [h1, h1', utf8_append, utf8_append]
  have hascii : ∀ ch ∈ ("sessions" ++ "/" ++ (partyAddress P).text).toList, ch.toNat < 128 := by
    cases P <;> simp only [String.toList_append, partyAddress, Address.text, partyAddressName] <;> decide
  rw [htxt, pathOf_utf8_eq (by decide)]
  exact ⟨pathStr_utf8_ascii hascii, utf8_ascii_bytes hascii⟩

theorem kyberOneTime_path_eq (id : BitVec 32) :
    pathStr (pathOf (utf8 "one-time-kyber-pre-keys") (keyName id)) =
      oneTimeKyberPreKeyFile id ∧
    (∀ bt ∈ pathOf (utf8 "one-time-kyber-pre-keys") (keyName id), bt.toNat < 128) := by
  have hk : keyName id = utf8 (toString id.toNat) := rfl
  have hascii : ∀ ch ∈ ("one-time-kyber-pre-keys" ++ "/" ++ toString id.toNat).toList,
      ch.toNat < 128 := by
    intro ch hch
    simp only [String.toList_append, List.mem_append] at hch
    rcases hch with (h | h) | h
    · revert ch h; decide
    · rw [show "/".toList = ['/'] from rfl, List.mem_singleton] at h; subst h; decide
    · exact (toString_nat_char_props id.toNat h).1
  rw [hk, pathOf_utf8_eq (by decide)]
  exact ⟨pathStr_utf8_ascii hascii, utf8_ascii_bytes hascii⟩

theorem baseKeys_path_eq (id : BitVec 32) :
    pathStr (pathOf (utf8 "last-resort-kyber-pre-keys") (baseKeysName id)) =
      baseKeysFile id ∧
    (∀ bt ∈ pathOf (utf8 "last-resort-kyber-pre-keys") (baseKeysName id), bt.toNat < 128) := by
  have hb : baseKeysName id = utf8 (toString id.toNat ++ ".base-keys") := (utf8_append _ _).symm
  have hascii : ∀ ch ∈
      ("last-resort-kyber-pre-keys" ++ "/" ++ (toString id.toNat ++ ".base-keys")).toList,
      ch.toNat < 128 := by
    intro ch hch
    simp only [String.toList_append, List.mem_append] at hch
    rcases hch with (h | h) | (h | h)
    · revert ch h; decide
    · rw [show "/".toList = ['/'] from rfl, List.mem_singleton] at h; subst h; decide
    · exact (toString_nat_char_props id.toNat h).1
    · revert ch h; decide
  rw [hb, pathOf_utf8_eq (by decide)]
  refine ⟨?_, utf8_ascii_bytes hascii⟩
  rw [pathStr_utf8_ascii hascii]
  simp [baseKeysFile, String.append_assoc]

theorem oneTime_path_eq (id : BitVec 32) :
    pathStr (pathOf (utf8 "one-time-pre-keys") (keyName id)) =
      oneTimePreKeyFile id ∧
    (∀ bt ∈ pathOf (utf8 "one-time-pre-keys") (keyName id), bt.toNat < 128) := by
  have hk : keyName id = utf8 (toString id.toNat) := rfl
  have hascii : ∀ ch ∈ ("one-time-pre-keys" ++ "/" ++ toString id.toNat).toList,
      ch.toNat < 128 := by
    intro ch hch
    simp only [String.toList_append, List.mem_append] at hch
    rcases hch with (h | h) | h
    · revert ch h; decide
    · rw [show "/".toList = ['/'] from rfl, List.mem_singleton] at h; subst h; decide
    · exact (toString_nat_char_props id.toNat h).1
  rw [hk, pathOf_utf8_eq (by decide)]
  exact ⟨pathStr_utf8_ascii hascii, utf8_ascii_bytes hascii⟩

theorem new_writes_nil (dir : List (BitVec 8)) : (DirGhost.new dir).writes = [] := rfl

theorem new_put_writes (dir name val : List (BitVec 8)) :
    ((DirGhost.new dir).put name val).writes = [(pathOf dir name, val)] := rfl

theorem namedWrites_of_dirs (P : Party) (idBytes sessBytes : List (BitVec 8))
    (kotDir klrDir otDir : DirGhost)
    {w8 w9 w7 : List (String × List (BitVec 8))}
    (hkot : (∀ pw ∈ kotDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
            kotDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w8)
    (hklr : (∀ pw ∈ klrDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
            klrDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w9)
    (hot  : (∀ pw ∈ otDir.writes, ∀ bt ∈ pw.1, bt.toNat < 128) ∧
            otDir.writes.map (fun pw => (pathStr pw.1, pw.2)) = w7) :
    namedWrites
      ({ StoresGhost.opened with
         identity :=
           { StoresGhost.opened.identity with
             peers := StoresGhost.opened.identity.peers.put
               (RunRefine.addrValE P).name idBytes }
         kyber := { oneTime := kotDir, lastResort := klrDir }
         oneTime := otDir
         sessions := StoresGhost.opened.sessions.put
           (addressText (RunRefine.addrValE P)) sessBytes }).writes =
      [(identityFile (partyAddressName P), idBytes)] ++ w8 ++ w9 ++ w7 ++
        [(sessionFile (partyAddress P), sessBytes)] := by
  obtain ⟨hid_str, hid_asc⟩ := idPeer_path_eq P
  obtain ⟨hses_str, hses_asc⟩ := sessPeer_path_eq P
  have hw_eq : ({ StoresGhost.opened with
      identity := { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put (RunRefine.addrValE P).name idBytes }
      kyber := { oneTime := kotDir, lastResort := klrDir }
      oneTime := otDir
      sessions := StoresGhost.opened.sessions.put
        (addressText (RunRefine.addrValE P)) sessBytes }).writes =
      [(pathOf (utf8 "identities") (RunRefine.addrValE P).name, idBytes)] ++
        (kotDir.writes ++ (klrDir.writes ++ (otDir.writes ++
          [(pathOf (utf8 "sessions") (addressText (RunRefine.addrValE P)), sessBytes)]))) := by
    unfold StoresGhost.writes
    dsimp only [StoresGhost.opened]
    rw [new_writes_nil, new_writes_nil, new_writes_nil, new_put_writes, new_put_writes]
    simp only [List.nil_append, List.append_nil, List.append_assoc]
  rw [hw_eq, MainHops.namedWrites_ascii]
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hid_str, hses_str, hkot.2, hklr.2, hot.2]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · intro pw hpw bt hbt
    simp only [List.mem_append, List.mem_singleton] at hpw
    rcases hpw with rfl | h2 | h3 | h4 | rfl
    · exact hid_asc bt hbt
    · exact hkot.1 pw h2 bt hbt
    · exact hklr.1 pw h3 bt hbt
    · exact hot.1 pw h4 bt hbt
    · exact hses_asc bt hbt

end CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
