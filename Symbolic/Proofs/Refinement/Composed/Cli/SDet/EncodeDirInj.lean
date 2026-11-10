/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.Defs
import all Init.Data.Repr
import all Init.Data.String.Defs
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.CodecInj
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.FilesOfAlg

/-!
# Directory Encoding Equivalence and Injectivity

Proves that `PqPartyEquiv` characterizes equality of `filesOf (encodeDir P st)` snapshots for
`PqParty` states in `PqxdhPartyInSpecDomain`.
-/

@[expose] public section

set_option autoImplicit false

namespace EncodeDirInjAux

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement.Cli.SDet
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.SignalSession

/-! ## Decimal `toString` injectivity and `.base-keys` separation -/

private def parseDecCore : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => parseDecCore cs (acc * 10 + (c.toNat - 48))

private theorem digitChar_val {r : Nat} (hr : r < 10) :
    (Nat.digitChar r).toNat - 48 = r := by
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
    have hrem := digitChar_val (Nat.mod_lt n (by omega))
    split
    · simp only [parseDecCore, hrem, Nat.zero_mul, Nat.zero_add]
      have hn : n % 10 = n := Nat.mod_eq_of_lt (by omega)
      rw [hn]
    · have hlt : n / 10 < fuel := by omega
      rw [parseDecCore_toDigitsCore fuel (n / 10) _ hlt]
      simp only [parseDecCore, hrem]
      have hdm : n / 10 * 10 + n % 10 = n := by omega
      rw [hdm]

private theorem toString_nat_inj {n m : Nat} (h : toString n = toString m) : n = m := by
  have hl : (toString n).toList = (toString m).toList := congrArg String.toList h
  rw [Nat.toString_eq_ofList_toDigits, Nat.toString_eq_ofList_toDigits,
      String.toList_ofList, String.toList_ofList] at hl
  have h1 := parseDecCore_toDigitsCore (n + 1) n [] (Nat.lt_succ_self n)
  have h2 := parseDecCore_toDigitsCore (m + 1) m [] (Nat.lt_succ_self m)
  change parseDecCore (Nat.toDigits 10 n) 0 = n at h1
  change parseDecCore (Nat.toDigits 10 m) 0 = m at h2
  rw [hl] at h1
  exact h1.symm.trans h2

private theorem keyId_inj {i j : BitVec 32} (h : toString i.toNat = toString j.toNat) : i = j :=
  BitVec.eq_of_toNat_eq (toString_nat_inj h)

private theorem keyId_suf_inj (suf : String) {i j : BitVec 32}
    (h : toString i.toNat ++ suf = toString j.toNat ++ suf) : i = j := by
  have hl := congrArg String.toList h
  simp only [String.toList_append] at hl
  have hlen : (toString i.toNat).toList.length = (toString j.toNat).toList.length := by
    have := congrArg List.length hl
    simp only [List.length_append] at this
    omega
  have hi := (List.append_inj hl hlen).1
  exact keyId_inj (by
    rw [← String.ofList_toList (s := toString i.toNat),
        ← String.ofList_toList (s := toString j.toNat), hi])

private theorem toString_ne_baseKeys (i j : BitVec 32) :
    toString i.toNat ≠ toString j.toNat ++ ".base-keys" := by
  intro h
  have hdot := (toString_nat_seg i.toNat).2.1
  have hmem : '.' ∈ (toString i.toNat).toList := by
    rw [h, String.toList_append]
    exact List.mem_append.mpr (Or.inr (by decide))
  exact hdot hmem

/-! ## Normalized paths of `encodeDir` entries -/

private theorem norm_signedPreKeyFile (i : BitVec 32) :
    Arm64.normalizePath (signedPreKeyFile i) = ["signed-pre-keys", toString i.toNat] := by
  simpa [signedPreKeyFile] using
    normalizePath_dir_nat_suf (d := "signed-pre-keys") (suf := "") i.toNat
      (by decide) (by decide) (by decide) (by decide)

private theorem norm_oneTimePreKeyFile (i : BitVec 32) :
    Arm64.normalizePath (oneTimePreKeyFile i) = ["one-time-pre-keys", toString i.toNat] := by
  simpa [oneTimePreKeyFile] using
    normalizePath_dir_nat_suf (d := "one-time-pre-keys") (suf := "") i.toNat
      (by decide) (by decide) (by decide) (by decide)

private theorem norm_oneTimeKyberPreKeyFile (i : BitVec 32) :
    Arm64.normalizePath (oneTimeKyberPreKeyFile i) =
      ["one-time-kyber-pre-keys", toString i.toNat] := by
  simpa [oneTimeKyberPreKeyFile] using
    normalizePath_dir_nat_suf (d := "one-time-kyber-pre-keys") (suf := "") i.toNat
      (by decide) (by decide) (by decide) (by decide)

private theorem norm_lastResortKyberPreKeyFile (i : BitVec 32) :
    Arm64.normalizePath (lastResortKyberPreKeyFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat] := by
  simpa [lastResortKyberPreKeyFile] using
    normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := "") i.toNat
      (by decide) (by decide) (by decide) (by decide)

private theorem norm_baseKeysFile (i : BitVec 32) :
    Arm64.normalizePath (baseKeysFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat ++ ".base-keys"] := by
  simpa [baseKeysFile] using
    normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := ".base-keys") i.toNat
      (by decide) (by decide) (by decide) (by decide)

/-! ## `pFold` algebra and keyed `Nodup` lookup -/

private def pFold (q : List String) (l : List (String × HwBytes)) (init : Option HwBytes) :
    Option HwBytes :=
  l.foldl (fun acc f => if q == Arm64.normalizePath f.1 then some f.2 else acc) init

private theorem filesOf_encodeDir_eq_pFold (P : PEParams) (st : PqParty) (p : String) :
    filesOf (encodeDir P st) p = pFold (Arm64.normalizePath p) (encodeDir P st) none :=
  filesOf_eq_optFold (regularFileList_encodeDir P st) p

private theorem pFold_or (q : List String) (l : List (String × HwBytes)) (init : Option HwBytes) :
    pFold q l init = (pFold q l none).or init := by
  induction l generalizing init with
  | nil => simp [pFold]
  | cons f fs ih =>
    simp only [pFold, List.foldl_cons]
    cases heq : q == Arm64.normalizePath f.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ih init
    · change pFold q fs (some f.2) = (pFold q fs (some f.2)).or init
      rw [ih (some f.2), Option.or_assoc]; simp

private theorem pFold_append_none (q : List String) (l₁ l₂ : List (String × HwBytes)) :
    pFold q (l₁ ++ l₂) none = (pFold q l₂ none).or (pFold q l₁ none) := by
  unfold pFold
  rw [List.foldl_append]
  exact pFold_or q l₂ _

private theorem pFold_eq_none_of_forall_ne {q : List String} {l : List (String × HwBytes)}
    (h : ∀ f ∈ l, q ≠ Arm64.normalizePath f.1) : pFold q l none = none := by
  induction l with
  | nil => rfl
  | cons f fs ih =>
    have hne : (q == Arm64.normalizePath f.1) = false :=
      beq_false_of_ne (h f (List.mem_cons_self ..))
    simp only [pFold, List.foldl_cons, hne, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun g hg => h g (List.mem_cons_of_mem _ hg))

private theorem pFold_map_keyed {V : Type} (dir : String) (pathOf : BitVec 32 → String)
    (valOf : BitVec 32 → V → HwBytes)
    (hpath : ∀ i, Arm64.normalizePath (pathOf i) = [dir, toString i.toNat])
    {l : List (BitVec 32 × V)} (hnodup : (l.map (·.1)).Nodup) (id : BitVec 32) :
    pFold [dir, toString id.toNat] (l.map fun (i, v) => (pathOf i, valOf i v)) none =
      (l.lookup id).map (valOf id) := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨i, v⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hi_nin, hrest_nd⟩ := hnodup
    by_cases hid : id = i
    · subst hid
      have hbeq : ([dir, toString id.toNat] == Arm64.normalizePath (pathOf id)) = true :=
        beq_iff_eq.mpr (hpath id).symm
      have hnone :
          pFold [dir, toString id.toNat] (rest.map fun (j, w) => (pathOf j, valOf j w)) none = none := by
        refine pFold_eq_none_of_forall_ne fun f hf heq => ?_
        simp only [List.mem_map] at hf
        rcases hf with ⟨⟨j, w⟩, hjw, rfl⟩
        rw [hpath j] at heq
        have hij : id = j := keyId_inj (List.cons.inj (List.cons.inj heq).2).1
        subst hij
        exact hi_nin (List.mem_map.mpr ⟨(id, w), hjw, rfl⟩)
      simp only [List.map_cons, pFold, List.foldl_cons, hbeq, ↓reduceIte, List.lookup,
        beq_self_eq_true, Option.map_some]
      change pFold [dir, toString id.toNat] (rest.map fun (j, w) => (pathOf j, valOf j w))
        (some (valOf id v)) = _
      rw [pFold_or, hnone]; rfl
    · have hbeq_id : (id == i) = false := beq_false_of_ne hid
      have hbeq_p : ([dir, toString id.toNat] == Arm64.normalizePath (pathOf i)) = false :=
        beq_false_of_ne fun heq =>
          hid (keyId_inj (List.cons.inj (List.cons.inj (heq.trans (hpath i))).2).1)
      simp only [List.map_cons, pFold, List.foldl_cons, hbeq_p, Bool.false_eq_true, ↓reduceIte,
        List.lookup, hbeq_id]
      exact ih hrest_nd

private theorem pFold_map_keyed_eq {V : Type} (dir : String) (pathOf : BitVec 32 → String)
    (valOf : BitVec 32 → V → HwBytes)
    (hpath : ∀ i, Arm64.normalizePath (pathOf i) = [dir, toString i.toNat])
    {l₁ l₂ : List (BitVec 32 × V)}
    (hnd₁ : (l₁.map (·.1)).Nodup) (hnd₂ : (l₂.map (·.1)).Nodup)
    (hlk : ∀ id, l₁.lookup id = l₂.lookup id) (q : List String) :
    pFold q (l₁.map fun (i, v) => (pathOf i, valOf i v)) none =
    pFold q (l₂.map fun (i, v) => (pathOf i, valOf i v)) none := by
  by_cases hq : ∃ id : BitVec 32, q = [dir, toString id.toNat]
  · rcases hq with ⟨id, rfl⟩
    rw [pFold_map_keyed dir pathOf valOf hpath hnd₁ id,
        pFold_map_keyed dir pathOf valOf hpath hnd₂ id, hlk id]
  · have hnone : ∀ (l : List (BitVec 32 × V)),
        pFold q (l.map fun (i, v) => (pathOf i, valOf i v)) none = none := fun l => by
      refine pFold_eq_none_of_forall_ne fun f hf heq => hq ?_
      simp only [List.mem_map] at hf
      rcases hf with ⟨⟨i, _⟩, _, rfl⟩
      exact ⟨i, heq.trans (hpath i)⟩
    rw [hnone l₁, hnone l₂]

private abbrev KyberLrVal := PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32)

private def kyberLrEntries (l : List (BitVec 32 × KyberLrVal)) : List (String × HwBytes) :=
  (l.map fun (i, k, seen) =>
    [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten

private theorem pFold_kyberLr_rec {l : List (BitVec 32 × KyberLrVal)}
    (hnodup : (l.map (·.1)).Nodup) (id : BitVec 32) :
    pFold ["last-resort-kyber-pre-keys", toString id.toNat] (kyberLrEntries l) none =
      (l.lookup id).map (fun p => kyberRecordBytes id p.1) := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨i, k, seen⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hi_nin, hrest_nd⟩ := hnodup
    have hbk_f : (["last-resort-kyber-pre-keys", toString id.toNat] ==
        Arm64.normalizePath (baseKeysFile i)) = false :=
      beq_false_of_ne fun heq =>
        toString_ne_baseKeys id i (List.cons.inj (List.cons.inj (heq.trans (norm_baseKeysFile i))).2).1
    by_cases hid : id = i
    · subst hid
      have hrec_t : (["last-resort-kyber-pre-keys", toString id.toNat] ==
          Arm64.normalizePath (lastResortKyberPreKeyFile id)) = true :=
        beq_iff_eq.mpr (norm_lastResortKyberPreKeyFile id).symm
      have hnone : pFold ["last-resort-kyber-pre-keys", toString id.toNat]
          (kyberLrEntries rest) none = none := by
        refine pFold_eq_none_of_forall_ne fun f hf heq => ?_
        unfold kyberLrEntries at hf
        simp only [List.mem_flatten, List.mem_map] at hf
        rcases hf with ⟨pair, ⟨⟨j, kj, sj⟩, hj, rfl⟩, hf_pair⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_pair
        rcases hf_pair with rfl | rfl
        · have hij : id = j := keyId_inj
            (List.cons.inj (List.cons.inj (heq.trans (norm_lastResortKyberPreKeyFile j))).2).1
          subst hij
          exact hi_nin (List.mem_map.mpr ⟨(id, kj, sj), hj, rfl⟩)
        · exact toString_ne_baseKeys id j
            (List.cons.inj (List.cons.inj (heq.trans (norm_baseKeysFile j))).2).1
      simp only [kyberLrEntries, List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
        pFold, List.foldl_cons, hrec_t, hbk_f, Bool.false_eq_true, ↓reduceIte, List.lookup,
        beq_self_eq_true, Option.map_some]
      change pFold ["last-resort-kyber-pre-keys", toString id.toNat] (kyberLrEntries rest)
        (some (kyberRecordBytes id k)) = _
      rw [pFold_or, hnone]; rfl
    · have hbeq_id : (id == i) = false := beq_false_of_ne hid
      have hrec_f : (["last-resort-kyber-pre-keys", toString id.toNat] ==
          Arm64.normalizePath (lastResortKyberPreKeyFile i)) = false :=
        beq_false_of_ne fun heq => hid (keyId_inj
          (List.cons.inj (List.cons.inj (heq.trans (norm_lastResortKyberPreKeyFile i))).2).1)
      simp only [kyberLrEntries, List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
        pFold, List.foldl_cons, hrec_f, hbk_f, Bool.false_eq_true, ↓reduceIte, List.lookup, hbeq_id]
      exact ih hrest_nd

private theorem pFold_kyberLr_base {l : List (BitVec 32 × KyberLrVal)}
    (hnodup : (l.map (·.1)).Nodup) (id : BitVec 32) :
    pFold ["last-resort-kyber-pre-keys", toString id.toNat ++ ".base-keys"] (kyberLrEntries l) none =
      (l.lookup id).map (fun p => baseKeysBytes p.2) := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨i, k, seen⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hi_nin, hrest_nd⟩ := hnodup
    have hrec_f : (["last-resort-kyber-pre-keys", toString id.toNat ++ ".base-keys"] ==
        Arm64.normalizePath (lastResortKyberPreKeyFile i)) = false :=
      beq_false_of_ne fun heq => toString_ne_baseKeys i id
        (List.cons.inj (List.cons.inj (heq.trans (norm_lastResortKyberPreKeyFile i))).2).1.symm
    by_cases hid : id = i
    · subst hid
      have hbk_t : (["last-resort-kyber-pre-keys", toString id.toNat ++ ".base-keys"] ==
          Arm64.normalizePath (baseKeysFile id)) = true :=
        beq_iff_eq.mpr (norm_baseKeysFile id).symm
      have hnone : pFold ["last-resort-kyber-pre-keys", toString id.toNat ++ ".base-keys"]
          (kyberLrEntries rest) none = none := by
        refine pFold_eq_none_of_forall_ne fun f hf heq => ?_
        unfold kyberLrEntries at hf
        simp only [List.mem_flatten, List.mem_map] at hf
        rcases hf with ⟨pair, ⟨⟨j, kj, sj⟩, hj, rfl⟩, hf_pair⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_pair
        rcases hf_pair with rfl | rfl
        · exact toString_ne_baseKeys j id
            (List.cons.inj (List.cons.inj (heq.trans (norm_lastResortKyberPreKeyFile j))).2).1.symm
        · have hij : id = j := keyId_suf_inj ".base-keys"
            (List.cons.inj (List.cons.inj (heq.trans (norm_baseKeysFile j))).2).1
          subst hij
          exact hi_nin (List.mem_map.mpr ⟨(id, kj, sj), hj, rfl⟩)
      simp only [kyberLrEntries, List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
        pFold, List.foldl_cons, hrec_f, hbk_t, Bool.false_eq_true, ↓reduceIte, List.lookup,
        beq_self_eq_true, Option.map_some]
      change pFold ["last-resort-kyber-pre-keys", toString id.toNat ++ ".base-keys"]
        (kyberLrEntries rest) (some (baseKeysBytes seen)) = _
      rw [pFold_or, hnone]; rfl
    · have hbeq_id : (id == i) = false := beq_false_of_ne hid
      have hbk_f : (["last-resort-kyber-pre-keys", toString id.toNat ++ ".base-keys"] ==
          Arm64.normalizePath (baseKeysFile i)) = false :=
        beq_false_of_ne fun heq => hid (keyId_suf_inj ".base-keys"
          (List.cons.inj (List.cons.inj (heq.trans (norm_baseKeysFile i))).2).1)
      simp only [kyberLrEntries, List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
        pFold, List.foldl_cons, hrec_f, hbk_f, Bool.false_eq_true, ↓reduceIte, List.lookup, hbeq_id]
      exact ih hrest_nd

private theorem pFold_kyberLr_eq {l₁ l₂ : List (BitVec 32 × KyberLrVal)}
    (hnd₁ : (l₁.map (·.1)).Nodup) (hnd₂ : (l₂.map (·.1)).Nodup)
    (hlk : ∀ id, l₁.lookup id = l₂.lookup id) (q : List String) :
    pFold q (kyberLrEntries l₁) none = pFold q (kyberLrEntries l₂) none := by
  by_cases h1 : ∃ id : BitVec 32, q = ["last-resort-kyber-pre-keys", toString id.toNat]
  · rcases h1 with ⟨id, rfl⟩
    rw [pFold_kyberLr_rec hnd₁ id, pFold_kyberLr_rec hnd₂ id, hlk id]
  · by_cases h2 : ∃ id : BitVec 32, q = ["last-resort-kyber-pre-keys", toString id.toNat ++ ".base-keys"]
    · rcases h2 with ⟨id, rfl⟩
      rw [pFold_kyberLr_base hnd₁ id, pFold_kyberLr_base hnd₂ id, hlk id]
    · have hnone : ∀ l : List (BitVec 32 × KyberLrVal), pFold q (kyberLrEntries l) none = none :=
        fun l => by
          refine pFold_eq_none_of_forall_ne fun f hf heq => ?_
          unfold kyberLrEntries at hf
          simp only [List.mem_flatten, List.mem_map] at hf
          rcases hf with ⟨pair, ⟨⟨i, _, _⟩, _, rfl⟩, hf_pair⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_pair
          rcases hf_pair with rfl | rfl
          · exact h1 ⟨i, heq.trans (norm_lastResortKyberPreKeyFile i)⟩
          · exact h2 ⟨i, heq.trans (norm_baseKeysFile i)⟩
      rw [hnone l₁, hnone l₂]

/-! ## Head-tag block decomposition of `encodeDir` -/

private def dirBlocks (P : PEParams) (st : PqParty) : List (String × List (String × HwBytes)) :=
  [("address", [(addressFile, textBytes (partyAddress st.party).text)]),
   ("identity-key-pair", [(identityKeyPairFile, IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf P.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩)]),
   ("registration-id", [(registrationIdFile, le32 st.me.regId)]),
   ("identities", match st.peerId with
      | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
      | none => []),
   ("sessions", match st.session with
      | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
      | none => []),
   ("signed-pre-keys", st.signed.map fun (i, k) => (signedPreKeyFile i, signedRecordBytes P.C i k)),
   ("one-time-pre-keys", st.oneTime.map fun (i, k) =>
      (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes P.C i sk | none => [])),
   ("one-time-kyber-pre-keys", st.kyberOneTime.map fun (i, k) =>
      (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])),
   ("last-resort-kyber-pre-keys", kyberLrEntries st.kyberLastResort)]

private theorem dirBlocks_flatten (P : PEParams) (st : PqParty) :
    ((dirBlocks P st).map (·.2)).flatten = encodeDir P st := by
  simp only [dirBlocks, encodeDir, kyberLrEntries, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  rfl

private theorem dirBlocks_tags_nodup (P : PEParams) (st : PqParty) :
    ((dirBlocks P st).map (·.1)).Nodup := by
  change ["address", "identity-key-pair", "registration-id", "identities", "sessions",
    "signed-pre-keys", "one-time-pre-keys", "one-time-kyber-pre-keys",
    "last-resort-kyber-pre-keys"].Nodup
  decide

private theorem dirBlocks_entry_head (P : PEParams) (st : PqParty)
    {b : String × List (String × HwBytes)} (hb : b ∈ dirBlocks P st)
    {f : String × HwBytes} (hf : f ∈ b.2) :
    (Arm64.normalizePath f.1).head? = some b.1 := by
  unfold dirBlocks at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [List.mem_singleton] at hf; subst hf; dsimp only; decide
  · rw [List.mem_singleton] at hf; subst hf; dsimp only; decide
  · rw [List.mem_singleton] at hf; subst hf; dsimp only; decide
  · dsimp only at hf ⊢
    cases hp : st.peerId with
    | none => simp [hp] at hf
    | some k => simp only [hp, List.mem_singleton] at hf; subst hf; dsimp only; cases st.party <;> decide
  · dsimp only at hf ⊢
    cases hs : st.session with
    | none => simp [hs] at hf
    | some xg => simp only [hs, List.mem_singleton] at hf; subst hf; dsimp only; cases st.party <;> decide
  · dsimp only at hf ⊢
    simp only [List.mem_map] at hf
    rcases hf with ⟨⟨i, _⟩, _, rfl⟩
    rw [norm_signedPreKeyFile i]; rfl
  · dsimp only at hf ⊢
    simp only [List.mem_map] at hf
    rcases hf with ⟨⟨i, _⟩, _, rfl⟩
    rw [norm_oneTimePreKeyFile i]; rfl
  · dsimp only at hf ⊢
    simp only [List.mem_map] at hf
    rcases hf with ⟨⟨i, _⟩, _, rfl⟩
    rw [norm_oneTimeKyberPreKeyFile i]; rfl
  · dsimp only at hf ⊢
    unfold kyberLrEntries at hf
    simp only [List.mem_flatten, List.mem_map] at hf
    rcases hf with ⟨pair, ⟨⟨i, _, _⟩, _, rfl⟩, hfp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfp
    rcases hfp with rfl | rfl
    · rw [norm_lastResortKyberPreKeyFile i]; rfl
    · rw [norm_baseKeysFile i]; rfl

private theorem pFold_select_block {bs : List (String × List (String × HwBytes))}
    (hnd : (bs.map (·.1)).Nodup)
    (hhd : ∀ b ∈ bs, ∀ f ∈ b.2, (Arm64.normalizePath f.1).head? = some b.1)
    {tag : String} {blk : List (String × HwBytes)} (hlk : bs.lookup tag = some blk)
    {q : List String} (hq : q.head? = some tag) :
    pFold q ((bs.map (·.2)).flatten) none = pFold q blk none := by
  induction bs with
  | nil => simp [List.lookup] at hlk
  | cons tl rest ih =>
    rcases tl with ⟨t, l⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ht_nin, hrest_nd⟩ := hnd
    simp only [List.map_cons, List.flatten_cons, pFold_append_none]
    by_cases htag : tag = t
    · subst htag
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hlk
      subst hlk
      have hrest_none : pFold q ((rest.map (·.2)).flatten) none = none := by
        refine pFold_eq_none_of_forall_ne fun f hf heq => ?_
        simp only [List.mem_flatten, List.mem_map] at hf
        rcases hf with ⟨l', ⟨⟨t', l''⟩, hmem_r, rfl⟩, hf_l⟩
        have hft := hhd (t', l'') (List.mem_cons_of_mem _ hmem_r) f hf_l
        have htt : tag = t' := Option.some.inj (hq.symm.trans (heq ▸ hft))
        subst htt
        exact ht_nin (List.mem_map.mpr ⟨(tag, l''), hmem_r, rfl⟩)
      rw [hrest_none, Option.none_or]
    · have hbeq : (tag == t) = false := beq_false_of_ne htag
      simp only [List.lookup, hbeq] at hlk
      have hl_none : pFold q l none = none := by
        refine pFold_eq_none_of_forall_ne fun f hf heq => ?_
        have hft := hhd (t, l) (List.mem_cons_self ..) f hf
        exact htag (Option.some.inj (hq.symm.trans (heq ▸ hft)))
      rw [hl_none, Option.or_none]
      exact ih hrest_nd (fun b hb => hhd b (List.mem_cons_of_mem _ hb)) hlk

private theorem filesOf_encodeDir_block (P : PEParams) (st : PqParty)
    {tag : String} {blk : List (String × HwBytes)}
    (hlk : (dirBlocks P st).lookup tag = some blk)
    {p : String} (hp : (Arm64.normalizePath p).head? = some tag) :
    filesOf (encodeDir P st) p = pFold (Arm64.normalizePath p) blk none := by
  rw [filesOf_encodeDir_eq_pFold, ← dirBlocks_flatten]
  exact pFold_select_block (dirBlocks_tags_nodup P st)
    (fun _ hb _ hf => dirBlocks_entry_head P st hb hf) hlk hp

/-! ## Main theorems -/

private theorem byteArray_toList_loop (l : List UInt8) :
    ∀ k i r, l.length - i = k →
      ByteArray.toList.loop ⟨⟨l⟩⟩ i r = r.reverse ++ l.drop i := by
  intro k
  induction k with
  | zero =>
    intro i r hk
    rw [ByteArray.toList.loop.eq_1]
    have hni : ¬ i < (⟨⟨l⟩⟩ : ByteArray).size := by
      change ¬ i < l.length
      omega
    simp only [hni, ↓reduceIte]
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ k ih =>
    intro i r hk
    rw [ByteArray.toList.loop.eq_1]
    have hi : i < (⟨⟨l⟩⟩ : ByteArray).size := by
      change i < l.length
      omega
    have hget : (⟨⟨l⟩⟩ : ByteArray).get! i = l[i]'hi :=
      getElem!_pos (⟨l⟩ : Array UInt8) i hi
    simp only [hi, ↓reduceIte]
    rw [ih (i + 1) ((⟨⟨l⟩⟩ : ByteArray).get! i :: r) (by omega),
      List.reverse_cons, List.append_assoc, List.singleton_append, hget,
      ← List.drop_eq_getElem_cons]

private theorem byteArray_toList_eq_data_toList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  rcases bs with ⟨⟨l⟩⟩
  unfold ByteArray.toList
  rw [byteArray_toList_loop l l.length 0 [] (Nat.sub_zero _), List.reverse_nil, List.nil_append,
    List.drop_zero]

private theorem textBytes_eq_flatMap (s : String) :
    textBytes s = (s.toList.flatMap String.utf8EncodeChar).map (fun b => BitVec.ofNat 8 b.toNat) := by
  unfold textBytes CryptoVerification.LibsignalTripleRatchetRepr.utf8
  congr 1
  conv_lhs => rw [← String.ofList_toList (s := s)]
  simp only [String.toUTF8, String.toByteArray_ofList, byteArray_toList_eq_data_toList,
    List.utf8Encode, List.data_toByteArray]

private theorem textBytes_addrE_A_ne_B :
    textBytes (partyAddress Party.A).text ≠ textBytes (partyAddress Party.B).text := by
  intro h
  have h0 := congrArg List.head? h
  rw [textBytes_eq_flatMap, textBytes_eq_flatMap] at h0
  revert h0
  decide

theorem filesOf_encodeDir_eq_of_pqPartyEquiv (P : PEParams) {st st' : PqParty}
    (h : PqPartyEquiv st st') (p : String) :
    filesOf (encodeDir P st) p = filesOf (encodeDir P st') p := by
  let q := Arm64.normalizePath p
  rw [filesOf_encodeDir_eq_pFold, filesOf_encodeDir_eq_pFold]
  change pFold q (encodeDir P st) none = pFold q (encodeDir P st') none
  have h_sig := pFold_map_keyed_eq "signed-pre-keys" signedPreKeyFile (signedRecordBytes P.C)
    norm_signedPreKeyFile h.signed_nodup.1 h.signed_nodup.2 h.signed_lookup q
  have h_ot := pFold_map_keyed_eq "one-time-pre-keys" oneTimePreKeyFile
    (fun i k => match k with | some sk => oneTimeRecordBytes P.C i sk | none => [])
    norm_oneTimePreKeyFile h.oneTime_nodup.1 h.oneTime_nodup.2 h.oneTime_lookup q
  have h_kot := pFold_map_keyed_eq "one-time-kyber-pre-keys" oneTimeKyberPreKeyFile
    (fun i k => match k with | some k => kyberRecordBytes i k | none => [])
    norm_oneTimeKyberPreKeyFile h.kyberOneTime_nodup.1 h.kyberOneTime_nodup.2 h.kyberOneTime_lookup q
  have h_klr := pFold_kyberLr_eq h.kyberLastResort_nodup.1 h.kyberLastResort_nodup.2
    h.kyberLastResort_lookup q
  unfold encodeDir
  simp only [pFold_append_none]
  refine congrArg₂ (fun x y : Option HwBytes => x.or y) h_klr ?_
  refine congrArg₂ (fun x y : Option HwBytes => x.or y) h_kot ?_
  refine congrArg₂ (fun x y : Option HwBytes => x.or y) h_ot ?_
  refine congrArg₂ (fun x y : Option HwBytes => x.or y) h_sig ?_
  refine congrArg₂ (fun x y : Option HwBytes => x.or y) ?_ ?_
  · rw [h.party_eq]
    have hsr := h.session_rel
    cases hs : st.session with
    | none =>
      cases hs' : st'.session with
      | none => rfl
      | some _ => rw [hs, hs'] at hsr; cases hsr
    | some p0 =>
      cases hs' : st'.session with
      | none => rw [hs, hs'] at hsr; cases hsr
      | some p1 =>
        rcases p0 with ⟨x, g⟩
        rcases p1 with ⟨x', g'⟩
        rw [hs, hs'] at hsr
        cases hsr with
        | some hse =>
          dsimp only at hse ⊢
          rw [encodeRecordX_eq_of_pqSessionEquiv hse]
  · refine congrArg₂ (fun x y : Option HwBytes => x.or y) ?_ ?_
    · rw [h.peerId_eq, h.party_eq]
    · rw [h.party_eq, h.me_eq]

theorem pqPartyEquiv_of_filesOf_encodeDir {P : PEParams} {st st' : PqParty}
    (hwf : PqxdhPartyInSpecDomain P st) (hwf' : PqxdhPartyInSpecDomain P st')
    (hfiles : ∀ p, filesOf (encodeDir P st) p = filesOf (encodeDir P st') p) :
    PqPartyEquiv st st' := by
  obtain ⟨hsess_wf, _, hnd_s, hnd_ot, hnd_kot, hnd_klr⟩ := hwf
  obtain ⟨hsess_wf', _, hnd_s', hnd_ot', hnd_kot', hnd_klr'⟩ := hwf'
  have hparty : st.party = st'.party := by
    have ha := hfiles addressFile
    rw [filesOf_encodeDir_block P st (tag := "address") rfl (by decide),
        filesOf_encodeDir_block P st' (tag := "address") rfl (by decide)] at ha
    simp only [pFold, List.foldl_cons, List.foldl_nil, beq_self_eq_true, ↓reduceIte,
      Option.some.injEq] at ha
    cases hp : st.party <;> cases hp' : st'.party
    · rfl
    · rw [hp, hp'] at ha; exact False.elim (textBytes_addrE_A_ne_B ha)
    · rw [hp, hp'] at ha; exact False.elim (textBytes_addrE_A_ne_B ha.symm)
    · rfl
  have hme : st.me = st'.me := by
    have hik := hfiles identityKeyPairFile
    rw [filesOf_encodeDir_block P st (tag := "identity-key-pair") rfl (by decide),
        filesOf_encodeDir_block P st' (tag := "identity-key-pair") rfl (by decide)] at hik
    simp only [pFold, List.foldl_cons, List.foldl_nil, beq_self_eq_true, ↓reduceIte,
      Option.some.injEq] at hik
    have hidPriv : st.me.idPriv = st'.me.idPriv := identityKeyPair_encode_inj P.C hik
    have hrg := hfiles registrationIdFile
    rw [filesOf_encodeDir_block P st (tag := "registration-id") rfl (by decide),
        filesOf_encodeDir_block P st' (tag := "registration-id") rfl (by decide)] at hrg
    simp only [pFold, List.foldl_cons, List.foldl_nil, beq_self_eq_true, ↓reduceIte,
      Option.some.injEq] at hrg
    have hregId : st.me.regId = st'.me.regId := le32_inj hrg
    cases hm : st.me; cases hm' : st'.me
    rw [hm, hm'] at hidPriv hregId
    dsimp only at hidPriv hregId
    rw [hidPriv, hregId]
  have hpeer : st.peerId = st'.peerId := by
    have hip := hfiles (identityFile (partyAddressName st.party.other))
    have hhd : (Arm64.normalizePath (identityFile (partyAddressName st.party.other))).head? =
        some "identities" := by cases st.party <;> decide
    rw [filesOf_encodeDir_block P st rfl hhd,
        filesOf_encodeDir_block P st' rfl hhd, ← hparty] at hip
    cases hp0 : st.peerId <;> cases hp1 : st'.peerId <;>
      simp only [hp0, hp1, pFold, List.foldl_cons, List.foldl_nil, beq_self_eq_true, ↓reduceIte,
        Option.some.injEq, reduceCtorEq] at hip
    · rfl
    · exact congrArg some (identityKey_serialize_inj hip)
  have hsess : Option.Rel (fun p p' => PqSessionEquiv p.1 p.2 p'.1 p'.2)
      st.session st'.session := by
    have hsp := hfiles (sessionFile (partyAddress st.party.other))
    have hhd : (Arm64.normalizePath (sessionFile (partyAddress st.party.other))).head? =
        some "sessions" := by cases st.party <;> decide
    rw [filesOf_encodeDir_block P st rfl hhd,
        filesOf_encodeDir_block P st' rfl hhd, ← hparty] at hsp
    cases hs0 : st.session <;> cases hs1 : st'.session
    · exact Option.Rel.none
    · rename_i xg1; rcases xg1 with ⟨x', g'⟩
      simp [hs0, hs1, pFold] at hsp
    · rename_i xg0; rcases xg0 with ⟨x, g⟩
      simp [hs0, hs1, pFold] at hsp
    · rename_i xg0 xg1; rcases xg0 with ⟨x, g⟩; rcases xg1 with ⟨x', g'⟩
      simp only [hs0, hs1, pFold, List.foldl_cons, List.foldl_nil, beq_self_eq_true, ↓reduceIte,
        Option.some.injEq] at hsp
      obtain ⟨_, hg_pty, hlen⟩ := hsess_wf x g hs0
      obtain ⟨_, hg'_pty, hlen'⟩ := hsess_wf' x' g' hs1
      exact Option.Rel.some
        (pqSessionEquiv_of_encodeRecordX_eq (hg_pty.trans (hparty.trans hg'_pty.symm))
          hlen hlen' hsp)
  have hlk_s : ∀ id, st.signed.lookup id = st'.signed.lookup id := fun id => by
    have hs := hfiles (signedPreKeyFile id)
    have hhd : (Arm64.normalizePath (signedPreKeyFile id)).head? = some "signed-pre-keys" := by
      rw [norm_signedPreKeyFile]; rfl
    rw [filesOf_encodeDir_block P st rfl hhd, filesOf_encodeDir_block P st' rfl hhd,
        norm_signedPreKeyFile,
        pFold_map_keyed "signed-pre-keys" signedPreKeyFile (signedRecordBytes P.C)
          norm_signedPreKeyFile hnd_s id,
        pFold_map_keyed "signed-pre-keys" signedPreKeyFile (signedRecordBytes P.C)
          norm_signedPreKeyFile hnd_s' id] at hs
    cases h0 : st.signed.lookup id <;> cases h1 : st'.signed.lookup id <;>
      simp only [h0, h1, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hs
    · rfl
    · exact congrArg some (signedRecordBytes_inj P.C id hs)
  have hlk_ot : ∀ id, st.oneTime.lookup id = st'.oneTime.lookup id := fun id => by
    have hs := hfiles (oneTimePreKeyFile id)
    have hhd : (Arm64.normalizePath (oneTimePreKeyFile id)).head? = some "one-time-pre-keys" := by
      rw [norm_oneTimePreKeyFile]; rfl
    rw [filesOf_encodeDir_block P st rfl hhd, filesOf_encodeDir_block P st' rfl hhd,
        norm_oneTimePreKeyFile,
        pFold_map_keyed "one-time-pre-keys" oneTimePreKeyFile
          (fun i k => match k with | some sk => oneTimeRecordBytes P.C i sk | none => [])
          norm_oneTimePreKeyFile hnd_ot id,
        pFold_map_keyed "one-time-pre-keys" oneTimePreKeyFile
          (fun i k => match k with | some sk => oneTimeRecordBytes P.C i sk | none => [])
          norm_oneTimePreKeyFile hnd_ot' id] at hs
    cases h0 : st.oneTime.lookup id <;> cases h1 : st'.oneTime.lookup id <;>
      simp only [h0, h1, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hs
    · rfl
    · rename_i v0 v1
      cases v0 <;> cases v1 <;> dsimp only at hs
      · rfl
      · exact False.elim (oneTimeRecordBytes_ne_nil P.C id _ hs.symm)
      · exact False.elim (oneTimeRecordBytes_ne_nil P.C id _ hs)
      · exact congrArg (some ∘ some) (oneTimeRecordBytes_inj P.C id hs)
  have hlk_kot : ∀ id, st.kyberOneTime.lookup id = st'.kyberOneTime.lookup id := fun id => by
    have hs := hfiles (oneTimeKyberPreKeyFile id)
    have hhd : (Arm64.normalizePath (oneTimeKyberPreKeyFile id)).head? =
        some "one-time-kyber-pre-keys" := by
      rw [norm_oneTimeKyberPreKeyFile]; rfl
    rw [filesOf_encodeDir_block P st rfl hhd, filesOf_encodeDir_block P st' rfl hhd,
        norm_oneTimeKyberPreKeyFile,
        pFold_map_keyed "one-time-kyber-pre-keys" oneTimeKyberPreKeyFile
          (fun i k => match k with | some k => kyberRecordBytes i k | none => [])
          norm_oneTimeKyberPreKeyFile hnd_kot id,
        pFold_map_keyed "one-time-kyber-pre-keys" oneTimeKyberPreKeyFile
          (fun i k => match k with | some k => kyberRecordBytes i k | none => [])
          norm_oneTimeKyberPreKeyFile hnd_kot' id] at hs
    cases h0 : st.kyberOneTime.lookup id <;> cases h1 : st'.kyberOneTime.lookup id <;>
      simp only [h0, h1, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hs
    · rfl
    · rename_i v0 v1
      cases v0 <;> cases v1 <;> dsimp only at hs
      · rfl
      · exact False.elim (kyberRecordBytes_ne_nil id _ hs.symm)
      · exact False.elim (kyberRecordBytes_ne_nil id _ hs)
      · exact congrArg (some ∘ some) (kyberRecordBytes_inj id hs)
  have hlk_klr : ∀ id, st.kyberLastResort.lookup id = st'.kyberLastResort.lookup id := fun id => by
    have hrec := hfiles (lastResortKyberPreKeyFile id)
    have hhd_r : (Arm64.normalizePath (lastResortKyberPreKeyFile id)).head? =
        some "last-resort-kyber-pre-keys" := by
      rw [norm_lastResortKyberPreKeyFile]; rfl
    rw [filesOf_encodeDir_block P st rfl hhd_r, filesOf_encodeDir_block P st' rfl hhd_r,
        norm_lastResortKyberPreKeyFile,
        pFold_kyberLr_rec hnd_klr id, pFold_kyberLr_rec hnd_klr' id] at hrec
    have hbk := hfiles (baseKeysFile id)
    have hhd_b : (Arm64.normalizePath (baseKeysFile id)).head? =
        some "last-resort-kyber-pre-keys" := by
      rw [norm_baseKeysFile]; rfl
    rw [filesOf_encodeDir_block P st rfl hhd_b, filesOf_encodeDir_block P st' rfl hhd_b,
        norm_baseKeysFile,
        pFold_kyberLr_base hnd_klr id, pFold_kyberLr_base hnd_klr' id] at hbk
    cases h0 : st.kyberLastResort.lookup id <;> cases h1 : st'.kyberLastResort.lookup id <;>
      simp only [h0, h1, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hrec hbk
    · rfl
    · rename_i p0 p1; rcases p0 with ⟨k0, s0⟩; rcases p1 with ⟨k1, s1⟩
      dsimp only at hrec hbk
      rw [kyberRecordBytes_inj id hrec, baseKeysBytes_inj hbk]
  exact ⟨hparty, hme, hpeer, hsess, hlk_s, hlk_ot, hlk_kot, hlk_klr,
    ⟨hnd_s, hnd_s'⟩, ⟨hnd_ot, hnd_ot'⟩, ⟨hnd_kot, hnd_kot'⟩, ⟨hnd_klr, hnd_klr'⟩⟩

end EncodeDirInjAux

namespace DY.Libsignal.Composed.Refinement.Cli.SDet

open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession

theorem pqPartyEquiv_of_filesOf_encodeDir {P : PEParams} {st st' : PqParty}
    (hwf : PqxdhPartyInSpecDomain P st) (hwf' : PqxdhPartyInSpecDomain P st')
    (hfiles : ∀ p, filesOf (encodeDir P st) p = filesOf (encodeDir P st') p) :
    PqPartyEquiv st st' :=
  EncodeDirInjAux.pqPartyEquiv_of_filesOf_encodeDir hwf hwf' hfiles

theorem filesOf_encodeDir_eq_of_pqPartyEquiv (P : PEParams) {st st' : PqParty}
    (h : PqPartyEquiv st st') (p : String) :
    filesOf (encodeDir P st) p = filesOf (encodeDir P st') p :=
  EncodeDirInjAux.filesOf_encodeDir_eq_of_pqPartyEquiv P h p

end DY.Libsignal.Composed.Refinement.Cli.SDet
