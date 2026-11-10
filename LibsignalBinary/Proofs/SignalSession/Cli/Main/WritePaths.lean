/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.DecodeHex32

/-!
# Store Write-Path Validity for `main`

Establishes `cliWrOk p` (`cliIo.pathOk p ∧ p.length < 2 ^ 32`) for every path written by
`Stores::commit`, and shows that the directory ghost invariant `StoresWrOk` is preserved across all
store updates.

Because `serviceIdParse uuidParse` constrains the byte length (36 or 40 bytes) for arbitrary
`uuidParse` without constraining byte values, `cliWrOk_peer` and `cliWrOk_session` take `CompOk`; at
`uuidTryParse`, `serviceIdParse_compOk` discharges `CompOk` unconditionally.
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.HooksE.HooksOkAux
open CryptoVerification.SignalSession.Cli.Decimal.Helpers

/-! ## Path Components -/

/-- Allowed byte values in store path components: `-`, `.`, `0`–`9`, `:`, `A`–`Z`, and `a`–`z`. -/
def nameCode (b : BitVec 8) : Bool :=
  b.toNat == 45 || b.toNat == 46 || (48 ≤ b.toNat && b.toNat ≤ 58) ||
    (65 ≤ b.toNat && b.toNat ≤ 90) || (97 ≤ b.toNat && b.toNat ≤ 122)

/-- Valid path component: every byte satisfies `nameCode` and at least one byte is not `.` (excluding `""`, `.`, and `..`). -/
def CompOk (p : List (BitVec 8)) : Prop :=
  (∀ b ∈ p, nameCode b = true) ∧ ∃ b ∈ p, b ≠ 0x2e#8

instance (p : List (BitVec 8)) : Decidable (CompOk p) :=
  inferInstanceAs (Decidable ((∀ b ∈ p, nameCode b = true) ∧ ∃ b ∈ p, b ≠ 0x2e#8))

theorem nameCode_facts : ∀ b : BitVec 8, nameCode b = true →
    b.toNat < 128 ∧ Char.ofNat b.toNat ≠ '/' ∧ Char.ofNat b.toNat ≠ '\x00' ∧
      Char.ofNat b.toNat ≠ '<' ∧ (Char.ofNat b.toNat = '.' → b = 0x2e#8) := by
  decide +kernel

theorem CompOk.ne_nil {p : List (BitVec 8)} (h : CompOk p) : p ≠ [] := by
  rintro rfl
  obtain ⟨b, hb, _⟩ := h.2
  exact List.not_mem_nil hb

theorem comp_good {p : List (BitVec 8)} (h : CompOk p) :
    (!isUnmodelledPathComponent (p.map fun b => Char.ofNat b.toNat) &&
      !(p.map fun b => Char.ofNat b.toNat).contains '\x00' &&
      !(stdioPaths.contains
        (String.ofList (p.map fun b => Char.ofNat b.toNat)))) = true := by
  obtain ⟨hall, b0, hb0, hne⟩ := h
  have hch : ∀ c ∈ p.map (fun b => Char.ofNat b.toNat), c ≠ '\x00' ∧ c ≠ '<' := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact ⟨(nameCode_facts b (hall b hb)).2.2.1, (nameCode_facts b (hall b hb)).2.2.2.1⟩
  have hdot : ∀ n, p.map (fun b => Char.ofNat b.toNat) ≠ List.replicate n '.' := by
    intro n heq
    have hm : Char.ofNat b0.toNat ∈ p.map (fun b => Char.ofNat b.toNat) :=
      List.mem_map.mpr ⟨b0, hb0, rfl⟩
    rw [heq] at hm
    exact hne ((nameCode_facts b0 (hall b0 hb0)).2.2.2.2 (List.eq_of_mem_replicate hm))
  generalize p.map (fun b => Char.ofNat b.toNat) = c at hch hdot ⊢
  have h0 : c ≠ [] := hdot 0
  have h1 : c ≠ ['.'] := hdot 1
  have h2 : c ≠ ['.', '.'] := hdot 2
  have hE : c.isEmpty = false := by
    cases c with
    | nil => exact absurd rfl h0
    | cons _ _ => rfl
  have hbad : isUnmodelledPathComponent c = false := by
    simp only [isUnmodelledPathComponent, hE, beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2, Bool.or_false]
  have hnul : c.contains '\x00' = false := by
    cases hcz : c.contains '\x00' with
    | false => rfl
    | true => exact absurd rfl (hch _ (List.contains_iff_mem.mp hcz)).1
  have hstd : stdioPaths.contains (String.ofList c) = false := by
    cases hcs : stdioPaths.contains (String.ofList c) with
    | false => rfl
    | true =>
      have hs := List.contains_iff_mem.mp hcs
      have hlt : '<' ∈ (String.ofList c).toList := by
        simp only [stdioPaths, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with hs | hs | hs <;> rw [hs] <;> decide
      rw [String.toList_ofList] at hlt
      exact absurd rfl (hch _ hlt).2
  simp only [hbad, hnul, hstd, Bool.not_false, Bool.and_self]

/-! ## `/`-Joined Components -/

theorem mem_intercalate_of {α : Type} (P : α → Prop) {sep : List α} (hsep : ∀ x ∈ sep, P x) :
    ∀ cs : List (List α), (∀ c ∈ cs, ∀ x ∈ c, P x) → ∀ x ∈ sep.intercalate cs, P x := by
  intro cs
  induction cs with
  | nil => intro _ x hx; simp at hx
  | cons c cs ih =>
    intro hcs x hx
    cases cs with
    | nil =>
      rw [List.intercalate_singleton] at hx
      exact hcs c List.mem_cons_self x hx
    | cons c' cs' =>
      rw [List.intercalate_cons_cons] at hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact hcs c List.mem_cons_self x hx
        · exact hsep x hx
      · exact ih (fun c'' hc'' => hcs c'' (List.mem_cons_of_mem _ hc'')) x hx

theorem map_intercalate {α β : Type} (f : α → β) (sep : List α) :
    ∀ cs : List (List α),
      (sep.intercalate cs).map f = (sep.map f).intercalate (cs.map fun c => c.map f)
  | [] => rfl
  | [c] => by simp only [List.intercalate_singleton, List.map_cons, List.map_nil]
  | c :: c' :: cs => by
    rw [List.intercalate_cons_cons, List.map_append, List.map_append,
      map_intercalate f sep (c' :: cs)]
    simp only [List.map_cons, List.intercalate_cons_cons]

/-- Nonempty `/`-intercalated `CompOk` components of total length `< cliPathMaxBytes` satisfy `cliIo.pathOk`. -/
theorem pathOk_intercalate (cs : List (List (BitVec 8))) (hne : cs ≠ [])
    (hcs : ∀ c ∈ cs, CompOk c)
    (hcmax : ∀ c ∈ cs, c.length ≤ NAME_MAX)
    (hlen : ([0x2f#8].intercalate cs).length < cliPathMaxBytes) :
    cliIo.pathOk ([0x2f#8].intercalate cs) := by
  have hmap : ([0x2f#8].intercalate cs).map (fun b => Char.ofNat b.toNat) =
      ['/'].intercalate (cs.map fun c => c.map fun b => Char.ofNat b.toNat) :=
    map_intercalate _ _ _
  refine ⟨?_, ⟨?_, ?_⟩, hlen⟩
  · unfold PathOk pathComps pathStr
    rw [String.toList_ofList, hmap, List.splitOn_intercalate]
    · rw [List.all_eq_true]
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact comp_good (hcs p hp)
    · intro l hl hsl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      obtain ⟨b, hb, hbc⟩ := List.mem_map.mp hsl
      exact (nameCode_facts b ((hcs p hp).1 b hb)).2.1 hbc
    · simpa using hne
  · exact mem_intercalate_of (fun b => b.toNat < 128) (sep := [0x2f#8]) (by decide) cs
      (fun c hc b hb => (nameCode_facts b ((hcs c hc).1 b hb)).1)
  · unfold pathComps pathStr
    rw [String.toList_ofList, hmap, List.splitOn_intercalate]
    · rw [List.all_eq_true]
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      rw [List.length_map]
      exact decide_eq_true (hcmax p hp)
    · intro l hl hsl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      obtain ⟨b, hb, hbc⟩ := List.mem_map.mp hsl
      exact (nameCode_facts b ((hcs p hp).1 b hb)).2.1 hbc
    · simpa using hne

theorem pathOf_eq_intercalate {dir : List (BitVec 8)} (hd : dir ≠ []) (name : List (BitVec 8)) :
    pathOf dir name = [0x2f#8].intercalate [dir, name] := by
  rw [pathOf_eq_path hd, List.intercalate_cons_cons, List.intercalate_singleton]

theorem length_pathOf {dir : List (BitVec 8)} (hd : dir ≠ []) (name : List (BitVec 8)) :
    (pathOf dir name).length = dir.length + 1 + name.length := by
  rw [pathOf_eq_path hd, List.length_append, List.length_append, List.length_singleton]

/-! ## Write-Path Predicate `cliWrOk` -/

/-- Valid committed write path: `cliIo.pathOk p` and `p.length < 2 ^ 32`. -/
abbrev cliWrOk (p : List (BitVec 8)) : Prop := cliIo.pathOk p ∧ p.length < 2 ^ 32

theorem cliWrOk_pathOf {dir name : List (BitVec 8)} (hd : CompOk dir) (hn : CompOk name)
    (hd_max : dir.length ≤ NAME_MAX) (hn_max : name.length ≤ NAME_MAX)
    (hlen : dir.length + 1 + name.length < cliPathMaxBytes) : cliWrOk (pathOf dir name) := by
  have hlenp : (pathOf dir name).length < cliPathMaxBytes := by
    rw [length_pathOf hd.ne_nil]; exact hlen
  refine ⟨?_, Nat.lt_trans hlenp (by decide)⟩
  rw [pathOf_eq_intercalate hd.ne_nil] at hlenp ⊢
  refine pathOk_intercalate _ (List.cons_ne_nil _ _) ?_ ?_ hlenp
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc <;> rw [hc]
    · exact hd
    · exact hn
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc <;> rw [hc]
    · exact hd_max
    · exact hn_max

theorem cliWrOk_own {name : List (BitVec 8)} (hn : CompOk name) (hlen : name.length ≤ NAME_MAX) :
    cliWrOk (pathOf [] name) := by
  have he : pathOf [] name = [0x2f#8].intercalate [name] := by simp [pathOf]
  have hlen' : ([0x2f#8].intercalate [name]).length < cliPathMaxBytes := by
    have : NAME_MAX = 255 := rfl
    have : cliPathMaxBytes = 4096 := rfl
    simp only [List.intercalate_singleton]
    omega
  rw [he]
  exact ⟨pathOk_intercalate _ (List.cons_ne_nil _ _) (by simpa using hn) (by simpa using hlen) hlen',
    Nat.lt_trans hlen' (by decide)⟩

/-- Store subdirectory names opened by `Stores::open()` (excluding the root `""`). -/
def storeDirs : List (List (BitVec 8)) :=
  [utf8 "identities", utf8 "signed-pre-keys", utf8 "one-time-kyber-pre-keys",
    utf8 "last-resort-kyber-pre-keys", utf8 "one-time-pre-keys", utf8 "sessions", utf8 "public"]

theorem storeDirs_ok : ∀ d ∈ storeDirs, CompOk d ∧ d.length ≤ 26 := by decide +kernel

theorem cliWrOk_storeDir {dir name : List (BitVec 8)} (hd : dir ∈ storeDirs) (hn : CompOk name)
    (hlen : name.length ≤ 255) : cliWrOk (pathOf dir name) :=
  cliWrOk_pathOf (storeDirs_ok dir hd).1 hn
    (by have := (storeDirs_ok dir hd).2; have : NAME_MAX = 255 := rfl; omega)
    (by have : NAME_MAX = 255 := rfl; omega)
    (by have := (storeDirs_ok dir hd).2; have : cliPathMaxBytes = 4096 := rfl; omega)

/-! ## Store Name Formats -/

theorem decimalText_bytes (n : Nat) : ∀ b ∈ decimalText n, 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b hb
    by_cases h10 : n < 10
    · rw [decimalText_digit n h10, List.mem_singleton] at hb
      subst hb
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [decimalText_ge10 n (by omega), List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | hb
      · exact ih (n / 10) (by omega) b hb
      · subst hb
        simp only [BitVec.toNat_ofNat]
        have := Nat.mod_lt n (show 10 > 0 by omega)
        omega

theorem decimalText_ne_nil (n : Nat) : decimalText n ≠ [] := by
  by_cases h10 : n < 10
  · rw [decimalText_digit n h10]; exact List.cons_ne_nil _ _
  · rw [decimalText_ge10 n (by omega)]; simp

theorem nameCode_digit : ∀ b : BitVec 8, 48 ≤ b.toNat ∧ b.toNat ≤ 57 →
    nameCode b = true ∧ b ≠ 0x2e#8 := by
  decide +kernel

theorem compOk_decimalText (n : Nat) : CompOk (decimalText n) := by
  refine ⟨fun b hb => (nameCode_digit b (decimalText_bytes n b hb)).1, ?_⟩
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (decimalText_ne_nil n)
  exact ⟨b, hb, (nameCode_digit b (decimalText_bytes n b hb)).2⟩

theorem compOk_append {p q : List (BitVec 8)} (hp : CompOk p) (hq : ∀ b ∈ q, nameCode b = true) :
    CompOk (p ++ q) := by
  obtain ⟨hall, b, hb, hne⟩ := hp
  refine ⟨fun x hx => ?_, b, List.mem_append_left _ hb, hne⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact hall x hx
  · exact hq x hx

theorem compOk_keyName (id : BitVec 32) : CompOk (keyName id) := compOk_decimalText id.toNat

theorem keyName_length (id : BitVec 32) : (keyName id).length ≤ 10 :=
  decimalText_length_le 10 id.toNat (by omega) (Nat.lt_trans id.isLt (by decide))

theorem dotBaseKeys_ok :
    (∀ b ∈ utf8 ".base-keys", nameCode b = true) ∧ (utf8 ".base-keys").length = 10 := by
  decide +kernel

theorem compOk_baseKeysName (id : BitVec 32) : CompOk (baseKeysName id) :=
  compOk_append (compOk_keyName id) dotBaseKeys_ok.1

theorem baseKeysName_length (id : BitVec 32) : (baseKeysName id).length ≤ 20 := by
  unfold baseKeysName
  rw [List.length_append, dotBaseKeys_ok.2]
  have := keyName_length id
  omega

theorem dot_ok : (∀ b ∈ utf8 ".", nameCode b = true) ∧ (utf8 ".").length = 1 := by
  decide +kernel

theorem compOk_addressText {a : LibsignalPublicApiRepr.AddrVal} (h : CompOk a.name) :
    CompOk (addressText a) :=
  compOk_append (compOk_append h dot_ok.1) (compOk_decimalText _).1

theorem addressText_length (a : LibsignalPublicApiRepr.AddrVal) :
    (addressText a).length ≤ a.name.length + 4 := by
  unfold addressText
  rw [List.length_append, List.length_append, dot_ok.2]
  have := decimalText_length_le 3 a.device.toNat (by omega) (Nat.lt_trans a.device.isLt (by decide))
  omega

/-- For any `uuidParse`, `serviceIdParse` accepts only 36-byte (ACI) or 40-byte (`PNI:`) names. -/
theorem serviceIdParse_length {uuidParse : UuidParser} {name : List (BitVec 8)}
    {r : Bool × List.Vector (BitVec 8) 16} (h : serviceIdParse uuidParse name = some r) :
    name.length = 36 ∨ name.length = 40 := by
  unfold serviceIdParse tryParseHyphenated at h
  split at h
  · rename_i hpre
    split at h
    · rename_i hl
      right
      have hle := (List.isPrefixOf_iff_prefix.mp hpre).length_le
      rw [List.length_drop] at hl
      have h4 : pniPrefix.length = 4 := by decide +kernel
      unfold hyphenatedLength at hl
      omega
    · simp at h
  · split at h
    · rename_i hl
      left
      unfold hyphenatedLength at hl
      exact hl
    · simp at h

/-! ## Per-Constructor `cliWrOk` Lemmas -/

theorem cliWrOk_peer {name : List (BitVec 8)} (hn : CompOk name) (hlen : name.length ≤ 40) :
    cliWrOk (pathOf (utf8 "identities") name) :=
  cliWrOk_storeDir (by decide +kernel) hn (by omega)

theorem cliWrOk_session {a : LibsignalPublicApiRepr.AddrVal} (hn : CompOk a.name)
    (hlen : a.name.length ≤ 40) : cliWrOk (pathOf (utf8 "sessions") (addressText a)) :=
  cliWrOk_storeDir (by decide +kernel) (compOk_addressText hn)
    (by have := addressText_length a; omega)

theorem cliWrOk_keyName {dir : List (BitVec 8)} (hd : dir ∈ storeDirs) (id : BitVec 32) :
    cliWrOk (pathOf dir (keyName id)) :=
  cliWrOk_storeDir hd (compOk_keyName id) (by have := keyName_length id; omega)

theorem cliWrOk_baseKeys (id : BitVec 32) :
    cliWrOk (pathOf (utf8 "last-resort-kyber-pre-keys") (baseKeysName id)) :=
  cliWrOk_storeDir (by decide +kernel) (compOk_baseKeysName id)
    (by have := baseKeysName_length id; omega)

/-- Party-local identity files (`IdentityFiles::create`). -/
def ownFiles : List (List (BitVec 8)) :=
  [utf8 "address", utf8 "identity-key-pair", utf8 "registration-id"]

theorem ownFiles_ok : ∀ n ∈ ownFiles, CompOk n ∧ n.length ≤ 17 := by decide +kernel

theorem cliWrOk_ownFile {name : List (BitVec 8)} (hn : name ∈ ownFiles) :
    cliWrOk (pathOf [] name) :=
  cliWrOk_own (ownFiles_ok name hn).1
    (by have := (ownFiles_ok name hn).2; have : NAME_MAX = 255 := rfl; omega)

/-- Public identity files (`PublicFiles::identity`). -/
def pubFiles : List (List (BitVec 8)) := [utf8 "identity-key", utf8 "registration-id"]

theorem pubFiles_ok : ∀ n ∈ pubFiles, CompOk n ∧ n.length ≤ 15 := by decide +kernel

theorem cliWrOk_pubFile {name : List (BitVec 8)} (hn : name ∈ pubFiles) :
    cliWrOk (pathOf (utf8 "public") name) :=
  cliWrOk_storeDir (by decide +kernel) (pubFiles_ok name hn).1
    (by have := (pubFiles_ok name hn).2; omega)

/-- Key subdirectories under `public/`. -/
def pubKeyDirs : List (List (BitVec 8)) :=
  [utf8 "signed-pre-keys", utf8 "one-time-pre-keys", utf8 "one-time-kyber-pre-keys",
    utf8 "last-resort-kyber-pre-keys"]

theorem pubKeyDirs_sub : ∀ d ∈ pubKeyDirs, d ∈ storeDirs := by decide +kernel

theorem cliWrOk_pubKey {sub : List (BitVec 8)} (hs : sub ∈ pubKeyDirs) (id : BitVec 32) :
    cliWrOk (pathOf (utf8 "public") (pathOf sub (keyName id))) := by
  have hpub : CompOk (utf8 "public") ∧ (utf8 "public").length = 6 := by decide +kernel
  have hsub := storeDirs_ok sub (pubKeyDirs_sub sub hs)
  have hk := compOk_keyName id
  have he : pathOf (utf8 "public") (pathOf sub (keyName id)) =
      [0x2f#8].intercalate [utf8 "public", sub, keyName id] := by
    rw [pathOf_eq_path hpub.1.ne_nil, pathOf_eq_path hsub.1.ne_nil, List.intercalate_cons_cons,
      List.intercalate_cons_cons, List.intercalate_singleton]
  have hlenp : (pathOf (utf8 "public") (pathOf sub (keyName id))).length < cliPathMaxBytes := by
    rw [length_pathOf hpub.1.ne_nil, length_pathOf hsub.1.ne_nil, hpub.2]
    have := keyName_length id
    have := hsub.2
    have : cliPathMaxBytes = 4096 := rfl
    omega
  refine ⟨?_, Nat.lt_trans hlenp (by decide)⟩
  rw [he] at hlenp ⊢
  refine pathOk_intercalate _ (List.cons_ne_nil _ _) ?_ ?_ hlenp
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc <;> rw [hc]
    · exact hpub.1
    · exact hsub.1
    · exact hk
  · intro c hc
    have hk_len := keyName_length id
    have hsub_len := hsub.2
    have hpub_len := hpub.2
    have hnm : NAME_MAX = 255 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc <;> rw [hc] <;> omega

/-! ## Store Ghost Invariant `StoresWrOk` -/

/-- Every modified entry in `d` maps to a path satisfying `ok`. -/
def DirWrOk (ok : List (BitVec 8) → Prop) (d : DirGhost) : Prop :=
  ∀ e ∈ d.changed, ok (pathOf d.path e.1)

theorem DirWrOk.new (ok : List (BitVec 8) → Prop) (path : List (BitVec 8)) :
    DirWrOk ok (DirGhost.new path) := by
  intro e he
  simp [DirGhost.new] at he

theorem mem_setOrPush {n bs : List (BitVec 8)} {e : List (BitVec 8) × List (BitVec 8)} :
    ∀ {l : List (List (BitVec 8) × List (BitVec 8))},
      e ∈ DirGhost.setOrPush n bs l → e ∈ l ∨ e.1 = n := by
  intro l
  induction l with
  | nil =>
    intro he
    simp only [DirGhost.setOrPush, List.mem_singleton] at he
    exact Or.inr (by subst he; rfl)
  | cons x xs ih =>
    intro he
    simp only [DirGhost.setOrPush] at he
    split at he
    · rcases List.mem_cons.mp he with he | he
      · exact Or.inr (by subst he; rfl)
      · exact Or.inl (List.mem_cons_of_mem _ he)
    · rcases List.mem_cons.mp he with he | he
      · exact Or.inl (by subst he; exact List.mem_cons_self)
      · rcases ih he with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem DirWrOk.put {ok : List (BitVec 8) → Prop} {d : DirGhost} (hd : DirWrOk ok d)
    {n : List (BitVec 8)} (hn : ok (pathOf d.path n)) (bs : List (BitVec 8)) :
    DirWrOk ok (d.put n bs) := by
  intro e he
  rcases mem_setOrPush he with he | he
  · exact hd e he
  · rw [he]; exact hn

theorem DirWrOk.writes {ok : List (BitVec 8) → Prop} {d : DirGhost} (hd : DirWrOk ok d) :
    ∀ pw ∈ d.writes, ok pw.1 := by
  intro pw hpw
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpw
  exact hd e he

/-- `DirWrOk ok` across all eight store directories in `g`. -/
structure StoresWrOk (ok : List (BitVec 8) → Prop) (g : StoresGhost) : Prop where
  own : DirWrOk ok g.identity.own
  peers : DirWrOk ok g.identity.peers
  signed : DirWrOk ok g.signed
  kyberOneTime : DirWrOk ok g.kyber.oneTime
  kyberLastResort : DirWrOk ok g.kyber.lastResort
  oneTime : DirWrOk ok g.oneTime
  sessions : DirWrOk ok g.sessions
  pub : DirWrOk ok g.pub

theorem StoresWrOk.opened (ok : List (BitVec 8) → Prop) : StoresWrOk ok StoresGhost.opened :=
  ⟨DirWrOk.new _ _, DirWrOk.new _ _, DirWrOk.new _ _, DirWrOk.new _ _, DirWrOk.new _ _,
    DirWrOk.new _ _, DirWrOk.new _ _, DirWrOk.new _ _⟩

theorem StoresWrOk.writes {ok : List (BitVec 8) → Prop} {g : StoresGhost} (h : StoresWrOk ok g) :
    ∀ pw ∈ g.writes, ok pw.1 := by
  intro pw hpw
  simp only [StoresGhost.writes, List.mem_append, or_assoc] at hpw
  rcases hpw with hpw | hpw | hpw | hpw | hpw | hpw | hpw | hpw
  · exact h.own.writes pw hpw
  · exact h.peers.writes pw hpw
  · exact h.signed.writes pw hpw
  · exact h.kyberOneTime.writes pw hpw
  · exact h.kyberLastResort.writes pw hpw
  · exact h.oneTime.writes pw hpw
  · exact h.sessions.writes pw hpw
  · exact h.pub.writes pw hpw

theorem StoresWrOk.hpaths {g : StoresGhost} (h : StoresWrOk cliWrOk g) :
    ∀ pw ∈ g.writes, cliIo.pathOk pw.1 ∧ pw.1.length < 2 ^ 32 :=
  h.writes

/-! ## Preservation Under Store Updates -/

theorem DirWrOk.saveUpd {ok : List (BitVec 8) → Prop} {rd : ReadRule} {F0 : FsFiles} {g : IdGhost}
    {a : LibsignalPublicApiRepr.AddrVal} {k} (hp : DirWrOk ok g.peers)
    (hn : ok (pathOf g.peers.path a.name)) : DirWrOk ok (g.saveUpd rd F0 a k).peers := by
  unfold IdGhost.saveUpd
  split
  · exact hp.put hn _
  · exact hp

theorem saveUpd_own (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (a : LibsignalPublicApiRepr.AddrVal) (k) : (g.saveUpd rd F0 a k).own = g.own := by
  unfold IdGhost.saveUpd
  split <;> rfl

theorem saveUpd_peers_path (rd : ReadRule) (F0 : FsFiles) (g : IdGhost)
    (a : LibsignalPublicApiRepr.AddrVal) (k) :
    (g.saveUpd rd F0 a k).peers.path = g.peers.path := by
  unfold IdGhost.saveUpd
  split <;> rfl

theorem DirWrOk.storeSession {ok : List (BitVec 8) → Prop} {R ε : Type}
    {enc : R → Except ε (List (BitVec 8))} {d : DirGhost} {a : LibsignalPublicApiRepr.AddrVal}
    {r : R} (hd : DirWrOk ok d) (hn : ok (pathOf d.path (addressText a))) :
    DirWrOk ok (Cli.storeSession enc d a r).2 := by
  unfold Cli.storeSession
  split
  · exact hd.put hn _
  · exact hd

theorem DirWrOk.removePreKey {ok : List (BitVec 8) → Prop} {rd : ReadRule} {F0 : FsFiles}
    {d : DirGhost} {id : BitVec 32} (hd : DirWrOk ok d) (hn : ok (pathOf d.path (keyName id))) :
    DirWrOk ok (Cli.removePreKey rd F0 d id).2 := by
  unfold Cli.removePreKey
  split <;> first | exact hd | exact hd.put hn _

theorem DirWrOk.mark_oneTime {ok : List (BitVec 8) → Prop} {rd : ReadRule} {F0 : FsFiles}
    {g : KyberGhost} {id signedId : BitVec 32} {baseKey} (hd : DirWrOk ok g.oneTime)
    (hn : ok (pathOf g.oneTime.path (keyName id))) :
    DirWrOk ok (g.mark rd F0 id signedId baseKey).2.oneTime := by
  unfold KyberGhost.mark
  repeat' first | split | dsimp only
  all_goals first | exact hd | exact hd.put hn _

theorem DirWrOk.mark_lastResort {ok : List (BitVec 8) → Prop} {rd : ReadRule} {F0 : FsFiles}
    {g : KyberGhost} {id signedId : BitVec 32} {baseKey} (hd : DirWrOk ok g.lastResort)
    (hn : ok (pathOf g.lastResort.path (baseKeysName id))) :
    DirWrOk ok (g.mark rd F0 id signedId baseKey).2.lastResort := by
  unfold KyberGhost.mark
  repeat' first | split | dsimp only
  all_goals first | exact hd | exact hd.put hn _

/-! ## Service-ID Names Under `uuidTryParse` -/

theorem hexNibble_nameCode : ∀ b : BitVec 8, (hexNibble b).isSome = true →
    nameCode b = true ∧ b ≠ 0x2e#8 := by
  decide +kernel

theorem decodeHex_hex : ∀ (l : List (BitVec 8)) (r : List (BitVec 8)), l.length % 2 = 0 →
    decodeHex l = some r → ∀ b ∈ l, (hexNibble b).isSome = true
  | [], _, _, _, b, hb => absurd hb List.not_mem_nil
  | [_], _, hl, _, _, _ => by simp at hl
  | hi :: lo :: rest, r, hl, h, b, hb => by
    unfold decodeHex at h
    cases hh : hexNibble hi with
    | none => simp [hh] at h
    | some x =>
      cases hl' : hexNibble lo with
      | none => simp [hh, hl'] at h
      | some y =>
        cases hr : decodeHex rest with
        | none => simp [hh, hl', hr] at h
        | some z =>
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | hb
          · simp [hh]
          · simp [hl']
          · exact decodeHex_hex rest z (by simp only [List.length_cons] at hl; omega) hr b hb

theorem decodeHex32_hex {l : List (BitVec 8)} {u : List.Vector (BitVec 8) 16} (hl : l.length = 32)
    (h : decodeHex32 l = some u) : ∀ b ∈ l, (hexNibble b).isSome = true := by
  unfold decodeHex32 at h
  cases hd : decodeHex l with
  | none => simp [hd] at h
  | some r => exact decodeHex_hex l r (by omega) hd

theorem mem_drop_take_of {s : List (BitVec 8)} {b : BitVec 8} {i d k : Nat} (hi : s[i]? = some b)
    (h1 : d ≤ i) (h2 : i < d + k) : b ∈ (s.drop d).take k := by
  have he : ((s.drop d).take k)[i - d]? = some b := by
    rw [List.getElem?_take, ite_eq_left_of_eq_true _ _ (eq_true (show i - d < k by omega)),
      List.getElem?_drop, Nat.add_sub_cancel' h1, hi]
  exact List.mem_of_getElem? he

/-- `parseHyphenated` succeeds only on 36-byte `CompOk` strings of hex digits and `-`. -/
theorem parseHyphenated_compOk {s : List (BitVec 8)} {u : List.Vector (BitVec 8) 16}
    (h : parseHyphenated s = some u) : CompOk s ∧ s.length = 36 := by
  unfold parseHyphenated at h
  split at h
  · rename_i hc
    obtain ⟨hlen, h8, h13, h18, h23⟩ := hc
    have hgl : (s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++
        s.drop 24).length = 32 := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    have hg := decodeHex32_hex hgl h
    have hhex : ∀ b ∈ s, nameCode b = true := by
      intro b hb
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
      have hlt : i < 36 := by
        rw [← hlen]
        exact (List.getElem?_eq_some_iff.mp hi).1
      have hhy : nameCode hyphen = true := by decide +kernel
      have hmem : i = 8 ∨ i = 13 ∨ i = 18 ∨ i = 23 ∨
          b ∈ s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++
            s.drop 24 := by
        by_cases hA : i < 8
        · right; right; right; right
          simp only [List.mem_append]
          left; left; left; left
          have := mem_drop_take_of (k := 8) (d := 0) hi (by omega) (by omega)
          simpa using this
        by_cases hB : 9 ≤ i ∧ i < 13
        · right; right; right; right
          simp only [List.mem_append]
          left; left; left; right
          exact mem_drop_take_of hi hB.1 (by omega)
        by_cases hC : 14 ≤ i ∧ i < 18
        · right; right; right; right
          simp only [List.mem_append]
          left; left; right
          exact mem_drop_take_of hi hC.1 (by omega)
        by_cases hD : 19 ≤ i ∧ i < 23
        · right; right; right; right
          simp only [List.mem_append]
          left; right
          exact mem_drop_take_of hi hD.1 (by omega)
        by_cases hE : 24 ≤ i
        · right; right; right; right
          simp only [List.mem_append]
          right
          have he : (s.drop 24)[i - 24]? = some b := by
            rw [List.getElem?_drop, Nat.add_sub_cancel' hE, hi]
          exact List.mem_of_getElem? he
        omega
      rcases hmem with rfl | rfl | rfl | rfl | hm
      · rw [h8] at hi; cases hi; exact hhy
      · rw [h13] at hi; cases hi; exact hhy
      · rw [h18] at hi; cases hi; exact hhy
      · rw [h23] at hi; cases hi; exact hhy
      · exact (hexNibble_nameCode b (hg b hm)).1
    have hs0 : s.take 8 ≠ [] := by
      intro h0
      have := congrArg List.length h0
      simp only [List.length_take, List.length_nil] at this
      omega
    obtain ⟨b0, hb0⟩ := List.exists_mem_of_ne_nil _ hs0
    have hg0 := hg b0 (by simp only [List.mem_append]; left; left; left; left; exact hb0)
    exact ⟨⟨hhex, b0, List.mem_of_mem_take hb0, (hexNibble_nameCode b0 hg0).2⟩, hlen⟩
  · simp at h

theorem uuidTryParse_of_length36 {s : List (BitVec 8)} (hs : s.length = 36) :
    uuidTryParse s = parseHyphenated s := by
  unfold uuidTryParse
  rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬s.length = 32 by omega)),
    ite_eq_left_of_eq_true _ _ (eq_true hs)]

theorem pniPrefix_ok : (∀ b ∈ pniPrefix, nameCode b = true) ∧ CompOk pniPrefix ∧
    pniPrefix.length = 4 := by
  decide +kernel

/-- Any name accepted by `serviceIdParse uuidTryParse` satisfies `CompOk` and has length 36 or 40. -/
theorem serviceIdParse_compOk {n : List (BitVec 8)} {r : Bool × List.Vector (BitVec 8) 16}
    (h : serviceIdParse uuidTryParse n = some r) : CompOk n ∧ n.length ≤ 40 := by
  unfold serviceIdParse tryParseHyphenated at h
  split at h
  · rename_i hpre
    obtain ⟨t, rfl⟩ := List.isPrefixOf_iff_prefix.mp hpre
    rw [List.drop_left] at h
    split at h
    · rename_i hl
      unfold hyphenatedLength at hl
      obtain ⟨u, hu, -⟩ := Option.map_eq_some_iff.mp h
      rw [uuidTryParse_of_length36 hl] at hu
      have ht := (parseHyphenated_compOk hu).1
      have hcomp : CompOk (pniPrefix ++ t) := by
        obtain ⟨hall, b, hb, hne⟩ := ht
        refine ⟨fun x hx => ?_, b, List.mem_append_right _ hb, hne⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact pniPrefix_ok.1 x hx
        · exact hall x hx
      refine ⟨hcomp, ?_⟩
      rw [List.length_append, pniPrefix_ok.2.2, hl]
    · simp at h
  · split at h
    · rename_i hl
      unfold hyphenatedLength at hl
      obtain ⟨u, hu, -⟩ := Option.map_eq_some_iff.mp h
      rw [uuidTryParse_of_length36 hl] at hu
      exact ⟨(parseHyphenated_compOk hu).1, by omega⟩
    · simp at h

theorem cliWrOk_peer_tryParse {name : List (BitVec 8)} {r : Bool × List.Vector (BitVec 8) 16}
    (h : serviceIdParse uuidTryParse name = some r) :
    cliWrOk (pathOf (utf8 "identities") name) :=
  cliWrOk_peer (serviceIdParse_compOk h).1 (serviceIdParse_compOk h).2

theorem cliWrOk_session_tryParse {a : LibsignalPublicApiRepr.AddrVal}
    {r : Bool × List.Vector (BitVec 8) 16} (h : serviceIdParse uuidTryParse a.name = some r) :
    cliWrOk (pathOf (utf8 "sessions") (addressText a)) :=
  cliWrOk_session (serviceIdParse_compOk h).1 (serviceIdParse_compOk h).2

theorem addrParse_name {uuidParse : UuidParser} {bs : List (BitVec 8)} {v : AddrV}
    (h : addrParse uuidParse bs = some v) : ∃ r, serviceIdParse uuidParse v.name = some r := by
  unfold addrParse at h
  split at h
  · simp at h
  · rename_i name dev _
    split at h
    · rename_i r d hs _
      split at h
      · cases h
        exact ⟨r, hs⟩
      · simp at h
    · simp at h

theorem cliWrOk_peer_addrParse {bs : List (BitVec 8)} {v : AddrV}
    (h : addrParse uuidTryParse bs = some v) : cliWrOk (pathOf (utf8 "identities") v.name) :=
  have ⟨_, hs⟩ := addrParse_name h
  cliWrOk_peer_tryParse hs

theorem cliWrOk_session_addrParse {bs : List (BitVec 8)} {v : AddrV}
    {a : LibsignalPublicApiRepr.AddrVal} (h : addrParse uuidTryParse bs = some v)
    (hname : a.name = v.name) : cliWrOk (pathOf (utf8 "sessions") (addressText a)) :=
  have ⟨_, hs⟩ := addrParse_name h
  cliWrOk_session_tryParse (hname ▸ hs)

end CryptoVerification.SignalSession.Cli.MainHops
