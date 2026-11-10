/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Repr
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Spec -- shake: keep
import LibsignalBinary.Specifications.CryptoGames.Party -- shake: keep
import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# Pointwise `filesOf` Evaluation and Store Commit Helpers

Connects `namedWrites` for committed identity and session files with two-segment path normalization
and pointwise `filesOf` evaluation (`filesOf_eq_evalAt`).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Agree

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunRefine

/-! ## UTF-8 encoding and `namedWrites` -/

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : Cli.utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [Cli.utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

theorem utf8_append (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  rw [utf8_eq_kutf8, utf8_eq_kutf8, utf8_eq_kutf8]
  simp [kutf8, String.toList_append, List.flatMap_append]

theorem addressText_addrValE (P : Party) :
    Cli.addressText (addrValE P) = utf8 (partyAddress P).text := by
  have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
  simp only [Cli.addressText, addrValE, decimalText, h1, Address.text, partyAddress]
  rw [← utf8_append, ← utf8_append]

theorem pathOf_identityFile (P : Party) :
    Cli.pathOf (utf8 "identities") (utf8 (partyAddressName P)) = utf8 (identityFile (partyAddressName P)) := by
  have hne : utf8 "identities" ≠ [] := by rw [utf8_eq_kutf8]; decide
  simp only [Cli.pathOf, hne, ↓reduceIte, identityFile]
  rw [← utf8_append, ← utf8_append]
  rfl

theorem pathOf_sessionFile (P : Party) :
    Cli.pathOf (utf8 "sessions") (Cli.addressText (addrValE P)) = utf8 (sessionFile (partyAddress P)) := by
  have hne : utf8 "sessions" ≠ [] := by rw [utf8_eq_kutf8]; decide
  rw [addressText_addrValE]
  simp only [Cli.pathOf, hne, ↓reduceIte, sessionFile]
  rw [← utf8_append, ← utf8_append]
  rfl

private theorem utf8_identityFile_ascii (P : Party) :
    ∀ b ∈ utf8 (identityFile (partyAddressName P)), b.toNat < 128 := by
  rw [utf8_eq_kutf8]
  intro b hb
  have hall : (kutf8 (identityFile (partyAddressName P))).all (fun x => decide (x.toNat < 128)) = true := by
    cases P <;> rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall b hb)

private theorem utf8_sessionFile_ascii (P : Party) :
    ∀ b ∈ utf8 (sessionFile (partyAddress P)), b.toNat < 128 := by
  rw [utf8_eq_kutf8]
  intro b hb
  have hall : (kutf8 (sessionFile (partyAddress P))).all (fun x => decide (x.toNat < 128)) = true := by
    cases P <;> rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall b hb)

private theorem pathStr_utf8_identityFile (P : Party) :
    pathStr (utf8 (identityFile (partyAddressName P))) = identityFile (partyAddressName P) := by
  unfold pathStr
  rw [utf8_eq_kutf8]
  cases P <;> rfl

private theorem pathStr_utf8_sessionFile (P : Party) :
    pathStr (utf8 (sessionFile (partyAddress P))) = sessionFile (partyAddress P) := by
  unfold pathStr
  rw [utf8_eq_kutf8]
  cases P <;> rfl

theorem namedWrites_id_session (P : Party) (idBytes recBytes : List (BitVec 8)) :
    let g : StoresGhost :=
      { StoresGhost.opened with
        identity := { StoresGhost.opened.identity with
                      peers := StoresGhost.opened.identity.peers.put (utf8 (partyAddressName P)) idBytes }
        sessions := StoresGhost.opened.sessions.put (Cli.addressText (addrValE P)) recBytes }
    namedWrites g.writes =
      [(identityFile (partyAddressName P), idBytes), (sessionFile (partyAddress P), recBytes)] := by
  intro g
  have hw : g.writes =
      [(utf8 (identityFile (partyAddressName P)), idBytes), (utf8 (sessionFile (partyAddress P)), recBytes)] := by
    simp [g, StoresGhost.writes, StoresGhost.opened, DirGhost.writes, DirGhost.new, DirGhost.put,
      DirGhost.setOrPush, pathOf_identityFile, pathOf_sessionFile]
  rw [hw, namedWrites_ascii]
  · simp only [List.map, pathStr_utf8_identityFile, pathStr_utf8_sessionFile]
  · intro pw hpw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpw
    rcases hpw with rfl | rfl
    · exact utf8_identityFile_ascii P
    · exact utf8_sessionFile_ascii P

/-! ## Two-segment path normalization -/

private theorem splitSlash_go_no_slash : ∀ (cs cur : List Char), '/' ∉ cs →
    splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by simp [splitSlash.go]
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.Mem.head _)
    have ih := splitSlash_go_no_slash cs (c :: cur) (fun hm => h (List.Mem.tail _ hm))
    have hstep : splitSlash.go cur (c :: cs) = splitSlash.go (c :: cur) cs := by
      rw [splitSlash.go.eq_def]
      split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq
        injection heq with h1 h2
        subst h1 h2
        rfl
    rw [hstep, ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem splitSlash_go_two : ∀ (cs1 cs2 cur : List Char),
    '/' ∉ cs1 → '/' ∉ cs2 →
    splitSlash.go cur (cs1 ++ ('/' :: cs2)) =
      [String.ofList (cur.reverse ++ cs1), String.ofList cs2]
  | [], cs2, cur, _, h2 => by
    have ih := splitSlash_go_no_slash cs2 [] h2
    simp [splitSlash.go, ih]
  | c :: cs1, cs2, cur, h1, h2 => by
    have hc : c ≠ '/' := fun he => h1 (he ▸ List.Mem.head _)
    have ih := splitSlash_go_two cs1 cs2 (c :: cur) (fun hm => h1 (List.Mem.tail _ hm)) h2
    have hstep : splitSlash.go cur (c :: (cs1 ++ '/' :: cs2)) =
        splitSlash.go (c :: cur) (cs1 ++ '/' :: cs2) := by
      rw [splitSlash.go.eq_def]
      split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq
        injection heq with h1' h2'
        subst h1' h2'
        rfl
    simpa [List.cons_append, List.reverse_cons, List.append_assoc] using hstep.trans ih

private theorem toDigitsCore_nonempty : ∀ (fuel n : Nat) (ds : List Char),
    ds ≠ [] → Nat.toDigitsCore 10 fuel n ds ≠ []
  | 0, _, ds, h => h
  | fuel + 1, n, ds, _ => by
    unfold Nat.toDigitsCore
    dsimp only
    split
    · simp
    · exact toDigitsCore_nonempty fuel (n / 10) _ (by simp)

private theorem toString_nat_toList_nonempty (n : Nat) : (toString n).toList ≠ [] := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  unfold Nat.toDigits Nat.toDigitsCore
  dsimp only
  split
  · simp
  · exact toDigitsCore_nonempty n (n / 10) _ (by simp)

private theorem toString_nat_mem_digit {n : Nat} {c : Char} (hc : c ∈ (toString n).toList) :
    Char.isDigit c = true := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

private theorem char_of_isDigit (c : Char) (h : Char.isDigit c = true) :
    c ≠ '/' ∧ c ≠ '.' := by
  refine ⟨?_, ?_⟩ <;> intro rfl <;> cases h

private theorem norm_twoSeg (d suf : String)
    (hd_noslash : '/' ∉ d.toList)
    (hd_norm : (!d.isEmpty && d != ".") = true)
    (hs_noslash : '/' ∉ suf.toList)
    (hs_head : ∃ c cs, suf.toList = c :: cs ∧ Char.isDigit c = true) :
    normalizePath ((d ++ "/") ++ suf) = [d, suf] := by
  obtain ⟨c, cs, hsuf, hdig⟩ := hs_head
  obtain ⟨_, hnotdot⟩ := char_of_isDigit c hdig
  have hplist : ((d ++ "/") ++ suf).toList = d.toList ++ ('/' :: suf.toList) := by
    rw [String.toList_append, String.toList_append]
    have hslash : "/".toList = ['/'] := by decide
    rw [hslash, List.append_assoc]
    rfl
  have hsplit : splitSlash ((d ++ "/") ++ suf) = [d, suf] := by
    unfold splitSlash
    rw [hplist, splitSlash_go_two d.toList suf.toList [] hd_noslash hs_noslash]
    simp [String.ofList_toList]
  have hsuf_not_empty : suf.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    have : suf.toList = [] := by
      have h1 : suf = "" := by simpa [String.isEmpty_iff] using he
      subst h1; decide
    rw [hsuf] at this
    cases this
  have hsuf_not_dot : (suf != ".") = true := by
    rw [bne_iff_ne]
    intro he
    subst he
    have hdot : ".".toList = ['.'] := by decide
    rw [hdot] at hsuf
    injection hsuf with h1 _
    exact hnotdot h1.symm
  unfold normalizePath
  rw [hsplit]
  simp [hd_norm, hsuf_not_empty, hsuf_not_dot]

theorem norm_prekey_nat (d : String) (n : Nat)
    (hd_noslash : '/' ∉ d.toList)
    (hd_norm : (!d.isEmpty && d != ".") = true) :
    normalizePath ((d ++ "/") ++ toString n) = [d, toString n] := by
  apply norm_twoSeg d (toString n) hd_noslash hd_norm
  · intro hm; exact (char_of_isDigit _ (toString_nat_mem_digit hm)).1 rfl
  · cases hl : (toString n).toList with
    | nil => exact absurd hl (toString_nat_toList_nonempty n)
    | cons c cs => exact ⟨c, cs, rfl, toString_nat_mem_digit (hl ▸ List.Mem.head _)⟩

theorem norm_basekeys_nat (d : String) (n : Nat)
    (hd_noslash : '/' ∉ d.toList)
    (hd_norm : (!d.isEmpty && d != ".") = true) :
    normalizePath (((d ++ "/") ++ toString n) ++ ".base-keys") =
      [d, toString n ++ ".base-keys"] := by
  have heq : ((d ++ "/") ++ toString n) ++ ".base-keys" =
      (d ++ "/") ++ (toString n ++ ".base-keys") := by
    simp [String.append_assoc]
  rw [heq]
  apply norm_twoSeg d (toString n ++ ".base-keys") hd_noslash hd_norm
  · rw [String.toList_append]
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact (char_of_isDigit _ (toString_nat_mem_digit h1)).1 rfl
    · revert h2; decide
  · rw [String.toList_append]
    cases hl : (toString n).toList with
    | nil => exact absurd hl (toString_nat_toList_nonempty n)
    | cons c cs =>
      exact ⟨c, cs ++ ".base-keys".toList, rfl, toString_nat_mem_digit (hl ▸ List.Mem.head _)⟩

/-! ## Pointwise `filesOf` evaluation on game paths -/

def storeParentDirs : List String :=
  ["identities", "sessions", "signed-pre-keys", "one-time-pre-keys",
   "one-time-kyber-pre-keys", "last-resort-kyber-pre-keys"]

def GameFilePath (p : String) : Prop :=
  (normalizePath p).isEmpty = false ∧
  (∀ d ∈ storeParentDirs, normalizePath p ≠ [d]) ∧
  ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast,
    ∃ d ∈ storeParentDirs, pref = [d]

private def NoDirFiles (a : FsState) : Prop :=
  ∀ d ∈ storeParentDirs, fileOfEntry (a.entries [d]) = none

private theorem foldl_anc_keep {a : FsState} {prefs : List FsPath}
    (ha : NoDirFiles a)
    (hp : ∀ pref ∈ prefs, ∃ d ∈ storeParentDirs, pref = [d]) :
    NoDirFiles (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) a) ∧
    SameFiles (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) a) a := by
  induction prefs generalizing a with
  | nil => exact ⟨ha, fun _ => rfl⟩
  | cons pref rest ih =>
    obtain ⟨d, hd, rfl⟩ := hp pref (List.mem_cons_self ..)
    have ha' : NoDirFiles (a.setEntry [d] (some .dir)) := by
      intro d' hd'
      simp only [FsState.setEntry]
      split
      · rfl
      · exact ha d' hd'
    have hs' : SameFiles (a.setEntry [d] (some .dir)) a := by
      intro q
      simp only [FsState.setEntry]
      split
      · rename_i heq
        rw [beq_iff_eq] at heq
        subst heq
        exact (ha d hd).symm
      · rfl
    obtain ⟨h1, h2⟩ := ih ha' (fun p hp' => hp p (List.mem_cons_of_mem _ hp'))
    exact ⟨h1, fun q => (h2 q).trans (hs' q)⟩

def stepAt (q : FsPath) (v : Option (List (BitVec 8))) (x : String × List (BitVec 8)) :
    Option (List (BitVec 8)) :=
  if q = normalizePath x.1 then some x.2 else v

def evalAt (q : FsPath) (v : Option (List (BitVec 8)))
    (l : List (String × List (BitVec 8))) : Option (List (BitVec 8)) :=
  l.foldl (stepAt q) v

private theorem filesFold_evalAt :
    ∀ (l : List (String × List (BitVec 8))) (a : FsState),
      (∀ x ∈ l, GameFilePath x.1) → NoDirFiles a →
      ∀ q, fileOfEntry ((filesFold l a).entries q) = evalAt q (fileOfEntry (a.entries q)) l
  | [], a, _, _, _ => rfl
  | (p, bs) :: rest, a, hl, ha, q => by
    obtain ⟨_, hnotd, hanc⟩ := hl (p, bs) (List.mem_cons_self ..)
    dsimp only at hnotd hanc
    let a1 := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) a
    obtain ⟨ha1, hs1⟩ := foldl_anc_keep ha hanc
    let a2 := a1.setFile p (some (.file bs))
    have ha2_eq : a2 = a1.setEntry (normalizePath p) (some (.file bs)) := by
      simp [a2, FsState.setFile]
    have ha2 : NoDirFiles a2 := by
      intro d hd
      rw [ha2_eq]
      simp only [FsState.setEntry]
      split
      · rename_i heq
        rw [beq_iff_eq] at heq
        exact absurd heq.symm (hnotd d hd)
      · exact ha1 d hd
    have hstep_q : fileOfEntry (a2.entries q) = stepAt q (fileOfEntry (a.entries q)) (p, bs) := by
      rw [ha2_eq]
      simp only [FsState.setEntry, stepAt]
      split
      · rename_i hbq
        have hq : q = normalizePath p := beq_iff_eq.mp hbq
        simp [hq, fileOfEntry]
      · rename_i hbq
        have hq : q ≠ normalizePath p := fun h => hbq (beq_iff_eq.mpr h)
        simp only [hq, ↓reduceIte]
        exact hs1 q
    have ih := filesFold_evalAt rest a2 (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ha2 q
    simpa [filesFold, evalAt, hstep_q] using ih

theorem filesOf_eq_evalAt {l : List (String × List (BitVec 8))}
    (hl : ∀ x ∈ l, GameFilePath x.1) (p : String) :
    filesOf l p =
      if normalizePath p ∈ stdioPaths.map normalizePath then none
      else if (normalizePath p).isEmpty then none
      else evalAt (normalizePath p) none l := by
  unfold filesOf fsView
  split
  · rfl
  · rename_i hstdio
    show fileOfEntry ((Process.initFsState { files := l }).files p) = _
    simp only [FsState.files, FsState.getEntry]
    split
    · rfl
    · rw [initFsState_entries { files := l } (normalizePath p) hstdio]
      have hdir : dirsFold [] ({} : FsState) = {} := rfl
      rw [hdir]
      have hnd : NoDirFiles ({} : FsState) := fun d _ => NoFiles.base [d]
      rw [filesFold_evalAt l {} hl hnd (normalizePath p), NoFiles.base (normalizePath p)]

theorem evalAt_append (q : FsPath) (v : Option (List (BitVec 8)))
    (l1 l2 : List (String × List (BitVec 8))) :
    evalAt q v (l1 ++ l2) = evalAt q (evalAt q v l1) l2 :=
  List.foldl_append

theorem evalAt_idle {q : FsPath} {l : List (String × List (BitVec 8))}
    (h : ∀ x ∈ l, normalizePath x.1 ≠ q) (v : Option (List (BitVec 8))) :
    evalAt q v l = v := by
  induction l generalizing v with
  | nil => rfl
  | cons x xs ih =>
    have hx : (q = normalizePath x.1) = False :=
      eq_false (fun he => h x (List.mem_cons_self ..) he.symm)
    simp only [evalAt, List.foldl_cons, stepAt, hx, ↓reduceIte]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) v

theorem evalAt_const_of_exists {q : FsPath} {l : List (String × List (BitVec 8))}
    (h : ∃ x ∈ l, normalizePath x.1 = q) (v1 v2 : Option (List (BitVec 8))) :
    evalAt q v1 l = evalAt q v2 l := by
  induction l generalizing v1 v2 with
  | nil => obtain ⟨_, hm, _⟩ := h; cases hm
  | cons x xs ih =>
    by_cases hx : q = normalizePath x.1
    · simp only [evalAt, List.foldl_cons, stepAt, hx, ↓reduceIte]
    · obtain ⟨y, hy, hyq⟩ := h
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd hyq.symm hx
      · simp only [evalAt, List.foldl_cons, stepAt, hx, ↓reduceIte]
        exact ih ⟨y, hy', hyq⟩ v1 v2

end CryptoVerification.SignalSession.Cli.RunProofs.Agree
