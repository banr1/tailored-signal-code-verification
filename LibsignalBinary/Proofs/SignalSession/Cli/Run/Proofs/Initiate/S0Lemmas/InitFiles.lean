/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.InitPaths
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.List.SplitOn.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-!
# Directory File-Lookup Lemmas for `initOk₀_pqInit`

Proves file-system lookup facts on `runFiles (pqInitInputs W st b t)` for `initOk₀_pqInit`
(`keyPairLt_pqInit`, `idPairDerived_pqInit`, `idGet_pqInit`, and `noSession_pqInit` when
`st.session = none`) by pruning `filesFold` entries across disjoint canonical head segments.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.InitS0

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunRefine

/-! ## Generic `normalizePath`, `filesFold`, and `blockingAncestorF` helpers -/

private theorem splitSlash_go_prefix : ∀ (cs1 cs2 cur : List Char), '/' ∉ cs1 →
    ∃ tl, splitSlash.go cur (cs1 ++ ('/' :: cs2)) = String.ofList (cur.reverse ++ cs1) :: tl
  | [], cs2, cur, _ => ⟨splitSlash.go [] cs2, by simp [splitSlash.go]⟩
  | c :: cs1, cs2, cur, h1 => by
    have hc : c ≠ '/' := fun he => h1 (he ▸ List.Mem.head _)
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
    obtain ⟨tl, ih⟩ := splitSlash_go_prefix cs1 cs2 (c :: cur) (fun hm => h1 (List.Mem.tail _ hm))
    exact ⟨tl, by simpa [List.cons_append, List.reverse_cons, List.append_assoc] using hstep.trans ih⟩

private theorem norm_head_slash_prefix (seg rest : String)
    (hns : '/' ∉ seg.toList) (hok : (!seg.isEmpty && seg != ".") = true) :
    (normalizePath ((seg ++ "/") ++ rest)).head? = some seg := by
  have hslash : "/".toList = ['/'] := rfl
  have hcs : ((seg ++ "/") ++ rest).toList = seg.toList ++ ('/' :: rest.toList) := by
    rw [String.toList_append, String.toList_append, hslash, List.append_assoc]
    rfl
  unfold normalizePath splitSlash
  rw [hcs]
  obtain ⟨tl, hgo⟩ := splitSlash_go_prefix seg.toList rest.toList [] hns
  simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hgo
  rw [hgo, List.filter_cons_of_pos (p := fun s => !s.isEmpty && s != ".") hok, List.head?_cons]

private theorem mem_of_mem_dropLast :
    ∀ {α : Type} {x : α} {l : List α}, x ∈ l.dropLast → x ∈ l
  | _, _, [], h => nomatch h
  | _, _, [_], h => nomatch h
  | _, _, _ :: _ :: _, h => by
    simp only [List.dropLast, List.mem_cons] at h
    rcases h with rfl | h
    · exact .head _
    · exact .tail _ (mem_of_mem_dropLast h)

private theorem head_of_mem_nonEmptyPrefixes :
    ∀ {segs q : FsPath}, q ∈ FsPath.nonEmptyPrefixes segs → q.head? = segs.head?
  | [], _, h => nomatch h
  | _ :: _, _, h => by
    simp only [FsPath.nonEmptyPrefixes, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

private theorem foldl_setEntry_entries_of_forall_ne (l : List FsPath) (fs : FsState) (k : FsPath)
    (h : ∀ p ∈ l, k ≠ p) :
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k = fs.entries k := by
  induction l generalizing fs with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldl_cons, ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have hne : (k == p) = false := beq_false_of_ne (h p (List.mem_cons_self ..))
    simp only [FsState.setEntry, hne, Bool.false_eq_true, ↓reduceIte]

private theorem filesFold_append (l1 l2 : List (String × List (BitVec 8))) (fs : FsState) :
    filesFold (l1 ++ l2) fs = filesFold l2 (filesFold l1 fs) :=
  List.foldl_append

private theorem filesFold_nil (fs : FsState) : filesFold [] fs = fs := rfl

private theorem filesFold_singleton (p : String) (bs : List (BitVec 8)) (fs : FsState) :
    filesFold [(p, bs)] fs =
      ((normalizePath p).nonEmptyPrefixes.dropLast.foldl
        (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs)) := rfl

private theorem nonEmptyPrefixes_dropLast_pair (a b : String) :
    (FsPath.nonEmptyPrefixes [a, b]).dropLast = [[a]] := rfl

private theorem filesFold_entries_of_head_ne (l : List (String × List (BitVec 8)))
    (fs : FsState) (k : FsPath) (h : ∀ x ∈ l, (normalizePath x.1).head? ≠ k.head?) :
    (filesFold l fs).entries k = fs.entries k := by
  induction l generalizing fs with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨p, bs⟩ := x
    have hp : (normalizePath p).head? ≠ k.head? := h (p, bs) (List.mem_cons_self ..)
    unfold filesFold
    rw [List.foldl_cons]
    change (filesFold l _).entries k = fs.entries k
    rw [ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hne_p : (k == normalizePath p) = false :=
      beq_false_of_ne (fun he => hp (he ▸ rfl))
    simp only [FsState.setFile, FsState.setEntry, hne_p, Bool.false_eq_true, ↓reduceIte]
    refine foldl_setEntry_entries_of_forall_ne _ fs k fun pref hpref he => ?_
    subst he
    exact hp (head_of_mem_nonEmptyPrefixes (mem_of_mem_dropLast hpref)).symm

private theorem runFiles_eq_entries (i : Inputs) {q : String}
    (hne : (normalizePath q).isEmpty = false)
    (hns : normalizePath q ∉ stdioPaths.map normalizePath) :
    runFiles i q = (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath q) := by
  unfold runFiles
  rw [files_eq_entries, ite_eq_right_iff.mpr (by simp [hne]),
    initFsState_entries (cliInputs i) (normalizePath q) hns]
  rfl

private theorem blockingAncestorF_of_split2 {F : FsFiles} {p dir : String} {c1 c2 : List Char}
    (hsplit : p.toList.splitOn '/' = [c1, c2]) (hc1 : c1 = dir.toList)
    (hdir : F dir = some .dir) :
    blockingAncestorF F p = none := by
  have hof : String.ofList (c1 ++ []) = dir :=
    String.toList_inj.mp (by rw [String.toList_ofList, List.append_nil]; exact hc1)
  have ha : ancestors p = [dir] := by
    unfold ancestors pathComps
    rw [hsplit]
    exact congrArg List.singleton hof
  unfold blockingAncestorF
  rw [ha, List.find?_cons, hdir]
  rfl

/-! ## Canonical head segments of `pqInitInputs` file entries -/

private theorem head_signedPreKeyFile (i : BitVec 32) :
    (normalizePath (signedPreKeyFile i)).head? = some "signed-pre-keys" :=
  norm_head_slash_prefix "signed-pre-keys" _ (by decide) (by decide)

private theorem head_oneTimePreKeyFile (i : BitVec 32) :
    (normalizePath (oneTimePreKeyFile i)).head? = some "one-time-pre-keys" :=
  norm_head_slash_prefix "one-time-pre-keys" _ (by decide) (by decide)

private theorem head_oneTimeKyberPreKeyFile (i : BitVec 32) :
    (normalizePath (oneTimeKyberPreKeyFile i)).head? = some "one-time-kyber-pre-keys" :=
  norm_head_slash_prefix "one-time-kyber-pre-keys" _ (by decide) (by decide)

private theorem head_lastResortKyberPreKeyFile (i : BitVec 32) :
    (normalizePath (lastResortKyberPreKeyFile i)).head? = some "last-resort-kyber-pre-keys" :=
  norm_head_slash_prefix "last-resort-kyber-pre-keys" _ (by decide) (by decide)

private theorem head_baseKeysFile (i : BitVec 32) :
    (normalizePath (baseKeysFile i)).head? = some "last-resort-kyber-pre-keys" := by
  unfold baseKeysFile
  rw [String.append_assoc]
  exact norm_head_slash_prefix "last-resort-kyber-pre-keys" _ (by decide) (by decide)

private theorem head_identityFile (s : String) :
    (normalizePath (identityFile s)).head? = some "identities" :=
  norm_head_slash_prefix "identities" s (by decide) (by decide)

private theorem head_sessionFile (a : Address) :
    (normalizePath (sessionFile a)).head? = some "sessions" :=
  norm_head_slash_prefix "sessions" a.text (by decide) (by decide)

private def pqTail (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : List (String × List (BitVec 8)) :=
  st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)) ++
    st.oneTime.map (fun (i, k) =>
      (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ++
    st.kyberOneTime.map (fun (i, k) =>
      (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ++
    (st.kyberLastResort.map fun (i, k, seen) =>
      [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
       (baseKeysFile i, baseKeysBytes seen)]).flatten ++
    (publicBundleOf b).files bundleDir ++
    [(coinsFile, t.toList)]

private theorem pqInitInputs_files_eq (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    (pqInitInputs W st b t).files =
      [(addressFile, textBytes (partyAddress st.party).text),
       (identityKeyPairFile, ikBytes W st),
       (registrationIdFile, SignalSession.le32 st.me.regId)] ++
      (match st.peerId with
       | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
       | none => []) ++
      (match st.session with
       | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
       | none => []) ++
      pqTail W st b t := by
  simp only [pqInitInputs, pqInputs, encodeDir, ikBytes, pqTail, List.append_assoc]
  rfl

private def pqTailHeads : List (Option String) :=
  [some "signed-pre-keys", some "one-time-pre-keys", some "one-time-kyber-pre-keys",
   some "last-resort-kyber-pre-keys", some "bundle", some "coins"]

private theorem pqTail_norm_head (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ∀ x ∈ pqTail W st b t, (normalizePath x.1).head? ∈ pqTailHeads := by
  intro x hx
  simp only [pqTail, List.mem_append, List.mem_singleton] at hx
  rcases hx with (((((h1 | h2) | h3) | h4) | h5) | rfl)
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h1
    dsimp only; rw [head_signedPreKeyFile]; decide
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h2
    dsimp only; rw [head_oneTimePreKeyFile]; decide
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h3
    dsimp only; rw [head_oneTimeKyberPreKeyFile]; decide
  · simp only [List.mem_flatten, List.mem_map] at h4
    obtain ⟨_, ⟨⟨_, _, _⟩, _, rfl⟩, hmem⟩ := h4
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · dsimp only; rw [head_lastResortKyberPreKeyFile]; decide
    · dsimp only; rw [head_baseKeysFile]; decide
  · simp only [PublicBundle.files, List.cons_append, List.nil_append, List.mem_cons] at h5
    rcases h5 with rfl | rfl | rfl | rfl | ho
    · dsimp only [bundleDir]; decide
    · dsimp only [bundleDir]; decide
    · dsimp only [bundleDir]; decide
    · dsimp only [bundleDir]; decide
    · cases hopt : (publicBundleOf b).oneTime with
      | none => rw [hopt] at ho; cases ho
      | some _ =>
        rw [hopt] at ho
        rcases List.mem_singleton.mp ho with rfl
        dsimp only [bundleDir]; decide
  · dsimp only [coinsFile]; decide

private theorem pqTail_head_ne {W : PEParams} {st : PqParty} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {hd : Option String}
    (hhd : hd ∉ pqTailHeads) :
    ∀ x ∈ pqTail W st b t, (normalizePath x.1).head? ≠ hd := by
  intro x hx heq
  exact hhd (heq ▸ pqTail_norm_head W st b t x hx)

/-! ## Parent directory entries in `runFiles (pqInitInputs W st b t)` -/

private theorem runFiles_identities_dir (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    runFiles (pqInitInputs W st b t) "identities" = some .dir := by
  rw [runFiles_eq_entries _ (by decide) (by decide)]
  have hn : normalizePath "identities" = ["identities"] := by decide
  have hd : (pqInitInputs W st b t).dirs = partyDirs ++ [bundleDir] := rfl
  rw [hn, hd, pqInitInputs_files_eq, filesFold_append, filesFold_append]
  rw [filesFold_entries_of_head_ne _ _ ["identities"] (pqTail_head_ne (by decide))]
  rw [filesFold_entries_of_head_ne _ _ ["identities"] (fun x hx => by
    cases hses : st.session with
    | none => rw [hses] at hx; cases hx
    | some _ =>
      rw [hses] at hx
      rcases List.mem_singleton.mp hx with rfl
      dsimp only
      rw [head_sessionFile]
      decide)]
  rw [filesFold_append]
  have hpre : (filesFold
      [(addressFile, textBytes (partyAddress st.party).text),
       (identityKeyPairFile, ikBytes W st),
       (registrationIdFile, SignalSession.le32 st.me.regId)]
      (dirsFold (partyDirs ++ [bundleDir]) {})).entries ["identities"] = some .dir := by
    rw [filesFold_entries_of_head_ne _ _ ["identities"] (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;>
        (dsimp only [addressFile, identityKeyPairFile, registrationIdFile]; decide))]
    decide
  cases hpid : st.peerId with
  | none =>
    rw [filesFold_nil]
    exact hpre
  | some k =>
    rw [filesFold_singleton]
    have hnorm : normalizePath (identityFile (partyAddressName st.party.other)) =
        ["identities", partyAddressName st.party.other] := by
      cases st.party.other <;> decide
    have hne_f : ((["identities"] : FsPath) == ["identities", partyAddressName st.party.other]) = false :=
      by simp
    simp only [FsState.setFile, hnorm, nonEmptyPrefixes_dropLast_pair, List.foldl_cons,
      List.foldl_nil, FsState.setEntry, hne_f, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]

private theorem runFiles_sessions_dir (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    runFiles (pqInitInputs W st b t) "sessions" = some .dir := by
  rw [runFiles_eq_entries _ (by decide) (by decide)]
  have hn : normalizePath "sessions" = ["sessions"] := by decide
  have hd : (pqInitInputs W st b t).dirs = partyDirs ++ [bundleDir] := rfl
  rw [hn, hd, pqInitInputs_files_eq, filesFold_append]
  rw [filesFold_entries_of_head_ne _ _ ["sessions"] (pqTail_head_ne (by decide))]
  rw [filesFold_append]
  have hpre : (filesFold
      ([(addressFile, textBytes (partyAddress st.party).text),
        (identityKeyPairFile, ikBytes W st),
        (registrationIdFile, SignalSession.le32 st.me.regId)] ++
       match st.peerId with
       | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
       | none => [])
      (dirsFold (partyDirs ++ [bundleDir]) {})).entries ["sessions"] = some .dir := by
    rw [filesFold_entries_of_head_ne _ _ ["sessions"] (fun x hx => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl) | hp
      · dsimp only [addressFile]; decide
      · dsimp only [identityKeyPairFile]; decide
      · dsimp only [registrationIdFile]; decide
      · cases hpid : st.peerId with
        | none => rw [hpid] at hp; cases hp
        | some _ =>
          rw [hpid] at hp
          rcases List.mem_singleton.mp hp with rfl
          dsimp only; rw [head_identityFile]; decide)]
    decide
  cases hses : st.session with
  | none =>
    rw [filesFold_nil]
    exact hpre
  | some pair =>
    rcases pair with ⟨x, g⟩
    rw [filesFold_singleton]
    have hnorm : normalizePath (sessionFile (partyAddress st.party.other)) =
        ["sessions", (partyAddress st.party.other).text] := by
      cases st.party.other <;> decide
    have hne_f : ((["sessions"] : FsPath) == ["sessions", (partyAddress st.party.other).text]) = false :=
      by simp
    simp only [FsState.setFile, hnorm, nonEmptyPrefixes_dropLast_pair, List.foldl_cons,
      List.foldl_nil, FsState.setEntry, hne_f, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]

/-! ## Store reads on `runFiles (pqInitInputs W st b t)` -/

theorem own_get_idKeyPair (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqInitInputs W st b t))
      (utf8 "identity-key-pair") = .ok (ikBytes W st) := by
  change cliRd (runFiles (pqInitInputs W st b t)) (utf8 "identity-key-pair") = .ok (ikBytes W st)
  have hp : pathStr (utf8 "identity-key-pair") = "identity-key-pair" :=
    String.toList_inj.mp (by unfold pathStr; rw [String.toList_ofList, utf8_eq_flatMap]; decide)
  have hb : blockingAncestorF (runFiles (pqInitInputs W st b t)) "identity-key-pair" = none := by
    unfold blockingAncestorF ancestors pathComps
    rfl
  have hf : runFiles (pqInitInputs W st b t) "identity-key-pair" = some (.file (ikBytes W st)) := by
    rw [runFiles_eq_entries _ (by decide) (by decide)]
    have hn : normalizePath "identity-key-pair" = ["identity-key-pair"] := by decide
    have hfiles : (pqInitInputs W st b t).files =
        [(addressFile, textBytes (partyAddress st.party).text),
         (identityKeyPairFile, ikBytes W st)] ++
        ([(registrationIdFile, SignalSession.le32 st.me.regId)] ++
         (match st.peerId with
          | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
          | none => []) ++
         (match st.session with
          | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
          | none => []) ++
         pqTail W st b t) := by
      rw [pqInitInputs_files_eq]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    rw [hn, hfiles, filesFold_append]
    rw [filesFold_entries_of_head_ne _ _ ["identity-key-pair"] (fun x hx => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with ((rfl | hp') | hs') | ht
      · dsimp only [registrationIdFile]; decide
      · cases hpid : st.peerId with
        | none => rw [hpid] at hp'; cases hp'
        | some _ =>
          rw [hpid] at hp'
          rcases List.mem_singleton.mp hp' with rfl
          dsimp only; rw [head_identityFile]; decide
      · cases hses : st.session with
        | none => rw [hses] at hs'; cases hs'
        | some _ =>
          rw [hses] at hs'
          rcases List.mem_singleton.mp hs' with rfl
          dsimp only; rw [head_sessionFile]; decide
      · exact pqTail_head_ne (by decide) x ht)]
    unfold filesFold
    rw [List.foldl_cons, List.foldl_cons, List.foldl_nil]
    have hni : normalizePath identityKeyPairFile = ["identity-key-pair"] := by decide
    simp only [FsState.setFile, FsState.setEntry, hni, beq_self_eq_true, ↓reduceIte]
  have hcap : (ikBytes W st).length ≤ fileCapBytes :=
    LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.idKeyPair_encode_length_le_fileCapBytes
      W.C st.me.idPriv
  unfold cliRd readViewF
  rw [hp, hb, hf]
  simp only [hcap, ↓reduceIte]

theorem keyPairLt_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hwf : PqxdhPartyInSpecDomain W st) :
    ∀ bs, StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqInitInputs W st b t))
      (utf8 "identity-key-pair") = .ok bs → bs.length < 2 ^ 32 := by
  intro bs hget
  rw [own_get_idKeyPair] at hget
  injection hget with hget
  subst hget
  have hlt : (ikBytes W st).length < 2 ^ 31 :=
    (hwf.2.1 (identityKeyPairFile, ikBytes W st) (by simp [encodeDir, ikBytes])).1
  omega

theorem idPairDerived_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ∀ kp, StoresGhost.opened.identity.keyPair cliIo.rd (runFiles (pqInitInputs W st b t)) =
      .ok kp → kp.identityKey.publicKey = (keyPairOf W.C kp.privateKey.bytes).publicKey := by
  intro kp hkp
  unfold IdGhost.keyPair at hkp
  rw [own_get_idKeyPair] at hkp
  dsimp only [Bind.bind, Except.bind] at hkp
  rw [tryFrom_ikBytes] at hkp
  injection hkp with hkp
  subst hkp
  simp only [keyPairOf, clampScalar_idem]

theorem idGet_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ∃ bs, StoresGhost.opened.identity.peers.get cliIo.rd (runFiles (pqInitInputs W st b t))
      (addrValE st.party.other).name = .ok bs ∧ IdFileWf bs := by
  have hp : pathStr (pathOf (utf8 "identities") (addrValE st.party.other).name) =
      identityFile (partyAddressName st.party.other) :=
    String.toList_inj.mp (by
      cases st.party.other <;>
        (unfold pathStr identityFile;
         rw [String.toList_ofList, String.toList_append];
         simp only [pathOf, addrValE, utf8_eq_flatMap, partyAddressName];
         decide))
  have hb : blockingAncestorF (runFiles (pqInitInputs W st b t))
      (identityFile (partyAddressName st.party.other)) = none := by
    cases st.party.other
    · exact blockingAncestorF_of_split2
        (c1 := "identities".toList) (c2 := (partyAddressName .A).toList)
        (by unfold identityFile; rw [String.toList_append]; decide) rfl
        (runFiles_identities_dir W st b t)
    · exact blockingAncestorF_of_split2
        (c1 := "identities".toList) (c2 := (partyAddressName .B).toList)
        (by unfold identityFile; rw [String.toList_append]; decide) rfl
        (runFiles_identities_dir W st b t)
  have hnorm : normalizePath (identityFile (partyAddressName st.party.other)) =
      ["identities", partyAddressName st.party.other] := by
    cases st.party.other <;> decide
  have hne : (normalizePath (identityFile (partyAddressName st.party.other))).isEmpty = false := by
    rw [hnorm]; rfl
  have hns : normalizePath (identityFile (partyAddressName st.party.other)) ∉ stdioPaths.map normalizePath := by
    cases st.party.other <;> decide
  have hd : (pqInitInputs W st b t).dirs = partyDirs ++ [bundleDir] := rfl
  have htail : ∀ (fs : FsState),
      (filesFold
        ((match st.session with
          | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
          | none => []) ++ pqTail W st b t) fs).entries ["identities", partyAddressName st.party.other] =
        fs.entries ["identities", partyAddressName st.party.other] := fun fs =>
    filesFold_entries_of_head_ne _ fs ["identities", partyAddressName st.party.other] (fun x hx => by
      simp only [List.mem_append] at hx
      rcases hx with hs' | ht
      · cases hses : st.session with
        | none => rw [hses] at hs'; cases hs'
        | some _ =>
          rw [hses] at hs'
          rcases List.mem_singleton.mp hs' with rfl
          dsimp only; rw [head_sessionFile]; dsimp only [List.head?]; decide
      · exact pqTail_head_ne (by dsimp only [List.head?]; decide) x ht)
  cases hpid : st.peerId with
  | none =>
    refine ⟨[], ?_, Or.inl rfl⟩
    change cliRd (runFiles (pqInitInputs W st b t))
      (pathOf (utf8 "identities") (addrValE st.party.other).name) = .ok []
    have hrf : runFiles (pqInitInputs W st b t) (identityFile (partyAddressName st.party.other)) = none := by
      rw [runFiles_eq_entries _ hne hns, hnorm, hd, pqInitInputs_files_eq, hpid,
        List.append_assoc, filesFold_append, htail]
      rw [filesFold_entries_of_head_ne _ _ ["identities", partyAddressName st.party.other] (fun x hx => by
        simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;>
          (dsimp only [addressFile, identityKeyPairFile, registrationIdFile, List.head?]; decide))]
      cases st.party.other <;> decide
    unfold cliRd readViewF
    rw [hp, hb, hrf]
  | some k =>
    refine ⟨k.serialize, ?_, Or.inr ⟨k, rfl⟩⟩
    change cliRd (runFiles (pqInitInputs W st b t))
      (pathOf (utf8 "identities") (addrValE st.party.other).name) = .ok k.serialize
    have hrf : runFiles (pqInitInputs W st b t) (identityFile (partyAddressName st.party.other)) =
        some (.file k.serialize) := by
      rw [runFiles_eq_entries _ hne hns, hnorm, hd, pqInitInputs_files_eq, hpid,
        List.append_assoc, filesFold_append, htail, filesFold_append, filesFold_singleton]
      simp only [FsState.setFile, FsState.setEntry, hnorm, beq_self_eq_true, ↓reduceIte]
    have hcap : k.serialize.length ≤ fileCapBytes :=
      LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.identityKey_serialize_length_le_fileCapBytes k
    unfold cliRd readViewF
    rw [hp, hb, hrf]
    simp only [hcap, ↓reduceIte]

theorem noSession_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hs : st.session = none) :
    StoresGhost.opened.sessions.get cliIo.rd (runFiles (pqInitInputs W st b t))
      (addressText (addrValE st.party.other)) = .ok [] := by
  change cliRd (runFiles (pqInitInputs W st b t))
    (pathOf (utf8 "sessions") (addressText (addrValE st.party.other))) = .ok []
  have hp : pathStr (pathOf (utf8 "sessions") (addressText (addrValE st.party.other))) =
      sessionFile (partyAddress st.party.other) :=
    String.toList_inj.mp (by
      cases st.party.other <;>
        (unfold pathStr sessionFile;
         rw [String.toList_ofList, String.toList_append];
         simp only [pathOf, addrValE, addressText, decimalText, partyAddress, Address.text,
           utf8_eq_flatMap, partyAddressName];
         decide))
  have hb : blockingAncestorF (runFiles (pqInitInputs W st b t))
      (sessionFile (partyAddress st.party.other)) = none := by
    cases st.party.other
    · exact blockingAncestorF_of_split2
        (c1 := "sessions".toList) (c2 := (partyAddress .A).text.toList)
        (by unfold sessionFile; rw [String.toList_append]; decide) rfl
        (runFiles_sessions_dir W st b t)
    · exact blockingAncestorF_of_split2
        (c1 := "sessions".toList) (c2 := (partyAddress .B).text.toList)
        (by unfold sessionFile; rw [String.toList_append]; decide) rfl
        (runFiles_sessions_dir W st b t)
  have hnorm : normalizePath (sessionFile (partyAddress st.party.other)) =
      ["sessions", (partyAddress st.party.other).text] := by
    cases st.party.other <;> decide
  have hne : (normalizePath (sessionFile (partyAddress st.party.other))).isEmpty = false := by
    rw [hnorm]; rfl
  have hns : normalizePath (sessionFile (partyAddress st.party.other)) ∉ stdioPaths.map normalizePath := by
    cases st.party.other <;> decide
  have hd : (pqInitInputs W st b t).dirs = partyDirs ++ [bundleDir] := rfl
  have hrf : runFiles (pqInitInputs W st b t) (sessionFile (partyAddress st.party.other)) = none := by
    rw [runFiles_eq_entries _ hne hns, hnorm, hd, pqInitInputs_files_eq, hs]
    rw [filesFold_entries_of_head_ne _ _ ["sessions", (partyAddress st.party.other).text] (fun x hx => by
      simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with ((rfl | rfl | rfl) | hp') | ht
      · dsimp only [addressFile, List.head?]; decide
      · dsimp only [identityKeyPairFile, List.head?]; decide
      · dsimp only [registrationIdFile, List.head?]; decide
      · cases hpid : st.peerId with
        | none => rw [hpid] at hp'; cases hp'
        | some _ =>
          rw [hpid] at hp'
          rcases List.mem_singleton.mp hp' with rfl
          dsimp only; rw [head_identityFile]; dsimp only [List.head?]; decide
      · exact pqTail_head_ne (by dsimp only [List.head?]; decide) x ht)]
    cases st.party.other <;> decide
  unfold cliRd readViewF
  rw [hp, hb, hrf]

end CryptoVerification.SignalSession.Cli.RunProofs.InitS0
