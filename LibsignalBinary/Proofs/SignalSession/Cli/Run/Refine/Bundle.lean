/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.List.SplitOn.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# `read_bundle` Evaluation on Typed Pre-Key Bundles

Proves `readBundleV_pqInit`: on `pqInitInputs W st b t`, `RunCompose.readBundleV` decodes the
serialized files in `bundle/` (`IdentityKey::decode`, `PublicKey::deserialize`,
`kem::Key::deserialize`, little-endian `u32` IDs, trailing 64-byte signatures, and optional
one-time pre-key) to `bundleVE b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunRefine

open Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose

/-- Decoded `BundleV` representation of a typed `PreKeyBundleFields` value for peer device `1`. -/
def bundleVE (b : PreKeyBundleFields) : BundleV :=
  { idKey := ⟨⟨b.idPub⟩⟩, regId := b.regId, device := 1#8, spkId := b.spkId, spk := ⟨b.spkPub⟩,
    spkSig := b.spkSig.toList, kpkId := b.kpkId, kpk := b.kpkPub.toList,
    kpkSig := b.kpkSig.toList, opk := b.opk.map fun (i, k) => (i, ⟨k⟩) }

private theorem ofLe32_extract (v : BitVec 32) :
    ofLe32 (v.extractLsb' 0 8) (v.extractLsb' 8 8) (v.extractLsb' 16 8) (v.extractLsb' 24 8) =
      v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofLe32, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs with h1 h2 h3
  · have hb : decide (i < 8) = true := decide_eq_true h1
    rw [hb, Bool.true_and, Nat.zero_add]
  · have hb : decide (i - 8 < 8) = true := decide_eq_true h2
    rw [hb, Bool.true_and]
    congr 1; omega
  · have hb : decide (i - 8 - 8 < 8) = true := decide_eq_true h3
    rw [hb, Bool.true_and]
    congr 1; omega
  · have h4 : i - 8 - 8 - 8 < 8 := by omega
    have hb : decide (i - 8 - 8 - 8 < 8) = true := decide_eq_true h4
    rw [hb, Bool.true_and]
    congr 1; omega

private theorem readU32LE_le32 (v : BitVec 32) :
    RunCompose.readU32LE (SignalSession.le32 v) = some v := by
  simp only [SignalSession.le32, RunCompose.readU32LE, ofLe32_extract]

private theorem splitId_le32_pure (id : BitVec 32) (key : List (BitVec 8)) :
    splitId (SignalSession.le32 id ++ key) = some (id, key) := by
  simp only [SignalSession.le32, List.cons_append, List.nil_append, splitId, ofLe32_extract]

private theorem splitSigned_le32_pure (id : BitVec 32) (key sig : List (BitVec 8))
    (hs : sig.length = 64) :
    splitSigned (SignalSession.le32 id ++ key ++ sig) = some (id, key, sig) := by
  rw [List.append_assoc, splitSigned, splitId_le32_pure]
  simp only [List.length_append, hs, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
    List.take_left', List.drop_left']

private theorem pubDeserialize_djbKey (k : List.Vector (BitVec 8) 32) :
    PublicKey.deserialize (djbKey k) = .ok ⟨k⟩ := by
  rcases k with ⟨l, hl⟩
  simp [djbKey, PublicKey.deserialize, djbType, hl, List.take_of_length_le (Nat.le_of_eq hl)]

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

private theorem toUTF8_toList (s : String) :
    s.toUTF8.toList = s.toList.flatMap String.utf8EncodeChar := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  simp only [String.toUTF8, String.toByteArray_ofList, byteArray_toList_eq_data_toList,
    List.utf8Encode, List.data_toByteArray]

private theorem decodeIdentityKey_djbKey (k : List.Vector (BitVec 8) 32) :
    CryptoVerification.RecordCodecs.decodeIdentityKey (djbKey k) = .ok ⟨⟨k⟩⟩ := by
  unfold CryptoVerification.RecordCodecs.decodeIdentityKey
  rw [pubDeserialize_djbKey]
  rfl

private theorem kemPkDeserialize_kyberKey (k : List.Vector (BitVec 8) 1568) :
    RunProofs.kemPkDeserialize (kyberKey k) = .ok k.toList := by
  unfold kyberKey RunProofs.kemPkDeserialize
  dsimp only
  split_ifs with h1 h2
  · exact absurd rfl h1
  · exact absurd k.toList_length h2
  · rfl

private theorem append_head_ne_b {p : String} (s : String)
    (hp : p.toList ≠ [] ∧ p.toList.head? ≠ some 'b') :
    (p ++ s).toList.head? ≠ some 'b' := by
  rw [String.toList_append]
  cases h : p.toList with
  | nil => exact absurd h hp.1
  | cons _ _ =>
    rw [h] at hp
    exact hp.2

private theorem ofList_bundle :
    String.ofList ['b', 'u', 'n', 'd', 'l', 'e'] = "bundle" := by
  rw [← String.toList_inj, String.toList_ofList]

private theorem splitSlash_go_head : ∀ (cs cur : List Char),
    ∃ pre, (Arm64.splitSlash.go cur cs).head? = some (String.ofList (cur.reverse ++ pre))
  | [], cur => ⟨[], by simp [Arm64.splitSlash.go]⟩
  | c :: cs, cur => by
    by_cases hc : c = '/'
    · subst hc; exact ⟨[], by simp [Arm64.splitSlash.go]⟩
    · have hstep : Arm64.splitSlash.go cur (c :: cs) = Arm64.splitSlash.go (c :: cur) cs := by
        rw [Arm64.splitSlash.go.eq_def]
        split
        · simp_all
        · simp_all
        · rename_i _ _ _ _ heq
          injection heq with h1 h2
          subst h1 h2
          rfl
      obtain ⟨pre, h⟩ := splitSlash_go_head cs (c :: cur)
      exact ⟨c :: pre, by simpa [hstep, List.reverse_cons, List.append_assoc] using h⟩

private theorem norm_head_ne_bundle {p : String}
    (h : ∃ c cs, p.toList = c :: cs ∧ (c ≠ '/' ∧ c ≠ '.' ∧ c ≠ 'b')) :
    (Arm64.normalizePath p).head? ≠ some "bundle" := by
  obtain ⟨c, cs, hp, hc1, hc2, hc3⟩ := h
  unfold Arm64.normalizePath Arm64.splitSlash
  rw [hp]
  have hstep : Arm64.splitSlash.go [] (c :: cs) = Arm64.splitSlash.go [c] cs := by
    rw [Arm64.splitSlash.go.eq_def]
    split
    · simp_all
    · simp_all
    · rename_i _ _ _ _ heq
      injection heq with h1 h2
      subst h1 h2
      rfl
  rw [hstep]
  obtain ⟨pre, hhead⟩ := splitSlash_go_head cs [c]
  cases hgo : Arm64.splitSlash.go [c] cs with
  | nil => rw [hgo] at hhead; cases hhead
  | cons s0 tl =>
    rw [hgo, List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hrev : [c].reverse ++ pre = c :: pre := rfl
    rw [hrev]
    have hlist : (String.ofList (c :: pre)).toList = c :: pre := String.toList_ofList
    have hne : (String.ofList (c :: pre)).isEmpty = false := by
      rw [Bool.eq_false_iff]
      intro he
      have : String.ofList (c :: pre) = "" := String.isEmpty_iff.mp he
      have := congrArg String.toList this
      rw [hlist] at this
      cases this
    have hndot : (String.ofList (c :: pre) != ".") = true := by
      rw [bne_iff_ne]
      intro he
      have := congrArg String.toList he
      rw [hlist] at this
      have hdot : ".".toList = ['.'] := by decide
      rw [hdot] at this
      injection this with h1 _
      exact hc2 h1
    have hpred : (!(String.ofList (c :: pre)).isEmpty && String.ofList (c :: pre) != ".") = true := by
      rw [hne, hndot]; rfl
    rw [List.filter_cons_of_pos (p := fun seg => !seg.isEmpty && seg != ".") hpred, List.head?_cons]
    intro heq
    injection heq with heq
    have := congrArg String.toList heq
    rw [hlist] at this
    have hbun : "bundle".toList = 'b' :: ['u', 'n', 'd', 'l', 'e'] := by decide
    rw [hbun] at this
    injection this with h1 _
    exact hc3 h1

private theorem prefix_norm_head_ne_bundle {p : String}
    (h : ∃ c cs, p.toList = c :: cs ∧ (c ≠ '/' ∧ c ≠ '.' ∧ c ≠ 'b')) (s : String) :
    (Arm64.normalizePath (p ++ s)).head? ≠ some "bundle" := by
  obtain ⟨c, cs, hp, hc⟩ := h
  exact norm_head_ne_bundle ⟨c, cs ++ s.toList, by rw [String.toList_append, hp, List.cons_append], hc⟩

private theorem encodeDir_head_ne_b (W : PEParams) (st : PqParty) :
    ∀ pb ∈ encodeDir W st, (Arm64.normalizePath pb.1).head? ≠ some "bundle" := by
  intro pb hpb
  simp only [encodeDir, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpb
  rcases hpb with ((((((h1 | h2) | h3) | h4) | h5) | h6) | h7)
  · rcases h1 with rfl | rfl | rfl <;>
      (dsimp only [addressFile, identityKeyPairFile, registrationIdFile];
       exact norm_head_ne_bundle ⟨_, _, rfl, by decide⟩)
  · cases hp : st.peerId with
    | none => simp [hp] at h2
    | some _ =>
      simp only [hp, List.mem_singleton] at h2; subst h2
      exact prefix_norm_head_ne_bundle ⟨_, _, rfl, by decide⟩ _
  · cases hs : st.session with
    | none => simp [hs] at h3
    | some _ =>
      simp only [hs, List.mem_singleton] at h3; subst h3
      exact prefix_norm_head_ne_bundle ⟨_, _, rfl, by decide⟩ _
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h4
    exact prefix_norm_head_ne_bundle ⟨_, _, rfl, by decide⟩ _
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h5
    exact prefix_norm_head_ne_bundle ⟨_, _, rfl, by decide⟩ _
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h6
    exact prefix_norm_head_ne_bundle ⟨_, _, rfl, by decide⟩ _
  · obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp h7
    obtain ⟨⟨_, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact prefix_norm_head_ne_bundle ⟨_, _, rfl, by decide⟩ _
    · unfold baseKeysFile; rw [String.append_assoc]
      exact prefix_norm_head_ne_bundle ⟨_, _, rfl, by decide⟩ _

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
    ∀ {segs q : Arm64.FsPath}, q ∈ Arm64.FsPath.nonEmptyPrefixes segs → q.head? = segs.head?
  | [], _, h => nomatch h
  | _ :: _, _, h => by
    simp only [Arm64.FsPath.nonEmptyPrefixes, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

private theorem foldl_setEntry_entries_of_forall_ne (l : List Arm64.FsPath) (fs : Arm64.FsState)
    (k : Arm64.FsPath) (h : ∀ p ∈ l, k ≠ p) :
    (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k = fs.entries k := by
  induction l generalizing fs with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldl_cons, ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have hne : (k == p) = false := beq_false_of_ne (h p (List.mem_cons_self ..))
    simp only [Arm64.FsState.setEntry, hne, Bool.false_eq_true, ↓reduceIte]

private def SameOnBundle (a b : Arm64.FsState) : Prop :=
  ∀ k : Arm64.FsPath, k.head? = some "bundle" → a.entries k = b.entries k

private theorem sameOnBundle_setEntry {a b : Arm64.FsState} (h : SameOnBundle a b)
    (p : Arm64.FsPath) (e : Option Arm64.FsEntry) :
    SameOnBundle (a.setEntry p e) (b.setEntry p e) := by
  intro k hk
  simp only [Arm64.FsState.setEntry]
  split
  · rfl
  · exact h k hk

private theorem sameOnBundle_foldl_dir {a b : Arm64.FsState} (h : SameOnBundle a b)
    (l : List Arm64.FsPath) :
    SameOnBundle (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) a)
      (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) b) := by
  induction l generalizing a b with
  | nil => exact h
  | cons _ _ ih => exact ih (sameOnBundle_setEntry h _ _)

private theorem sameOnBundle_filesFold {a b : Arm64.FsState} (h : SameOnBundle a b)
    (l : List (String × List (BitVec 8))) : SameOnBundle (filesFold l a) (filesFold l b) := by
  induction l generalizing a b with
  | nil => exact h
  | cons x _ ih =>
    obtain ⟨_, _⟩ := x
    exact ih (sameOnBundle_setEntry (sameOnBundle_foldl_dir h _) _ _)

private theorem filesFold_sameOnBundle_of_head_ne (l : List (String × List (BitVec 8)))
    (fs : Arm64.FsState) (h : ∀ x ∈ l, (Arm64.normalizePath x.1).head? ≠ some "bundle") :
    SameOnBundle (filesFold l fs) fs := by
  intro k hk
  induction l generalizing fs with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨p, bs⟩ := x
    have hp := h (p, bs) (List.mem_cons_self ..)
    unfold filesFold
    rw [List.foldl_cons]
    change (filesFold l _).entries k = fs.entries k
    rw [ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hne_p : (k == Arm64.normalizePath p) = false := beq_false_of_ne (fun he => hp (he ▸ hk))
    simp only [Arm64.FsState.setFile, Arm64.FsState.setEntry, hne_p, Bool.false_eq_true, ↓reduceIte]
    refine foldl_setEntry_entries_of_forall_ne _ fs k fun pref hpref he => ?_
    subst he
    have hh := head_of_mem_nonEmptyPrefixes (mem_of_mem_dropLast hpref)
    rw [hk] at hh
    exact hp hh.symm

private def bundleQueryPaths : List String :=
  ["bundle", "bundle/identity-key", "bundle/registration-id",
   "bundle/signed-pre-key", "bundle/kyber-pre-key", "bundle/one-time-pre-key"]

private theorem runFiles_pqInit_b (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) {q : String}
    (hq : q ∈ bundleQueryPaths) :
    runFiles (pqInitInputs W st b t) q =
      match ((publicBundleOf b).files bundleDir).reverse.find? (fun x => x.1 == q) with
      | some pb => some (.file pb.2)
      | none => if q ∈ partyDirs ++ [bundleDir] then some .dir else none := by
  have hne : (Arm64.normalizePath q).isEmpty = false := by revert q hq; decide
  have hns : Arm64.normalizePath q ∉ stdioPaths.map Arm64.normalizePath := by revert q hq; decide
  have hhead : (Arm64.normalizePath q).head? = some "bundle" := by revert q hq; decide
  unfold runFiles
  rw [files_eq_entries, ite_eq_right_iff.mpr (by simp [hne]),
    initFsState_entries (cliInputs (pqInitInputs W st b t)) (Arm64.normalizePath q) hns]
  change (filesFold (pqInitInputs W st b t).files
    (dirsFold (pqInitInputs W st b t).dirs {})).entries (Arm64.normalizePath q) = _
  have hfiles_eq : (pqInitInputs W st b t).files =
      encodeDir W st ++ ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)]) := by
    simp [pqInitInputs, pqInputs, List.append_assoc]
  have hdirs_eq : (pqInitInputs W st b t).dirs = partyDirs ++ [bundleDir] := rfl
  rw [hfiles_eq, hdirs_eq]
  have hfold_app : ∀ (l1 l2 : List (String × List (BitVec 8))) (a : Arm64.FsState),
      filesFold (l1 ++ l2) a = filesFold l2 (filesFold l1 a) := fun _ _ _ => List.foldl_append
  rw [hfold_app,
    sameOnBundle_filesFold
      (filesFold_sameOnBundle_of_head_ne (encodeDir W st) _ (encodeDir_head_ne_b W st))
      ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)])
      (Arm64.normalizePath q) hhead]
  simp only [bundleQueryPaths, List.mem_cons, List.not_mem_nil, or_false] at hq
  cases hopk : b.opk with
  | none =>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [filesFold, dirsFold, publicBundleOf, PublicBundle.files, bundleDir, partyDirs,
        coinsFile, hopk, Arm64.FsState.setFile, Arm64.FsState.setEntry, Arm64.normalizePath,
        Arm64.splitSlash, Arm64.splitSlash.go, Arm64.FsPath.nonEmptyPrefixes]
  | some opk =>
    rcases opk with ⟨opkId, opkKey⟩
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [filesFold, dirsFold, publicBundleOf, PublicBundle.files, bundleDir, partyDirs,
        coinsFile, hopk, Arm64.FsState.setFile, Arm64.FsState.setEntry, Arm64.normalizePath,
        Arm64.splitSlash, Arm64.splitSlash.go, Arm64.FsPath.nonEmptyPrefixes]

private theorem runFiles_pqInit_bundle (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    runFiles (pqInitInputs W st b t) "bundle" = some .dir := by
  rw [runFiles_pqInit_b W st b t (by decide)]
  cases hopk : b.opk <;> simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]

private theorem bundleFile_pqInit_of_full (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (name full : String)
    (hp : ((bundlePath (bytesOfString bundleDir) name).map fun x => Char.ofNat x.toNat) =
      full.toList)
    (hc : ∃ rest, pathComps full = [['b', 'u', 'n', 'd', 'l', 'e'], rest])
    (hnd : full ∉ partyDirs ++ [bundleDir])
    (hf : full ∈ bundleQueryPaths) :
    bundleFile (runFiles (pqInitInputs W st b t)) (bytesOfString bundleDir) name =
      match ((publicBundleOf b).files bundleDir).reverse.find?
          (fun x => x.1 == full) with
      | some pb => some pb.2
      | none => some [] := by
  have hp' : pathStr (bundlePath (bytesOfString bundleDir) name) = full := by
    unfold pathStr
    rw [← String.toList_inj, String.toList_ofList]
    exact hp
  obtain ⟨_, hcs⟩ := hc
  have ha : ancestors full = ["bundle"] := by
    unfold ancestors
    rw [hcs]
    dsimp
    rw [List.map_singleton, List.take_zero, List.intercalate_singleton, ofList_bundle]
  have hb : blockingAncestorF (runFiles (pqInitInputs W st b t)) full = none := by
    unfold blockingAncestorF
    rw [ha, List.find?_cons, runFiles_pqInit_bundle W st b t]
    rfl
  have hrf := runFiles_pqInit_b W st b t hf
  unfold bundleFile
  show exceptOpt (cliRd (runFiles (pqInitInputs W st b t))
    (bundlePath (bytesOfString bundleDir) name)) = _
  unfold cliRd readViewF
  rw [hp', hb]
  dsimp only
  rw [hrf]
  cases hfind : ((publicBundleOf b).files bundleDir).reverse.find? (fun x => x.1 == full) with
  | some pb =>
    have hmem : pb ∈ (publicBundleOf b).files bundleDir :=
      List.mem_reverse.mp (List.mem_of_find?_eq_some hfind)
    have hcap : pb.2.length ≤ fileCapBytes := by
      unfold PublicBundle.files publicBundleOf at hmem
      cases hopk : b.opk <;> simp only [hopk, Option.map, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      · rcases hmem with rfl | rfl | rfl | rfl <;>
          simp [djbKey, kyberKey, SignalSession.le32, List.Vector.toList_length, fileCapBytes]
      · rename_i p; rcases p with ⟨_, _⟩
        rcases hmem with (rfl | rfl | rfl | rfl) | rfl <;>
          simp [djbKey, kyberKey, SignalSession.le32, List.Vector.toList_length, fileCapBytes]
    simp only [hcap, ↓reduceIte]; rfl
  | none => simp only [hnd, ↓reduceIte]; rfl

/-- `readBundleV` on `pqInitInputs W st b t` evaluates to `.ok (some (bundleVE b))`. -/
theorem readBundleV_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    readBundleV (runFiles (pqInitInputs W st b t)) (bytesOfString bundleDir) 1#8 =
      some (bundleVE b) := by
  have hik := bundleFile_pqInit_of_full W st b t "identity-key" "bundle/identity-key"
    (by unfold bundleDir bundlePath bytesOfString utf8; rw [toUTF8_toList]; decide)
    ⟨"identity-key".toList, by unfold pathComps; decide⟩
    (by unfold partyDirs bundleDir; decide) (by decide)
  have hreg := bundleFile_pqInit_of_full W st b t "registration-id" "bundle/registration-id"
    (by unfold bundleDir bundlePath bytesOfString utf8; rw [toUTF8_toList]; decide)
    ⟨"registration-id".toList, by unfold pathComps; decide⟩
    (by unfold partyDirs bundleDir; decide) (by decide)
  have hspk := bundleFile_pqInit_of_full W st b t "signed-pre-key" "bundle/signed-pre-key"
    (by unfold bundleDir bundlePath bytesOfString utf8; rw [toUTF8_toList]; decide)
    ⟨"signed-pre-key".toList, by unfold pathComps; decide⟩
    (by unfold partyDirs bundleDir; decide) (by decide)
  have hkpk := bundleFile_pqInit_of_full W st b t "kyber-pre-key" "bundle/kyber-pre-key"
    (by unfold bundleDir bundlePath bytesOfString utf8; rw [toUTF8_toList]; decide)
    ⟨"kyber-pre-key".toList, by unfold pathComps; decide⟩
    (by unfold partyDirs bundleDir; decide) (by decide)
  have hopkf := bundleFile_pqInit_of_full W st b t "one-time-pre-key" "bundle/one-time-pre-key"
    (by unfold bundleDir bundlePath bytesOfString utf8; rw [toUTF8_toList]; decide)
    ⟨"one-time-pre-key".toList, by unfold pathComps; decide⟩
    (by unfold partyDirs bundleDir; decide) (by decide)
  unfold readBundleV bundleVE
  rw [hik, hreg, hspk, hkpk, hopkf]
  cases hopk : b.opk with
  | none =>
    have hf1 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/identity-key") = some ("bundle/identity-key", djbKey b.idPub) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    have hf2 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/registration-id") =
        some ("bundle/registration-id", SignalSession.le32 b.regId) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    have hf3 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/signed-pre-key") =
        some ("bundle/signed-pre-key",
          SignalSession.le32 b.spkId ++ djbKey b.spkPub ++ b.spkSig.toList) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    have hf4 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/kyber-pre-key") =
        some ("bundle/kyber-pre-key",
          SignalSession.le32 b.kpkId ++ kyberKey b.kpkPub ++ b.kpkSig.toList) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    have hf5 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/one-time-pre-key") = none := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    rw [hf1, hf2, hf3, hf4, hf5]
    dsimp only [bind, Option.bind]
    rw [decodeIdentityKey_djbKey, readU32LE_le32,
      splitSigned_le32_pure _ _ _ b.spkSig.toList_length,
      splitSigned_le32_pure _ _ _ b.kpkSig.toList_length]
    dsimp
    simp only [pubDeserialize_djbKey, kemPkDeserialize_kyberKey]
    rfl
  | some opk =>
    rcases opk with ⟨opkId, opkKey⟩
    have hf1 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/identity-key") = some ("bundle/identity-key", djbKey b.idPub) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    have hf2 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/registration-id") =
        some ("bundle/registration-id", SignalSession.le32 b.regId) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    have hf3 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/signed-pre-key") =
        some ("bundle/signed-pre-key",
          SignalSession.le32 b.spkId ++ djbKey b.spkPub ++ b.spkSig.toList) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    have hf4 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/kyber-pre-key") =
        some ("bundle/kyber-pre-key",
          SignalSession.le32 b.kpkId ++ kyberKey b.kpkPub ++ b.kpkSig.toList) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    have hf5 : ((publicBundleOf b).files bundleDir).reverse.find?
        (fun x => x.1 == "bundle/one-time-pre-key") =
        some ("bundle/one-time-pre-key", SignalSession.le32 opkId ++ djbKey opkKey) := by
      simp [publicBundleOf, PublicBundle.files, bundleDir, hopk]
    rw [hf1, hf2, hf3, hf4, hf5]
    have hne : (SignalSession.le32 opkId ++ djbKey opkKey).isEmpty = false := rfl
    dsimp only [bind, Option.bind]
    rw [decodeIdentityKey_djbKey, readU32LE_le32,
      splitSigned_le32_pure _ _ _ b.spkSig.toList_length,
      splitSigned_le32_pure _ _ _ b.kpkSig.toList_length,
      hne, splitId_le32_pure]
    dsimp
    simp only [pubDeserialize_djbKey, kemPkDeserialize_kyberKey]
    rfl

end CryptoVerification.SignalSession.Cli.RunRefine
