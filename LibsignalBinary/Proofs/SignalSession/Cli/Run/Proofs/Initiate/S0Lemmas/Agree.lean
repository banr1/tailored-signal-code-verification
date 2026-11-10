/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bundle
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.List.SplitOn.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Spec
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

/-!
# Model Agreement Lemmas for `pqInitiateAgrees_initDef`

Proves `agree_pqInit`, showing that `initDef` agrees with `pqInitModel` on every input of
`CliSpecPqxdh`'s `init` arm once `readBundleV` returns `RunRefine.bundleVE b`, by expressing
`runFiles` and `filesOf` via `FsState.entries` and `filesFold` and pruning store reads and commit
writes across disjoint head-segment classes.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.InitS0

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose

/-! ## Vector, coins, party, and clamping lemmas -/

theorem vec_eta {α : Type} {n : Nat} (v : List.Vector α n) (h : v.toList.length = n) :
    (⟨v.toList, h⟩ : List.Vector α n) = v := by
  rcases v with ⟨l, hl⟩
  rfl

theorem opk_map_roundtrip (opk : Option (BitVec 32 × List.Vector (BitVec 8) 32)) :
    ((opk.map fun (i, k) => (i, (⟨k⟩ : PublicKey))).map fun (i, k) => (i, k.bytes)) = opk := by
  cases opk with
  | none => rfl
  | some p => rfl

theorem padCoins_vec_eq (t : List.Vector (BitVec 8) initiateTapeLen)
    (h : (t.toList.take initiateTapeLen ++
      List.replicate (initiateTapeLen - t.toList.length) 0#8).length = initiateTapeLen) :
    (⟨t.toList.take initiateTapeLen ++
      List.replicate (initiateTapeLen - t.toList.length) 0#8, h⟩ :
      List.Vector (BitVec 8) initiateTapeLen) = t := by
  rcases t with ⟨l, hl⟩
  apply Subtype.ext
  dsimp only [List.Vector.toList]
  rw [hl, Nat.sub_self, List.replicate_zero, List.append_nil,
    List.take_of_length_le (Nat.le_of_eq hl)]

/-! ## `String`, `utf8`, and `pathStr` helpers -/

private theorem drop_getElem_cons {α : Type} :
    ∀ (xs : List α) (i : Nat) (h : i < xs.length), xs[i]'h :: xs.drop (i + 1) = xs.drop i
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, h => drop_getElem_cons xs i (Nat.lt_of_succ_lt_succ h)

private theorem drop_of_le {α : Type} :
    ∀ (xs : List α) (i : Nat), xs.length ≤ i → xs.drop i = []
  | [], _, _ => by simp
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: xs, i + 1, h => drop_of_le xs i (Nat.le_of_succ_le_succ h)

private theorem byteArray_loop_eq (arr : Array UInt8) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop ⟨arr⟩ i r = r.reverse ++ arr.toList.drop i := by
  unfold ByteArray.toList.loop
  split
  · next h =>
    have hi : i < arr.size := h
    have his : i < arr.toList.length := by simpa using hi
    have hget : (ByteArray.mk arr).get! i = arr.toList[i]'his := by
      simp [ByteArray.get!, getElem!_pos arr i hi]
    rw [byteArray_loop_eq arr (i + 1) ((ByteArray.mk arr).get! i :: r), hget,
      List.reverse_cons, List.append_assoc, List.singleton_append,
      drop_getElem_cons arr.toList i his]
  · next h =>
    have hi : arr.toList.length ≤ i := by
      have : ¬ i < arr.size := h
      simp at *; omega
    rw [drop_of_le arr.toList i hi, List.append_nil]
termination_by arr.size - i
decreasing_by
  have : i < arr.size := ‹_›
  omega

private theorem toList_toByteArray_eq (l : List UInt8) : l.toByteArray.toList = l := by
  unfold ByteArray.toList
  have h1 : l.toByteArray = ⟨l.toArray⟩ := by
    ext1
    exact List.data_toByteArray
  rw [h1, byteArray_loop_eq]
  simp

private theorem ofList_toList_eq (s : String) : String.ofList s.toList = s := by
  simp

private theorem utf8_eq_flatMap (s : String) :
    utf8 s = (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat := by
  conv_lhs => rw [← ofList_toList_eq s]
  unfold utf8
  simp only [String.toUTF8, String.toByteArray_ofList, List.utf8Encode, toList_toByteArray_eq]

theorem initParty_eq (P : Party) :
    (if RunRefine.addrValE P.other = RunRefine.addrValE .A then Party.B else Party.A) = P := by
  cases P with
  | B => simp only [Party.other, ↓reduceIte]
  | A =>
    have hne : RunRefine.addrValE .B ≠ RunRefine.addrValE .A := by
      intro h
      have h' : utf8 (partyAddressName .B) = utf8 (partyAddressName .A) := congrArg AddrVal.name h
      rw [utf8_eq_flatMap, utf8_eq_flatMap] at h'
      exact absurd h' (by decide)
    simp only [Party.other, hne, ↓reduceIte]

private theorem clamp_byte0 (b : BitVec 8) : (b &&& 0xf8#8) &&& 0xf8#8 = b &&& 0xf8#8 := by
  rw [BitVec.and_assoc]
  rfl

private theorem clamp_byte31 (b : BitVec 8) :
    (((b &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8 = (b &&& 0x7f#8) ||| 0x40#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases b.getLsbD i <;> cases (0x7f#8).getLsbD i <;> cases (0x40#8).getLsbD i <;> rfl

private theorem clampScalar_idem (sk : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar sk) = Ratchet.clampScalar sk := by
  apply List.Vector.ext
  intro i
  unfold Ratchet.clampScalar
  by_cases h31 : i = 31
  · subst h31
    simp only [List.Vector.get_set_same, clamp_byte31]
  · by_cases h0 : i = 0
    · subst h0
      have hne : (31 : Fin 32) ≠ 0 := by decide
      simp only [List.Vector.get_set_of_ne hne, List.Vector.get_set_same, clamp_byte0]
    · have hne31 : (31 : Fin 32) ≠ i := fun e => h31 e.symm
      have hne0 : (0 : Fin 32) ≠ i := fun e => h0 e.symm
      simp only [List.Vector.get_set_of_ne hne31, List.Vector.get_set_of_ne hne0]

theorem keyPairOf_clampScalar (C : Crypto) (sk : List.Vector (BitVec 8) 32) :
    keyPairOf C (Ratchet.clampScalar sk) = keyPairOf C sk := by
  unfold keyPairOf
  rw [clampScalar_idem]

theorem initiateState_clampScalar (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party) (me : LocalIdentity)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    initiateState X W P ⟨Ratchet.clampScalar me.idPriv, me.regId⟩ b t =
      initiateState X W P me b t := by
  have hi : initiateInput W ⟨Ratchet.clampScalar me.idPriv, me.regId⟩ b t =
      initiateInput W me b t := by
    unfold initiateInput
    dsimp only
    rw [keyPairOf_clampScalar]
  have hx : ∀ base ct, initiatorRecordExtras ⟨Ratchet.clampScalar me.idPriv, me.regId⟩ b base ct =
      initiatorRecordExtras me b base ct := fun _ _ => rfl
  unfold initiateState
  rw [hi]
  cases SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
  | none => rfl
  | some p =>
    dsimp only
    rw [keyPairOf_clampScalar]
    cases initializeInitiatorSession W.C (pqxdhSpqrSession W) ⟨(keyPairOf W.C me.idPriv).publicKey⟩
        ⟨⟨b.idPub⟩⟩ ⟨b.spkPub⟩ (HKDF.bytesToKey32 (ofU8 p.1.rootKey))
        (HKDF.bytesToKey32 (ofU8 p.1.chainKey)) (HKDF.bytesToKey32 (ofU8 p.1.pqrKey))
        (HKDF.bytesToKey32 ((t.toList.drop 160).take 32)) with
    | error _ => rfl
    | ok s =>
      dsimp only
      rw [hx]

/-! ## Canonical head-segment classes and `filesFold` combinators -/

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

private def EntryDichotomy (f : FsState → FsState) (k : FsPath) : Prop :=
  (∀ fs, (f fs).entries k = fs.entries k) ∨
  (∀ fs₁ fs₂, (f fs₁).entries k = (f fs₂).entries k)

private theorem entryDichotomy_id (k : FsPath) : EntryDichotomy id k :=
  Or.inl fun _ => rfl

private theorem entryDichotomy_comp {f g : FsState → FsState} {k : FsPath}
    (hf : EntryDichotomy f k) (hg : EntryDichotomy g k) :
    EntryDichotomy (fun fs => g (f fs)) k := by
  rcases hg with hg | hg
  · rcases hf with hf | hf
    · exact Or.inl fun fs => (hg (f fs)).trans (hf fs)
    · exact Or.inr fun fs₁ fs₂ => (hg (f fs₁)).trans ((hf fs₁ fs₂).trans (hg (f fs₂)).symm)
  · exact Or.inr fun fs₁ fs₂ => hg (f fs₁) (f fs₂)

private theorem entryDichotomy_setEntry (p : FsPath) (e : Option FsEntry) (k : FsPath) :
    EntryDichotomy (fun fs => fs.setEntry p e) k := by
  by_cases h : (k == p) = true
  · exact Or.inr fun fs₁ fs₂ => by simp only [FsState.setEntry, h, ↓reduceIte]
  · have hf : (k == p) = false := Bool.eq_false_iff.mpr h
    exact Or.inl fun fs => by simp only [FsState.setEntry, hf, Bool.false_eq_true, ↓reduceIte]

private theorem entryDichotomy_foldl_dir (l : List FsPath) (k : FsPath) :
    EntryDichotomy (fun fs => l.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) k := by
  induction l with
  | nil => exact entryDichotomy_id k
  | cons p l ih =>
    simpa only [List.foldl_cons] using entryDichotomy_comp (entryDichotomy_setEntry p (some .dir) k) ih

private theorem entryDichotomy_filesFold (l : List (String × List (BitVec 8))) (k : FsPath) :
    EntryDichotomy (filesFold l) k := by
  induction l with
  | nil => exact entryDichotomy_id k
  | cons x l ih =>
    obtain ⟨p, bs⟩ := x
    let step : FsState → FsState := fun fs =>
      (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))
    have hstep : EntryDichotomy step k :=
      entryDichotomy_comp
        (entryDichotomy_foldl_dir _ k)
        (entryDichotomy_setEntry (normalizePath p) (some (.file bs)) k)
    change EntryDichotomy (fun fs => filesFold l (step fs)) k
    exact entryDichotomy_comp (f := step) (g := filesFold l) hstep ih

private theorem filesFold_congr_entry (l : List (String × List (BitVec 8)))
    {fs₁ fs₂ : FsState} {k : FsPath} (h : fs₁.entries k = fs₂.entries k) :
    (filesFold l fs₁).entries k = (filesFold l fs₂).entries k := by
  rcases entryDichotomy_filesFold l k with hl | hr
  · rw [hl fs₁, hl fs₂, h]
  · exact hr fs₁ fs₂

private theorem filesFold_idem_entry (l : List (String × List (BitVec 8)))
    (fs : FsState) (k : FsPath) :
    (filesFold l (filesFold l fs)).entries k = (filesFold l fs).entries k := by
  rcases entryDichotomy_filesFold l k with hl | hr
  · exact hl (filesFold l fs)
  · exact hr (filesFold l fs) fs

private def preHeads : List (Option String) :=
  [some "address", some "identity-key-pair", some "registration-id"]

private def postHeads : List (Option String) :=
  [some "signed-pre-keys", some "one-time-pre-keys", some "one-time-kyber-pre-keys",
   some "last-resort-kyber-pre-keys"]

private def extraHeads : List (Option String) :=
  [some "bundle", some "coins"]

private def dirPre (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  [(addressFile, textBytes (partyAddress st.party).text),
   (identityKeyPairFile, IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩),
   (registrationIdFile, SignalSession.le32 st.me.regId)]

private def dirPeer (st : PqParty) : List (String × List (BitVec 8)) :=
  match st.peerId with
  | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
  | none => []

private def dirPost (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)) ++
  st.oneTime.map (fun (i, k) =>
    (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) =>
    (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten

private theorem encodeDir_eq_parts (W : PEParams) (st : PqParty) (hs : st.session = none) :
    encodeDir W st = dirPre W st ++ dirPeer st ++ dirPost W st := by
  simp only [encodeDir, hs, dirPre, dirPeer, dirPost, List.append_nil, List.append_assoc]
  rfl

private theorem head_dirPre (W : PEParams) (st : PqParty) {x : String × List (BitVec 8)}
    (hx : x ∈ dirPre W st) : (normalizePath x.1).head? ∈ preHeads := by
  simp only [dirPre, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    (dsimp only [addressFile, identityKeyPairFile, registrationIdFile]; decide)

private theorem head_dirPeer (st : PqParty) {x : String × List (BitVec 8)}
    (hx : x ∈ dirPeer st) : (normalizePath x.1).head? = some "identities" := by
  unfold dirPeer at hx
  cases hp : st.peerId with
  | none => simp [hp] at hx
  | some k =>
    simp only [hp, List.mem_singleton] at hx
    subst hx
    exact norm_head_slash_prefix "identities" _ (by decide) (by decide)

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

private theorem head_dirPost (W : PEParams) (st : PqParty) {x : String × List (BitVec 8)}
    (hx : x ∈ dirPost W st) : (normalizePath x.1).head? ∈ postHeads := by
  simp only [dirPost, List.mem_append] at hx
  rcases hx with ((h1 | h2) | h3) | h4
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h1
    dsimp only; rw [head_signedPreKeyFile]; decide
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h2
    dsimp only; rw [head_oneTimePreKeyFile]; decide
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp h3
    dsimp only; rw [head_oneTimeKyberPreKeyFile]; decide
  · obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp h4
    obtain ⟨⟨_, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · dsimp only; rw [head_lastResortKyberPreKeyFile]; decide
    · dsimp only; rw [head_baseKeysFile]; decide

private theorem head_initExtra (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    {x : String × List (BitVec 8)}
    (hx : x ∈ (publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)]) :
    (normalizePath x.1).head? ∈ extraHeads := by
  rcases List.mem_append.mp hx with hb | hc
  · simp only [PublicBundle.files, List.cons_append, List.nil_append, List.mem_cons] at hb
    rcases hb with rfl | rfl | rfl | rfl | ho
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
  · rw [List.mem_singleton] at hc
    subst hc
    dsimp only [coinsFile]; decide

/-! ## Store reads on `runFiles (pqInitInputs W st b t)` -/

private theorem runFiles_eq_entries (i : Inputs) {q : String}
    (hne : (normalizePath q).isEmpty = false)
    (hns : normalizePath q ∉ stdioPaths.map normalizePath) :
    runFiles i q = (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath q) := by
  unfold runFiles
  rw [files_eq_entries, ite_eq_right_iff.mpr (by simp [hne]),
    initFsState_entries (cliInputs i) (normalizePath q) hns]
  rfl

private theorem tail_head_not_pre_or_id (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen)
    {x : String × List (BitVec 8)}
    (hx : x ∈ dirPost W st ++ ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)]))
    {hd : Option String} (hhd : hd ∉ postHeads ∧ hd ∉ extraHeads) :
    (normalizePath x.1).head? ≠ hd := by
  intro heq
  rcases List.mem_append.mp hx with h1 | h2
  · exact hhd.1 (heq ▸ head_dirPost W st h1)
  · exact hhd.2 (heq ▸ head_initExtra b t h2)

private theorem runFiles_pqInit_identities (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hs : st.session = none) :
    runFiles (pqInitInputs W st b t) "identities" = some .dir := by
  rw [runFiles_eq_entries _ (by decide) (by decide)]
  have hn : normalizePath "identities" = ["identities"] := by decide
  have hd : (pqInitInputs W st b t).dirs = partyDirs ++ [bundleDir] := rfl
  have hf : (pqInitInputs W st b t).files =
      (dirPre W st ++ dirPeer st) ++
        (dirPost W st ++ ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)])) := by
    simp only [pqInitInputs, pqInputs, encodeDir_eq_parts W st hs, List.append_assoc]
  rw [hn, hd, hf, filesFold_append]
  rw [filesFold_entries_of_head_ne _ _ ["identities"] (fun x hx =>
    tail_head_not_pre_or_id W st b t hx (by decide))]
  rw [filesFold_append]
  have hpre : (filesFold (dirPre W st) (dirsFold (partyDirs ++ [bundleDir]) {})).entries
      ["identities"] = some .dir := by
    rw [filesFold_entries_of_head_ne _ _ ["identities"] (fun x hx heq => by
      have hm := head_dirPre W st hx
      rw [heq] at hm
      exact absurd hm (by decide))]
    decide
  unfold dirPeer
  cases hp : st.peerId with
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

private theorem tail3_head_ne_pre (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen)
    {x : String × List (BitVec 8)}
    (hx : x ∈ dirPeer st ++ (dirPost W st ++
      ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)])))
    {hd : Option String} (hhd : hd ∈ preHeads) :
    (normalizePath x.1).head? ≠ hd := by
  intro heq
  simp only [preHeads, List.mem_cons, List.not_mem_nil, or_false] at hhd
  rcases List.mem_append.mp hx with hp | hrest
  · have h1 := head_dirPeer st hp
    rw [heq] at h1
    rcases hhd with rfl | rfl | rfl <;> exact absurd h1 (by decide)
  · refine tail_head_not_pre_or_id W st b t hrest ⟨?_, ?_⟩ heq
    · rcases hhd with rfl | rfl | rfl <;> decide
    · rcases hhd with rfl | rfl | rfl <;> decide

theorem keyPair_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hs : st.session = none) :
    StoresGhost.opened.identity.keyPair cliIo.rd (runFiles (pqInitInputs W st b t)) =
      .ok ⟨⟨(keyPairOf W.C st.me.idPriv).publicKey⟩, ⟨Ratchet.clampScalar st.me.idPriv⟩⟩ := by
  let enc := IdentityKeyPairStructure.encode
    ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩
  have hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqInitInputs W st b t))
      (utf8 "identity-key-pair") = .ok enc := by
    change cliRd (runFiles (pqInitInputs W st b t)) (utf8 "identity-key-pair") = .ok enc
    have hp : pathStr (utf8 "identity-key-pair") = "identity-key-pair" := by
      unfold pathStr; rw [utf8_eq_flatMap]; rfl
    have hb : blockingAncestorF (runFiles (pqInitInputs W st b t)) "identity-key-pair" = none := by
      unfold blockingAncestorF ancestors pathComps; rfl
    have hf : runFiles (pqInitInputs W st b t) "identity-key-pair" = some (.file enc) := by
      rw [runFiles_eq_entries _ (by decide) (by decide)]
      have hn : normalizePath "identity-key-pair" = ["identity-key-pair"] := by decide
      have hfiles : (pqInitInputs W st b t).files =
          dirPre W st ++ (dirPeer st ++ (dirPost W st ++
            ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)]))) := by
        simp only [pqInitInputs, pqInputs, encodeDir_eq_parts W st hs, List.append_assoc]
      rw [hn, hfiles, filesFold_append]
      rw [filesFold_entries_of_head_ne _ _ ["identity-key-pair"] (fun x hx =>
        tail3_head_ne_pre W st b t hx (by decide))]
      unfold dirPre filesFold
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
      have hne_reg : ((["identity-key-pair"] : FsPath) == normalizePath registrationIdFile) = false :=
        by decide
      have hni : normalizePath identityKeyPairFile = ["identity-key-pair"] := by decide
      have hdrop_reg : (FsPath.nonEmptyPrefixes (normalizePath registrationIdFile)).dropLast = [] :=
        by decide
      simp only [hdrop_reg, List.foldl_nil, FsState.setFile, FsState.setEntry, hne_reg,
        Bool.false_eq_true, hni, beq_self_eq_true, ↓reduceIte]; rfl
    have hcap : enc.length ≤ fileCapBytes :=
      LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.idKeyPair_encode_length_le_fileCapBytes
        W.C st.me.idPriv
    unfold cliRd readViewF
    rw [hp, hb, hf]
    simp only [hcap, ↓reduceIte]
  have hpub_len : (djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes).length < 2 ^ 64 := by
    simp [djbKey]
  have hpriv_len : st.me.idPriv.toList.length < 2 ^ 64 := by
    simp [st.me.idPriv.toList_length]
  have hdec := IdentityKeyPairStructure.decode_encode
    ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩ hpub_len hpriv_len
  have hik : decodeIdentityKey (djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes) =
      .ok ⟨(keyPairOf W.C st.me.idPriv).publicKey⟩ :=
    decodeIdentityKey_serialize ⟨(keyPairOf W.C st.me.idPriv).publicKey⟩
  have hsk : deserializePrivateKey st.me.idPriv.toList = .ok ⟨Ratchet.clampScalar st.me.idPriv⟩ := by
    simp only [deserializePrivateKey, st.me.idPriv.toList_length, ↓reduceDIte, vec_eta]
  unfold IdGhost.keyPair
  rw [hget]
  dsimp only [bind, Except.bind]
  unfold IdentityKeyPair.tryFrom
  rw [hdec]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hik]
  dsimp only
  rw [hsk]

private theorem le32_concat (v : BitVec 32) :
    v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  ext i hi
  have eq_bit : ∀ k, k = i → v.getLsbD k = v[i]'hi := fun _ e => e ▸ rfl
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split_ifs <;> exact eq_bit _ (by omega)

theorem regId_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hs : st.session = none) :
    StoresGhost.opened.identity.regId cliIo.rd (runFiles (pqInitInputs W st b t)) =
      .ok st.me.regId := by
  have hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqInitInputs W st b t))
      (utf8 "registration-id") = .ok (SignalSession.le32 st.me.regId) := by
    change cliRd (runFiles (pqInitInputs W st b t)) (utf8 "registration-id") =
      .ok (SignalSession.le32 st.me.regId)
    have hp : pathStr (utf8 "registration-id") = "registration-id" := by
      unfold pathStr; rw [utf8_eq_flatMap]; rfl
    have hb : blockingAncestorF (runFiles (pqInitInputs W st b t)) "registration-id" = none := by
      unfold blockingAncestorF ancestors pathComps; rfl
    have hf : runFiles (pqInitInputs W st b t) "registration-id" =
        some (.file (SignalSession.le32 st.me.regId)) := by
      rw [runFiles_eq_entries _ (by decide) (by decide)]
      have hn : normalizePath "registration-id" = ["registration-id"] := by decide
      have hfiles : (pqInitInputs W st b t).files =
          dirPre W st ++ (dirPeer st ++ (dirPost W st ++
            ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)]))) := by
        simp only [pqInitInputs, pqInputs, encodeDir_eq_parts W st hs, List.append_assoc]
      rw [hn, hfiles, filesFold_append]
      rw [filesFold_entries_of_head_ne _ _ ["registration-id"] (fun x hx =>
        tail3_head_ne_pre W st b t hx (by decide))]
      unfold dirPre filesFold
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
      have hnr : normalizePath registrationIdFile = ["registration-id"] := by decide
      simp only [FsState.setFile, FsState.setEntry, hnr, beq_self_eq_true, ↓reduceIte]
    have hcap : (SignalSession.le32 st.me.regId).length ≤ fileCapBytes :=
      LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.le32_length_le_fileCapBytes st.me.regId
    unfold cliRd readViewF
    rw [hp, hb, hf]
    simp only [hcap, ↓reduceIte]
  unfold IdGhost.regId
  rw [hget]
  simp only [SignalSession.le32, Except.bind, le32_concat]

private theorem pathStr_idPeer (P : Party) :
    pathStr (pathOf (utf8 "identities") (utf8 (partyAddressName P))) = identityFile (partyAddressName P) := by
  rw [← String.toList_inj]
  unfold pathStr pathOf identityFile
  simp only [utf8_eq_flatMap, String.toList_ofList, String.toList_append]
  cases P <;> decide

private theorem pathStr_sessPeer (P : Party) :
    pathStr (pathOf (utf8 "sessions") (addressText (RunRefine.addrValE P))) =
      sessionFile (partyAddress P) := by
  rw [← String.toList_inj]
  unfold pathStr pathOf addressText decimalText RunRefine.addrValE sessionFile Address.text partyAddress
  have h1 : toString (1 : Nat) = "1" := rfl
  have h1' : toString (1#8).toNat = "1" := rfl
  rw [h1, h1']
  simp only [utf8_eq_flatMap, String.toList_ofList, String.toList_append]
  cases P <;> decide

private theorem ancestors_idFile (P : Party) :
    ancestors (identityFile (partyAddressName P)) = ["identities"] := by
  have hcs : pathComps (identityFile (partyAddressName P)) = ["identities".toList, (partyAddressName P).toList] := by
    unfold pathComps identityFile
    rw [String.toList_append]
    cases P <;> decide
  unfold ancestors
  rw [hcs]
  dsimp
  rw [List.map_singleton, List.take_zero, List.intercalate_singleton]

theorem idPeer_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hs : st.session = none) :
    StoresGhost.opened.identity.peer cliIo.rd (runFiles (pqInitInputs W st b t))
      (RunRefine.addrValE st.party.other) = .ok st.peerId := by
  have hb : blockingAncestorF (runFiles (pqInitInputs W st b t))
      (identityFile (partyAddressName st.party.other)) = none := by
    unfold blockingAncestorF
    rw [ancestors_idFile, List.find?_cons, runFiles_pqInit_identities W st b t hs]
    rfl
  have hnorm : normalizePath (identityFile (partyAddressName st.party.other)) =
      ["identities", partyAddressName st.party.other] := by
    cases st.party.other <;> decide
  have hne : (normalizePath (identityFile (partyAddressName st.party.other))).isEmpty = false := by
    rw [hnorm]; rfl
  have hns : normalizePath (identityFile (partyAddressName st.party.other)) ∉ stdioPaths.map normalizePath := by
    cases st.party.other <;> decide
  have hd : (pqInitInputs W st b t).dirs = partyDirs ++ [bundleDir] := rfl
  have hf : (pqInitInputs W st b t).files =
      (dirPre W st ++ dirPeer st) ++
        (dirPost W st ++ ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)])) := by
    simp only [pqInitInputs, pqInputs, encodeDir_eq_parts W st hs, List.append_assoc]
  have hget : StoresGhost.opened.identity.peers.get cliIo.rd (runFiles (pqInitInputs W st b t))
      (RunRefine.addrValE st.party.other).name =
      .ok (match st.peerId with | some k => k.serialize | none => []) := by
    change cliRd (runFiles (pqInitInputs W st b t))
      (pathOf (utf8 "identities") (utf8 (partyAddressName st.party.other))) = _
    unfold cliRd readViewF
    rw [pathStr_idPeer, hb]
    dsimp only
    rw [runFiles_eq_entries _ hne hns, hnorm, hd, hf, filesFold_append]
    rw [filesFold_entries_of_head_ne _ _ ["identities", partyAddressName st.party.other] (fun x hx =>
      tail_head_not_pre_or_id W st b t hx (by dsimp only [List.head?]; decide))]
    rw [filesFold_append]
    unfold dirPeer
    cases hp : st.peerId with
    | none =>
      rw [filesFold_nil]
      rw [filesFold_entries_of_head_ne _ _ ["identities", partyAddressName st.party.other] (fun x hx heq => by
        have hm := head_dirPre W st hx
        rw [heq] at hm
        dsimp only [List.head?] at hm
        exact absurd hm (by decide))]
      have hdir_none :
          (dirsFold (partyDirs ++ [bundleDir]) {}).entries ["identities", partyAddressName st.party.other] =
            none := by
        cases st.party.other <;> decide
      rw [hdir_none]
    | some k =>
      have hcap : k.serialize.length ≤ fileCapBytes :=
        LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.identityKey_serialize_length_le_fileCapBytes k
      rw [filesFold_singleton]
      simp only [FsState.setFile, FsState.setEntry, hnorm, beq_self_eq_true, ↓reduceIte, hcap]
  unfold IdGhost.peer
  rw [hget]
  cases hp : st.peerId with
  | none => rfl
  | some k =>
    dsimp only [bind, Except.bind]
    have hser : k.serialize = 0x05#8 :: k.publicKey.bytes.toList := rfl
    have hdec := decodeIdentityKey_serialize k
    rw [hser] at hdec ⊢
    simp only [record, hdec]

/-! ## Commit writes and pathwise `filesOf` equality -/

private theorem idPeer_ascii (P : Party) :
    ∀ bt ∈ pathOf (utf8 "identities") (utf8 (partyAddressName P)), bt.toNat < 128 := by
  unfold pathOf
  simp only [utf8_eq_flatMap]
  cases P <;> decide

private theorem sessPeer_ascii (P : Party) :
    ∀ bt ∈ pathOf (utf8 "sessions") (addressText (RunRefine.addrValE P)), bt.toNat < 128 := by
  unfold pathOf addressText decimalText RunRefine.addrValE
  have h1' : toString (1#8).toNat = "1" := rfl
  rw [h1']
  simp only [utf8_eq_flatMap]
  cases P <;> decide

private theorem namedWrites_init (P : Party) (idBytes sessBytes : List (BitVec 8)) :
    namedWrites
      ({ StoresGhost.opened with
         identity :=
           { StoresGhost.opened.identity with
             peers := StoresGhost.opened.identity.peers.put
               (RunRefine.addrValE P).name idBytes }
         sessions :=
           StoresGhost.opened.sessions.put
             (addressText (RunRefine.addrValE P)) sessBytes }).writes =
      [(identityFile (partyAddressName P), idBytes), (sessionFile (partyAddress P), sessBytes)] := by
  have hname : (RunRefine.addrValE P).name = utf8 (partyAddressName P) := rfl
  rw [hname, MainHops.namedWrites_ascii]
  · simp only [StoresGhost.writes, StoresGhost.opened, DirGhost.new, DirGhost.put,
      DirGhost.setOrPush, DirGhost.writes, List.map_nil, List.map_cons, List.nil_append,
      List.cons_append, pathStr_idPeer, pathStr_sessPeer]
  · intro pw hpw bt hbt
    simp only [StoresGhost.writes, StoresGhost.opened, DirGhost.new, DirGhost.put,
      DirGhost.setOrPush, DirGhost.writes, List.map_nil, List.map_cons, List.nil_append,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hpw
    rcases hpw with rfl | rfl
    · exact idPeer_ascii P bt hbt
    · exact sessPeer_ascii P bt hbt

private theorem filesOf_eq_of_filesFold_entries {L1 L2 : List (String × List (BitVec 8))}
    (h : ∀ k : FsPath, (filesFold L1 {}).entries k = (filesFold L2 {}).entries k) :
    filesOf L1 = filesOf L2 := by
  funext q
  unfold filesOf fsView
  split
  · rfl
  · rename_i hns
    rw [files_eq_entries, files_eq_entries]
    by_cases hemp : (normalizePath q).isEmpty = true
    · simp only [hemp, ↓reduceIte]
    · simp only [hemp]
      rw [initFsState_entries { files := L1 } (normalizePath q) hns,
          initFsState_entries { files := L2 } (normalizePath q) hns]
      change (match (filesFold L1 {}).entries (normalizePath q) with
              | some (.file bs) => some bs | _ => none) =
             (match (filesFold L2 {}).entries (normalizePath q) with
              | some (.file bs) => some bs | _ => none)
      rw [h (normalizePath q)]

private theorem filesFold_overwrite_eq
    {pre mid post extra ws : List (String × List (BitVec 8))}
    (h_pre_in : ∀ x ∈ pre, (normalizePath x.1).head? ∈ preHeads)
    (h_post_in : ∀ x ∈ post, (normalizePath x.1).head? ∈ postHeads)
    (h_other_pre : ∀ x ∈ mid ++ extra ++ ws, (normalizePath x.1).head? ∉ preHeads)
    (h_other_post : ∀ x ∈ mid ++ extra ++ ws, (normalizePath x.1).head? ∉ postHeads)
    (fs0 : FsState) (k : FsPath) :
    (filesFold (pre ++ mid ++ post ++ extra ++ ws) fs0).entries k =
      (filesFold (pre ++ mid ++ post ++ extra ++ (pre ++ ws ++ post)) fs0).entries k := by
  have h_disj : ∀ hd ∈ preHeads, hd ∉ postHeads := by
    intro hd hhd
    simp only [preHeads, List.mem_cons, List.not_mem_nil, or_false] at hhd
    rcases hhd with rfl | rfl | rfl <;> decide
  by_cases hk1 : k.head? ∈ preHeads
  · have hk_not_post : k.head? ∉ postHeads := h_disj k.head? hk1
    have h_mid_ne : ∀ x ∈ mid, (normalizePath x.1).head? ≠ k.head? :=
      fun x hx he => h_other_pre x (by simp [hx]) (he ▸ hk1)
    have h_post_ne : ∀ x ∈ post, (normalizePath x.1).head? ≠ k.head? :=
      fun x hx he => hk_not_post (he ▸ h_post_in x hx)
    have h_ext_ne : ∀ x ∈ extra, (normalizePath x.1).head? ≠ k.head? :=
      fun x hx he => h_other_pre x (by simp [hx]) (he ▸ hk1)
    have h_ws_ne : ∀ x ∈ ws, (normalizePath x.1).head? ≠ k.head? :=
      fun x hx he => h_other_pre x (by simp [hx]) (he ▸ hk1)
    simp only [List.append_assoc, filesFold_append]
    have hlhs :
        (filesFold ws (filesFold extra (filesFold post (filesFold mid (filesFold pre fs0))))).entries k =
          (filesFold pre fs0).entries k := by
      rw [filesFold_entries_of_head_ne ws _ k h_ws_ne,
          filesFold_entries_of_head_ne extra _ k h_ext_ne,
          filesFold_entries_of_head_ne post _ k h_post_ne,
          filesFold_entries_of_head_ne mid _ k h_mid_ne]
    have hrhs_in :
        (filesFold extra (filesFold post (filesFold mid (filesFold pre fs0)))).entries k =
          (filesFold pre fs0).entries k := by
      rw [filesFold_entries_of_head_ne extra _ k h_ext_ne,
          filesFold_entries_of_head_ne post _ k h_post_ne,
          filesFold_entries_of_head_ne mid _ k h_mid_ne]
    rw [hlhs,
        filesFold_entries_of_head_ne post _ k h_post_ne,
        filesFold_entries_of_head_ne ws _ k h_ws_ne,
        filesFold_congr_entry pre hrhs_in,
        filesFold_idem_entry pre fs0 k]
  · by_cases hk2 : k.head? ∈ postHeads
    · have h_pre_ne : ∀ x ∈ pre, (normalizePath x.1).head? ≠ k.head? :=
        fun x hx he => hk1 (he ▸ h_pre_in x hx)
      have h_mid_ne : ∀ x ∈ mid, (normalizePath x.1).head? ≠ k.head? :=
        fun x hx he => h_other_post x (by simp [hx]) (he ▸ hk2)
      have h_ext_ne : ∀ x ∈ extra, (normalizePath x.1).head? ≠ k.head? :=
        fun x hx he => h_other_post x (by simp [hx]) (he ▸ hk2)
      have h_ws_ne : ∀ x ∈ ws, (normalizePath x.1).head? ≠ k.head? :=
        fun x hx he => h_other_post x (by simp [hx]) (he ▸ hk2)
      simp only [List.append_assoc, filesFold_append]
      rw [filesFold_entries_of_head_ne ws _ k h_ws_ne,
          filesFold_entries_of_head_ne extra _ k h_ext_ne]
      have hlhs : (filesFold post (filesFold mid (filesFold pre fs0))).entries k =
          (filesFold post fs0).entries k :=
        filesFold_congr_entry post
          ((filesFold_entries_of_head_ne mid _ k h_mid_ne).trans
           (filesFold_entries_of_head_ne pre _ k h_pre_ne))
      rw [hlhs]
      have hrhs_in :
          (filesFold ws (filesFold pre (filesFold extra
            (filesFold post (filesFold mid (filesFold pre fs0)))))).entries k =
          (filesFold post fs0).entries k := by
        rw [filesFold_entries_of_head_ne ws _ k h_ws_ne,
            filesFold_entries_of_head_ne pre _ k h_pre_ne,
            filesFold_entries_of_head_ne extra _ k h_ext_ne,
            hlhs]
      rw [filesFold_congr_entry post hrhs_in, filesFold_idem_entry post fs0 k]
    · have h_pre_ne : ∀ x ∈ pre, (normalizePath x.1).head? ≠ k.head? :=
        fun x hx he => hk1 (he ▸ h_pre_in x hx)
      have h_post_ne : ∀ x ∈ post, (normalizePath x.1).head? ≠ k.head? :=
        fun x hx he => hk2 (he ▸ h_post_in x hx)
      let base := pre ++ mid ++ post ++ extra
      change (filesFold (base ++ ws) fs0).entries k =
        (filesFold (base ++ (pre ++ ws ++ post)) fs0).entries k
      simp only [List.append_assoc, filesFold_append]
      rw [filesFold_entries_of_head_ne post _ k h_post_ne]
      exact (filesFold_congr_entry ws (filesFold_entries_of_head_ne pre _ k h_pre_ne)).symm

private theorem filesOf_accept_eq (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hs : st.session = none)
    (x : RecordExtras) (gs : GhostState E2E.Bytes) :
    filesOf ((pqInitInputs W st b t).files ++
      namedWrites
        ({ StoresGhost.opened with
           identity :=
             { StoresGhost.opened.identity with
               peers := StoresGhost.opened.identity.peers.put
                 (RunRefine.addrValE st.party.other).name
                 (⟨⟨b.idPub⟩⟩ : IdentityKey).serialize }
           sessions :=
             StoresGhost.opened.sessions.put
               (addressText (RunRefine.addrValE st.party.other))
               (encodeRecordUnderExtras (fun _ => x) gs) }).writes) =
      filesOf ((pqInitInputs W st b t).files ++
        encodeDir W { st with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, gs) }) := by
  let ws2 : List (String × List (BitVec 8)) :=
    [(identityFile (partyAddressName st.party.other), (⟨⟨b.idPub⟩⟩ : IdentityKey).serialize),
     (sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) gs)]
  have hwrites :
      namedWrites
        ({ StoresGhost.opened with
           identity :=
             { StoresGhost.opened.identity with
               peers := StoresGhost.opened.identity.peers.put
                 (RunRefine.addrValE st.party.other).name
                 (⟨⟨b.idPub⟩⟩ : IdentityKey).serialize }
           sessions :=
             StoresGhost.opened.sessions.put
               (addressText (RunRefine.addrValE st.party.other))
               (encodeRecordUnderExtras (fun _ => x) gs) }).writes = ws2 :=
    namedWrites_init st.party.other _ _
  have hdir' :
      encodeDir W { st with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, gs) } =
        dirPre W st ++ ws2 ++ dirPost W st := by
    simp only [ws2, encodeDir, dirPre, dirPost, List.append_assoc]
    rfl
  have hfiles : (pqInitInputs W st b t).files =
      dirPre W st ++ dirPeer st ++ dirPost W st ++
        ((publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)]) := by
    simp only [pqInitInputs, pqInputs, encodeDir_eq_parts W st hs, List.append_assoc]
  have hws_heads : ∀ w ∈ ws2,
      (normalizePath w.1).head? = some "identities" ∨
      (normalizePath w.1).head? = some "sessions" := by
    intro w hw
    simp only [ws2, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · left; exact norm_head_slash_prefix "identities" _ (by decide) (by decide)
    · right; exact norm_head_slash_prefix "sessions" _ (by decide) (by decide)
  rw [hwrites, hdir', hfiles]
  refine filesOf_eq_of_filesFold_entries fun k =>
    filesFold_overwrite_eq
      (fun u hu => head_dirPre W st hu)
      (fun u hu => head_dirPost W st hu)
      (fun u hu hm => ?_)
      (fun u hu hm => ?_)
      {} k
  · rcases List.mem_append.mp hu with h12 | hw
    · rcases List.mem_append.mp h12 with hp | he
      · rw [head_dirPeer st hp] at hm; exact absurd hm (by decide)
      · have h := head_initExtra b t he
        simp only [extraHeads, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> (rw [h] at hm; exact absurd hm (by decide))
    · rcases hws_heads u hw with h | h <;> (rw [h] at hm; exact absurd hm (by decide))
  · rcases List.mem_append.mp hu with h12 | hw
    · rcases List.mem_append.mp h12 with hp | he
      · rw [head_dirPeer st hp] at hm; exact absurd hm (by decide)
      · have h := head_initExtra b t he
        simp only [extraHeads, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> (rw [h] at hm; exact absurd hm (by decide))
    · rcases hws_heads u hw with h | h <;> (rw [h] at hm; exact absurd hm (by decide))

/-! ## Master agreement theorem (`agree_pqInit`) -/

theorem agree_pqInit (X : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (_hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none) :
    let i := pqInitInputs W st b t
    let F := runFiles i
    let peer := RunRefine.addrValE st.party.other
    let bv := RunRefine.bundleVE b
    let g := StoresGhost.opened
    let ans : SlotAns Unit :=
      match g.identity.trusted cliIo.rd F peer bv.idKey with
      | .error _ => some none
      | .ok false => some none
      | .ok true =>
        match g.identity.keyPair cliIo.rd F, g.identity.regId cliIo.rd F with
        | .ok kp, .ok reg =>
          match initiateState X W st.party ⟨kp.privateKey.bytes, reg⟩ b t with
          | none => some none
          | some (x, gs) =>
            some (some ({ g with
              identity := g.identity.saveUpd cliIo.rd F peer bv.idKey
              sessions := g.sessions.put (addressText peer) (encodeRecordUnderExtras (fun _ => x) gs) },
              ()))
        | _, _ => some none
    observe i.files (finish ans (fun _ => [])) = pqxdhExpectedOutcome W i (pqInitModel X W st b t) := by
  dsimp only
  have hpeer := idPeer_pqInit W st b t hs
  have htrust : StoresGhost.opened.identity.trusted cliIo.rd
      (runFiles (pqInitInputs W st b t)) (RunRefine.addrValE st.party.other)
      (RunRefine.bundleVE b).idKey = .ok (st.trusts ⟨⟨b.idPub⟩⟩) := by
    unfold IdGhost.trusted PqParty.trusts RunRefine.bundleVE
    rw [hpeer]
    cases st.peerId <;> rfl
  rw [htrust]
  unfold pqInitModel pqxdhExpectedOutcome
  cases ht : st.trusts ⟨⟨b.idPub⟩⟩ with
  | false => rfl
  | true =>
    dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [keyPair_pqInit W st b t hs, regId_pqInit W st b t hs]
    dsimp only
    rw [initiateState_clampScalar]
    cases hinit : initiateState X W st.party st.me b t with
    | none => rfl
    | some pair =>
      rcases pair with ⟨x, gs⟩
      have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd
          (runFiles (pqInitInputs W st b t)) (RunRefine.addrValE st.party.other)
          (RunRefine.bundleVE b).idKey =
          { StoresGhost.opened.identity with
            peers := StoresGhost.opened.identity.peers.put
              (RunRefine.addrValE st.party.other).name
              (⟨⟨b.idPub⟩⟩ : IdentityKey).serialize } := by
        unfold IdGhost.saveUpd RunRefine.bundleVE
        rw [hpeer]
      dsimp only [finish, Option.map_some, observe]
      rw [hsave]
      exact congrArg (Outcome.exited 0 []) (filesOf_accept_eq W st b t hs x gs)

end CryptoVerification.SignalSession.Cli.RunProofs.InitS0
