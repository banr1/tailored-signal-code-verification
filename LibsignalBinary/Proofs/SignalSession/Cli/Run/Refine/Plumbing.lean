/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Spec
import all Init.Data.String.Defs
import all Init.Data.Repr
import all Init.Data.List.SplitOn.Basic
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Pre-Dispatch Reduction of `runAns` on Domain Inputs

Evaluates `parseArgs`, the local `address` file (`Dir::get` at root `""`), the `coins` file, and
the `recv` wire-type dispatch (`2` for whisper, `3` for pre-key, rejection otherwise), reducing
`RunCompose.runAns S` on each PQXDH and Signal-Message domain input to the corresponding slot of `S`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunRefine

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose

/-! ## UTF-8 and string reduction helpers -/

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
      List.reverse_cons, List.append_assoc, List.singleton_append, drop_getElem_cons arr.toList i his]
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

private theorem string_ne_of_toList {s1 s2 : String} (h : s1.toList ≠ s2.toList) : s1 ≠ s2 :=
  fun e => h (congrArg String.toList e)

private theorem ne_address_of_toList {s : String} (h : s.toList.head? ≠ some 'a') :
    s ≠ "address" :=
  fun e => h (congrArg (fun x => x.toList.head?) e)

private theorem prefix_ne_address {p : String} (h : ∃ c cs, p.toList = c :: cs ∧ c ≠ 'a')
    (s : String) : p ++ s ≠ "address" := by
  obtain ⟨c, cs, hp, hc⟩ := h
  exact ne_address_of_toList (by rw [String.toList_append, hp]; simp [hc])

private theorem utf8_eq_flatMap (s : String) :
    utf8 s = (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat := by
  conv_lhs => rw [← ofList_toList_eq s]
  unfold utf8
  simp only [String.toUTF8, String.toByteArray_ofList, List.utf8Encode, toList_toByteArray_eq]

private theorem tri_utf8_eq_flatMap (s : String) :
    LibsignalTripleRatchetRepr.utf8 s =
      (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat := by
  conv_lhs => rw [← ofList_toList_eq s]
  unfold LibsignalTripleRatchetRepr.utf8
  simp only [String.toUTF8, String.toByteArray_ofList, List.utf8Encode, toList_toByteArray_eq]

private theorem pniPrefix_eq : pniPrefix = [0x50#8, 0x4e#8, 0x49#8, 0x3a#8] := by
  unfold pniPrefix
  rw [tri_utf8_eq_flatMap]
  rfl

private theorem textBytes_addrE_eq (P : Party) :
    textBytes (partyAddress P).text = bytesOfString (partyAddress P).text := by
  unfold textBytes bytesOfString
  rw [tri_utf8_eq_flatMap]
  cases P <;>
    simp only [Address.text, partyAddress, partyAddressName, String.toList_append] <;>
    rfl

/-! ## Addresses -/

private theorem addrParse_bytesOfString (P : Party) :
    addrParse uuidTryParse (bytesOfString (partyAddress P).text) = some ⟨utf8 (partyAddressName P), 1#8⟩ := by
  unfold bytesOfString addrParse serviceIdParse
  rw [pniPrefix_eq, utf8_eq_flatMap]
  cases P <;>
    simp only [Address.text, partyAddress, partyAddressName, String.toList_append] <;>
    rfl

/-- A party's address text parses to `addrValE P` (UUID bytes with device ID `1`). -/
theorem addrParse_textBytes (P : Party) :
    addrParse uuidTryParse (textBytes (partyAddress P).text) = some ⟨utf8 (partyAddressName P), 1#8⟩ := by
  rw [textBytes_addrE_eq]
  exact addrParse_bytesOfString P

/-- Every byte of a party's address text is ASCII (`< 128`). -/
theorem textBytes_addrE_ascii (P : Party) : ∀ b ∈ textBytes (partyAddress P).text, b.toNat < 128 := by
  rw [textBytes_addrE_eq]
  unfold bytesOfString
  cases P <;>
    simp only [Address.text, partyAddress, partyAddressName, String.toList_append] <;>
    decide

/-! ## Command-line parsing -/

theorem parseArgs_init (P : Party) (dir : String) :
    parseArgs uuidTryParse ((Cmd.init (partyAddress P) dir).argv.map bytesOfString) =
      some (.init ⟨utf8 (partyAddressName P), 1#8⟩ (bytesOfString dir)) := by
  have hi : bytesOfString "init" = utf8 "init" := by
    unfold bytesOfString
    rw [utf8_eq_flatMap]
    rfl
  have hk : utf8 "init" ≠ utf8 "keygen" := by
    rw [utf8_eq_flatMap, utf8_eq_flatMap]
    decide
  have ha := addrParse_bytesOfString P
  simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hi, hk, ha, Option.map_some,
    ↓reduceIte]

theorem parseArgs_send (P : Party) :
    parseArgs uuidTryParse ((Cmd.send (partyAddress P)).argv.map bytesOfString) =
      some (.send ⟨utf8 (partyAddressName P), 1#8⟩) := by
  have hs : bytesOfString "send" = utf8 "send" := by
    unfold bytesOfString
    rw [utf8_eq_flatMap]
    rfl
  have ha := addrParse_bytesOfString P
  simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hs, ha, Option.map_some,
    ↓reduceIte]

theorem parseArgs_recv (P : Party) :
    parseArgs uuidTryParse ((Cmd.recv (partyAddress P)).argv.map bytesOfString) =
      some (.recv ⟨utf8 (partyAddressName P), 1#8⟩) := by
  have hr : bytesOfString "recv" = utf8 "recv" := by
    unfold bytesOfString
    rw [utf8_eq_flatMap]
    rfl
  have hrs : utf8 "recv" ≠ utf8 "send" := by
    rw [utf8_eq_flatMap, utf8_eq_flatMap]
    decide
  have ha := addrParse_bytesOfString P
  simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hr, hrs, ha, Option.map_some,
    ↓reduceIte]

/-! ## The own `address` file (`Dir::get`, root `""`) -/

private theorem splitSlash_go_head : ∀ (cs cur : List Char),
    ∃ pre, (splitSlash.go cur cs).head? = some (String.ofList (cur.reverse ++ pre))
  | [], cur => ⟨[], by simp [splitSlash.go]⟩
  | c :: cs, cur => by
    by_cases hc : c = '/'
    · subst hc; exact ⟨[], by simp [splitSlash.go]⟩
    · have hstep : splitSlash.go cur (c :: cs) = splitSlash.go (c :: cur) cs := by
        rw [splitSlash.go.eq_def]
        split
        · simp_all
        · simp_all
        · rename_i _ _ _ _ heq
          injection heq with h1 h2
          subst h1 h2
          rfl
      obtain ⟨pre, h⟩ := splitSlash_go_head cs (c :: cur)
      exact ⟨c :: pre, by simpa [hstep, List.reverse_cons, List.append_assoc] using h⟩

private theorem norm_head_ne_address {p : String}
    (h : ∃ c cs, p.toList = c :: cs ∧ (c ≠ '/' ∧ c ≠ '.' ∧ c ≠ 'a')) :
    (normalizePath p).head? ≠ some "address" := by
  obtain ⟨c, cs, hp, hc1, hc2, hc3⟩ := h
  unfold normalizePath splitSlash
  rw [hp]
  have hstep : splitSlash.go [] (c :: cs) = splitSlash.go [c] cs := by
    rw [splitSlash.go.eq_def]
    split
    · simp_all
    · simp_all
    · rename_i _ _ _ _ heq
      injection heq with h1 h2
      subst h1 h2
      rfl
  rw [hstep]
  obtain ⟨pre, hhead⟩ := splitSlash_go_head cs [c]
  cases hgo : splitSlash.go [c] cs with
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
    have haddr : "address".toList = 'a' :: ['d', 'd', 'r', 'e', 's', 's'] := by decide
    rw [haddr] at this
    injection this with h1 _
    exact hc3 h1

private theorem prefix_norm_head_ne_address {p : String}
    (h : ∃ c cs, p.toList = c :: cs ∧ (c ≠ '/' ∧ c ≠ '.' ∧ c ≠ 'a')) (s : String) :
    (normalizePath (p ++ s)).head? ≠ some "address" := by
  obtain ⟨c, cs, hp, hc⟩ := h
  exact norm_head_ne_address ⟨c, cs ++ s.toList, by rw [String.toList_append, hp, List.cons_append], hc⟩

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

private theorem filesFold_entries_address (l : List (String × List (BitVec 8))) (fs : FsState)
    (h : ∀ x ∈ l, (normalizePath x.1).head? ≠ some "address") :
    (filesFold l fs).entries ["address"] = fs.entries ["address"] := by
  induction l generalizing fs with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨p, bs⟩ := x
    have hp : (normalizePath p).head? ≠ some "address" := h (p, bs) (List.mem_cons_self ..)
    unfold filesFold
    rw [List.foldl_cons]
    change (filesFold l _).entries ["address"] = fs.entries ["address"]
    rw [ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hne_p : ((["address"] : FsPath) == normalizePath p) = false :=
      beq_false_of_ne (fun he => hp (he ▸ rfl))
    simp only [FsState.setFile, FsState.setEntry, hne_p, Bool.false_eq_true, ↓reduceIte]
    refine foldl_setEntry_entries_of_forall_ne _ fs ["address"] fun pref hpref he => ?_
    subst he
    exact hp (head_of_mem_nonEmptyPrefixes (mem_of_mem_dropLast hpref)).symm

private theorem ownAddr_of_head {i : Inputs} {bs : List (BitVec 8)}
    {rest : List (String × List (BitVec 8))}
    (hfiles : i.files = ("address", bs) :: rest)
    (hrest : ∀ x ∈ rest, (normalizePath x.1).head? ≠ some "address")
    (hcap : bs.length ≤ fileCapBytes) :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") = .ok bs := by
  change cliRd (initFsState (cliInputs i)).files (utf8 "address") = .ok bs
  have hp : pathStr (utf8 "address") = "address" := by
    unfold pathStr
    rw [utf8_eq_flatMap]
    rfl
  have hb : blockingAncestorF (initFsState (cliInputs i)).files "address" = none := by
    unfold blockingAncestorF ancestors pathComps
    rfl
  have hf : (initFsState (cliInputs i)).files "address" = some (.file bs) := by
    have hne : (normalizePath "address").isEmpty = false := by decide
    have hns : normalizePath "address" ∉ stdioPaths.map normalizePath := by decide
    have hn : normalizePath "address" = ["address"] := by decide
    rw [files_eq_entries, ite_eq_right_iff.mpr (by simp [hne]),
      initFsState_entries (cliInputs i) (normalizePath "address") hns, hn]
    change (filesFold i.files (dirsFold i.dirs {})).entries ["address"] = some (.file bs)
    rw [hfiles]
    unfold filesFold
    rw [List.foldl_cons]
    change (filesFold rest _).entries ["address"] = some (.file bs)
    rw [filesFold_entries_address rest _ hrest]
    simp only [FsState.setFile, hn, FsState.setEntry, beq_self_eq_true, ↓reduceIte]
  unfold cliRd readViewF
  rw [hp, hb, hf]
  simp only [hcap, ↓reduceIte]

private theorem encodeDir_head_ne_address (W : PEParams) (st : PqParty) :
    ∃ rest, encodeDir W st = ("address", textBytes (partyAddress st.party).text) :: rest ∧
      ∀ x ∈ rest, (normalizePath x.1).head? ≠ some "address" := by
  refine ⟨_, rfl, fun x hx => ?_⟩
  simp at hx
  rcases hx with rfl | rfl | hx | hx | hx | hx | hx | hx
  · dsimp only; exact norm_head_ne_address ⟨_, _, rfl, by decide⟩
  · dsimp only; exact norm_head_ne_address ⟨_, _, rfl, by decide⟩
  · cases hp : st.peerId with
    | none => rw [hp] at hx; cases hx
    | some _ =>
      rw [hp] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · cases hs : st.session with
    | none => rw [hs] at hx; cases hx
    | some _ =>
      rw [hs] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · obtain ⟨_, _, _, rfl⟩ := hx
    exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · obtain ⟨_, _, _, rfl⟩ := hx
    exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · obtain ⟨_, _, _, rfl⟩ := hx
    exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · obtain ⟨_, _, _, _, rfl | rfl⟩ := hx
    · exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
    · unfold baseKeysFile
      rw [String.append_assoc]
      exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _

private theorem ownAddr_pqInputs (W : PEParams) (st : PqParty) (cmd : Cmd)
    (extra : List (String × List (BitVec 8))) (coins stdin : List (BitVec 8))
    (hextra : ∀ x ∈ extra, (normalizePath x.1).head? ≠ some "address") :
    StoresGhost.opened.identity.own.get cliIo.rd
        (runFiles (pqInputs W st cmd extra coins stdin)) (utf8 "address") =
      .ok (textBytes (partyAddress st.party).text) := by
  obtain ⟨rest, hdir, hrest⟩ := encodeDir_head_ne_address W st
  refine ownAddr_of_head (rest := rest ++ extra ++ [(coinsFile, coins)]) ?_ ?_
      (by cases st.party <;> decide +kernel)
  · simp only [pqInputs, hdir, List.cons_append]
  · intro x hx
    simp only [List.mem_append, List.mem_singleton, or_assoc] at hx
    rcases hx with hx | hx | rfl
    · exact hrest x hx
    · exact hextra x hx
    · dsimp only; exact norm_head_ne_address ⟨_, _, rfl, by decide⟩

private theorem ownAddr_smInputs (g : GhostState (List (BitVec 8))) (cmd : Cmd)
    (coins stdin : List (BitVec 8)) :
    StoresGhost.opened.identity.own.get cliIo.rd
        (runFiles (smInputs g cmd coins stdin)) (utf8 "address") =
      .ok (textBytes (partyAddress g.party).text) := by
  refine ownAddr_of_head
    (rest := [(identityFile (partyAddressName g.party.other), (partyIdentityKey g.party.other).serialize),
      (sessionFile (partyAddress g.party.other), encodeRecord g),
      (coinsFile, coins)]) rfl ?_ (by cases g.party <;> decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · dsimp only; exact norm_head_ne_address ⟨_, _, rfl, by decide⟩

theorem ownAddr_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqInitInputs W st b t))
        (utf8 "address") = .ok (textBytes (partyAddress st.party).text) := by
  refine ownAddr_pqInputs W st _ _ _ _ fun x hx => ?_
  simp only [PublicBundle.files, List.cons_append, List.nil_append, List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | rfl | hx
  · exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _
  · cases ho : (publicBundleOf b).oneTime with
    | none => rw [ho] at hx; cases hx
    | some _ =>
      rw [ho] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact prefix_norm_head_ne_address ⟨_, _, rfl, by decide⟩ _

theorem ownAddr_pqSend (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqSendInputs W st m r))
        (utf8 "address") = .ok (textBytes (partyAddress st.party).text) := by
  exact ownAddr_pqInputs W st _ [] _ _ (fun _ h => nomatch h)

theorem ownAddr_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles (pqRecvInputs W st c rc))
        (utf8 "address") = .ok (textBytes (partyAddress st.party).text) := by
  exact ownAddr_pqInputs W st _ [] _ _ (fun _ h => nomatch h)

theorem ownAddr_smSend (g : GhostState (List (BitVec 8))) (m : List (BitVec 8)) :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles (smSendInputs g m))
        (utf8 "address") = .ok (textBytes (partyAddress g.party).text) := by
  exact ownAddr_smInputs g _ _ _

theorem ownAddr_smRecv (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256) :
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles (smRecvInputs g c rc))
        (utf8 "address") = .ok (textBytes (partyAddress g.party).text) := by
  exact ownAddr_smInputs g _ _ _

/-! ## The `coins` file -/

private theorem coinsOf_snoc {i : Inputs} {l : List (String × List (BitVec 8))}
    {coins : List (BitVec 8)} (hf : i.files = l ++ [(coinsFile, coins)]) :
    MainHops.coinsOf i = coins := by
  have hns : normalizePath "coins" ∉ stdioPaths.map normalizePath := by decide
  have hne : (normalizePath "coins").isEmpty = false := by decide
  unfold MainHops.coinsOf filesOf fsView
  rw [ite_eq_right_iff.mpr (fun h => absurd h hns), files_eq_entries,
    ite_eq_right_iff.mpr (by simp [hne]),
    initFsState_entries { files := i.files } (normalizePath "coins") hns]
  change (match (filesFold i.files (dirsFold [] {})).entries (normalizePath "coins") with
    | some (.file bs) => some bs | _ => none).getD [] = coins
  rw [hf]
  unfold filesFold
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [coinsFile, FsState.setFile, FsState.setEntry, beq_self_eq_true, ↓reduceIte,
    Option.getD_some]

theorem coinsOf_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    MainHops.coinsOf (pqInitInputs W st b t) = t.toList := by
  exact coinsOf_snoc rfl

theorem coinsOf_pqSend (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) : MainHops.coinsOf (pqSendInputs W st m r) = r.toList := by
  exact coinsOf_snoc rfl

theorem coinsOf_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    MainHops.coinsOf (pqRecvInputs W st c rc) = HMAC.keyToBytes32 rc := by
  exact coinsOf_snoc rfl

theorem coinsOf_smSend (g : GhostState (List (BitVec 8))) (m : List (BitVec 8)) :
    MainHops.coinsOf (smSendInputs g m) = [] := by
  exact coinsOf_snoc rfl

theorem coinsOf_smRecv (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256) :
    MainHops.coinsOf (smRecvInputs g c rc) = HMAC.keyToBytes32 rc := by
  exact coinsOf_snoc rfl

/-! ## `runAns` reductions on domain inputs -/

theorem runAns_pqInit_eq (S : RunSem) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    runAns S (pqInitInputs W st b t) =
      match readBundleV (runFiles (pqInitInputs W st b t)) (bytesOfString bundleDir) 1#8 with
      | none => some none
      | some bv => finish (S.initiate (runFiles (pqInitInputs W st b t))
          (addrValE st.party.other) (addrValE st.party) bv t.toList) (fun _ => []) := by
  unfold runAns
  have harg : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
  rw [harg, parseArgs_init]
  dsimp only
  rw [ownAddr_pqInit]
  dsimp only
  rw [addrParse_textBytes, coinsOf_pqInit]
  rfl

theorem runAns_pqSend_eq (S : RunSem) (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    runAns S (pqSendInputs W st m r) =
      finish (S.encrypt (runFiles (pqSendInputs W st m r)) (addrValE st.party.other)
        (addrValE st.party) m r.toList) ctWire := by
  unfold runAns
  have harg : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
  rw [harg, parseArgs_send]
  dsimp only
  rw [ownAddr_pqSend]
  dsimp only
  rw [addrParse_textBytes, coinsOf_pqSend]
  rfl

theorem runAns_pqRecvWhisper_eq (S : RunSem) (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    runAns S (pqRecvInputs W st (wireWhisper :: c) rc) =
      match SignalMessage.tryFrom protoSignalCodec c with
      | .ok msg => finish (S.decryptSignal (runFiles (pqRecvInputs W st (wireWhisper :: c) rc))
          (addrValE st.party.other) (addrValE st.party) msg (HMAC.keyToBytes32 rc)) id
      | .error _ => some none := by
  unfold runAns
  have harg : (pqRecvInputs W st (wireWhisper :: c) rc).argv =
      (Cmd.recv (partyAddress st.party.other)).argv := rfl
  rw [harg, parseArgs_recv]
  dsimp only
  rw [ownAddr_pqRecv]
  dsimp only
  rw [addrParse_textBytes, coinsOf_pqRecv]
  rfl

theorem runAns_pqRecvPrekey_eq (S : RunSem) (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    runAns S (pqRecvInputs W st (wirePrekey :: c) rc) =
      match S.pksmParse c with
      | some pm => finish (S.decryptPrekey (runFiles (pqRecvInputs W st (wirePrekey :: c) rc))
          (addrValE st.party.other) (addrValE st.party) pm (HMAC.keyToBytes32 rc)) id
      | none => some none := by
  unfold runAns
  have harg : (pqRecvInputs W st (wirePrekey :: c) rc).argv =
      (Cmd.recv (partyAddress st.party.other)).argv := rfl
  rw [harg, parseArgs_recv]
  dsimp only
  rw [ownAddr_pqRecv]
  dsimp only
  rw [addrParse_textBytes, coinsOf_pqRecv]
  rfl

/-- `recv` rejects any input that is empty or whose leading byte is neither `wireWhisper` (`2`) nor
`wirePrekey` (`3`). -/
theorem runAns_pqRecvBad (S : RunSem) (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h2 : c.head? ≠ some wireWhisper) (h3 : c.head? ≠ some wirePrekey) :
    runAns S (pqRecvInputs W st c rc) = some none := by
  unfold runAns
  have harg : (pqRecvInputs W st c rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  have hin : (pqRecvInputs W st c rc).stdin = c := rfl
  rw [harg, hin, parseArgs_recv]
  dsimp only
  rw [ownAddr_pqRecv]
  dsimp only
  rw [addrParse_textBytes]
  dsimp only
  cases c with
  | nil => rfl
  | cons t _ =>
    dsimp only
    have ht2 : t ≠ 2#8 := fun h => h2 (h ▸ rfl)
    have ht3 : t ≠ 3#8 := fun h => h3 (h ▸ rfl)
    simp only [ht2, ht3, ↓reduceIte]

theorem runAns_smSend_eq (S : RunSem) (g : GhostState (List (BitVec 8))) (m : List (BitVec 8)) :
    runAns S (smSendInputs g m) =
      finish (S.encrypt (runFiles (smSendInputs g m)) (addrValE g.party.other)
        (addrValE g.party) m []) ctWire := by
  unfold runAns
  have harg : (smSendInputs g m).argv = (Cmd.send (partyAddress g.party.other)).argv := rfl
  rw [harg, parseArgs_send]
  dsimp only
  rw [ownAddr_smSend]
  dsimp only
  rw [addrParse_textBytes, coinsOf_smSend]
  rfl

theorem runAns_smRecv_eq (S : RunSem) (g : GhostState (List (BitVec 8))) (c : List (BitVec 8))
    (rc : BitVec 256) :
    runAns S (smRecvInputs g c rc) =
      match SignalMessage.tryFrom protoSignalCodec c with
      | .ok msg => finish (S.decryptSignal (runFiles (smRecvInputs g c rc))
          (addrValE g.party.other) (addrValE g.party) msg (HMAC.keyToBytes32 rc)) id
      | .error _ => some none := by
  unfold runAns
  have harg : (smRecvInputs g c rc).argv = (Cmd.recv (partyAddress g.party.other)).argv := rfl
  rw [harg, parseArgs_recv]
  dsimp only
  rw [ownAddr_smRecv]
  dsimp only
  rw [addrParse_textBytes, coinsOf_smRecv]
  rfl

end CryptoVerification.SignalSession.Cli.RunRefine
