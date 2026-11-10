/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
import all Init.Data.Repr
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
public import ProofLib.Lemmas
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import Symbolic.Proofs.Tests.Refinement.Cli.ParStdinIff -- shake: keep

/-!
# Guard Lemmas for Bob's Initial Last-Resort Kyber Pre-Key Record in `initDirs`

Proves that for every `interp` and well-formed `ProtocolSetupWF r`, Bob's initial
`last-resort-kyber-pre-keys/<kpkId>` file in `initDirs` decodes under
`SignedPreKeyRecordStructure.decode` to the record written by `bobPreKeyFiles`, whose `privateKey`
has length `3169` and leading type byte `0x08`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli

open Arm64 Arm64.Process
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (filesOf fsView stdioPaths oneTimePreKeyFile
  lastResortKyberPreKeyFile baseKeysFile filesFold dirsFold initFsState_entries)
open CryptoVerification.RecordCodecs (SignedPreKeyRecordStructure)

private theorem digitChar_props {r : Nat} (hr : r < 10) :
    Nat.digitChar r ≠ '/' ∧ Nat.digitChar r ≠ '.' := by
  match r with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | _ + 10 => omega

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

private theorem toString_nat_toList_eq (n : Nat) : (toString n).toList = Nat.toDigits 10 n := by
  change (Nat.repr n).toList = Nat.toDigits 10 n
  unfold Nat.repr
  exact String.toList_ofList

private theorem toString_nat_no_slash_dot (n : Nat) {c : Char} (hc : c ∈ (toString n).toList) :
    c ≠ '/' ∧ c ≠ '.' := by
  rw [toString_nat_toList_eq] at hc
  rcases mem_toDigitsCore (n + 1) n [] c hc with hnil | ⟨r, hr, rfl⟩
  · nomatch hnil
  · exact digitChar_props hr

private theorem toString_nat_ne_nil (n : Nat) : (toString n).toList ≠ [] := by
  rw [toString_nat_toList_eq]
  exact toDigitsCore_ne_nil (n + 1) n [] (Or.inl (Nat.succ_ne_zero n))

private theorem toString_nat_ne_dot (n : Nat) : toString n ≠ "." := by
  intro h
  have hmem : '.' ∈ (toString n).toList := by
    rw [h]
    decide
  exact (toString_nat_no_slash_dot n hmem).2 rfl

private theorem splitSlash_go_no_slash :
    ∀ (cs cur : List Char), '/' ∉ cs →
      splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by simp [splitSlash.go]
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self ..)
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
    have hc : c ≠ '/' := fun e => h1 (e ▸ List.mem_cons_self ..)
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

private theorem normalizePath_dir_sfx {d sfx : String}
    (hd_ns : '/' ∉ d.toList) (hd_ne : d.toList ≠ []) (hd_nd : d ≠ ".")
    (hs_ns : '/' ∉ sfx.toList) (hs_ne : sfx.toList ≠ []) (hs_nd : sfx ≠ ".") :
    normalizePath (d ++ "/" ++ sfx) = [d, sfx] := by
  have hl : (d ++ "/" ++ sfx).toList = d.toList ++ '/' :: sfx.toList := by
    simp [String.toList_append]
  unfold normalizePath splitSlash
  rw [hl, splitSlash_go_two hs_ns d.toList [] hd_ns, List.reverse_nil, List.nil_append,
    String.ofList_toList, String.ofList_toList]
  simp only [List.filter, seg_filter_ok hd_ne hd_nd, seg_filter_ok hs_ne hs_nd]

private theorem norm_lastResortKyberPreKeyFile (i : BitVec 32) :
    normalizePath (lastResortKyberPreKeyFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat] := by
  have heq : lastResortKyberPreKeyFile i =
      "last-resort-kyber-pre-keys" ++ "/" ++ toString i.toNat := by
    simp [lastResortKyberPreKeyFile]
  rw [heq]
  exact normalizePath_dir_sfx (by decide) (by decide) (by decide)
    (fun m => (toString_nat_no_slash_dot i.toNat m).1 rfl)
    (toString_nat_ne_nil i.toNat) (toString_nat_ne_dot i.toNat)

private theorem norm_baseKeysFile (i : BitVec 32) :
    normalizePath (baseKeysFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat ++ ".base-keys"] := by
  have heq : baseKeysFile i =
      "last-resort-kyber-pre-keys" ++ "/" ++ (toString i.toNat ++ ".base-keys") := by
    simp [baseKeysFile, String.append_assoc]
  rw [heq]
  refine normalizePath_dir_sfx (by decide) (by decide) (by decide) ?_ ?_ ?_
  · intro m
    rw [String.toList_append] at m
    rcases List.mem_append.mp m with h1 | h2
    · exact (toString_nat_no_slash_dot i.toNat h1).1 rfl
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

private theorem norm_oneTimePreKeyFile (i : BitVec 32) :
    normalizePath (oneTimePreKeyFile i) = ["one-time-pre-keys", toString i.toNat] := by
  have heq : oneTimePreKeyFile i = "one-time-pre-keys" ++ "/" ++ toString i.toNat := by
    simp [oneTimePreKeyFile]
  rw [heq]
  exact normalizePath_dir_sfx (by decide) (by decide) (by decide)
    (fun m => (toString_nat_no_slash_dot i.toNat m).1 rfl)
    (toString_nat_ne_nil i.toNat) (toString_nat_ne_dot i.toNat)

private theorem step_entries_two {d0 s0 : String} (fs : FsState) (p : String) (bs : HwBytes)
    (d s : String) (hn : normalizePath p = [d, s]) :
    ((((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile p (some (.file bs))).entries
        [d0, s0] =
      if [d0, s0] == [d, s] then some (.file bs) else fs.entries [d0, s0] := by
  simp only [FsState.setFile, hn, FsPath.nonEmptyPrefixes, List.map_cons, List.map_nil,
    List.dropLast, List.foldl_cons, List.foldl_nil, FsState.setEntry]
  cases hk2 : ([d0, s0] == [d, s]) with
  | true => rfl
  | false =>
    have hk1 : ([d0, s0] == [d]) = false := beq_false_of_ne (by simp)
    rw [hk1]
    rfl

private theorem two_not_mem_stdioPaths (d sfx : String) :
    [d, sfx] ∉ stdioPaths.map normalizePath := by
  have hlen : ∀ q ∈ stdioPaths.map normalizePath, q.length = 1 := by
    intro q hq; revert q hq; decide
  intro hm
  have h := hlen [d, sfx] hm
  nomatch h

/-- Bob's initial `last-resort-kyber-pre-keys/<kpkId>` file in `initDirs` decodes under
`SignedPreKeyRecordStructure.decode` to the exact `SignedPreKeyRecordStructure` written by
`bobPreKeyFiles`. -/
theorem initDirs_bob_lastResortKyber_decode
    (interp : ExternInterpretation) (r : ProtocolSetup) (hr : ProtocolSetupWF r) :
    ∃ bs : HwBytes,
      initDirs interp r r.bob (lastResortKyberPreKeyFile r.kpkId) = some bs ∧
      SignedPreKeyRecordStructure.decode bs = some
        ⟨r.kpkId, kyberKey (r.opaqueBytes (setupPublic r 6)),
          kyberKey (r.kyberSecB.drop 1), r.opaqueBytes (setupPublic r 7), 0⟩ := by
  obtain ⟨hne, _, _, _, hk6, hs7, hsecB, _⟩ := hr
  have hba : r.bob ≠ r.alice := hne.symm
  let m : SignedPreKeyRecordStructure :=
    ⟨r.kpkId, kyberKey (r.opaqueBytes (setupPublic r 6)),
      kyberKey (r.kyberSecB.drop 1), r.opaqueBytes (setupPublic r 7), 0⟩
  let spkPair : String × HwBytes :=
    (CryptoVerification.SignalSession.signedPreKeyFile r.spkId,
      SignedPreKeyRecordStructure.encode
        ⟨r.spkId, ecKey (pubBytes interp (secretBytes r 2)), secretBytes r 2,
          r.opaqueBytes (setupPublic r 5), 0⟩)
  let kpkPair : String × HwBytes := (lastResortKyberPreKeyFile r.kpkId, m.encode)
  let bkPair : String × HwBytes := (baseKeysFile r.kpkId, [])
  let opkList : List (String × HwBytes) :=
    if r.withOpk then
      [(oneTimePreKeyFile r.opkId,
        CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode
          ⟨r.opkId, ecKey (pubBytes interp (secretBytes r 6)), secretBytes r 6⟩)]
    else []
  let L := commonFiles interp r r.bob ++ bobPreKeyFiles interp r
  have hL : L = (commonFiles interp r r.bob ++ [spkPair]) ++ [kpkPair] ++ ([bkPair] ++ opkList) := by
    simp [L, bobPreKeyFiles, spkPair, kpkPair, bkPair, opkList, m, List.append_assoc,
      ProtocolSetup.spkSecBytes, ProtocolSetup.spkSigTerm, ProtocolSetup.pqpkPubTerm,
      ProtocolSetup.pqpkSigTerm, ProtocolSetup.opkSecBytes]
  let d0 := "last-resort-kyber-pre-keys"
  let s0 := toString r.kpkId.toNat
  have hnk : normalizePath (lastResortKyberPreKeyFile r.kpkId) = [d0, s0] :=
    norm_lastResortKyberPreKeyFile r.kpkId
  have hstdio : normalizePath (lastResortKyberPreKeyFile r.kpkId) ∉ stdioPaths.map normalizePath := by
    rw [hnk]
    exact two_not_mem_stdioPaths d0 s0
  have hfold_kpk : ∀ fs : FsState, (filesFold [kpkPair] fs).entries [d0, s0] = some (.file m.encode) := by
    intro fs
    unfold filesFold
    rw [List.foldl_cons, List.foldl_nil,
      step_entries_two fs kpkPair.1 kpkPair.2 d0 s0 hnk, beq_self_eq_true]
    rfl
  have hbk_ne : ([d0, s0] == [d0, s0 ++ ".base-keys"]) = false := by
    refine beq_false_of_ne ?_
    intro heq
    injection heq with _ hs
    injection hs with hs _
    have hl := congrArg (fun x => x.toList.length) hs
    rw [String.toList_append, List.length_append] at hl
    have h10 : ".base-keys".toList.length = 10 := by decide
    omega
  have hfold_bk : ∀ fs : FsState, (filesFold [bkPair] fs).entries [d0, s0] = fs.entries [d0, s0] := by
    intro fs
    unfold filesFold
    rw [List.foldl_cons, List.foldl_nil,
      step_entries_two fs bkPair.1 bkPair.2 d0 (s0 ++ ".base-keys") (norm_baseKeysFile r.kpkId),
      hbk_ne]
    rfl
  have hfold_opk : ∀ fs : FsState, (filesFold opkList fs).entries [d0, s0] = fs.entries [d0, s0] := by
    intro fs
    dsimp only [opkList]
    cases r.withOpk with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      unfold filesFold
      rw [List.foldl_cons, List.foldl_nil,
        step_entries_two fs (oneTimePreKeyFile r.opkId) _
          "one-time-pre-keys" (toString r.opkId.toNat) (norm_oneTimePreKeyFile r.opkId)]
      have hopk_ne : ([d0, s0] == ["one-time-pre-keys", toString r.opkId.toNat]) = false := by
        refine beq_false_of_ne ?_
        intro heq
        injection heq with hd _
        exact absurd hd (by decide)
      rw [hopk_ne]
      rfl
  have hentries : (filesFold L {}).entries [d0, s0] = some (.file m.encode) := by
    rw [hL]
    simp only [filesFold, List.foldl_append]
    change (filesFold opkList (filesFold [bkPair] (filesFold [kpkPair] _))).entries [d0, s0] = _
    rw [hfold_opk, hfold_bk, hfold_kpk]
  have hlookup : initDirs interp r r.bob (lastResortKyberPreKeyFile r.kpkId) = some m.encode := by
    simp only [initDirs, hba, ↓reduceIte]
    unfold filesOf fsView
    rw [ite_eq_right_iff.mpr (fun hm => absurd hm hstdio)]
    have hget : (Process.initFsState { files := L }).files (lastResortKyberPreKeyFile r.kpkId) =
        some (.file m.encode) := by
      simp only [FsState.files, FsState.getEntry, hnk, List.isEmpty_cons, Bool.false_eq_true,
        ↓reduceIte]
      have hstd' : [d0, s0] ∉ stdioPaths.map normalizePath := two_not_mem_stdioPaths d0 s0
      rw [initFsState_entries { files := L } [d0, s0] hstd']
      have hdir : dirsFold [] ({} : FsState) = {} := rfl
      rw [hdir]
      exact hentries
    rw [hget]
  have hpub : m.publicKey.length < 2 ^ 64 := by
    simp [m, kyberKey, ProtocolSetup.pqpkPubTerm] at hk6 ⊢; omega
  have hpriv : m.privateKey.length < 2 ^ 64 := by
    simp [m, kyberKey, hsecB]
  have hsig : m.signature.length < 2 ^ 64 := by
    simp [m, ProtocolSetup.pqpkSigTerm] at hs7 ⊢; omega
  exact ⟨m.encode, hlookup, SignedPreKeyRecordStructure.decode_encode m hpub hpriv hsig⟩

/-- Under `ProtocolSetupWF r`, Bob's `lastResortKyberPreKeyFile r.kpkId` entry in `initDirs`
decodes to a `SignedPreKeyRecordStructure` whose `privateKey` has length `3169` and leading type
byte `0x08`. -/
theorem initDirs_bob_lastResortKyber_privateKey
    (interp : ExternInterpretation) (r : ProtocolSetup) (hr : ProtocolSetupWF r) :
    ∃ (bs : HwBytes) (rec : SignedPreKeyRecordStructure),
      initDirs interp r r.bob (lastResortKyberPreKeyFile r.kpkId) = some bs ∧
      SignedPreKeyRecordStructure.decode bs = some rec ∧
      rec.privateKey.length = 3169 ∧
      rec.privateKey[0]? = some 0x08#8 := by
  obtain ⟨bs, hbs, hdec⟩ := initDirs_bob_lastResortKyber_decode interp r hr
  refine ⟨bs, _, hbs, hdec, ?_, rfl⟩
  have hsecB : r.kyberSecB.length = 3169 := hr.2.2.2.2.2.2.1
  simp [kyberKey, hsecB]

end Symbolic.Proofs.Tests.Refinement.Cli
