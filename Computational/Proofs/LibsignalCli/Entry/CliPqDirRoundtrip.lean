/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch
public import LibsignalBinary.Specifications.SignalSession.SmScheme
import all Init.Data.Repr
public import LibsignalBinary.Proofs.SignalSession.PqStep
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run

/-!
# Directory roundtrip lemmas for `signal-session` on PQXDH directories

File-system roundtrip lemmas connecting `encodeDir`, `pqInputs`, and `pqxdhExpectedOutcome` to
file-level directory read-back (`readBackDir`) and `cliPqRawInputs`. Every accepted `PqStep`
preserves pre-key ID lists and candidate paths, so reading back `pqPartyCandidatePathsOf st` after
an accepted call recovers `encodeDir W st'` as an exact list equality.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-! ## Candidate file paths and input constructors -/

/-- Candidate relative file paths of a `PqParty` directory, in the order written by `encodeDir`. -/
def pqPartyCandidatePaths (party : Party)
    (spkIds opkIds otkIds lrkIds : List (BitVec 32)) : List String :=
  [addressFile, identityKeyPairFile, registrationIdFile,
   identityFile (partyAddressName party.other),
   sessionFile (partyAddress party.other)] ++
  spkIds.map signedPreKeyFile ++
  opkIds.map oneTimePreKeyFile ++
  otkIds.map oneTimeKyberPreKeyFile ++
  (lrkIds.map fun i => [lastResortKyberPreKeyFile i, baseKeysFile i]).flatten

def pqPartyCandidatePathsOf (st : PqParty) : List String :=
  pqPartyCandidatePaths st.party
    (st.signed.map (·.1))
    (st.oneTime.map (·.1))
    (st.kyberOneTime.map (·.1))
    (st.kyberLastResort.map (·.1))

/-- Candidate relative file paths of a `PqParty` directory excluding `sessions/<peer>`. -/
def pqPartyNoSessionPaths (party : Party)
    (spkIds opkIds otkIds lrkIds : List (BitVec 32)) : List String :=
  [addressFile, identityKeyPairFile, registrationIdFile,
   identityFile (partyAddressName party.other)] ++
  spkIds.map signedPreKeyFile ++
  opkIds.map oneTimePreKeyFile ++
  otkIds.map oneTimeKyberPreKeyFile ++
  (lrkIds.map fun i => [lastResortKyberPreKeyFile i, baseKeysFile i]).flatten

def pqPartyNoSessionPathsOf (st : PqParty) : List String :=
  pqPartyNoSessionPaths st.party
    (st.signed.map (·.1))
    (st.oneTime.map (·.1))
    (st.kyberOneTime.map (·.1))
    (st.kyberLastResort.map (·.1))

/-- Read back an ordered `(path, bytes)` directory list from an outcome file lookup `fs`, omitting
missing paths while keeping empty files. -/
def readBackDir (paths : List String) (fs : String → Option (List (BitVec 8))) :
    List (String × List (BitVec 8)) :=
  paths.filterMap fun p => (fs p).map fun bs => (p, bs)

/-- File-level `Inputs` constructor from an on-disk `dirFiles` list. -/
def cliPqRawInputs (cmd : Cmd) (dirFiles extra : List (String × List (BitVec 8)))
    (coins stdin : List (BitVec 8)) : Inputs :=
  { argv := cmd.argv
    dirs := partyDirs ++ (match cmd with | .init _ dir => [dir] | _ => [])
    files := dirFiles ++ extra ++ [(coinsFile, coins)]
    stdin := stdin }

def cliPqRecvInputsFromFiles (party : Party) (dirFiles : List (String × List (BitVec 8)))
    (c : List (BitVec 8)) (rc : BitVec 256) : Inputs :=
  cliPqRawInputs (.recv (partyAddress party.other)) dirFiles [] (HMAC.keyToBytes32 rc) c

/-- Pre-key ID distinctness component of `PqxdhPartyInSpecDomain`. -/
def PqDirIdsNodup (st : PqParty) : Prop :=
  (st.signed.map (·.1)).Nodup ∧
  (st.oneTime.map (·.1)).Nodup ∧
  (st.kyberOneTime.map (·.1)).Nodup ∧
  (st.kyberLastResort.map (·.1)).Nodup

theorem pqDirIdsNodup_of_wfPq {W : PEParams} {st : PqParty} (h : PqxdhPartyInSpecDomain W st) :
    PqDirIdsNodup st :=
  h.2.2

@[simp]
theorem cliPqRecvInputsFromFiles_encodeDir_eq (W : PEParams) (st : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256) :
    cliPqRecvInputsFromFiles st.party (encodeDir W st) c rc = pqRecvInputs W st c rc :=
  rfl

/-! ## Shape preservation under `PqStep` -/

private theorem map_fst_clear_opt {α β : Type} [DecidableEq α] (l : List (α × Option β)) (j : α) :
    ((l.map fun (i, k) => if i = j then (i, none) else (i, k)).map (·.1)) = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨i, k⟩; simp only [List.map_cons, ih]; split_ifs <;> rfl
private theorem map_fst_append_seen {α β γ : Type} [DecidableEq α]
    (l : List (α × β × List γ)) (j : α) (u : γ) :
    ((l.map fun (i, k, s) => if i = j then (i, k, s ++ [u]) else (i, k, s)).map (·.1)) =
      l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨i, k, s⟩; simp only [List.map_cons, ih]; split_ifs <;> rfl
private theorem some_some_fst {α β : Type} {a a' : α} {b b' : β}
    (h : some (some (a, b)) = some (some (a', b'))) : a = a' := by cases h; rfl
private theorem markKyberUsed_shape {st st1 : PqParty} {m : PreKeyMessageFields}
    (hm : markKyberUsed st m = some st1) :
    st1.party = st.party ∧ st1.me = st.me ∧ st1.signed.map (·.1) = st.signed.map (·.1) ∧
    st1.oneTime.map (·.1) = st.oneTime.map (·.1) ∧
    st1.kyberOneTime.map (·.1) = st.kyberOneTime.map (·.1) ∧
    st1.kyberLastResort.map (·.1) = st.kyberLastResort.map (·.1) := by
  unfold markKyberUsed at hm; split at hm
  · injection hm with hm'; subst hm'; exact ⟨rfl, rfl, rfl, rfl, map_fst_clear_opt _ _, rfl⟩
  · split at hm
    · cases hm
    · rename_i _ seen _; by_cases hmem : (m.spkId, m.baseKey) ∈ seen
      · simp only [hmem, or_true, ↓reduceIte] at hm; cases hm
      · simp only [hmem, or_false] at hm; split_ifs at hm; injection hm with hm'; subst hm'
        exact ⟨rfl, rfl, rfl, rfl, rfl, map_fst_append_seen _ _ _⟩
private theorem removeOpk_shape (st1 : PqParty) (m : PreKeyMessageFields) :
    (removeOpk st1 m).party = st1.party ∧ (removeOpk st1 m).me = st1.me ∧
    (removeOpk st1 m).signed.map (·.1) = st1.signed.map (·.1) ∧
    (removeOpk st1 m).oneTime.map (·.1) = st1.oneTime.map (·.1) ∧
    (removeOpk st1 m).kyberOneTime.map (·.1) = st1.kyberOneTime.map (·.1) ∧
    (removeOpk st1 m).kyberLastResort.map (·.1) = st1.kyberLastResort.map (·.1) := by
  unfold removeOpk; cases m.opkId with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some j => exact ⟨rfl, rfl, rfl, map_fst_clear_opt _ _, rfl, rfl⟩
private theorem shape_bundle_of_fields {st st' : PqParty}
    (hp : st'.party = st.party) (hme : st'.me = st.me)
    (hs : st'.signed.map (·.1) = st.signed.map (·.1))
    (ho : st'.oneTime.map (·.1) = st.oneTime.map (·.1))
    (hko : st'.kyberOneTime.map (·.1) = st.kyberOneTime.map (·.1))
    (hkl : st'.kyberLastResort.map (·.1) = st.kyberLastResort.map (·.1))
    (hpeer : st'.peerId.isSome = true) (hsess : st'.session.isSome = true) :
    st'.party = st.party ∧ st'.me = st.me ∧ st'.signed.map (·.1) = st.signed.map (·.1) ∧
    st'.oneTime.map (·.1) = st.oneTime.map (·.1) ∧
    st'.kyberOneTime.map (·.1) = st.kyberOneTime.map (·.1) ∧
    st'.kyberLastResort.map (·.1) = st.kyberLastResort.map (·.1) ∧
    pqPartyCandidatePathsOf st' = pqPartyCandidatePathsOf st ∧
    pqPartyNoSessionPathsOf st' = pqPartyNoSessionPathsOf st ∧
    st'.peerId.isSome = true ∧ st'.session.isSome = true := by
  refine ⟨hp, hme, hs, ho, hko, hkl, ?_, ?_, hpeer, hsess⟩
  · unfold pqPartyCandidatePathsOf; rw [hp, hs, ho, hko, hkl]
  · unfold pqPartyNoSessionPathsOf; rw [hp, hs, ho, hko, hkl]

/-- Every accepted `PqStep` preserves `party`, `me`, and all four pre-key ID lists, and sets both
`peerId` and `session`. -/
theorem pqStep_preserves_shape {X : UnreachedPqxdhPrimitives} {W : PEParams} {st st' : PqParty}
    (h : PqStep X W st st') :
    st'.party = st.party ∧
    st'.me = st.me ∧
    st'.signed.map (·.1) = st.signed.map (·.1) ∧
    st'.oneTime.map (·.1) = st.oneTime.map (·.1) ∧
    st'.kyberOneTime.map (·.1) = st.kyberOneTime.map (·.1) ∧
    st'.kyberLastResort.map (·.1) = st.kyberLastResort.map (·.1) ∧
    pqPartyCandidatePathsOf st' = pqPartyCandidatePathsOf st ∧
    pqPartyNoSessionPathsOf st' = pqPartyNoSessionPathsOf st ∧
    st'.peerId.isSome = true ∧
    st'.session.isSome = true := by
  cases h with
  | init b t st' out _ hinit =>
    unfold pqInitModel at hinit; cases ht : st.trusts ⟨⟨b.idPub⟩⟩
    · rw [ht] at hinit; cases hinit
    · rw [ht] at hinit; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinit
      cases hi : initiateState X W st.party st.me b t with
      | none => rw [hi] at hinit; cases hinit
      | some xg =>
        rcases xg with ⟨x, g⟩; rw [hi] at hinit; rcases some_some_fst hinit with rfl
        exact shape_bundle_of_fields rfl rfl rfl rfl rfl rfl rfl rfl
  | send m r st' out _ hsend =>
    unfold pqSendModel at hsend; cases hsess : st.session with
    | none => rw [hsess] at hsend; cases hsend
    | some xg =>
      rcases xg with ⟨x, g⟩; rw [hsess] at hsend; dsimp only at hsend
      rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).sendAddrs g.party) m r.toList g.session with ⟨err | msg, s⟩
      · rw [henc] at hsend; cases err <;> cases hsend
      · rw [henc] at hsend; dsimp only at hsend; cases hk : g.session.remoteIdentity with
        | none => rw [hk] at hsend; cases hsend
        | some k =>
          rw [hk] at hsend; dsimp only at hsend; cases ht : st.trusts k
          · rw [ht] at hsend; cases hsend
          · rw [ht] at hsend; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsend
            rcases some_some_fst hsend with rfl
            exact shape_bundle_of_fields rfl rfl rfl rfl rfl rfl rfl rfl
  | recvWhisper c rc st' out _ hrecv =>
    unfold pqRecvWhisperModel at hrecv; cases hsess : st.session with
    | none => rw [hsess] at hrecv; cases hrecv
    | some xg =>
      rcases xg with ⟨x, g⟩; rw [hsess] at hrecv; dsimp only at hrecv
      cases htry : SignalMessage.tryFrom protoSignalCodec c with
      | error _ => rw [htry] at hrecv; cases hrecv
      | ok msg =>
        rw [htry] at hrecv; dsimp only at hrecv; unfold pqxdhSessionDecryptModel at hrecv
        rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨err | pt, s⟩
        · rw [hdec] at hrecv; cases err <;> cases hrecv
        · rw [hdec] at hrecv; dsimp only at hrecv; cases hk : s.remoteIdentity with
          | none => rw [hk] at hrecv; cases hrecv
          | some k =>
            rw [hk] at hrecv; dsimp only at hrecv; cases ht : st.trusts k
            · rw [ht] at hrecv; cases hrecv
            · rw [ht] at hrecv; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrecv
              rcases some_some_fst hrecv with rfl
              exact shape_bundle_of_fields rfl rfl rfl rfl rfl rfl rfl rfl
  | recvPrekey m rc st' out _ _ hrecv =>
    unfold pqRecvPrekeyModel at hrecv
    cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
    | error _ => rw [htry] at hrecv; cases hrecv
    | ok inner =>
      rw [htry] at hrecv; dsimp only at hrecv; cases ht : st.trusts ⟨⟨m.idPub⟩⟩
      · rw [ht] at hrecv; cases hrecv
      · rw [ht] at hrecv; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrecv
        cases hsess : st.session with
        | some xg =>
          rcases xg with ⟨x, g⟩; rw [hsess] at hrecv; dsimp only at hrecv
          by_cases hm_match : PqSessionMatches x g m
          · simp only [hm_match, ↓reduceIte] at hrecv; split_ifs at hrecv
            · cases hrecv
            · rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                  ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session with ⟨err | pt, s⟩
              · rw [hdec] at hrecv; cases err <;> cases hrecv
              · rw [hdec] at hrecv; rcases some_some_fst hrecv with rfl
                exact shape_bundle_of_fields rfl rfl rfl rfl rfl rfl rfl rfl
          · simp only [hm_match, ↓reduceIte] at hrecv; cases hrecv
        | none =>
          rw [hsess] at hrecv; dsimp only at hrecv; cases hk : preKeysNamedBy st m with
          | none => rw [hk] at hrecv; cases hrecv
          | some k =>
            rw [hk] at hrecv; dsimp only at hrecv
            cases hrs : recvPrekeyState X W st.party st.me k m rc with
            | none => rw [hrs] at hrecv; cases hrecv
            | some opt =>
              cases opt with
              | none => rw [hrs] at hrecv; cases hrecv
              | some xgpt =>
                rcases xgpt with ⟨x, g, pt⟩; rw [hrs] at hrecv; dsimp only at hrecv
                cases hm : markKyberUsed st m with
                | none => rw [hm] at hrecv; cases hrecv
                | some st1 =>
                  rw [hm] at hrecv; rcases some_some_fst hrecv with rfl
                  rcases markKyberUsed_shape hm with ⟨hp1, hme1, hs1, ho1, hko1, hkl1⟩
                  rcases removeOpk_shape st1 m with ⟨hp2, hme2, hs2, ho2, hko2, hkl2⟩
                  exact shape_bundle_of_fields (hp2.trans hp1) (hme2.trans hme1)
                    (hs2.trans hs1) (ho2.trans ho1) (hko2.trans hko1) (hkl2.trans hkl1) rfl rfl

theorem pqStep_preserves_idsNodup {X : UnreachedPqxdhPrimitives} {W : PEParams} {st st' : PqParty}
    (hnd : PqDirIdsNodup st) (h : PqStep X W st st') :
    PqDirIdsNodup st' := by
  rcases pqStep_preserves_shape h with ⟨_, _, hs, ho, hko, hkl, _, _, _, _⟩
  unfold PqDirIdsNodup at hnd ⊢; rw [hs, ho, hko, hkl]; exact hnd

/-! ## Directory roundtrip theorems -/

private def digitVal : Char → Nat
  | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
  | '5' => 5 | '6' => 6 | '7' => 7 | '8' => 8 | '9' => 9 | _ => 0
private def evalDigits (acc : Nat) : List Char → Nat
  | [] => acc
  | c :: cs => evalDigits (acc * 10 + digitVal c) cs
private theorem digitVal_digitChar (d : Nat) (hd : d < 10) : digitVal (Nat.digitChar d) = d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | d + 10 => omega
private theorem evalDigits_toDigitsCore : ∀ (fuel n : Nat) (ds : List Char),
    n < fuel → evalDigits 0 (Nat.toDigitsCore 10 fuel n ds) = evalDigits n ds
  | 0, _, _, h => by omega
  | fuel + 1, n, ds, hlt => by
    have hd : digitVal (Nat.digitChar (n % 10)) = n % 10 := digitVal_digitChar (n % 10) (by omega)
    unfold Nat.toDigitsCore; dsimp only; split
    · dsimp only [evalDigits]; rw [hd]; exact congrArg (fun k => evalDigits k ds) (by omega)
    · rw [evalDigits_toDigitsCore fuel (n / 10) _ (by omega)]
      dsimp only [evalDigits]; rw [hd]; exact congrArg (fun k => evalDigits k ds) (by omega)
private theorem evalDigits_toString (n : Nat) : evalDigits 0 (toString n).toList = n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  exact evalDigits_toDigitsCore (n + 1) n [] (by omega)
private theorem toString_nat_inj {m n : Nat} (h : toString m = toString n) : m = n := by
  have hm := evalDigits_toString m; have hn := evalDigits_toString n
  rw [h] at hm; exact hm.symm.trans hn
private theorem toString_bv32_inj {i j : BitVec 32} (h : toString i.toNat = toString j.toNat) :
    i = j := BitVec.eq_of_toNat_eq (toString_nat_inj h)
private theorem toString_ne_baseKeys (m n : Nat) : toString m ≠ toString n ++ ".base-keys" := by
  intro h; have hdot := count_dot_toString m
  rw [h, String.toList_append, List.count_append, count_dot_toString] at hdot
  have hbk : (".base-keys".toList).count '.' = 1 := by decide
  omega
private theorem string_append_right_cancel {s1 s2 suf : String} (h : s1 ++ suf = s2 ++ suf) :
    s1 = s2 := by
  have hl : s1.toList ++ suf.toList = s2.toList ++ suf.toList := by
    simpa [String.toList_append] using congrArg String.toList h
  simpa [String.ofList_toList] using congrArg String.ofList (List.append_cancel_right hl)
private theorem baseKeys_seg_inj {i j : BitVec 32}
    (h : toString i.toNat ++ ".base-keys" = toString j.toNat ++ ".base-keys") : i = j :=
  toString_bv32_inj (string_append_right_cancel h)

private theorem splitSlash_go_no_slash : ∀ (cs cur : List Char), '/' ∉ cs →
    Arm64.splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by simp [Arm64.splitSlash.go]
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.Mem.head _)
    have ih := splitSlash_go_no_slash cs (c :: cur) (fun hm => h (List.Mem.tail _ hm))
    have hstep : Arm64.splitSlash.go cur (c :: cs) = Arm64.splitSlash.go (c :: cur) cs := by
      rw [Arm64.splitSlash.go.eq_def]; split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq; injection heq with h1 h2; subst h1 h2; rfl
    rw [hstep, ih]; simp [List.reverse_cons, List.append_assoc]
private theorem splitSlash_go_two : ∀ (cs1 : List Char) (cs2 cur : List Char),
    '/' ∉ cs1 → '/' ∉ cs2 →
    Arm64.splitSlash.go cur (cs1 ++ ('/' :: cs2)) =
      [String.ofList (cur.reverse ++ cs1), String.ofList cs2]
  | [], cs2, cur, _, h2 => by simp [Arm64.splitSlash.go, splitSlash_go_no_slash cs2 [] h2]
  | c :: cs1, cs2, cur, h1, h2 => by
    have hc : c ≠ '/' := fun he => h1 (he ▸ List.Mem.head _)
    have ih := splitSlash_go_two cs1 cs2 (c :: cur) (fun hm => h1 (List.Mem.tail _ hm)) h2
    have hstep : Arm64.splitSlash.go cur (c :: (cs1 ++ '/' :: cs2)) =
        Arm64.splitSlash.go (c :: cur) (cs1 ++ '/' :: cs2) := by
      rw [Arm64.splitSlash.go.eq_def]; split
      · simp_all
      · simp_all
      · rename_i _ _ _ _ heq; injection heq with h1' h2'; subst h1' h2'; rfl
    simpa [List.cons_append, List.reverse_cons, List.append_assoc] using hstep.trans ih
private theorem toDigitsCore_nonempty : ∀ (fuel n : Nat) (ds : List Char),
    ds ≠ [] → Nat.toDigitsCore 10 fuel n ds ≠ []
  | 0, _, ds, h => h
  | fuel + 1, n, ds, _ => by
    unfold Nat.toDigitsCore; dsimp only; split
    · simp
    · exact toDigitsCore_nonempty fuel (n / 10) _ (by simp)
private theorem toString_nat_toList_nonempty (n : Nat) : (toString n).toList ≠ [] := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  unfold Nat.toDigits Nat.toDigitsCore; dsimp only; split
  · simp
  · exact toDigitsCore_nonempty n (n / 10) _ (by simp)
private theorem toString_nat_mem_digit {n : Nat} {c : Char} (hc : c ∈ (toString n).toList) :
    Char.isDigit c = true := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
private theorem char_of_isDigit (c : Char) (h : Char.isDigit c = true) : c ≠ '/' ∧ c ≠ '.' := by
  refine ⟨?_, ?_⟩ <;> intro rfl <;> cases h
private theorem normalizePath_twoSeg_digit (d suf : String)
    (hd_noslash : '/' ∉ d.toList) (hd_norm : (!d.isEmpty && d != ".") = true)
    (hs_noslash : '/' ∉ suf.toList)
    (hs_head : ∃ c cs, suf.toList = c :: cs ∧ Char.isDigit c = true) :
    Arm64.normalizePath ((d ++ "/") ++ suf) = [d, suf] := by
  obtain ⟨c, cs, hsuf, hdig⟩ := hs_head; obtain ⟨_, hnotdot⟩ := char_of_isDigit c hdig
  have hplist : ((d ++ "/") ++ suf).toList = d.toList ++ ('/' :: suf.toList) := by
    rw [String.toList_append, String.toList_append]
    have hslash : "/".toList = ['/'] := by decide
    rw [hslash, List.append_assoc]; rfl
  have hsplit : Arm64.splitSlash ((d ++ "/") ++ suf) = [d, suf] := by
    unfold Arm64.splitSlash
    rw [hplist, splitSlash_go_two d.toList suf.toList [] hd_noslash hs_noslash]
    simp [String.ofList_toList]
  have hsuf_not_empty : suf.isEmpty = false := by
    rw [Bool.eq_false_iff]; intro he
    have h1 : suf = "" := by simpa [String.isEmpty_iff] using he
    subst h1; cases hsuf
  have hsuf_not_dot : (suf != ".") = true := by
    rw [bne_iff_ne]; intro he; subst he
    have hdot : ".".toList = ['.'] := by decide
    rw [hdot] at hsuf; injection hsuf with h1 _; exact hnotdot h1.symm
  unfold Arm64.normalizePath; rw [hsplit]; simp [hd_norm, hsuf_not_empty, hsuf_not_dot]
private theorem normalizePath_prekey_nat (d : String) (n : Nat)
    (hd_noslash : '/' ∉ d.toList) (hd_norm : (!d.isEmpty && d != ".") = true) :
    Arm64.normalizePath ((d ++ "/") ++ toString n) = [d, toString n] := by
  apply normalizePath_twoSeg_digit d (toString n) hd_noslash hd_norm
  · intro hm; exact (char_of_isDigit _ (toString_nat_mem_digit hm)).1 rfl
  · cases hl : (toString n).toList with
    | nil => exact absurd hl (toString_nat_toList_nonempty n)
    | cons c cs => exact ⟨c, cs, rfl, toString_nat_mem_digit (hl ▸ List.Mem.head _)⟩
private theorem normalizePath_baseKeys_nat (d : String) (n : Nat)
    (hd_noslash : '/' ∉ d.toList) (hd_norm : (!d.isEmpty && d != ".") = true) :
    Arm64.normalizePath (((d ++ "/") ++ toString n) ++ ".base-keys") =
      [d, toString n ++ ".base-keys"] := by
  have heq : ((d ++ "/") ++ toString n) ++ ".base-keys" =
      (d ++ "/") ++ (toString n ++ ".base-keys") := by simp [String.append_assoc]
  rw [heq]; apply normalizePath_twoSeg_digit d (toString n ++ ".base-keys") hd_noslash hd_norm
  · rw [String.toList_append]; intro hm; rcases List.mem_append.mp hm with h1 | h2
    · exact (char_of_isDigit _ (toString_nat_mem_digit h1)).1 rfl
    · revert h2; decide
  · rw [String.toList_append]; cases hl : (toString n).toList with
    | nil => exact absurd hl (toString_nat_toList_nonempty n)
    | cons c cs =>
      exact ⟨c, cs ++ ".base-keys".toList, rfl, toString_nat_mem_digit (hl ▸ List.Mem.head _)⟩

private theorem norm_addressFile : Arm64.normalizePath addressFile = ["address"] := by decide
private theorem norm_identityKeyPairFile :
    Arm64.normalizePath identityKeyPairFile = ["identity-key-pair"] := by decide
private theorem norm_registrationIdFile :
    Arm64.normalizePath registrationIdFile = ["registration-id"] := by decide
private theorem norm_identityFile (P : Party) :
    Arm64.normalizePath (identityFile (partyAddressName P)) = ["identities", partyAddressName P] := by cases P <;> decide
private theorem norm_sessionFile (P : Party) :
    Arm64.normalizePath (sessionFile (partyAddress P)) = ["sessions", (partyAddress P).text] := by
  cases P <;> decide
private theorem norm_signedPreKeyFile (i : BitVec 32) :
    Arm64.normalizePath (signedPreKeyFile i) = ["signed-pre-keys", toString i.toNat] :=
  normalizePath_prekey_nat "signed-pre-keys" i.toNat (by decide) (by decide)
private theorem norm_oneTimePreKeyFile (i : BitVec 32) :
    Arm64.normalizePath (oneTimePreKeyFile i) = ["one-time-pre-keys", toString i.toNat] :=
  normalizePath_prekey_nat "one-time-pre-keys" i.toNat (by decide) (by decide)
private theorem norm_oneTimeKyberPreKeyFile (i : BitVec 32) :
    Arm64.normalizePath (oneTimeKyberPreKeyFile i) =
      ["one-time-kyber-pre-keys", toString i.toNat] :=
  normalizePath_prekey_nat "one-time-kyber-pre-keys" i.toNat (by decide) (by decide)
private theorem norm_lastResortKyberPreKeyFile (i : BitVec 32) :
    Arm64.normalizePath (lastResortKyberPreKeyFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat] :=
  normalizePath_prekey_nat "last-resort-kyber-pre-keys" i.toNat (by decide) (by decide)
private theorem norm_baseKeysFile (i : BitVec 32) :
    Arm64.normalizePath (baseKeysFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat ++ ".base-keys"] :=
  normalizePath_baseKeys_nat "last-resort-kyber-pre-keys" i.toNat (by decide) (by decide)

private def rootFileNames : List String :=
  ["address", "identity-key-pair", "registration-id", "coins"]
private def subFileDirs : List String :=
  ["identities", "sessions", "signed-pre-keys", "one-time-pre-keys",
   "one-time-kyber-pre-keys", "last-resort-kyber-pre-keys", "bundle"]
private def IsValidFsKey (k : Arm64.FsPath) : Prop :=
  (∃ r, k = [r] ∧ r ∈ rootFileNames) ∨ (∃ d a, k = [d, a] ∧ d ∈ subFileDirs)
private theorem validFsKey_nonEmpty {k : Arm64.FsPath} (hk : IsValidFsKey k) :
    k.isEmpty = false := by rcases hk with ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;> rfl
private theorem validFsKey_not_stdio {k : Arm64.FsPath} (hk : IsValidFsKey k) :
    k ∉ stdioPaths.map Arm64.normalizePath := by
  rcases hk with ⟨r, rfl, hr⟩ | ⟨d, a, rfl, _⟩
  · revert r hr; decide
  · have hexp : stdioPaths.map Arm64.normalizePath = [["<stdin>"], ["<stdout>"], ["<stderr>"]] := by
      decide
    rw [hexp]; simp
private theorem root_not_in_subFileDirs {r : String} (hr : r ∈ rootFileNames) :
    r ∉ subFileDirs := by revert r hr; decide
private theorem validFsKey_not_dropLast_prefix {k₁ k₂ : Arm64.FsPath}
    (hk₁ : IsValidFsKey k₁) (hk₂ : IsValidFsKey k₂) :
    k₁ ∉ (Arm64.FsPath.nonEmptyPrefixes k₂).dropLast := by
  rcases hk₂ with ⟨r₂, rfl, _⟩ | ⟨d₂, a₂, rfl, hd₂⟩
  · intro hm; cases hm
  · show k₁ ∉ [[d₂]]; simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hk₁ with ⟨r₁, rfl, hr₁⟩ | ⟨d₁, a₁, rfl, _⟩
    · intro heq; injection heq with h1; subst h1; exact root_not_in_subFileDirs hr₁ hd₂
    · intro heq; cases heq
private theorem foldl_dir_entries_not_mem (prefs : List Arm64.FsPath) (fs : Arm64.FsState)
    (k : Arm64.FsPath) (hnin : k ∉ prefs) :
    (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k = fs.entries k := by
  induction prefs generalizing fs with
  | nil => rfl
  | cons p ps ih =>
    have hne : k ≠ p := fun he => hnin (by rw [he]; exact List.Mem.head _)
    rw [List.foldl_cons, ih _ (fun hm => hnin (List.Mem.tail _ hm))]
    simp only [Arm64.FsState.setEntry, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
private theorem filesFold_append (l₁ l₂ : List (String × List (BitVec 8))) (fs : Arm64.FsState) :
    filesFold (l₁ ++ l₂) fs = filesFold l₂ (filesFold l₁ fs) := by
  unfold filesFold; exact List.foldl_append
private theorem filesFold_entries_miss (suf : List (String × List (BitVec 8)))
    (fs : Arm64.FsState) (k : Arm64.FsPath) (hk : IsValidFsKey k)
    (hsuf : ∀ f ∈ suf, IsValidFsKey (Arm64.normalizePath f.1))
    (hnin : ∀ f ∈ suf, k ≠ Arm64.normalizePath f.1) : (filesFold suf fs).entries k = fs.entries k := by
  induction suf generalizing fs with
  | nil => rfl
  | cons f rest ih =>
    rcases f with ⟨p, bs⟩
    have hp : IsValidFsKey (Arm64.normalizePath p) := hsuf (p, bs) (List.Mem.head _)
    have hne : k ≠ Arm64.normalizePath p := hnin (p, bs) (List.Mem.head _)
    unfold filesFold at ih ⊢
    rw [List.foldl_cons,
      ih _ (fun x hx => hsuf x (List.Mem.tail _ hx)) (fun x hx => hnin x (List.Mem.tail _ hx))]
    simp only [Arm64.FsState.setFile, Arm64.FsState.setEntry, beq_false_of_ne hne,
      Bool.false_eq_true, ↓reduceIte]
    exact foldl_dir_entries_not_mem _ fs k (validFsKey_not_dropLast_prefix hk hp)
private theorem filesFold_entries_hit (pre suf : List (String × List (BitVec 8)))
    (p : String) (bs : List (BitVec 8)) (fs : Arm64.FsState)
    (hp : IsValidFsKey (Arm64.normalizePath p))
    (hsuf : ∀ f ∈ suf, IsValidFsKey (Arm64.normalizePath f.1))
    (hnin : ∀ f ∈ suf, Arm64.normalizePath p ≠ Arm64.normalizePath f.1) :
    (filesFold (pre ++ (p, bs) :: suf) fs).entries (Arm64.normalizePath p) = some (.file bs) := by
  rw [filesFold_append]; unfold filesFold; rw [List.foldl_cons]
  change (filesFold suf _).entries (Arm64.normalizePath p) = some (.file bs)
  rw [filesFold_entries_miss suf _ (Arm64.normalizePath p) hp hsuf hnin]
  simp [Arm64.FsState.setFile, Arm64.FsState.setEntry]
private theorem filesOf_eq_fileOfEntry (files : List (String × List (BitVec 8))) (p : String)
    (hp : IsValidFsKey (Arm64.normalizePath p)) :
    filesOf files p = fileOfEntry ((filesFold files {}).entries (Arm64.normalizePath p)) := by
  unfold filesOf fsView; simp only [validFsKey_not_stdio hp, ↓reduceIte]
  show fileOfEntry ((Arm64.Process.initFsState { files := files }).files p) = _
  simp only [Arm64.FsState.files, Arm64.FsState.getEntry, validFsKey_nonEmpty hp,
    Bool.false_eq_true, ↓reduceIte]; rfl
private theorem filesOf_hit (pre suf : List (String × List (BitVec 8)))
    (p : String) (bs : List (BitVec 8)) (hp : IsValidFsKey (Arm64.normalizePath p))
    (hsuf : ∀ f ∈ suf, IsValidFsKey (Arm64.normalizePath f.1))
    (hnin : ∀ f ∈ suf, Arm64.normalizePath p ≠ Arm64.normalizePath f.1) :
    filesOf (pre ++ (p, bs) :: suf) p = some bs := by
  rw [filesOf_eq_fileOfEntry _ p hp, filesFold_entries_hit pre suf p bs {} hp hsuf hnin]; rfl

private def dirGroupTag : String → Nat
  | "signed-pre-keys" => 1 | "one-time-pre-keys" => 2
  | "one-time-kyber-pre-keys" => 3 | "last-resort-kyber-pre-keys" => 4
  | "bundle" => 5 | "coins" => 6 | _ => 0
private def keyGroupTag : Arm64.FsPath → Nat
  | d :: _ => dirGroupTag d | [] => 0
private def preKeySuffix (W : PEParams) (st : PqParty) : List (String × List (BitVec 8)) :=
  (encodeDir W { st with peerId := none, session := none }).drop 3
private theorem preKeySuffix_valid_and_tag (W : PEParams) (st : PqParty) :
    ∀ f ∈ preKeySuffix W st,
      IsValidFsKey (Arm64.normalizePath f.1) ∧ 1 ≤ keyGroupTag (Arm64.normalizePath f.1) ∧
        keyGroupTag (Arm64.normalizePath f.1) ≤ 4 := by
  intro f hf; unfold preKeySuffix encodeDir at hf
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, List.mem_append, List.mem_map, List.mem_flatten] at hf
  rcases hf with ⟨⟨i, _⟩, _, rfl⟩ | ⟨⟨i, _⟩, _, rfl⟩ | ⟨⟨i, _⟩, _, rfl⟩ |
      ⟨l, ⟨⟨i, _, _⟩, _, rfl⟩, hl⟩
  · rw [norm_signedPreKeyFile]; exact ⟨Or.inr ⟨"signed-pre-keys", _, rfl, by decide⟩,
      by dsimp only [keyGroupTag]; decide, by dsimp only [keyGroupTag]; decide⟩
  · rw [norm_oneTimePreKeyFile]; exact ⟨Or.inr ⟨"one-time-pre-keys", _, rfl, by decide⟩,
      by dsimp only [keyGroupTag]; decide, by dsimp only [keyGroupTag]; decide⟩
  · rw [norm_oneTimeKyberPreKeyFile]; exact ⟨Or.inr ⟨"one-time-kyber-pre-keys", _, rfl, by decide⟩,
      by dsimp only [keyGroupTag]; decide, by dsimp only [keyGroupTag]; decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; rcases hl with rfl | rfl
    · rw [norm_lastResortKyberPreKeyFile]; exact
        ⟨Or.inr ⟨"last-resort-kyber-pre-keys", _, rfl, by decide⟩,
          by dsimp only [keyGroupTag]; decide, by dsimp only [keyGroupTag]; decide⟩
    · rw [norm_baseKeysFile]; exact ⟨Or.inr ⟨"last-resort-kyber-pre-keys", _, rfl, by decide⟩,
        by dsimp only [keyGroupTag]; decide, by dsimp only [keyGroupTag]; decide⟩

/-- When `st'` holds session `(x, g)`, `filesOf (prefixFiles ++ encodeDir W st')` at the peer
session file evaluates to `some (encodeRecordUnderExtras (fun _ => x) g)`. -/
theorem filesOf_append_encodeDir_sessionFile_eq (W : PEParams)
    (prefixFiles : List (String × List (BitVec 8)))
    (st' : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (hsess : st'.session = some (x, g)) :
    filesOf (prefixFiles ++ encodeDir W st') (sessionFile (partyAddress st'.party.other)) =
      some (encodeRecordUnderExtras (fun _ => x) g) := by
  let hdr :=
    [(addressFile, textBytes (partyAddress st'.party).text),
     (identityKeyPairFile, RecordCodecs.IdentityKeyPairStructure.encode
        ⟨djbKey (keyPairOf W.C st'.me.idPriv).publicKey.bytes, st'.me.idPriv.toList⟩),
     (registrationIdFile, le32 st'.me.regId)] ++
    (match st'.peerId with
     | some k => [(identityFile (partyAddressName st'.party.other), k.serialize)]
     | none => [])
  have henc : prefixFiles ++ encodeDir W st' =
      (prefixFiles ++ hdr) ++
        (sessionFile (partyAddress st'.party.other), encodeRecordUnderExtras (fun _ => x) g) ::
          preKeySuffix W st' := by
    cases hp : st'.peerId <;>
      simp only [encodeDir, preKeySuffix, hdr, hp, hsess, List.append_assoc, List.cons_append,
        List.nil_append, List.drop_succ_cons, List.drop_zero]
  rw [henc]
  have hsess_valid : IsValidFsKey (Arm64.normalizePath (sessionFile (partyAddress st'.party.other))) := by
    rw [norm_sessionFile]; exact Or.inr ⟨"sessions", _, rfl, by decide⟩
  have hsess_tag : keyGroupTag (Arm64.normalizePath (sessionFile (partyAddress st'.party.other))) = 0 := by
    rw [norm_sessionFile]; rfl
  apply filesOf_hit (prefixFiles ++ hdr) (preKeySuffix W st') _ _ hsess_valid
  · intro f hf; exact (preKeySuffix_valid_and_tag W st' f hf).1
  · intro f hf heq
    have htag := (preKeySuffix_valid_and_tag W st' f hf).2.1
    rw [← heq, hsess_tag] at htag; omega

theorem encodeRecordX_isEmpty_eq_false (E : Party → RecordExtras)
    (g : GhostState (List (BitVec 8))) :
    (encodeRecordUnderExtras E g).isEmpty = false :=
  rfl

/-- Splice `rec` in place of `st.session` inside `encodeDir W st`. -/
def cliPqDirRawSpec (W : PEParams) (st : PqParty) (rec : List (BitVec 8)) :
    List (String × List (BitVec 8)) :=
  let hdrOnly : PqParty :=
    { st with session := none, signed := [], oneTime := [], kyberOneTime := [],
              kyberLastResort := [] }
  encodeDir W hdrOnly ++
    (if rec.isEmpty then [] else [(sessionFile (partyAddress st.party.other), rec)]) ++
    (encodeDir W { st with session := none, peerId := none }).drop 3

/-- Extract `(sessionBytes, stdout)` on exit code `0`. -/
def cliPqAfterSpec (P : Party) : Option Outcome → Option (List (BitVec 8) × List (BitVec 8))
  | some (.exited 0 out fs) => some ((fs (sessionFile (partyAddress P.other))).getD [], out)
  | _ => none

theorem cliPqDirRawSpec_nil_eq_encodeDir (W : PEParams) (st : PqParty) :
    cliPqDirRawSpec W st [] = encodeDir W { st with session := none } := by
  unfold cliPqDirRawSpec encodeDir; simp [List.append_assoc]

theorem cliPqDirRawSpec_encodeRecordX_eq_encodeDir (W : PEParams) (st : PqParty)
    (x : RecordExtras) (g : GhostState (List (BitVec 8))) :
    cliPqDirRawSpec W st (encodeRecordUnderExtras (fun _ => x) g) =
      encodeDir W { st with session := some (x, g) } := by
  unfold cliPqDirRawSpec; rw [encodeRecordX_isEmpty_eq_false]
  unfold encodeDir; simp [List.append_assoc]

/-- Characterize `cliPqAfterSpec` on `pqxdhExpectedOutcome` across panic, rejection, and acceptance. -/
theorem cliPqAfterSpec_pqObserve_eq (W : PEParams) (P : Party) (i : Inputs)
    (r : Option (Option (PqParty × List (BitVec 8))))
    (h_ok : ∀ st' out, r = some (some (st', out)) →
      st'.party = P ∧ ∃ x' g', st'.session = some (x', g')) :
    cliPqAfterSpec P (some (pqxdhExpectedOutcome W i r)) =
      (r.join).map (fun (st', out) =>
        (match st'.session with
         | some (x', g') => encodeRecordUnderExtras (fun _ => x') g'
         | none => [], out)) := by
  unfold pqxdhExpectedOutcome; cases r with
  | none => rfl
  | some opt =>
    cases opt with
    | none => rfl
    | some pair =>
      rcases pair with ⟨st', out⟩
      obtain ⟨hP, x', g', hsess⟩ := h_ok st' out rfl; subst hP
      simp only [Option.map_some, Option.join_some, observe, cliPqAfterSpec, hsess,
        filesOf_append_encodeDir_sessionFile_eq W i.files st' x' g' hsess, Option.getD_some]

private def specPresent (spec : List (String × Option (List (BitVec 8)))) :
    List (String × List (BitVec 8)) := spec.filterMap fun (p, obs) => obs.map fun bs => (p, bs)
private theorem specPresent_append (a b : List (String × Option (List (BitVec 8)))) :
    specPresent (a ++ b) = specPresent a ++ specPresent b := List.filterMap_append
private theorem mem_split {α : Type} {x : α} {l : List α} (h : x ∈ l) : ∃ u v, l = u ++ x :: v := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact ⟨[], ys, rfl⟩
    · obtain ⟨u, v, rfl⟩ := ih hmem; exact ⟨y :: u, v, rfl⟩
private theorem nodup_split_not_mem {α : Type} {u v : List α} {x : α}
    (h : (u ++ x :: v).Nodup) : x ∉ u ∧ x ∉ v := by
  induction u with
  | nil => rw [List.nil_append] at h; exact ⟨(fun hm => nomatch hm), (List.nodup_cons.mp h).1⟩
  | cons y ys ih =>
    rw [List.cons_append] at h; obtain ⟨hy, hrest⟩ := List.nodup_cons.mp h
    obtain ⟨hnu, hnv⟩ := ih hrest; refine ⟨fun hm => ?_, hnv⟩
    rcases List.mem_cons.mp hm with rfl | hms
    · exact hy (List.mem_append_right _ (List.Mem.head _))
    · exact hnu hms
private theorem nodup_append_of_disjoint {α : Type} {a b : List α}
    (ha : a.Nodup) (hb : b.Nodup) (hdisj : ∀ x ∈ a, ∀ y ∈ b, x ≠ y) : (a ++ b).Nodup := by
  induction a with
  | nil => simpa using hb
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp ha; rw [List.cons_append]
    refine List.Nodup.cons (fun hm => ?_)
      (ih hxs fun z hz y hy => hdisj z (List.Mem.tail _ hz) y hy)
    rcases List.mem_append.mp hm with h1 | h2
    · exact hx h1
    · exact hdisj x (List.Mem.head _) x h2 rfl

private theorem mem_specPresent_mem {spec : List (String × Option (List (BitVec 8)))}
    {f : String × List (BitVec 8)} (hf : f ∈ specPresent spec) : (f.1, some f.2) ∈ spec := by
  unfold specPresent at hf; obtain ⟨⟨p, obs⟩, hmem, heq⟩ := List.mem_filterMap.mp hf
  cases obs with
  | none => cases heq
  | some bs => simp only [Option.map_some, Option.some.injEq] at heq; subst heq; exact hmem
private theorem spec_lookup_some (spec : List (String × Option (List (BitVec 8))))
    (prefixFiles : List (String × List (BitVec 8))) (p : String) (bs : List (BitVec 8))
    (hvalid : ∀ e ∈ spec, IsValidFsKey (Arm64.normalizePath e.1))
    (hnodup : (spec.map fun e => Arm64.normalizePath e.1).Nodup)
    (hmem : (p, some bs) ∈ spec) : filesOf (prefixFiles ++ specPresent spec) p = some bs := by
  obtain ⟨u, v, rfl⟩ := mem_split hmem
  have hnd' : ((u.map fun e => Arm64.normalizePath e.1) ++
      Arm64.normalizePath p :: (v.map fun e => Arm64.normalizePath e.1)).Nodup := by
    simpa [List.map_append] using hnodup
  have hnv := (nodup_split_not_mem hnd').2
  have hpres : prefixFiles ++ specPresent (u ++ (p, some bs) :: v) =
      (prefixFiles ++ specPresent u) ++ (p, bs) :: specPresent v := by
    simp [specPresent, List.filterMap_append, List.append_assoc]
  rw [hpres]; apply filesOf_hit (prefixFiles ++ specPresent u) (specPresent v) p bs
  · exact hvalid (p, some bs) (List.mem_append_right _ (List.Mem.head _))
  · intro f hf; exact hvalid (f.1, some f.2)
      (List.mem_append_right _ (List.Mem.tail _ (mem_specPresent_mem hf)))
  · intro f hf heq
    exact hnv (heq ▸ List.mem_map.mpr ⟨(f.1, some f.2), mem_specPresent_mem hf, rfl⟩)
private theorem readBackDir_of_spec (spec : List (String × Option (List (BitVec 8))))
    (fs : String → Option (List (BitVec 8))) (hfs : ∀ p obs, (p, obs) ∈ spec → fs p = obs) :
    readBackDir (spec.map Prod.fst) fs = specPresent spec := by
  unfold readBackDir specPresent; induction spec with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨p, obs⟩
    simp only [List.map_cons, List.filterMap_cons, hfs p obs (List.Mem.head _)]
    rw [ih (fun q o hm => hfs q o (List.Mem.tail _ hm))]

private def pqPreKeySpec (W : PEParams) (st : PqParty) : List (String × Option (List (BitVec 8))) :=
  (preKeySuffix W st).map fun (p, bs) => (p, some bs)
private def pqHdrNoSessSpec (W : PEParams) (st : PqParty) :
    List (String × Option (List (BitVec 8))) :=
  [(addressFile, some (textBytes (partyAddress st.party).text)),
   (identityKeyPairFile, some (RecordCodecs.IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩)),
   (registrationIdFile, some (le32 st.me.regId)),
   (identityFile (partyAddressName st.party.other), st.peerId.map IdentityKey.serialize)]
private def pqDirSpec (W : PEParams) (st : PqParty) : List (String × Option (List (BitVec 8))) :=
  pqHdrNoSessSpec W st ++
  [(sessionFile (partyAddress st.party.other),
      st.session.map fun (x, g) => encodeRecordUnderExtras (fun _ => x) g)] ++
  pqPreKeySpec W st
private theorem map_fst_lrk_enc
    (l : List (BitVec 32 × PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32))) :
    ((l.map fun (i, k, seen) =>
        [(lastResortKyberPreKeyFile i, kyberRecordBytes i k),
         (baseKeysFile i, baseKeysBytes seen)]).flatten).map Prod.fst =
      ((l.map (·.1)).map fun i => [lastResortKyberPreKeyFile i, baseKeysFile i]).flatten := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, k, seen⟩
    simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append, ih]
private theorem pqPreKeySpec_map_fst (W : PEParams) (st : PqParty) :
    (pqPreKeySpec W st).map Prod.fst =
      (st.signed.map (·.1)).map signedPreKeyFile ++ (st.oneTime.map (·.1)).map oneTimePreKeyFile ++
      (st.kyberOneTime.map (·.1)).map oneTimeKyberPreKeyFile ++
      ((st.kyberLastResort.map (·.1)).map fun i =>
        [lastResortKyberPreKeyFile i, baseKeysFile i]).flatten := by
  unfold pqPreKeySpec; rw [List.map_map]; change (preKeySuffix W st).map Prod.fst = _
  unfold preKeySuffix encodeDir
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, List.map_append, List.map_map, map_fst_lrk_enc]; rfl
private theorem pqDirSpec_map_fst (W : PEParams) (st : PqParty) :
    (pqDirSpec W st).map Prod.fst = pqPartyCandidatePathsOf st := by
  unfold pqDirSpec pqHdrNoSessSpec pqPartyCandidatePathsOf pqPartyCandidatePaths
  rw [List.map_append, List.map_append, pqPreKeySpec_map_fst]
  simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
private theorem specPresent_map_some {α : Type} (l : List α)
    (p : α → String) (b : α → List (BitVec 8)) :
    specPresent (l.map fun x => (p x, some (b x))) = l.map fun x => (p x, b x) := by
  unfold specPresent; induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, List.filterMap_cons, Option.map_some, ih]
private theorem specPresent_pqPreKeySpec (W : PEParams) (st : PqParty) :
    specPresent (pqPreKeySpec W st) = preKeySuffix W st := by
  unfold pqPreKeySpec; simpa using specPresent_map_some (preKeySuffix W st) Prod.fst Prod.snd
private theorem specPresent_pqDirSpec (W : PEParams) (st : PqParty) :
    specPresent (pqDirSpec W st) = encodeDir W st := by
  unfold pqDirSpec; rw [specPresent_append, specPresent_append, specPresent_pqPreKeySpec]
  rcases hp : st.peerId with _ | k <;> rcases hs : st.session with _ | ⟨x, g⟩ <;>
    simp only [pqHdrNoSessSpec, specPresent, preKeySuffix, encodeDir, hp, hs,
      Option.map_none, Option.map_some, List.filterMap_cons, List.filterMap_nil,
      List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]

private theorem nodup_map_prekey_keys (ids : List (BitVec 32)) (p : BitVec 32 → String)
    (d : String) (hnorm : ∀ i, Arm64.normalizePath (p i) = [d, toString i.toNat])
    (hnd : ids.Nodup) : ((ids.map p).map Arm64.normalizePath).Nodup := by
  induction ids with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨hni, hnd_rest⟩ := List.nodup_cons.mp hnd; simp only [List.map_cons, hnorm i]
    refine List.Nodup.cons (fun hm => ?_) (ih hnd_rest)
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hm; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    rw [hnorm j] at heq; injection heq with _ h2; injection h2 with hstr
    have hij := toString_bv32_inj hstr; subst hij; exact hni hj
private theorem nodup_lrk_keys (ids : List (BitVec 32)) (hnd : ids.Nodup) :
    (((ids.map fun i => [lastResortKyberPreKeyFile i, baseKeysFile i]).flatten).map
      Arm64.normalizePath).Nodup := by
  induction ids with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨hni, hnd_rest⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
      norm_lastResortKyberPreKeyFile, norm_baseKeysFile]
    refine List.Nodup.cons (fun hm => ?_) (List.Nodup.cons (fun htail => ?_) (ih hnd_rest))
    · rcases List.mem_cons.mp hm with hself | htail
      · injection hself with _ h2; injection h2 with hstr
        exact toString_ne_baseKeys i.toNat i.toNat hstr
      · obtain ⟨q, hq, heq⟩ := List.mem_map.mp htail; obtain ⟨pair, hpair, hqp⟩ := List.mem_flatten.mp hq
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hpair
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hqp; rcases hqp with rfl | rfl
        · rw [norm_lastResortKyberPreKeyFile] at heq; injection heq with _ h2; injection h2 with hstr
          have hij := toString_bv32_inj hstr; subst hij; exact hni hj
        · rw [norm_baseKeysFile] at heq; injection heq with _ h2; injection h2 with hstr
          exact toString_ne_baseKeys i.toNat j.toNat hstr.symm
    · obtain ⟨q, hq, heq⟩ := List.mem_map.mp htail; obtain ⟨pair, hpair, hqp⟩ := List.mem_flatten.mp hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hpair
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hqp; rcases hqp with rfl | rfl
      · rw [norm_lastResortKyberPreKeyFile] at heq; injection heq with _ h2; injection h2 with hstr
        exact toString_ne_baseKeys j.toNat i.toNat hstr
      · rw [norm_baseKeysFile] at heq; injection heq with _ h2; injection h2 with hstr
        have hij := baseKeys_seg_inj hstr; subst hij; exact hni hj
private theorem pqCandidatePaths_valid_and_tag (st : PqParty) :
    ∀ p ∈ pqPartyCandidatePathsOf st,
      IsValidFsKey (Arm64.normalizePath p) ∧ keyGroupTag (Arm64.normalizePath p) ≤ 4 := by
  intro p hp; unfold pqPartyCandidatePathsOf pqPartyCandidatePaths at hp
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatten, or_assoc] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl |
      ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ | ⟨l, ⟨i, _, rfl⟩, hl⟩
  · rw [norm_addressFile]; exact ⟨Or.inl ⟨"address", rfl, by decide⟩, by decide⟩
  · rw [norm_identityKeyPairFile]; exact ⟨Or.inl ⟨"identity-key-pair", rfl, by decide⟩, by decide⟩
  · rw [norm_registrationIdFile]; exact ⟨Or.inl ⟨"registration-id", rfl, by decide⟩, by decide⟩
  · rw [norm_identityFile]; exact ⟨Or.inr ⟨"identities", _, rfl, by decide⟩,
      by dsimp only [keyGroupTag]; decide⟩
  · rw [norm_sessionFile]; exact ⟨Or.inr ⟨"sessions", _, rfl, by decide⟩,
      by dsimp only [keyGroupTag]; decide⟩
  · rw [norm_signedPreKeyFile]; exact ⟨Or.inr ⟨"signed-pre-keys", _, rfl, by decide⟩,
      by dsimp only [keyGroupTag]; decide⟩
  · rw [norm_oneTimePreKeyFile]; exact ⟨Or.inr ⟨"one-time-pre-keys", _, rfl, by decide⟩,
      by dsimp only [keyGroupTag]; decide⟩
  · rw [norm_oneTimeKyberPreKeyFile]; exact ⟨Or.inr ⟨"one-time-kyber-pre-keys", _, rfl, by decide⟩,
      by dsimp only [keyGroupTag]; decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; rcases hl with rfl | rfl
    · rw [norm_lastResortKyberPreKeyFile]; exact
        ⟨Or.inr ⟨"last-resort-kyber-pre-keys", _, rfl, by decide⟩,
          by dsimp only [keyGroupTag]; decide⟩
    · rw [norm_baseKeysFile]; exact ⟨Or.inr ⟨"last-resort-kyber-pre-keys", _, rfl, by decide⟩,
        by dsimp only [keyGroupTag]; decide⟩
private theorem pqDirSpec_valid (W : PEParams) (st : PqParty) :
    ∀ e ∈ pqDirSpec W st, IsValidFsKey (Arm64.normalizePath e.1) := by
  intro e he
  have hmem : e.1 ∈ pqPartyCandidatePathsOf st := by
    rw [← pqDirSpec_map_fst W st]; exact List.mem_map.mpr ⟨e, he, rfl⟩
  exact (pqCandidatePaths_valid_and_tag st e.1 hmem).1
private theorem hdrPaths_nodup (P : Party) :
    ([addressFile, identityKeyPairFile, registrationIdFile,
      identityFile (partyAddressName P), sessionFile (partyAddress P)].map Arm64.normalizePath).Nodup := by
  cases P <;> decide
private theorem hdrPaths_tag (P : Party) (k : Arm64.FsPath)
    (hk : k ∈ [addressFile, identityKeyPairFile, registrationIdFile,
      identityFile (partyAddressName P), sessionFile (partyAddress P)].map Arm64.normalizePath) :
    keyGroupTag k < 1 := by cases P <;> revert k hk <;> decide
private theorem nodup_append_tag {a b : List Arm64.FsPath} {t : Nat}
    (h : a.Nodup ∧ ∀ x ∈ a, keyGroupTag x < t) (hb : b.Nodup) (htb : ∀ y ∈ b, keyGroupTag y = t) :
    (a ++ b).Nodup ∧ ∀ z ∈ a ++ b, keyGroupTag z < t + 1 := by
  refine ⟨nodup_append_of_disjoint h.1 hb fun x hx y hy heq => ?_, fun z hz => ?_⟩
  · have := h.2 x hx; have := htb y hy; subst heq; omega
  · rcases List.mem_append.mp hz with h1 | h2
    · have := h.2 z h1; omega
    · have := htb z h2; omega
private theorem pqDirSpec_nodup (W : PEParams) (st : PqParty) (hnd : PqDirIdsNodup st) :
    ((pqDirSpec W st).map fun e => Arm64.normalizePath e.1).Nodup := by
  have hmap : ((pqDirSpec W st).map fun e => Arm64.normalizePath e.1) =
      (pqPartyCandidatePathsOf st).map Arm64.normalizePath := by
    rw [← pqDirSpec_map_fst W st, List.map_map]; rfl
  rw [hmap]; rcases hnd with ⟨hnd_s, hnd_o, hnd_ko, hnd_kl⟩
  unfold pqPartyCandidatePathsOf pqPartyCandidatePaths; simp only [List.map_append]
  have s0 := And.intro (hdrPaths_nodup st.party.other) (hdrPaths_tag st.party.other)
  have s1 := nodup_append_tag s0
    (nodup_map_prekey_keys _ signedPreKeyFile "signed-pre-keys" norm_signedPreKeyFile hnd_s)
    (fun k hk => by
      obtain ⟨_, hp, rfl⟩ := List.mem_map.mp hk; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      rw [norm_signedPreKeyFile]; rfl)
  have s2 := nodup_append_tag s1
    (nodup_map_prekey_keys _ oneTimePreKeyFile "one-time-pre-keys" norm_oneTimePreKeyFile hnd_o)
    (fun k hk => by
      obtain ⟨_, hp, rfl⟩ := List.mem_map.mp hk; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      rw [norm_oneTimePreKeyFile]; rfl)
  have s3 := nodup_append_tag s2
    (nodup_map_prekey_keys _ oneTimeKyberPreKeyFile "one-time-kyber-pre-keys"
      norm_oneTimeKyberPreKeyFile hnd_ko)
    (fun k hk => by
      obtain ⟨_, hp, rfl⟩ := List.mem_map.mp hk; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      rw [norm_oneTimeKyberPreKeyFile]; rfl)
  exact (nodup_append_tag s3 (nodup_lrk_keys _ hnd_kl) fun k hk => by
    obtain ⟨_, hp, rfl⟩ := List.mem_map.mp hk; obtain ⟨_, hpair, hp_in⟩ := List.mem_flatten.mp hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hpair; rcases List.mem_cons.mp hp_in with rfl | h2
    · rw [norm_lastResortKyberPreKeyFile]; rfl
    · rcases List.mem_cons.mp h2 with rfl | hnil
      · rw [norm_baseKeysFile]; rfl
      · cases hnil).1
private theorem pqPreKeySpec_isSome {W : PEParams} {st : PqParty} {p : String}
    {obs : Option (List (BitVec 8))} (hm : (p, obs) ∈ pqPreKeySpec W st) :
    ∃ bs, obs = some bs := by
  obtain ⟨⟨_, bs⟩, _, heq⟩ := List.mem_map.mp hm; injection heq with _ h2; exact ⟨bs, h2.symm⟩
private theorem pqHdrNoSessSpec_isSome {W : PEParams} {st : PqParty} {p : String}
    {obs : Option (List (BitVec 8))} (hpeer : st.peerId.isSome = true)
    (hm : (p, obs) ∈ pqHdrNoSessSpec W st) : ∃ bs, obs = some bs := by
  unfold pqHdrNoSessSpec at hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h1 | h2 | h3 | h4
  · cases h1; exact ⟨_, rfl⟩
  · cases h2; exact ⟨_, rfl⟩
  · cases h3; exact ⟨_, rfl⟩
  · cases hp : st.peerId with
    | none => simp [hp] at hpeer
    | some k => simp only [hp, Option.map_some] at h4; cases h4; exact ⟨_, rfl⟩

/-- When `st'.peerId` and `st'.session` are present, `readBackDir` on
`filesOf (prefixFiles ++ encodeDir W st')` recovers `encodeDir W st'` for any `prefixFiles`. -/
theorem readBackDir_append_encodeDir_full_eq (W : PEParams)
    (prefixFiles : List (String × List (BitVec 8))) (st' : PqParty)
    (hnd : PqDirIdsNodup st')
    (hpeer : st'.peerId.isSome = true) (hsess : st'.session.isSome = true) :
    readBackDir (pqPartyCandidatePathsOf st') (filesOf (prefixFiles ++ encodeDir W st')) =
      encodeDir W st' := by
  rw [← pqDirSpec_map_fst W st']
  refine (readBackDir_of_spec (pqDirSpec W st') _ ?_).trans (specPresent_pqDirSpec W st')
  intro p obs hmem
  have hsome : ∃ bs, obs = some bs := by
    unfold pqDirSpec at hmem; rcases List.mem_append.mp hmem with hleft | hpre
    · rcases List.mem_append.mp hleft with hhdr | hs5
      · exact pqHdrNoSessSpec_isSome hpeer hhdr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs5
        cases hs : st'.session with
        | none => simp [hs] at hsess
        | some xg =>
          rcases xg with ⟨x, g⟩; simp only [hs, Option.map_some] at hs5; cases hs5; exact ⟨_, rfl⟩
    · exact pqPreKeySpec_isSome hpre
  obtain ⟨bs, rfl⟩ := hsome; rw [← specPresent_pqDirSpec W st']
  exact spec_lookup_some (pqDirSpec W st') prefixFiles p bs
    (pqDirSpec_valid W st') (pqDirSpec_nodup W st' hnd) hmem

/-- Reading back `pqPartyCandidatePathsOf st` after an accepted `PqStep X W st st'` yields
`encodeDir W st'`. -/
theorem readBackDir_pqObserve_ok_eq {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {st st' : PqParty} (prefixFiles : List (String × List (BitVec 8)))
    (hnd : PqDirIdsNodup st) (hstep : PqStep X W st st') :
    readBackDir (pqPartyCandidatePathsOf st) (filesOf (prefixFiles ++ encodeDir W st')) =
      encodeDir W st' := by
  obtain ⟨_, _, _, _, _, _, hcand, _, hpeer, hsess⟩ := pqStep_preserves_shape hstep; rw [← hcand]
  exact readBackDir_append_encodeDir_full_eq W prefixFiles st'
    (pqStep_preserves_idsNodup hnd hstep) hpeer hsess
end CryptoVerification.SignalSession
